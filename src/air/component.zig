//! A Stwo component whose constraints are an `ir.Air`, evaluated by the shared
//! interpreter on both the verifier side (out-of-domain point) and the prover
//! side (composition over the evaluation domain).
//!
//! Lookups (IR v2) add an interaction tree: `nBatches` secure columns (4 limbs each) holding
//! Stwo's LogUp cumulative sums; `logupConstraintValues` is the formula proven sound in
//! lean/StarkedAir/LogUp.lean (`logup_sum`). In a system, components share the trees and each
//! reads its own columns from `pre_offset`, `main_offset` and `inter_offset`.
//!
//! v0 restrictions, checked in `init`:
//! - Every column of a component has 2^log_size rows. In a system of mixed sizes (D-045) stwo-zig
//!   lifts the smaller components to the largest, `max_log_degree_bound`: masks step by the
//!   max domain's generator and the quotient divides by Z_max(p) (= Z_n(π^k p)).
//! - Preprocessed columns are only read at offset 0. stwo-zig samples
//!   preprocessed columns at the OODS point alone.
//! - Constraint degree ≤ 3, so the composition fits in a 2^(log_size+1) domain.

const std = @import("std");
const ir = @import("ir.zig");
const interp = @import("interp.zig");
const core_air_accumulation = @import("stwo_core").air.accumulation;
const core_air_components = @import("stwo_core").air.components;
const core_air_derive = @import("stwo_core").air.derive;
const core_constraints = @import("stwo_core").constraints;
const canonic = @import("stwo_core").poly.circle.canonic;
const utils = @import("stwo_core").utils;
const M31 = @import("stwo_core").fields.m31.M31;
const QM31 = @import("stwo_core").fields.qm31.QM31;
const CirclePointQM31 = @import("stwo_core").circle.CirclePointQM31;
const prover_air_accumulation = @import("stwo_prover_engine").air.accumulation;
const prover_component = @import("stwo_prover_engine").air.component_prover;
const prover_circle = @import("stwo_prover_engine").poly.circle;
const prover_twiddles = @import("stwo_prover_engine").poly.twiddles;

pub const MAX_DEGREE: u32 = 3;
/// Largest lookup tuple (values after the relation id).
pub const MAX_LOOKUP_VALS: usize = 32;

/// LogUp parameters, known once the lookup elements are drawn.
pub const Logup = struct {
    z: QM31,
    alpha: QM31,
    claimed_sum: QM31,
};

/// Secure interaction columns: one per pair of lookups.
pub fn nBatches(air: ir.Air) usize {
    return (air.lookups.len + 1) / 2;
}

/// `Σ eᵢ αⁱ − z` over `e = (rel, vals…)`.
pub fn denominator(rel: u32, vals: []const QM31, z: QM31, alpha: QM31) QM31 {
    var acc = QM31.zero();
    var i = vals.len;
    while (i > 0) {
        i -= 1;
        acc = acc.mul(alpha).add(vals[i]);
    }
    acc = acc.mul(alpha).add(QM31.fromBase(M31.fromCanonical(rel)));
    return acc.sub(z);
}

/// The LogUp constraints of one row (Lean `logup_sum`): batch `b` pairs lookups `2b, 2b+1`;
/// `S` are the secure columns at the row, `s_prev` the last one at the previous row, `shift` is
/// `claimed_sum / 2^log_size`.
pub fn logupConstraintValues(mults: []const QM31, dens: []const QM31, S: []const QM31, s_prev: QM31, shift: QM31, out: []QM31) void {
    const n_batches = S.len;
    for (0..n_batches) |b| {
        const j = 2 * b;
        const pair = j + 1 < mults.len;
        const N = if (pair) mults[j].mul(dens[j + 1]).add(mults[j + 1].mul(dens[j])) else mults[j];
        const D = if (pair) dens[j].mul(dens[j + 1]) else dens[j];
        const diff = if (b + 1 < n_batches)
            S[b].sub(if (b == 0) QM31.zero() else S[b - 1])
        else
            S[b].sub(s_prev).sub(if (n_batches == 1) QM31.zero() else S[n_batches - 2]).add(shift);
        out[b] = diff.mul(D).sub(N);
    }
}

pub const Component = struct {
    allocator: std.mem.Allocator,
    air: ir.Air,
    log_size: u32,
    /// Public input values (canonical M31).
    pubs: []const M31,
    /// Sorted distinct offsets read from each main column.
    main_offsets: [][]i32,
    /// First column of this component in each tree (a system concatenates its components).
    pre_offset: usize = 0,
    main_offset: usize = 0,
    inter_offset: usize = 0,
    /// Trees in the proof: 2, or 3 when the system has an interaction tree.
    n_trees: usize = 2,
    /// Set once the lookup elements are drawn; required when the AIR has lookups.
    logup: ?Logup = null,
    /// Row-tiled expansion of coefficient-only columns in the composition (compact storage).
    tiling: ?Tiling = null,

    const Adapter = core_air_derive.ComponentAdapter(
        @This(),
        prover_component.ComponentProver,
        prover_component.Trace,
        prover_air_accumulation.DomainEvaluationAccumulator,
    );

    pub fn init(allocator: std.mem.Allocator, air: ir.Air, log_size: u32, pubs: []const M31) !Component {
        try air.validate();
        if (pubs.len != air.n_pub) return error.PublicInputCountMismatch;
        if (try air.maxConstraintDegree(allocator) > MAX_DEGREE) return error.DegreeTooHigh;
        for (air.exprs) |e| switch (e) {
            .col => |c| if (c.tree == .preprocessed and c.offset != 0)
                return error.PreprocessedOffsetUnsupported,
            else => {},
        };
        for (air.lookups) |l| if (l.vals.len > MAX_LOOKUP_VALS) return error.LookupTooWide;
        if (air.lookups.len != 0) {
            // (S − …)·D − N must have degree ≤ 3: deg D + 1 ≤ 3 and deg N ≤ 3.
            const deg = try air.degrees(allocator);
            defer allocator.free(deg);
            var b: usize = 0;
            while (2 * b < air.lookups.len) : (b += 1) {
                var dd: u32 = 0;
                var nd: u32 = 0;
                const pair = 2 * b + 1 < air.lookups.len;
                const l0 = air.lookups[2 * b];
                var d0: u32 = 0;
                for (l0.vals) |v| d0 = @max(d0, deg[v]);
                if (pair) {
                    const l1 = air.lookups[2 * b + 1];
                    var d1: u32 = 0;
                    for (l1.vals) |v| d1 = @max(d1, deg[v]);
                    dd = d0 + d1;
                    nd = @max(deg[l0.mult] + d1, deg[l1.mult] + d0);
                } else {
                    dd = d0;
                    nd = deg[l0.mult];
                }
                if (dd + 1 > MAX_DEGREE or nd > MAX_DEGREE) return error.LookupDegreeTooHigh;
            }
        }
        return .{
            .allocator = allocator,
            .air = air,
            .log_size = log_size,
            .pubs = pubs,
            .main_offsets = try air.columnOffsets(allocator, .main),
        };
    }

    pub fn deinit(self: *Component) void {
        for (self.main_offsets) |o| self.allocator.free(o);
        self.allocator.free(self.main_offsets);
    }

    pub fn asVerifierComponent(self: *const @This()) core_air_components.Component {
        return Adapter.asVerifierComponent(self);
    }

    pub fn asProverComponent(self: *const @This()) prover_component.ComponentProver {
        return Adapter.asProverComponent(self);
    }

    pub fn nConstraints(self: *const @This()) usize {
        return self.air.constraints.len + nBatches(self.air);
    }

    fn claimedShift(self: *const @This()) !QM31 {
        return self.logup.?.claimed_sum.divM31(M31.fromU64(@as(u64, 1) << @intCast(self.log_size)));
    }

    pub fn maxConstraintLogDegreeBound(self: *const @This()) u32 {
        return self.log_size + 1;
    }

    pub fn traceLogDegreeBounds(
        self: *const @This(),
        allocator: std.mem.Allocator,
    ) !core_air_components.TraceLogDegreeBounds {
        const pre = try allocator.alloc(u32, self.air.n_preprocessed);
        errdefer allocator.free(pre);
        @memset(pre, self.log_size);
        const main = try allocator.alloc(u32, self.air.n_main);
        errdefer allocator.free(main);
        @memset(main, self.log_size);
        if (self.n_trees == 2) return core_air_components.TraceLogDegreeBounds.initOwned(
            try allocator.dupe([]u32, &.{ pre, main }),
        );
        const inter = try allocator.alloc(u32, 4 * nBatches(self.air));
        errdefer allocator.free(inter);
        @memset(inter, self.log_size);
        return core_air_components.TraceLogDegreeBounds.initOwned(
            try allocator.dupe([]u32, &.{ pre, main, inter }),
        );
    }

    pub fn maskPoints(
        self: *const @This(),
        allocator: std.mem.Allocator,
        point: CirclePointQM31,
        max_log_degree_bound: u32,
    ) !core_air_components.MaskPoints {
        if (max_log_degree_bound < self.log_size) return error.InvalidLogSize;
        const step = canonic.CanonicCoset.new(max_log_degree_bound).coset_value.step;
        const pre = try allocator.alloc([]CirclePointQM31, self.air.n_preprocessed);
        for (pre) |*col| col.* = try allocator.dupe(CirclePointQM31, &.{point});
        const main = try allocator.alloc([]CirclePointQM31, self.air.n_main);
        for (main, self.main_offsets) |*col, offsets| {
            col.* = try allocator.alloc(CirclePointQM31, offsets.len);
            for (col.*, offsets) |*p, off| {
                const shift = step.mulSigned(@as(isize, off));
                p.* = point.add(.{ .x = QM31.fromBase(shift.x), .y = QM31.fromBase(shift.y) });
            }
        }
        if (self.n_trees == 2) return core_air_components.MaskPoints.initOwned(
            try allocator.dupe([][]CirclePointQM31, &.{ pre, main }),
        );
        // Cumulative sums: every limb at the point; the last secure column also at the previous row.
        const n_inter = 4 * nBatches(self.air);
        const inter = try allocator.alloc([]CirclePointQM31, n_inter);
        const back = step.mulSigned(-1);
        const prev = point.add(.{ .x = QM31.fromBase(back.x), .y = QM31.fromBase(back.y) });
        for (inter, 0..) |*col, k| col.* = if (k + 4 >= n_inter)
            try allocator.dupe(CirclePointQM31, &.{ prev, point })
        else
            try allocator.dupe(CirclePointQM31, &.{point});
        return core_air_components.MaskPoints.initOwned(
            try allocator.dupe([][]CirclePointQM31, &.{ pre, main, inter }),
        );
    }

    pub fn preprocessedColumnIndices(self: *const @This(), allocator: std.mem.Allocator) ![]usize {
        const out = try allocator.alloc(usize, self.air.n_preprocessed);
        for (out, 0..) |*v, i| v.* = self.pre_offset + i;
        return out;
    }

    const PointCtx = struct {
        pre: []const []const QM31,
        main: []const []const QM31,
        offsets: []const []const i32,

        pub fn read(self: *const PointCtx, tree: ir.Tree, index: u32, offset: i32) QM31 {
            return switch (tree) {
                .preprocessed => self.pre[index][0],
                .main => self.main[index][std.mem.indexOfScalar(i32, self.offsets[index], offset).?],
            };
        }
    };

    pub fn evaluateConstraintQuotientsAtPoint(
        self: *const @This(),
        point: CirclePointQM31,
        mask: *const core_air_components.MaskValues,
        accumulator: *core_air_accumulation.PointEvaluationAccumulator,
        max_log_degree_bound: u32,
    ) !void {
        if (max_log_degree_bound < self.log_size) return error.InvalidLogSize;
        const n_pre = self.air.n_preprocessed;
        const n_main = self.air.n_main;
        const n_inter = 4 * nBatches(self.air);
        if (mask.items.len < self.n_trees or mask.items[0].len < self.pre_offset + n_pre or
            mask.items[1].len < self.main_offset + n_main) return error.InvalidProofShape;
        const pre_mask = mask.items[0][self.pre_offset..][0..n_pre];
        const main_mask = mask.items[1][self.main_offset..][0..n_main];
        for (pre_mask) |c| if (c.len != 1) return error.InvalidProofShape;
        for (main_mask, self.main_offsets) |c, o| if (c.len != o.len) return error.InvalidProofShape;

        const scratch = try self.allocator.alloc(QM31, self.air.exprs.len);
        defer self.allocator.free(scratch);
        const out = try self.allocator.alloc(QM31, self.air.constraints.len);
        defer self.allocator.free(out);
        const ctx = PointCtx{
            .pre = @ptrCast(pre_mask),
            .main = @ptrCast(main_mask),
            .offsets = @ptrCast(self.main_offsets),
        };
        interp.evalConstraints(QM31, self.air, self.pubs, scratch, &ctx, out);

        // Lifted: Z_n(π^k p) = Z_N(p) for the max size N.
        const denominator_inv = try core_constraints.cosetVanishing(
            QM31,
            canonic.CanonicCoset.new(max_log_degree_bound).coset(),
            point,
        ).inv();
        for (out) |c| accumulator.accumulate(c.mul(denominator_inv));
        if (n_inter == 0) return;

        // LogUp.
        if (self.n_trees != 3 or mask.items[2].len < self.inter_offset + n_inter) return error.InvalidProofShape;
        const lu = self.logup orelse return error.MissingLookupElements;
        const inter_mask = mask.items[2][self.inter_offset..][0..n_inter];
        for (inter_mask, 0..) |c, k| if (c.len != (if (k + 4 >= n_inter) @as(usize, 2) else 1)) return error.InvalidProofShape;
        const nl = self.air.lookups.len;
        const B = nBatches(self.air);
        const buf = try self.allocator.alloc(QM31, 2 * nl + 2 * B + MAX_LOOKUP_VALS);
        defer self.allocator.free(buf);
        const mults = buf[0..nl];
        const dens = buf[nl..][0..nl];
        const S = buf[2 * nl ..][0..B];
        const lout = buf[2 * nl + B ..][0..B];
        const vals = buf[2 * nl + 2 * B ..][0..MAX_LOOKUP_VALS];
        for (self.air.lookups, mults, dens) |l, *m, *d| {
            if (l.vals.len > vals.len) return error.LookupTooWide;
            m.* = scratch[l.mult];
            for (l.vals, 0..) |v, i| vals[i] = scratch[v];
            d.* = denominator(l.rel, vals[0..l.vals.len], lu.z, lu.alpha);
        }
        for (S, 0..) |*sv, b| {
            const at: usize = if (b + 1 == B) 1 else 0;
            sv.* = QM31.fromPartialEvals(.{ inter_mask[4 * b][at], inter_mask[4 * b + 1][at], inter_mask[4 * b + 2][at], inter_mask[4 * b + 3][at] });
        }
        const last = 4 * (B - 1);
        const s_prev = QM31.fromPartialEvals(.{ inter_mask[last][0], inter_mask[last + 1][0], inter_mask[last + 2][0], inter_mask[last + 3][0] });
        logupConstraintValues(mults, dens, S, s_prev, try self.claimedShift(), lout);
        for (lout) |c| accumulator.accumulate(c.mul(denominator_inv));
    }

    pub fn evaluateConstraintQuotientsOnDomain(
        self: *const @This(),
        trace: *const prover_component.Trace,
        accumulator: *prover_air_accumulation.DomainEvaluationAccumulator,
    ) !void {
        const n_inter = 4 * nBatches(self.air);
        if (trace.polys.items.len < self.n_trees or trace.polys.items[0].len < self.pre_offset + self.air.n_preprocessed or
            trace.polys.items[1].len < self.main_offset + self.air.n_main or
            (n_inter != 0 and trace.polys.items[2].len < self.inter_offset + n_inter)) return error.InvalidProofShape;
        const allocator = accumulator.allocator;
        const eval_log_size = self.log_size + 1;
        const eval_domain = canonic.CanonicCoset.new(eval_log_size).circleDomain();
        const eval_size = eval_domain.size();

        var columns = try accumulator.columns(allocator, &.{.{
            .log_size = eval_log_size,
            .n_cols = self.nConstraints(),
        }});
        defer allocator.free(columns);
        const column = &columns[0];
        const values = try allocator.alloc(QM31, eval_size);
        defer allocator.free(values);
        var table = try ReadTable.init(allocator, self);
        defer table.deinit(allocator);

        // Coefficient-only columns (compact storage) expanded a row tile at a time.
        if (self.tiling) |tiling| {
            if (try tiling.plan(tiling.ctx, trace)) |plan| {
                defer tiling.release(tiling.ctx);
                for (0..plan.tiles) |tile| {
                    try tiling.load(tiling.ctx, tile);
                    try table.resolve(self, .{ .tiling = tiling });
                    try self.evaluateRows(allocator, &table, column.random_coeff_powers, tile * plan.rows, (tile + 1) * plan.rows, values);
                }
                for (values, 0..) |v, row| column.accumulate(row, v);
                return;
            }
        }

        // Whole columns on the evaluation domain (extending coefficient-only ones).
        var buffers = std.ArrayList([]M31).empty;
        defer {
            for (buffers.items) |b| allocator.free(b);
            buffers.deinit(allocator);
        }
        const n_cols = self.air.n_preprocessed + self.air.n_main + n_inter;
        const whole = try allocator.alloc([]const M31, n_cols);
        defer allocator.free(whole);
        const Span = struct { offset: usize, n: usize };
        const trees = [3]Span{
            .{ .offset = self.pre_offset, .n = self.air.n_preprocessed },
            .{ .offset = self.main_offset, .n = self.air.n_main },
            .{ .offset = self.inter_offset, .n = n_inter },
        };
        var k: usize = 0;
        for (trees, 0..) |t, tree| {
            if (t.n == 0) continue;
            for (trace.polys.items[tree][t.offset..][0..t.n]) |poly| {
                whole[k] = try onDomain(allocator, poly, self.log_size, eval_log_size, eval_size, &buffers);
                k += 1;
            }
        }
        if (buffers.items.len != 0) {
            var twiddles = try prover_twiddles.precomputeM31(allocator, eval_domain.half_coset);
            defer prover_twiddles.deinitM31(allocator, &twiddles);
            const view = prover_twiddles.TwiddleTree([]const M31).init(
                twiddles.root_coset,
                twiddles.twiddles,
                twiddles.itwiddles,
            );
            try prover_circle.poly.evaluateBuffersWithTwiddles(buffers.items, eval_domain, view);
        }
        try table.resolve(self, .{ .whole = whole });
        try self.evaluateRows(allocator, &table, column.random_coeff_powers, 0, eval_size, values);
        for (values, 0..) |v, row| column.accumulate(row, v);
    }

    /// Evaluates rows `[start, end)` of the evaluation domain into `values` (threads over rows).
    fn evaluateRows(self: *const @This(), allocator: std.mem.Allocator, table: *const ReadTable, powers: []const QM31, start: usize, end: usize, values: []QM31) !void {
        const eval_log_size = self.log_size + 1;
        const n_inter = 4 * nBatches(self.air);
        const trace_coset = canonic.CanonicCoset.new(self.log_size).coset();
        const eval_domain = canonic.CanonicCoset.new(eval_log_size).circleDomain();
        const denominator_inv = [_]M31{
            try core_constraints.cosetVanishing(M31, trace_coset, eval_domain.at(0)).inv(),
            try core_constraints.cosetVanishing(M31, trace_coset, eval_domain.at(1)).inv(),
        };
        const job = DomainJob{
            .air = self.air,
            .pubs = self.pubs,
            .table = table,
            .log_size = self.log_size,
            .eval_log_size = eval_log_size,
            .logup = if (n_inter != 0) self.logup orelse return error.MissingLookupElements else null,
            .shift = if (n_inter != 0) try self.claimedShift() else QM31.zero(),
            .powers = powers,
            .denominator_inv = denominator_inv,
            .values = values,
        };
        const rows = end - start;
        const n_threads = @min(std.Thread.getCpuCount() catch 1, 64, @max(rows / 1024, 1));
        var threads: [64]std.Thread = undefined;
        // Scratch is allocated up front: the caller's allocator need not be thread-safe.
        const per = self.air.exprs.len + self.air.constraints.len;
        const scratch = try allocator.alloc(M31, n_threads * per);
        defer allocator.free(scratch);
        const nl = self.air.lookups.len;
        const per_q = 2 * nl + 2 * nBatches(self.air) + MAX_LOOKUP_VALS;
        const qscratch = try allocator.alloc(QM31, n_threads * per_q);
        defer allocator.free(qscratch);
        const chunk = (rows + n_threads - 1) / n_threads;
        for (0..n_threads) |t| {
            const mine = scratch[t * per ..][0..per];
            threads[t] = try std.Thread.spawn(.{}, DomainJob.run, .{
                &job, mine[0..self.air.exprs.len], mine[self.air.exprs.len..], qscratch[t * per_q ..][0..per_q], start + t * chunk, start + @min((t + 1) * chunk, rows),
            });
        }
        for (threads[0..n_threads]) |th| th.join();
    }
};

/// How a column is read on the evaluation domain: row `r` at mask offset `o` reads
/// `values[((p >> shift) << 1) + (p & 1) - base]` with `p` the offset row, or `values[r - base]`
/// when `row_indexed` (stwo-zig's `simd_evaluator.ResolvedColumn`).
pub const Resolved = struct {
    values: []const M31,
    shift: u6 = 1,
    base: usize = 0,
    row_indexed: bool = false,

    inline fn at(self: Resolved, row: usize, offset: i32, log_size: u32, eval_log_size: u32) M31 {
        if (self.row_indexed) return self.values[row - self.base];
        const p = if (offset == 0) row else utils.offsetBitReversedCircleDomainIndex(row, log_size, eval_log_size, offset);
        return self.values[((p >> self.shift) << 1) + (p & 1) - self.base];
    }
};

pub const TilePlan = struct { tiles: usize, rows: usize };

/// Row-tiled reading of coefficient-only columns (`stwzeva.Tiling`).
pub const Tiling = struct {
    ctx: *anyopaque,
    /// Null when nothing needs tiling.
    plan: *const fn (ctx: *anyopaque, trace: *const prover_component.Trace) anyerror!?TilePlan,
    load: *const fn (ctx: *anyopaque, tile: usize) anyerror!void,
    /// `tree` 0/1/2, `local` within the component's span.
    resolve: *const fn (ctx: *anyopaque, tree: u8, local: u32, offset: i32) anyerror!Resolved,
    release: *const fn (ctx: *anyopaque) void,
};

/// Every read site of a component, resolved: main columns at each mask offset, preprocessed at 0,
/// interaction limbs at 0 and the last batch at −1.
const ReadTable = struct {
    pre: []Resolved,
    main: [][]Resolved,
    inter: []Resolved,
    inter_prev: [4]Resolved = undefined,
    offsets: []const []const i32,
    /// Preprocessed columns the AIR reads (the others are never resolved).
    pre_read: []bool,

    fn init(a: std.mem.Allocator, c: *const Component) !ReadTable {
        const main = try a.alloc([]Resolved, c.air.n_main);
        for (main, c.main_offsets) |*m, o| m.* = try a.alloc(Resolved, o.len);
        const pre_read = try a.alloc(bool, c.air.n_preprocessed);
        @memset(pre_read, false);
        for (c.air.exprs) |e| switch (e) {
            .col => |col| if (col.tree == .preprocessed) {
                pre_read[col.index] = true;
            },
            else => {},
        };
        return .{
            .pre_read = pre_read,
            .pre = try a.alloc(Resolved, c.air.n_preprocessed),
            .main = main,
            .inter = try a.alloc(Resolved, 4 * nBatches(c.air)),
            .offsets = @ptrCast(c.main_offsets),
        };
    }

    fn deinit(self: *ReadTable, a: std.mem.Allocator) void {
        a.free(self.pre);
        a.free(self.pre_read);
        for (self.main) |m| a.free(m);
        a.free(self.main);
        a.free(self.inter);
    }

    const Source = union(enum) {
        /// Whole columns on the evaluation domain, pre ‖ main ‖ inter.
        whole: []const []const M31,
        tiling: Tiling,
    };

    fn get(src: Source, c: *const Component, tree: u8, local: u32, offset: i32) !Resolved {
        return switch (src) {
            .whole => |w| .{ .values = w[local + switch (tree) {
                0 => @as(usize, 0),
                1 => c.air.n_preprocessed,
                else => c.air.n_preprocessed + c.air.n_main,
            }] },
            .tiling => |t| try t.resolve(t.ctx, tree, local, offset),
        };
    }

    fn resolve(self: *ReadTable, c: *const Component, src: Source) !void {
        for (self.pre, self.pre_read, 0..) |*r, read, i| r.* = if (read) try get(src, c, 0, @intCast(i), 0) else .{ .values = &.{} };
        for (self.main, self.offsets, 0..) |m, offs, i| for (m, offs) |*r, off| {
            r.* = try get(src, c, 1, @intCast(i), off);
        };
        const n = self.inter.len;
        for (self.inter, 0..) |*r, k| r.* = try get(src, c, 2, @intCast(k), 0);
        if (n != 0) for (0..4) |l| {
            self.inter_prev[l] = try get(src, c, 2, @intCast(n - 4 + l), -1);
        };
    }
};

const DomainJob = struct {
    air: ir.Air,
    pubs: []const M31,
    table: *const ReadTable,
    log_size: u32,
    eval_log_size: u32,
    powers: []const QM31,
    denominator_inv: [2]M31,
    values: []QM31,
    logup: ?Logup,
    shift: QM31,

    const Ctx = struct {
        job: *const DomainJob,
        row: usize,
        pub fn read(self: *const Ctx, tree: ir.Tree, index: u32, offset: i32) M31 {
            const t = self.job.table;
            return switch (tree) {
                .preprocessed => t.pre[index].at(self.row, 0, self.job.log_size, self.job.eval_log_size),
                .main => t.main[index][std.mem.indexOfScalar(i32, t.offsets[index], offset).?].at(self.row, offset, self.job.log_size, self.job.eval_log_size),
            };
        }
    };

    fn run(self: *const DomainJob, scratch: []M31, out: []M31, qscratch: []QM31, start: usize, end: usize) void {
        const n_base = self.air.constraints.len;
        const nl = self.air.lookups.len;
        const B = nBatches(self.air);
        const n = n_base + B;
        const mults = qscratch[0..nl];
        const dens = qscratch[nl..][0..nl];
        const S = qscratch[2 * nl ..][0..B];
        const lout = qscratch[2 * nl + B ..][0..B];
        const vals = qscratch[2 * nl + 2 * B ..][0..MAX_LOOKUP_VALS];
        const t = self.table;
        for (start..end) |row| {
            const ctx = Ctx{ .job = self, .row = row };
            interp.evalConstraints(M31, self.air, self.pubs, scratch, &ctx, out);
            var combined = QM31.zero();
            for (out, 0..) |c, i| combined = combined.add(self.powers[n - 1 - i].mulM31(c));
            if (self.logup) |lu| {
                for (self.air.lookups, mults, dens) |l, *m, *d| {
                    m.* = QM31.fromBase(scratch[l.mult]);
                    for (l.vals, 0..) |v, i| vals[i] = QM31.fromBase(scratch[v]);
                    d.* = denominator(l.rel, vals[0..l.vals.len], lu.z, lu.alpha);
                }
                for (S, 0..) |*sv, b| {
                    var limbs: [4]M31 = undefined;
                    for (&limbs, 0..) |*x, l| x.* = t.inter[4 * b + l].at(row, 0, self.log_size, self.eval_log_size);
                    sv.* = QM31.fromM31Array(limbs);
                }
                var prev: [4]M31 = undefined;
                for (&prev, 0..) |*x, l| x.* = t.inter_prev[l].at(row, -1, self.log_size, self.eval_log_size);
                logupConstraintValues(mults, dens, S, QM31.fromM31Array(prev), self.shift, lout);
                for (lout, 0..) |c, b| combined = combined.add(self.powers[n - 1 - (n_base + b)].mul(c));
            }
            self.values[row] = combined.mulM31(self.denominator_inv[row >> @intCast(self.log_size)]);
        }
    }
};

fn onDomain(
    allocator: std.mem.Allocator,
    poly: prover_component.Poly,
    trace_log_size: u32,
    eval_log_size: u32,
    eval_size: usize,
    buffers: *std.ArrayList([]M31),
) ![]const M31 {
    try poly.validate();
    // Compact storage keeps coefficients only (no values) at the committed log size.
    if (poly.log_size == eval_log_size and poly.values.len != 0) return poly.values;
    const coefficients = poly.coefficients orelse return error.InvalidProofShape;
    if (coefficients.logSize() != trace_log_size) return error.InvalidProofShape;
    const values = try allocator.alloc(M31, eval_size);
    errdefer allocator.free(values);
    const source = coefficients.coefficients();
    @memcpy(values[0..source.len], source);
    @memset(values[source.len..], M31.zero());
    try buffers.append(allocator, values);
    return values;
}
