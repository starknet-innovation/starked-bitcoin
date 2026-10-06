//! A Stwo component whose constraints are an `ir.Air`, evaluated by the shared
//! interpreter on both the verifier side (out-of-domain point) and the prover
//! side (composition over the evaluation domain).
//!
//! v0 restrictions, checked in `init`:
//! - Single trace size: every column has 2^log_size rows and nothing is
//!   lifted, so `max_log_degree_bound == log_size`.
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

pub const Component = struct {
    allocator: std.mem.Allocator,
    air: ir.Air,
    log_size: u32,
    /// Sorted distinct offsets read from each main column.
    main_offsets: [][]i32,

    const Adapter = core_air_derive.ComponentAdapter(
        @This(),
        prover_component.ComponentProver,
        prover_component.Trace,
        prover_air_accumulation.DomainEvaluationAccumulator,
    );

    pub fn init(allocator: std.mem.Allocator, air: ir.Air, log_size: u32) !Component {
        try air.validate();
        if (try air.maxConstraintDegree(allocator) > MAX_DEGREE) return error.DegreeTooHigh;
        for (air.exprs) |e| switch (e) {
            .col => |c| if (c.tree == .preprocessed and c.offset != 0)
                return error.PreprocessedOffsetUnsupported,
            else => {},
        };
        return .{
            .allocator = allocator,
            .air = air,
            .log_size = log_size,
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
        return self.air.constraints.len;
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
        return core_air_components.TraceLogDegreeBounds.initOwned(
            try allocator.dupe([]u32, &.{ pre, main }),
        );
    }

    pub fn maskPoints(
        self: *const @This(),
        allocator: std.mem.Allocator,
        point: CirclePointQM31,
        max_log_degree_bound: u32,
    ) !core_air_components.MaskPoints {
        if (max_log_degree_bound != self.log_size) return error.LiftingUnsupported;
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
        return core_air_components.MaskPoints.initOwned(
            try allocator.dupe([][]CirclePointQM31, &.{ pre, main }),
        );
    }

    pub fn preprocessedColumnIndices(self: *const @This(), allocator: std.mem.Allocator) ![]usize {
        const out = try allocator.alloc(usize, self.air.n_preprocessed);
        for (out, 0..) |*v, i| v.* = i;
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
        if (max_log_degree_bound != self.log_size) return error.LiftingUnsupported;
        if (mask.items.len < 2 or mask.items[0].len < self.air.n_preprocessed or
            mask.items[1].len != self.air.n_main) return error.InvalidProofShape;
        for (mask.items[0][0..self.air.n_preprocessed]) |c| if (c.len != 1) return error.InvalidProofShape;
        for (mask.items[1], self.main_offsets) |c, o| if (c.len != o.len) return error.InvalidProofShape;

        const scratch = try self.allocator.alloc(QM31, self.air.exprs.len);
        defer self.allocator.free(scratch);
        const out = try self.allocator.alloc(QM31, self.air.constraints.len);
        defer self.allocator.free(out);
        const ctx = PointCtx{
            .pre = @ptrCast(mask.items[0]),
            .main = @ptrCast(mask.items[1]),
            .offsets = @ptrCast(self.main_offsets),
        };
        interp.evalConstraints(QM31, self.air, scratch, &ctx, out);

        const denominator_inv = try core_constraints.cosetVanishing(
            QM31,
            canonic.CanonicCoset.new(self.log_size).coset(),
            point,
        ).inv();
        for (out) |c| accumulator.accumulate(c.mul(denominator_inv));
    }

    const DomainCtx = struct {
        pre: []const []const M31,
        main: []const []const M31,
        log_size: u32,
        eval_log_size: u32,
        row: usize = 0,

        pub fn read(self: *const DomainCtx, tree: ir.Tree, index: u32, offset: i32) M31 {
            return switch (tree) {
                .preprocessed => self.pre[index][self.row],
                .main => self.main[index][
                    if (offset == 0) self.row else utils.offsetBitReversedCircleDomainIndex(
                        self.row,
                        self.log_size,
                        self.eval_log_size,
                        offset,
                    )
                ],
            };
        }
    };

    pub fn evaluateConstraintQuotientsOnDomain(
        self: *const @This(),
        trace: *const prover_component.Trace,
        accumulator: *prover_air_accumulation.DomainEvaluationAccumulator,
    ) !void {
        if (trace.polys.items.len < 2 or trace.polys.items[0].len != self.air.n_preprocessed or
            trace.polys.items[1].len != self.air.n_main) return error.InvalidProofShape;
        const allocator = accumulator.allocator;
        const eval_log_size = self.log_size + 1;
        const eval_domain = canonic.CanonicCoset.new(eval_log_size).circleDomain();
        const eval_size = eval_domain.size();

        var buffers = std.ArrayList([]M31).empty;
        defer {
            for (buffers.items) |b| allocator.free(b);
            buffers.deinit(allocator);
        }
        const pre = try allocator.alloc([]const M31, self.air.n_preprocessed);
        defer allocator.free(pre);
        const main = try allocator.alloc([]const M31, self.air.n_main);
        defer allocator.free(main);
        for (trace.polys.items[0], pre) |poly, *o| o.* = try onDomain(allocator, poly, self.log_size, eval_log_size, eval_size, &buffers);
        for (trace.polys.items[1], main) |poly, *o| o.* = try onDomain(allocator, poly, self.log_size, eval_log_size, eval_size, &buffers);
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

        const trace_coset = canonic.CanonicCoset.new(self.log_size).coset();
        const denominator_inv = [_]M31{
            try core_constraints.cosetVanishing(M31, trace_coset, eval_domain.at(0)).inv(),
            try core_constraints.cosetVanishing(M31, trace_coset, eval_domain.at(1)).inv(),
        };
        var columns = try accumulator.columns(allocator, &.{.{
            .log_size = eval_log_size,
            .n_cols = self.air.constraints.len,
        }});
        defer allocator.free(columns);
        const column = &columns[0];

        const scratch = try allocator.alloc(M31, self.air.exprs.len);
        defer allocator.free(scratch);
        const out = try allocator.alloc(M31, self.air.constraints.len);
        defer allocator.free(out);
        var ctx = DomainCtx{ .pre = pre, .main = main, .log_size = self.log_size, .eval_log_size = eval_log_size };
        const n = self.air.constraints.len;
        for (0..eval_size) |row| {
            ctx.row = row;
            interp.evalConstraints(M31, self.air, scratch, &ctx, out);
            var combined = QM31.zero();
            for (out, 0..) |c, i| combined = combined.add(column.random_coeff_powers[n - 1 - i].mulM31(c));
            column.accumulate(row, combined.mulM31(denominator_inv[row >> @intCast(self.log_size)]));
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
    if (poly.log_size == eval_log_size) return poly.values;
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
