//! A system of IR components proven together in one STARK under the `proving_5a7c5ed` profile
//! (roadmap IR-LOGUP; Lean semantics in lean/StarkedAir/Lookup.lean). Components share the
//! preprocessed, main and interaction trees; their lookups are tied together by LogUp.
//!
//! Transcript: config → preprocessed commitment → statement (per component: log size, AIR
//! digest, public inputs) → main commitment → lookup elements `(z, α)` → claimed sums →
//! interaction commitment → STARK. The verifier pins the preprocessed root and checks that the
//! claimed sums add to zero (the relations balance; `LogUp.logup_sum` in Lean).
//!
//! v0: every component has the same log size (no lifting).

const std = @import("std");
const core = @import("stwo_core");
const ir = @import("ir.zig");
const base = @import("prove.zig");
const rec = @import("prove_rec.zig");
const interp = @import("interp.zig");
const component_mod = @import("component.zig");
const stwzeva = @import("stwzeva.zig");
const prover_component = @import("stwo_prover_engine").air.component_prover;
const logup_columns = @import("stwo_prover_engine").air.logup_columns;
const prover_pcs = @import("stwo_prover_engine").pcs;
const prover_circle = @import("stwo_prover_engine").poly.circle;
const prover_twiddles = @import("stwo_prover_engine").poly.twiddles;
const canonic = core.poly.circle.canonic;
const lookup_transcript = core.channel.lookup_transcript;
const utils = core.utils;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Revision = core.protocol_revision.Revision;

/// One component of a system: its AIR, trace size and public inputs.
pub const Part = struct {
    air: *const ir.Air,
    log_size: u32,
    pubs: []const M31 = &.{},
};

/// A lookup entry the verifier contributes (e.g. a public root consumed with multiplicity −1).
pub const PubEntry = struct {
    rel: u32,
    vals: []const M31,
    mult: M31,
};

pub const Proof = struct {
    stark: rec.Proof,
    /// Claimed LogUp sums of the components with lookups, in component order.
    claimed_sums: []QM31,
};

fn hasLookups(parts: []const Part) bool {
    for (parts) |p| if (p.air.lookups.len != 0) return true;
    return false;
}

/// The system's largest log size (the PCS lifts every tree to it, D-045).
pub fn maxLogSize(parts: []const Part) !u32 {
    if (parts.len == 0) return error.EmptySystem;
    var max: u32 = 0;
    for (parts) |p| max = @max(max, p.log_size);
    return max;
}

fn mixStatements(channel: anytype, allocator: std.mem.Allocator, parts: []const Part) !void {
    channel.mixU32s(&.{@intCast(parts.len)});
    for (parts) |p| base.mixStatement(channel, p.log_size, try p.air.digest(allocator), p.pubs);
}

/// Components wired into the shared trees.
fn components(allocator: std.mem.Allocator, parts: []const Part) ![]component_mod.Component {
    const out = try allocator.alloc(component_mod.Component, parts.len);
    var pre: usize = 0;
    var main: usize = 0;
    var inter: usize = 0;
    const trees: usize = if (hasLookups(parts)) 3 else 2;
    for (parts, out) |p, *c| {
        c.* = try component_mod.Component.init(allocator, p.air.*, p.log_size, p.pubs);
        c.pre_offset = pre;
        c.main_offset = main;
        c.inter_offset = inter;
        c.n_trees = trees;
        pre += p.air.n_preprocessed;
        main += p.air.n_main;
        inter += 4 * component_mod.nBatches(p.air.*);
    }
    return out;
}

fn preprocessedStorage(allocator: std.mem.Allocator, parts: []const Part) ![]prover_pcs.ColumnEvaluation {
    var cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    for (parts) |p| {
        const pre = try p.air.genPreprocessed(allocator, p.log_size);
        defer {
            for (pre) |c| allocator.free(c);
            allocator.free(pre);
        }
        const st = try base.toStorage(allocator, p.log_size, @ptrCast(pre));
        defer allocator.free(st);
        try cols.appendSlice(allocator, st);
    }
    return cols.toOwnedSlice(allocator);
}

/// Root of the preprocessed tree of `parts`, as the honest prover commits it.
pub fn preprocessedRoot(allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part) !rec.Hasher.Hash {
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var scheme = try E.initRevision(allocator, cfg);
    defer E.deinit(&scheme, allocator);
    var channel = rec.Channel{};
    try E.commit(&scheme, allocator, try preprocessedStorage(allocator, parts), null, &channel);
    try E.flushPendingCommit(&scheme, allocator, &channel);
    var roots = try scheme.roots(allocator);
    defer roots.deinit(allocator);
    return roots.items[0];
}

/// One component's LogUp fractions, computed per storage row as stwo-zig's interaction builder
/// asks for them (on its worker threads): nothing per row is stored, so the only memory is the
/// natural-order columns the lookups read.
const Fractions = struct {
    air: ir.Air,
    reads: LookupReads,
    pubs: []const M31,
    log_size: u32,
    /// Natural-order preprocessed columns (owned).
    pre: [][]M31,
    /// Natural-order main columns; only `reads.main` ones are read.
    main: []const []const M31,
    el: lookup_transcript.LookupElements,
    batches: usize,
    /// Storage (bit-reversed circle-domain) index → natural row (owned).
    natural: []usize,

    fn deinit(self: *Fractions, allocator: std.mem.Allocator) void {
        allocator.free(self.natural);
        for (self.pre) |c| allocator.free(c);
        allocator.free(self.pre);
        self.reads.deinit(allocator);
    }

    threadlocal var scratch_tl: []M31 = &.{};

    fn scratch(n: usize) ![]M31 {
        if (scratch_tl.len < n) {
            std.heap.smp_allocator.free(scratch_tl);
            scratch_tl = &.{};
            scratch_tl = try std.heap.smp_allocator.alloc(M31, n);
        }
        return scratch_tl[0..n];
    }

    fn fill(self: *const Fractions, storage_row: usize, out: []logup_columns.Fraction) anyerror!void {
        const air = self.air;
        const values = try scratch(air.exprs.len);
        const trace = interp.RowTrace{ .log_size = self.log_size, .pubs = self.pubs, .preprocessed = @ptrCast(self.pre), .main = self.main, .row = self.natural[storage_row] };
        // Only what the lookups read.
        for (air.exprs, self.reads.exprs, 0..) |e, l, id| {
            if (!l) continue;
            values[id] = switch (e) {
                .col => |c| trace.read(c.tree, c.index, c.offset),
                .constant => |v| M31.fromCanonical(v),
                .add => |x| values[x[0]].add(values[x[1]]),
                .sub => |x| values[x[0]].sub(values[x[1]]),
                .mul => |x| values[x[0]].mul(values[x[1]]),
                .neg => |x| values[x].neg(),
                .@"pub" => |i| self.pubs[i],
            };
        }
        var vals: [component_mod.MAX_LOOKUP_VALS]QM31 = undefined;
        for (out, 0..) |*o, b| {
            var fr: [2]logup_columns.Fraction = undefined;
            const k: usize = if (2 * b + 1 < air.lookups.len) 2 else 1;
            for (0..k) |t| {
                const l = air.lookups[2 * b + t];
                for (l.vals, 0..) |v, i| vals[i] = QM31.fromBase(values[v]);
                fr[t] = .{ .numerator = QM31.fromBase(values[l.mult]), .denominator = component_mod.denominator(l.rel, vals[0..l.vals.len], self.el.z, self.el.alpha) };
            }
            o.* = if (k == 2) .{
                .numerator = fr[0].numerator.mul(fr[1].denominator).add(fr[1].numerator.mul(fr[0].denominator)),
                .denominator = fr[0].denominator.mul(fr[1].denominator),
            } else fr[0];
        }
    }
};

fn fractions(allocator: std.mem.Allocator, part: Part, main: []const []const M31, el: lookup_transcript.LookupElements) !Fractions {
    const air = part.air.*;
    const n = @as(usize, 1) << @intCast(part.log_size);
    const reads = try LookupReads.init(allocator, air);
    errdefer reads.deinit(allocator);
    const pre = try air.genPreprocessed(allocator, part.log_size);
    const natural = try allocator.alloc(usize, n);
    for (0..n) |i| natural[utils.bitReverseIndex(utils.cosetIndexToCircleDomainIndex(i, part.log_size), part.log_size)] = i;
    return .{ .air = air, .reads = reads, .pubs = part.pubs, .log_size = part.log_size, .pre = pre, .main = main, .el = el, .batches = component_mod.nBatches(air), .natural = natural };
}

/// The natural-order main columns of `part` that its lookups read, recomputed from the committed
/// (compact) coefficients: the trace domain's evaluations, in storage order, permuted back. The
/// other entries are empty. Free with `freeColumns`.
fn lookupColumnsFromCoefficients(
    a: std.mem.Allocator,
    coefficients: []const prover_component.Poly,
    part: Part,
    reads: []const bool,
) ![][]M31 {
    const log_size = part.log_size;
    const n = @as(usize, 1) << @intCast(log_size);
    const out = try a.alloc([]M31, reads.len);
    for (out) |*c| c.* = &.{};
    const domain = canonic.CanonicCoset.new(log_size).circleDomain();
    var twiddles = try prover_twiddles.precomputeM31(a, domain.half_coset);
    defer prover_twiddles.deinitM31(a, &twiddles);
    const view = prover_twiddles.TwiddleTree([]const M31).init(twiddles.root_coset, twiddles.twiddles, twiddles.itwiddles);
    const buffer = try a.alloc(M31, n);
    defer a.free(buffer);
    for (reads, coefficients, out) |keep, poly, *col| {
        if (!keep) continue;
        const coeffs = (poly.coefficients orelse return error.NoCoefficients).coefficients();
        if (coeffs.len != n) return error.NoCoefficients;
        @memcpy(buffer, coeffs);
        try prover_circle.poly.evaluateBuffersWithTwiddles(&.{buffer}, domain, view);
        col.* = try a.alloc(M31, n);
        for (col.*, 0..) |*v, i| v.* = buffer[utils.bitReverseIndex(utils.cosetIndexToCircleDomainIndex(i, log_size), log_size)];
    }
    return out;
}

fn freeColumns(a: std.mem.Allocator, cols: [][]M31) void {
    for (cols) |c| a.free(c);
    a.free(cols);
}

/// Expressions the lookups read (their multiplicities and values, transitively), and the main
/// columns among them. The fractions need only these; the rest of the witness is dead once it is
/// in storage order.
pub const LookupReads = struct {
    exprs: []bool,
    main: []bool,

    pub fn init(allocator: std.mem.Allocator, air: ir.Air) !LookupReads {
        const live = try allocator.alloc(bool, air.exprs.len);
        @memset(live, false);
        for (air.lookups) |l| {
            live[l.mult] = true;
            for (l.vals) |v| live[v] = true;
        }
        var id = air.exprs.len;
        while (id > 0) {
            id -= 1;
            if (!live[id]) continue;
            switch (air.exprs[id]) {
                .add, .sub, .mul => |args| for (args) |x| {
                    live[x] = true;
                },
                .neg => |x| live[x] = true,
                else => {},
            }
        }
        const main = try allocator.alloc(bool, air.n_main);
        @memset(main, false);
        for (air.exprs, live) |e, l| if (l) switch (e) {
            .col => |c| if (c.tree == .main) {
                main[c.index] = true;
            },
            else => {},
        };
        return .{ .exprs = live, .main = main };
    }

    pub fn deinit(self: LookupReads, allocator: std.mem.Allocator) void {
        allocator.free(self.exprs);
        allocator.free(self.main);
    }
};


/// How the prover evaluates the composition polynomial (the proof bytes are the same).
pub const Composition = enum {
    /// Our IR interpreter (`component.zig`).
    interpreter,
    /// stwo-zig's captured-AIR runtime over the lowered STWZEVA programs (`stwzeva.zig`).
    stwzeva,
    /// As `stwzeva`, with the kernels stwo-zig's C code generator built for `stwzeva.aot_airs`
    /// (other programs stay on the SIMD interpreter).
    stwzeva_native,
};

/// Proves the system. `mains[i]` are part `i`'s main columns in natural row order.
/// `a` should be an arena (intermediate buffers are not freed individually).
pub fn prove(comptime E: type, caller_allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31) !Proof {
    return proveWith(E, caller_allocator, cfg, parts, mains, .interpreter);
}

/// `prove` with a choice of composition evaluator.
pub fn proveWith(comptime E: type, caller_allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31, composition: Composition) !Proof {
    return proveOpts(E, caller_allocator, cfg, parts, mains, .{ .composition = composition });
}

pub const Options = struct {
    composition: Composition = .interpreter,
    /// A device composition stage over the lowered programs (requires a `stwzeva` composition),
    /// e.g. `gpu/metal_composition.zig`. Components it declines run on the host.
    device: ?stwzeva.Device = null,
    /// Filled with the stage's counts when `device` is set.
    counts: ?*stwzeva.DeviceCounts = null,
    /// The prover's working allocator (thread-safe, freeing); `std.heap.smp_allocator` by default.
    work_allocator: ?std.mem.Allocator = null,
    /// The caller will not read `mains` again: once the interaction trace is built, their pages
    /// are returned to the OS (their contents become undefined). Saves one main-trace copy.
    discard_mains: bool = false,
    /// How the commitment scheme keeps committed trees (stwo-zig execution choices; proof bytes
    /// are the same).
    storage: Storage = .default,
    /// With compact storage and the interpreter, expand about this many columns at a time in the
    /// composition (stwo-zig's row tiles) instead of a whole component; 0 = whole components.
    /// Off by default: at 2^17 it cuts the peak 9 % but makes the proof 2.2× slower.
    tile_columns: usize = 0,
};

pub const Storage = enum {
    /// stwo-zig's default: each tree's coefficients and its blown-up evaluations (3 trace-size
    /// copies per column at blowup 1).
    default,
    /// Blown-up evaluations only (`CoefficientRetentionPolicy.never`): 2 copies.
    evaluations_only,
    /// Coefficients only, committed by streaming batches (`setCompactPolynomialStorage`):
    /// 1 copy; composition and quotients re-extend columns as they need them.
    compact,
};

/// `STARKED_PHASES=1` prints the prover's phase times (benchmarks).
const Phases = struct {
    on: bool,
    timer: ?std.time.Timer,

    fn start() Phases {
        const on = std.process.hasEnvVarConstant("STARKED_PHASES");
        return .{ .on = on, .timer = if (on) std.time.Timer.start() catch null else null };
    }

    fn mark(self: *Phases, name: []const u8) void {
        // `STWO_HOST_MEMORY_PROFILE=1`: process footprint (current, lifetime peak) at each phase.
        @import("stwo_prover_engine").measurement.process_usage.reportStage(name);
        if (!self.on) return;
        if (self.timer) |*t| std.debug.print("  phase {s}: {d} ms\n", .{ name, t.lap() / std.time.ns_per_ms });
    }
};

/// `prove` with options.
pub fn proveOpts(comptime E: type, caller_allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31, opts: Options) !Proof {
    const composition = opts.composition;
    // Compact storage keeps the committed coefficients: the lookups' columns are recomputed from
    // them, so the witness is not read after its storage-order copy.
    const recompute = opts.storage == .compact;
    if (opts.device != null and composition == .interpreter) return error.DeviceNeedsStwzeva;
    var phase = Phases.start();
    // Everything the prover builds is freed as soon as it is dead, so all of it comes from a
    // freeing, thread-safe allocator (stwo-zig's components evaluate on concurrent threads). Only
    // the result is copied into `caller_allocator` (often an arena, which never frees).
    const a = opts.work_allocator orelse std.heap.smp_allocator;
    const max_log = try maxLogSize(parts);
    var channel = rec.Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try E.initRevision(a, cfg);
    var scheme_owned = true;
    errdefer if (scheme_owned) E.deinit(&scheme, a);
    switch (opts.storage) {
        .default => {},
        .evaluations_only => scheme.setCoefficientRetentionPolicy(.never),
        .compact => scheme.setCompactPolynomialStorage(0),
    }
    const commit = struct {
        fn f(s_: *E.Scheme, al: std.mem.Allocator, cols: []prover_pcs.ColumnEvaluation, ch: *rec.Channel, storage: Storage) !void {
            if (storage == .compact)
                try s_.commitOwnedStreamingWithRecorder(al, cols, 0, null, ch)
            else
                try E.commit(s_, al, cols, null, ch);
        }
    }.f;

    // `commit` consumes its columns (and their slice).
    try commit(&scheme, a, try preprocessedStorage(a, parts), &channel, opts.storage);
    try E.flushPendingCommit(&scheme, a, &channel);
    phase.mark("preprocessed commit");
    try mixStatements(&channel, a, parts);
    var main_cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    for (parts, mains) |p, m| {
        if (m.len != p.air.n_main) return error.InvalidPreparedGeometry;
        const st = try base.toStorage(a, p.log_size, m);
        defer a.free(st);
        try main_cols.appendSlice(a, st);
        // Witness columns no lookup reads are dead once in storage order; with coefficients
        // retained (`recompute`), all of them are.
        if (opts.discard_mains) {
            const reads = try LookupReads.init(a, p.air.*);
            defer reads.deinit(a);
            for (m, reads.main) |col, keep| if (!keep or recompute) discardPages(col);
        }
    }
    phase.mark("main storage order");
    try commit(&scheme, a, try main_cols.toOwnedSlice(a), &channel, opts.storage);
    try E.flushPendingCommit(&scheme, a, &channel);
    phase.mark("main commit");

    const comps = try components(a, parts);
    defer {
        for (comps) |*c| c.deinit();
        a.free(comps);
    }
    var sums = std.ArrayList(QM31).empty;
    defer sums.deinit(a);
    if (hasLookups(parts)) {
        const el = try lookup_transcript.drawLookupElements(a, &channel);
        var inter_cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
        var committed: ?prover_component.Trace = if (recompute) try scheme.trace(a) else null;
        defer if (committed) |*t| t.polys.deinitDeep(a);
        for (parts, mains, comps) |p, m, *c| {
            // A component's witness is dead once its fractions are built.
            defer if (opts.discard_mains and !recompute) for (m) |col| discardPages(col);
            if (p.air.lookups.len == 0) continue;
            var recomputed: ?[][]M31 = null;
            defer if (recomputed) |cols| freeColumns(a, cols);
            if (committed) |t| {
                const reads = try LookupReads.init(a, p.air.*);
                defer reads.deinit(a);
                recomputed = try lookupColumnsFromCoefficients(a, t.polys.items[1][c.main_offset..][0..p.air.n_main], p, reads.main);
            }
            // One component's fractions at a time.
            var fr = try fractions(a, p, if (recomputed) |cols| @ptrCast(cols) else m, el);
            defer fr.deinit(a);
            phase.mark("  fractions");
            const built = try logup_columns.build(a, p.log_size, fr.batches, &fr, struct {
                fn f(ctx: *const Fractions, row: usize, out: []logup_columns.Fraction) anyerror!void {
                    return ctx.fill(row, out);
                }
            }.f);
            defer a.free(built.columns);
            try inter_cols.appendSlice(a, built.columns);
            try sums.append(a, built.claimed_sum);
            c.logup = .{ .z = el.z, .alpha = el.alpha, .claimed_sum = built.claimed_sum };
        }
        phase.mark("interaction trace (host)");
        lookup_transcript.mixInteractionClaim(&channel, sums.items);
        try commit(&scheme, a, try inter_cols.toOwnedSlice(a), &channel, opts.storage);
        phase.mark("interaction commit");
    } else if (opts.discard_mains) for (mains) |m| for (m) |col| discardPages(col);
    const provers = try a.alloc(prover_component.ComponentProver, comps.len);
    defer a.free(provers);
    // Compact storage: the interpreter expands columns a row tile at a time (about 64 columns'
    // worth of evaluations at once), not a whole component.
    var tile_lowered: []stwzeva.composition.Component = &.{};
    var tile_sources: []stwzeva.TileSource = &.{};
    defer {
        for (tile_lowered) |*l| stwzeva.composition.deinitComponent(a, l);
        a.free(tile_lowered);
        a.free(tile_sources);
    }
    if (opts.storage == .compact and composition == .interpreter and opts.tile_columns != 0) {
        tile_lowered = try a.alloc(stwzeva.composition.Component, comps.len);
        tile_sources = try a.alloc(stwzeva.TileSource, comps.len);
        for (parts, comps, tile_lowered, tile_sources) |p, *c, *l, *t| {
            l.* = try stwzeva.lowerComponent(a, p.air.*, p.pubs, .{
                .log_size = p.log_size,
                .pre_offset = @intCast(c.pre_offset),
                .main_offset = @intCast(c.main_offset),
                .inter_offset = @intCast(c.inter_offset),
            });
            t.* = .{ .allocator = a, .captured = l, .budget = opts.tile_columns * (@as(usize, 4) << @intCast(p.log_size + 1)) };
            c.tiling = t.tiling();
        }
    }
    var lowered: []stwzeva.composition.Component = &.{};
    var wrapped: []stwzeva.Component = &.{};
    defer {
        for (lowered) |*l| stwzeva.composition.deinitComponent(a, l);
        a.free(lowered);
        for (wrapped) |w| a.free(w.preprocessed_logs);
        a.free(wrapped);
    }
    switch (composition) {
        .interpreter => for (comps, provers) |*c, *p| {
            p.* = c.asProverComponent();
        },
        .stwzeva, .stwzeva_native => {
            lowered = try a.alloc(stwzeva.composition.Component, comps.len);
            wrapped = try a.alloc(stwzeva.Component, comps.len);
            var pre_logs = std.ArrayList(u32).empty;
            defer pre_logs.deinit(a);
            for (parts) |p| try pre_logs.appendNTimes(a, p.log_size, p.air.n_preprocessed);
            var rc_offset: u32 = 0;
            for (parts, comps, lowered, wrapped, provers) |p, *c, *l, *w, *out| {
                l.* = try stwzeva.lowerComponent(a, p.air.*, p.pubs, .{
                    .log_size = p.log_size,
                    .pre_offset = @intCast(c.pre_offset),
                    .main_offset = @intCast(c.main_offset),
                    .inter_offset = @intCast(c.inter_offset),
                    .rc_offset = rc_offset,
                });
                rc_offset += l.n_constraints;
                w.* = try stwzeva.Component.init(a, c, l, pre_logs.items, max_log);
                if (composition == .stwzeva_native) w.prover.native_executor = @import("stwzeva_cpu_aot").executor();
                out.* = w.asProverComponent();
            }
        },
    }
    var captured: []stwzeva.Captured = &.{};
    defer a.free(captured);
    var bound: ?stwzeva.DeviceBound = null;
    defer if (bound) |*b| b.close();
    if (opts.device) |device| {
        if (try device.open(device.context, a, lowered, &.{})) |session| {
            captured = try a.alloc(stwzeva.Captured, wrapped.len);
            for (captured, wrapped) |*c, w| c.* = w.prover;
            bound = .{ .allocator = a, .components = captured, .captured = lowered, .session = session, .recorder = null };
        }
    }
    phase.mark("components ready");
    scheme_owned = false;
    var extended = try E.prove(a, provers, &channel, scheme, .{
        .composition_stage = if (bound) |*b| b.asStage() else null,
    });
    extended.aux.deinit(a);
    defer extended.proof.deinit(a);
    phase.mark("STARK done");
    if (opts.counts) |out| out.* = if (bound) |b| b.counts else .{};
    // The result, in the caller's allocator (postcard round trip: a deep copy).
    var bytes = std.ArrayList(u8).empty;
    defer bytes.deinit(a);
    try @import("stwo_postcard").serializeProof(rec.Hasher, bytes.writer(a), extended.proof);
    var fbs = std.io.fixedBufferStream(bytes.items);
    const stark = try @import("stwo_postcard").deserializeProof(rec.Hasher, caller_allocator, fbs.reader());
    return .{ .stark = stark, .claimed_sums = try caller_allocator.dupe(QM31, sums.items) };
}

/// The interaction trace of `parts` for lookup elements `el`: its columns in storage order, as
/// `proveOpts` commits them, and the claimed sums of the components with lookups. The host half of
/// the resident CUDA prover (src/gpu/cuda/prover.zig), which commits the columns on the device.
pub const InteractionTrace = struct {
    columns: []prover_pcs.ColumnEvaluation,
    sums: []QM31,
};

pub fn interactionTrace(a: std.mem.Allocator, parts: []const Part, mains: []const []const []const M31, el: lookup_transcript.LookupElements) !InteractionTrace {
    var cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    errdefer cols.deinit(a);
    var sums = std.ArrayList(QM31).empty;
    errdefer sums.deinit(a);
    for (parts, mains) |p, m| {
        if (p.air.lookups.len == 0) continue;
        var fr = try fractions(a, p, m, el);
        defer fr.deinit(a);
        const built = try logup_columns.build(a, p.log_size, fr.batches, &fr, struct {
            fn f(ctx: *const Fractions, row: usize, out: []logup_columns.Fraction) anyerror!void {
                return ctx.fill(row, out);
            }
        }.f);
        defer a.free(built.columns);
        try cols.appendSlice(a, built.columns);
        try sums.append(a, built.claimed_sum);
    }
    return .{ .columns = try cols.toOwnedSlice(a), .sums = try sums.toOwnedSlice(a) };
}

/// The preprocessed and main roots `proveOpts` commits (CPU, compact storage). The resident CUDA
/// prover needs them on the host to draw the lookup elements before its one device transaction.
pub fn traceRoots(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31) ![2]rec.Hasher.Hash {
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var scheme = try E.initRevision(a, cfg);
    defer E.deinit(&scheme, a);
    scheme.setCompactPolynomialStorage(0);
    var channel = rec.Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    try scheme.commitOwnedStreamingWithRecorder(a, try preprocessedStorage(a, parts), 0, null, &channel);
    try E.flushPendingCommit(&scheme, a, &channel);
    try mixStatements(&channel, a, parts);
    var main_cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    for (parts, mains) |p, m| {
        if (m.len != p.air.n_main) return error.InvalidPreparedGeometry;
        const st = try base.toStorage(a, p.log_size, m);
        defer a.free(st);
        try main_cols.appendSlice(a, st);
    }
    try scheme.commitOwnedStreamingWithRecorder(a, try main_cols.toOwnedSlice(a), 0, null, &channel);
    try E.flushPendingCommit(&scheme, a, &channel);
    var roots = try scheme.roots(a);
    defer roots.deinit(a);
    return .{ roots.items[0], roots.items[1] };
}

/// The preprocessed columns of `parts` in storage order (as committed).
pub fn preprocessedColumns(a: std.mem.Allocator, parts: []const Part) ![]prover_pcs.ColumnEvaluation {
    return preprocessedStorage(a, parts);
}

/// Every preprocessed column of `parts` in natural (coset) row order, generated on all cores: what
/// the CUDA prover uploads (it reorders on the device, src/gpu/cuda/reorder.zig).
pub fn preprocessedNatural(a: std.mem.Allocator, parts: []const Part) ![]prover_pcs.ColumnEvaluation {
    var n: usize = 0;
    for (parts) |p| n += p.air.preprocessed.len;
    const out = try a.alloc(prover_pcs.ColumnEvaluation, n);
    var made: usize = 0;
    errdefer {
        for (out[0..made]) |c| a.free(c.values);
        a.free(out);
    }
    const defs = try a.alloc(ir.PreCol, n);
    defer a.free(defs);
    const values = try a.alloc([]M31, n);
    defer a.free(values);
    for (parts) |p| for (p.air.preprocessed) |def| {
        values[made] = try a.alloc(M31, @as(usize, 1) << @intCast(p.log_size));
        defs[made] = def;
        out[made] = .{ .log_size = p.log_size, .values = values[made] };
        made += 1;
    };
    ir.fillParallel(defs, values);
    return out;
}

/// Returns `column`'s whole pages to the OS; their contents become undefined. For witness columns
/// the caller will not read again (`Options.discard_mains`), possibly inside an arena.
fn discardPages(column: []const M31) void {
    const page = std.heap.pageSize();
    const start = std.mem.alignForward(usize, @intFromPtr(column.ptr), page);
    const end = std.mem.alignBackward(usize, @intFromPtr(column.ptr) + column.len * @sizeOf(M31), page);
    if (end <= start) return;
    const advice: u32 = if (@import("builtin").os.tag == .macos) 7 else std.posix.MADV.DONTNEED; // MADV_FREE_REUSABLE
    std.posix.madvise(@ptrFromInt(start), end - start, advice) catch {};
}

/// The proof's bytes: claimed sums, then the STARK proof in stwo's postcard encoding.
pub fn proofBytes(a: std.mem.Allocator, proof: Proof) ![]u8 {
    var out = std.ArrayList(u8).empty;
    for (proof.claimed_sums) |sum| for (sum.toM31Array()) |x| {
        var w: [4]u8 = undefined;
        std.mem.writeInt(u32, &w, x.toU32(), .little);
        try out.appendSlice(a, &w);
    };
    try @import("stwo_postcard").serializeProof(rec.Hasher, out.writer(a), proof.stark);
    return out.toOwnedSlice(a);
}

/// Parity (b): the system proved with the interpreter's composition, with stwo-zig's STWZEVA
/// runtime, and with that runtime plus the C-generated kernels gives byte-identical proofs, and
/// the STWZEVA one passes `verifyExt`.
/// Returns the proof size in bytes.
pub fn checkStwzevaProof(comptime E: type, a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31, ext: []const PubEntry) !usize {
    const want = try proofBytes(a, try proveWith(E, a, cfg, parts, mains, .interpreter));
    const proof = try proveWith(E, a, cfg, parts, mains, .stwzeva);
    const got = try proofBytes(a, proof);
    try std.testing.expectEqualSlices(u8, want, got);
    try std.testing.expectEqualSlices(u8, want, try proofBytes(a, try proveWith(E, a, cfg, parts, mains, .stwzeva_native)));
    // The block prover's default (compact, witness discarded), on a copy of the witness.
    {
        const copies = try a.alloc([]const []const M31, mains.len);
        for (copies, mains) |*c, m| {
            const cols = try a.alloc([]const M31, m.len);
            for (cols, m) |*d, col| d.* = try a.dupe(M31, col);
            c.* = cols;
        }
        try std.testing.expectEqualSlices(u8, want, try proofBytes(a, try proveOpts(E, a, cfg, parts, copies, .{ .storage = .compact, .discard_mains = true })));
        // Row-tiled composition.
        try std.testing.expectEqualSlices(u8, want, try proofBytes(a, try proveOpts(E, a, cfg, parts, mains, .{ .storage = .compact, .tile_columns = 4 })));
    }
    // Storage policies change only memory, never bytes.
    for ([_]Storage{ .evaluations_only, .compact }) |storage| {
        for ([_]Composition{ .interpreter, .stwzeva }) |c|
            try std.testing.expectEqualSlices(u8, want, try proofBytes(a, try proveOpts(E, a, cfg, parts, mains, .{ .composition = c, .storage = storage })));
    }
    try verifyExt(a, cfg, parts, ext, proof);
    return got.len;
}

/// Verifies a system proof. `a` should be an arena.
pub fn verify(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, proof: Proof) !void {
    return verifyImpl(a, cfg, parts, &.{}, proof, null, false, null);
}

/// `verify` with public lookup entries: the relations balance with them included.
pub fn verifyExt(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof) !void {
    return verifyImpl(a, cfg, parts, ext, proof, null, false, null);
}

/// `verifyExt` against a preprocessed root the caller computed with `preprocessedRoot(cfg, parts)`
/// for these same `cfg` and parts' AIRs and sizes (it depends on nothing else), e.g. once for many
/// proofs of one shape: computing it costs as much memory as committing the preprocessed columns.
pub fn verifyExtPre(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof, pre_root: rec.Hasher.Hash) !void {
    return verifyImpl(a, cfg, parts, ext, proof, null, false, pre_root);
}

/// `verify`, also capturing what the in-circuit verifier needs (`plain_verifier.fromCapture`).
/// Consumes `proof`; see `verifyCaptureBorrowed` to keep it.
pub fn verifyCapture(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof, capture: *core.verifier.ProofCapture(rec.Hasher)) !void {
    return verifyImpl(a, cfg, parts, ext, proof, capture, false, null);
}

/// `verifyCapture` without consuming `proof` (stwo-zig's borrowed capture), so the same proof can
/// then be converted for the in-circuit verifier: one proof per segment instead of two.
pub fn verifyCaptureBorrowed(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: *const Proof, capture: *core.verifier.ProofCapture(rec.Hasher)) !void {
    return verifyImpl(a, cfg, parts, ext, proof.*, capture, true, null);
}

/// `Σ mult / (Σ eᵢ αⁱ − z)` over public entries.
pub fn extSum(ext: []const PubEntry, el: lookup_transcript.LookupElements) !QM31 {
    var sum = QM31.zero();
    var vals: [component_mod.MAX_LOOKUP_VALS]QM31 = undefined;
    for (ext) |e| {
        if (e.vals.len > vals.len) return error.LookupTooWide;
        for (e.vals, 0..) |v, i| vals[i] = QM31.fromBase(v);
        const d = component_mod.denominator(e.rel, vals[0..e.vals.len], el.z, el.alpha);
        sum = sum.add(QM31.fromBase(e.mult).mul(try d.inv()));
    }
    return sum;
}

fn verifyImpl(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof, capture: ?*core.verifier.ProofCapture(rec.Hasher), borrowed: bool, pre_root: ?rec.Hasher.Hash) !void {
    _ = try maxLogSize(parts);
    const lookups = hasLookups(parts);
    const n_trees: usize = if (lookups) 3 else 2;
    if (proof.stark.commitment_scheme_proof.commitments.items.len != n_trees + 1) return error.InvalidProofShape;
    var channel = rec.Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(rec.Hasher, rec.MerkleChannel).init(a, cfg);
    defer scheme.deinit(a);

    var pre_logs = std.ArrayList(u32).empty;
    var main_logs = std.ArrayList(u32).empty;
    var inter_logs = std.ArrayList(u32).empty;
    for (parts) |p| {
        try pre_logs.appendNTimes(a, p.log_size, p.air.n_preprocessed);
        try main_logs.appendNTimes(a, p.log_size, p.air.n_main);
        try inter_logs.appendNTimes(a, p.log_size, 4 * component_mod.nBatches(p.air.*));
    }
    const roots = proof.stark.commitment_scheme_proof.commitments.items;
    const expected_pre = pre_root orelse try preprocessedRoot(a, cfg, parts);
    if (!std.mem.eql(u8, std.mem.asBytes(&expected_pre), std.mem.asBytes(&roots[0]))) return error.PreprocessedRootMismatch;
    try scheme.commit(a, roots[0], pre_logs.items, &channel);
    try mixStatements(&channel, a, parts);
    try scheme.commit(a, roots[1], main_logs.items, &channel);

    const comps = try components(a, parts);
    if (lookups) {
        const el = try lookup_transcript.drawLookupElements(a, &channel);
        var n_with: usize = 0;
        for (parts) |p| {
            if (p.air.lookups.len != 0) n_with += 1;
        }
        if (proof.claimed_sums.len != n_with) return error.InvalidProofShape;
        // The relations balance: the claimed sums and the public entries add to zero.
        var total = try extSum(ext, el);
        for (proof.claimed_sums) |s| total = total.add(s);
        if (!total.isZero()) return error.LookupsUnbalanced;
        var k: usize = 0;
        for (parts, comps) |p, *c| {
            if (p.air.lookups.len == 0) continue;
            c.logup = .{ .z = el.z, .alpha = el.alpha, .claimed_sum = proof.claimed_sums[k] };
            k += 1;
        }
        lookup_transcript.mixInteractionClaim(&channel, proof.claimed_sums);
        try scheme.commit(a, roots[2], inter_logs.items, &channel);
    }
    const verifiers = try a.alloc(core.air.components.Component, comps.len);
    for (comps, verifiers) |*c, *v| v.* = c.asVerifierComponent();
    if (capture) |c| {
        if (borrowed)
            try core.verifier.verifyBorrowedWithProofCapture(rec.Hasher, rec.MerkleChannel, a, verifiers, &channel, &scheme, &proof.stark, c)
        else
            try core.verifier.verifyWithProofCapture(rec.Hasher, rec.MerkleChannel, a, verifiers, &channel, &scheme, proof.stark, c);
    } else
        try core.verifier.verify(rec.Hasher, rec.MerkleChannel, a, verifiers, &channel, &scheme, proof.stark);
}

// ---------------------------------------------------------------- tests

/// Toy system from Lean (`Testing/ByteLookup.lean`, theorem `user_bytes`): a byte table
/// (preprocessed 0..255, main multiplicity column) and a user whose main column is looked up with
/// multiplicity −1.
pub fn byteSystem(a: std.mem.Allocator) ![2]ir.Air {
    return .{
        (try ir.Air.parseJson(a, @embedFile("air:byte_table"))).value,
        (try ir.Air.parseJson(a, @embedFile("air:byte_user"))).value,
    };
}

test "LogUp system: a byte range check proves and verifies; out-of-range values are rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try byteSystem(a);
    const log_size: u32 = 8;
    const n = 256;
    const parts = [_]Part{ .{ .air = &airs[0], .log_size = log_size }, .{ .air = &airs[1], .log_size = log_size } };
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);

    var prng = std.Random.DefaultPrng.init(7);
    const x = try a.alloc(M31, n);
    const mult = try a.alloc(M31, n);
    @memset(mult, M31.zero());
    for (x) |*v| {
        const b = prng.random().int(u8);
        v.* = M31.fromCanonical(b);
        mult[b] = mult[b].add(M31.one());
    }
    const mains = [_][]const []const M31{ &.{mult}, &.{x} };
    try verify(a, cfg, &parts, try prove(E, a, cfg, &parts, &mains));

    // A value outside the table cannot balance (whatever the multiplicities).
    const bad = try a.dupe(M31, x);
    bad[3] = M31.fromCanonical(300);
    const bad_mains = [_][]const []const M31{ &.{mult}, &.{bad} };
    try std.testing.expectError(error.LookupsUnbalanced, verify(a, cfg, &parts, try prove(E, a, cfg, &parts, &bad_mains)));

    // Forged claimed sums that add to zero do not match the committed interaction columns.
    var forged = try prove(E, a, cfg, &parts, &bad_mains);
    forged.claimed_sums[1] = forged.claimed_sums[0].neg();
    try std.testing.expect(std.meta.isError(verify(a, cfg, &parts, forged)));
}

test "LogUp system: the byte system's STWZEVA-composed proof is byte-identical and verifies" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try byteSystem(a);
    const log_size: u32 = 8;
    const parts = [_]Part{ .{ .air = &airs[0], .log_size = log_size }, .{ .air = &airs[1], .log_size = log_size } };
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    var prng = std.Random.DefaultPrng.init(7);
    const x = try a.alloc(M31, 256);
    const mult = try a.alloc(M31, 256);
    @memset(mult, M31.zero());
    for (x) |*v| {
        const b = prng.random().int(u8);
        v.* = M31.fromCanonical(b);
        mult[b] = mult[b].add(M31.one());
    }
    const mains = [_][]const []const M31{ &.{mult}, &.{x} };
    const n = try checkStwzevaProof(rec.Engine(@import("stwo_cpu_backend").CpuBackend), a, cfg, &parts, &mains, &.{});
    std.debug.print("byte system: STWZEVA proof byte-identical ({d} bytes)\n", .{n});
}

test "LogUp system of mixed sizes (lifting, D-045): proves, verifies, STWZEVA byte-identical; a wrong table fails" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try byteSystem(a);
    // The table at 2^8, the user at 2^10 (and the reverse sizes below).
    for ([_][2]u32{ .{ 8, 10 }, .{ 10, 8 } }) |logs| {
        const n_user = @as(usize, 1) << @intCast(logs[1]);
        const parts = [_]Part{ .{ .air = &airs[0], .log_size = logs[0] }, .{ .air = &airs[1], .log_size = logs[1] } };
        const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), @max(logs[0], logs[1]));
        var prng = std.Random.DefaultPrng.init(11);
        const x = try a.alloc(M31, n_user);
        const mult = try a.alloc(M31, @as(usize, 1) << @intCast(logs[0]));
        @memset(mult, M31.zero());
        for (x) |*v| {
            const b = prng.random().int(u8);
            v.* = M31.fromCanonical(b);
            mult[b] = mult[b].add(M31.one());
        }
        const mains = [_][]const []const M31{ &.{mult}, &.{x} };
        const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
        const n = try checkStwzevaProof(E, a, cfg, &parts, &mains, &.{});
        std.debug.print("mixed sizes {d}/{d}: proof byte-identical across evaluators ({d} bytes)\n", .{ logs[0], logs[1], n });
        // The same columns claimed at uniform sizes do not verify against the mixed proof.
        const uniform = [_]Part{ .{ .air = &airs[0], .log_size = @max(logs[0], logs[1]) }, .{ .air = &airs[1], .log_size = @max(logs[0], logs[1]) } };
        try std.testing.expect(std.meta.isError(verify(a, cfg, &uniform, try prove(E, a, cfg, &parts, &mains))));
    }
}
