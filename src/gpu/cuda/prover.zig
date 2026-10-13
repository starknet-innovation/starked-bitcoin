//! The resident CUDA block-system prover: same transcript and proof bytes as `system.proveOpts`
//! (src/air/system.zig), adapted from `circuit_cuda/resident_prover.zig`.
//!
//! First version (docs/design/gpu-cuda.md § Witness and interaction):
//! 1. Host: the preprocessed and main roots (`system.traceRoots`, CPU), the prefix replay to (z, α)
//!    (`transcript.HostSink`), the interaction columns and claimed sums (`system.interactionTrace`).
//! 2. Device, one transaction (`proofPass`): ingress uploads all three trace trees as evaluations
//!    (into staging slots), the statement, claims, z and α⁰…α^w; the schedule
//!    (`pipeline.zig`) assembles them from staging (`.trace_generation`), commits, draws (z, α) itself and
//!    runs the STARK tail; the terminal bundle decodes to `system.Proof`.
//! The runtime runs every stage in order with kernel work in each, so a roots-only device
//! transaction is not possible; device LogUp will remove the host commit.
//! The caller verifies the result (`system.verifyExt`); the roots of pass 1 must equal pass 2's.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const prover_engine = @import("stwo_prover_engine");
const cuda = @import("stwo_cuda_backend");
const cc = @import("stwo_circuit_cuda_integration");
const catalog_mod = @import("catalog.zig");
const plan_mod = @import("plan.zig");
const transcript = @import("transcript.zig");
const memory = @import("memory.zig");
const masks = @import("masks.zig");
const terminal = @import("terminal.zig");
const controller = @import("composition_controller.zig");
const pipeline = @import("pipeline.zig");
const system = sb.air.system;
const rec = sb.air.prove_rec;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const common = cuda.runtime.stages.common;
const field = cuda.abi.field;
const arena = cuda.runtime.arena;
const Transaction = cuda.runtime.proof_transaction.ResidentProofTransaction;
const ColumnEvaluation = prover_engine.pcs.ColumnEvaluation;

/// SM targets the session accepts: the archive's (`-Dcuda-arch`, e.g. "sm_80,sm_89,sm_90").
pub const accepted_sms = parseSms(@import("cuda_build").architectures);

fn parseSms(comptime text: []const u8) [countSms(text)]u32 {
    @setEvalBranchQuota(100_000);
    var out: [countSms(text)]u32 = undefined;
    var it = std.mem.tokenizeAny(u8, text, ", ");
    var i: usize = 0;
    while (it.next()) |tok| : (i += 1) {
        const digits = if (std.mem.startsWith(u8, tok, "sm_")) tok[3..] else tok;
        out[i] = std.fmt.parseInt(u32, digits, 10) catch @compileError("bad -Dcuda-arch entry: " ++ tok);
    }
    return out;
}
fn countSms(comptime text: []const u8) usize {
    var it = std.mem.tokenizeAny(u8, text, ", ");
    var n: usize = 0;
    while (it.next()) |_| n += 1;
    return n;
}

pub const Input = struct {
    parts: []const system.Part,
    /// `mains[i]`: part `i`'s main columns in natural row order.
    mains: []const []const []const M31,
    config: core.pcs.config_v2.PcsConfigV2,
    catalog: *const catalog_mod.Catalog,
};

pub const Result = struct {
    proof: system.Proof,
    verdict: cuda.runtime.verdict.Verdict,
    planned_arena_bytes: usize,
};

/// Everything planned before any device work, for one proof.
pub const Prepared = struct {
    allocator: std.mem.Allocator,
    plans: plan_mod.Plans,
    statement: transcript.Statement,
    terminal_layout: terminal.Layout,
    terminal_decommit: terminal.Decommit,
    terminal_bundle: terminal.Bundle,
    memory: memory.Plan,
    claims_mixed: usize,
    alpha_powers: usize,

    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part, cat: *const catalog_mod.Catalog, config: core.pcs.config_v2.PcsConfigV2) !Prepared {
        var plans = try plan_mod.Plans.init(allocator, parts, cat, config);
        errdefer plans.deinit();
        var statement = try transcript.Statement.init(allocator, parts);
        errdefer statement.deinit(allocator);
        var claims: usize = 0;
        for (parts) |p| claims += @intFromBool(p.air.lookups.len != 0);
        if (claims == 0) return error.ResidentNeedsLookups;
        const layout = try terminal.Layout.init(&plans.geometry, &plans.oods, claims, config);
        const decommit = terminal.Decommit{ .capacity_words = plans.decommit.topology.assembly_capacity_words };
        var bundle = try terminal.Bundle.init(allocator, layout, decommit);
        errdefer bundle.deinit(allocator);
        const alpha_powers = plan_mod.lookupWidth(parts) + 1;
        var mem = try memory.Plan.init(allocator, .{
            .twiddle_words = plans.twiddle_words,
            .statement_words = statement.words.len,
            .claims_mixed = claims,
            .claims_component = parts.len,
            .alpha_powers = alpha_powers,
            .commitments = &plans.commits,
            .composition = &plans.composition,
            .oods = &plans.oods,
            .quotient = &plans.quotient,
            .fri = &plans.fri,
            .decommit = &plans.decommit,
            .terminal = &bundle,
        });
        errdefer mem.deinit();
        return .{
            .allocator = allocator,
            .plans = plans,
            .statement = statement,
            .terminal_layout = layout,
            .terminal_decommit = decommit,
            .terminal_bundle = bundle,
            .memory = mem,
            .claims_mixed = claims,
            .alpha_powers = alpha_powers,
        };
    }

    pub fn deinit(self: *Prepared) void {
        self.memory.deinit();
        self.terminal_bundle.deinit(self.allocator);
        self.statement.deinit(self.allocator);
        self.plans.deinit();
        self.* = undefined;
    }
};

/// Storage-order evaluations of every trace column, by tree (host memory).
pub const HostTrees = struct {
    trees: [3][]ColumnEvaluation = .{ &.{}, &.{}, &.{} },

    pub fn deinit(self: *HostTrees, allocator: std.mem.Allocator) void {
        for (self.trees) |t| {
            for (t) |c| allocator.free(c.values);
            allocator.free(t);
        }
    }
};

/// Bit-reversed evaluations of the preprocessed and main trees.
pub fn hostTraceTrees(allocator: std.mem.Allocator, input: Input) !HostTrees {
    var out = HostTrees{};
    errdefer out.deinit(allocator);
    out.trees[0] = try system.preprocessedColumns(allocator, input.parts);
    var main = std.ArrayList(ColumnEvaluation).empty;
    errdefer {
        for (main.items) |c| allocator.free(c.values);
        main.deinit(allocator);
    }
    for (input.parts, input.mains) |p, m| {
        if (m.len != p.air.n_main) return error.InvalidPreparedGeometry;
        const st = try sb.air.prove.toStorage(allocator, p.log_size, m);
        defer allocator.free(st);
        try main.appendSlice(allocator, st);
    }
    out.trees[1] = try main.toOwnedSlice(allocator);
    return out;
}

/// The whole proof (see the file comment).
pub fn prove(allocator: std.mem.Allocator, input: Input) !Result {
    var prepared = try Prepared.init(allocator, input.parts, input.catalog, input.config);
    defer prepared.deinit();
    var host = try hostTraceTrees(allocator, input);
    defer host.deinit(allocator);
    var twiddles = try Twiddles.init(allocator, prepared.plans.twiddle_words);
    defer twiddles.deinit();

    // Host: the trace roots, (z, α), interaction columns, claims.
    const roots = try system.traceRoots(allocator, input.config, input.parts, input.mains);
    const el = try lookupElements(&prepared, input.config, roots);
    const inter = try system.interactionTrace(allocator, input.parts, input.mains, el);
    host.trees[2] = inter.columns;
    defer allocator.free(inter.sums);

    // Device: the proof.
    var result = try proofPass(allocator, &prepared, &host, &twiddles, input, el, inter.sums);
    errdefer result.proof.stark.deinit(allocator);
    const proved = result.proof.stark.commitment_scheme_proof.commitments.items;
    if (!std.mem.eql(u8, std.mem.asBytes(&proved[0]), std.mem.asBytes(&roots[0])) or
        !std.mem.eql(u8, std.mem.asBytes(&proved[1]), std.mem.asBytes(&roots[1])))
        return error.ResidentRootsDiverged; // device and host commits of trees 0–1 differ
    return result;
}

/// The host replay of our prefix up to the lookup draw, from pass 1's roots.
pub fn lookupElements(prepared: *const Prepared, config: core.pcs.config_v2.PcsConfigV2, roots: [2]rec.Hasher.Hash) !core.channel.lookup_transcript.LookupElements {
    var sink = transcript.HostSink{};
    var prefix = transcript.Prefix(transcript.HostSink){ .sink = &sink };
    try prefix.mixConfig(config);
    try prefix.commitPreprocessed(roots[0]);
    try prefix.mixStatement(prepared.statement, prepared.statement.words);
    try prefix.commitMain(roots[1]);
    return prefix.drawLookupElements();
}

/// The resident proof (one device transaction).
pub fn proofPass(
    allocator: std.mem.Allocator,
    prepared: *const Prepared,
    host: *const HostTrees,
    twiddles: *const Twiddles,
    input: Input,
    el: core.channel.lookup_transcript.LookupElements,
    sums: []const QM31,
) !Result {
    const plans = &prepared.plans;
    const blowup = input.config.fri_config.log_blowup_factor;
    var tx = try Transaction.openPrepared(allocator, &accepted_sms, try prepared.memory.placement.clone(allocator));
    var finished = false;
    defer if (!finished) tx.abort() catch {};
    const session = tx.proofSession();
    var views = try memory.bind(allocator, &tx, .{
        .plans = &prepared.memory,
        .commitments = &plans.commits,
        .fri = &plans.fri,
        .terminal = &prepared.terminal_bundle,
    });
    defer views.deinit();

    // ---- ingress: host data.
    try session.context.uploadSlice(u32, views.twiddles_forward, twiddles.forwardWords());
    try session.context.uploadSlice(u32, views.twiddles_inverse, twiddles.inverseWords());
    for (views.columns, host.trees) |dst, src| try uploadTree(session, dst, src);
    try session.context.uploadSlice(u32, views.statement, prepared.statement.words);
    try uploadFelts(allocator, session, try views.claims_mixed.cast(u32), sums);
    const per_component = try allocator.alloc(QM31, input.parts.len);
    defer allocator.free(per_component);
    {
        var k: usize = 0;
        for (input.parts, per_component) |p, *s| {
            if (p.air.lookups.len == 0) {
                s.* = QM31.zero();
            } else {
                s.* = sums[k];
                k += 1;
            }
        }
    }
    try uploadFelts(allocator, session, try views.claims_component.cast(u32), per_component);
    try uploadFelts(allocator, session, try views.relation_z.cast(u32), &.{el.z});
    const powers = try allocator.alloc(QM31, prepared.alpha_powers);
    defer allocator.free(powers);
    for (powers, 0..) |*x, i| x.* = if (i == 0) QM31.one() else powers[i - 1].mul(el.alpha);
    try uploadFelts(allocator, session, try views.relation_alpha_powers.cast(u32), powers);
    try tx.zeroResidentSlice(u32, .ingress, (try prepared.memory.slot(.error_flag, 0)).requirement.id, 0, 1);
    const terminal_id = (try prepared.memory.slot(.terminal_bundle, 0)).requirement.id;
    try tx.zeroResidentSlice(u32, .ingress, terminal_id, 0, prepared.terminal_bundle.total_words);
    try session.context.uploadSlice(u32, try views.proof.bundle.sub(0, prepared.terminal_bundle.static_header.len), prepared.terminal_bundle.static_header);

    // ---- ingress: stage priming.
    var sink = try transcript.NativeSink.init(session, views.transcript, plans.geometry.identity);
    try sink.prime(input.config);
    var commits: [4]cc.resident_commit.Bound = undefined;
    for (&commits, &plans.commits, views.commits) |*bound, *plan, buffers| {
        bound.* = try cc.resident_commit.Bound.init(plan, buffers);
        try bound.prime(session);
    }
    var evaluator = try controller.Bound.init(allocator, &plans.composition, views.composition);
    defer evaluator.deinit();
    try evaluator.prime(session);
    try plans.oods.upload(session, views.oods);
    var oods_bound = try plans.oods.bind(allocator, views.commits);
    defer oods_bound.deinit();
    var quotient_bound = try masks.prepareQuotient(allocator, session, &plans.bundle, &plans.geometry, &plans.oods, blowup, views.commits, views.oods, views.quotient, views.twiddles_forward, views.twiddles_inverse);
    defer quotient_bound.deinit();
    try plans.fri.upload(session, views.fri, views.twiddles_inverse);
    try plans.decommit.upload(session, views.decommit);
    try tx.finishIngress();

    var schedule = pipeline.Native{
        .transaction = &tx,
        .sink = &sink,
        .statement = &prepared.statement,
        .statement_words = views.statement,
        .claims_mixed = views.claims_mixed,
        .composition = &evaluator,
        .oods = &oods_bound,
        .quotient = &quotient_bound,
        .fri_plan = &plans.fri,
        .decommit_plan = &plans.decommit,
        .commitments = &commits,
        .columns = .{ views.columns[0], views.columns[1], views.columns[2] },
        .staging = views.staging,
        .error_flag = views.error_flag,
        .oods_view = views.oods,
        .quotient_challenge = views.quotient.challenge,
        .fri_view = views.fri,
        .decommit_view = views.decommit,
        .proof = views.proof,
        .twiddles_inverse = views.twiddles_inverse,
    };
    try schedule.execute(input.config);
    const transport = try allocator.alloc(u32, prepared.terminal_bundle.total_words);
    defer allocator.free(transport);
    const verdict = try tx.assembleAndFinish(transport, terminal_id);
    finished = true;
    if (!verdict.isResident()) return error.NonresidentProof;
    var decoded = terminal.Proof.decode(allocator, prepared.terminal_layout, prepared.terminal_decommit, transport, .{
        .operations = verdict.counters.d2h_proof_operations,
        .bytes = verdict.counters.d2h_proof_bytes,
        .runtime_compile_attempts = verdict.aot.aot_misses,
        .cpu_fallback_attempts = verdict.counters.cpu_fallback_attempts,
    }) catch |err| {
        // The device-written header word 15 is the final-layer degree verdict (0 = accepted).
        std.debug.print("cuda: terminal decode failed: {s}; header {any}\n", .{ @errorName(err), transport[0..@min(transport.len, 16)] });
        inline for (.{ .trace_commitments, .sampled_values, .fri_commitments, .fri_last_layer, .proof_of_work, .decommitment }) |kind| {
            const sec = prepared.terminal_bundle.section(kind);
            std.debug.print("  section {s}: words {d}..{d}, head {any}\n", .{ @tagName(kind), sec.offset_words, sec.offset_words + sec.words, transport[sec.offset_words..][0..@min(sec.words, 8)] });
        }
        return err;
    };
    defer decoded.deinit(allocator);
    return .{
        .proof = try decoded.toSystemProof(allocator, &plans.proof_layout, input.config),
        .verdict = verdict,
        .planned_arena_bytes = try prepared.memory.bytes(),
    };
}

/// Each column's destination inside a tree's coefficient buffer (`resident_commit` cohort order).
fn inPlaceColumns(allocator: std.mem.Allocator, plan: *const cc.resident_commit.Plan, coefficients: common.Words) ![]common.Words {
    const out = try allocator.alloc(common.Words, plan.column_logs.len);
    errdefer allocator.free(out);
    for (plan.cohorts) |cohort| {
        const rows = @as(usize, 1) << @intCast(cohort.trace_log);
        for (0..cohort.count) |local| out[cohort.first_column + local] = try coefficients.sub(cohort.coefficient_offset + local * rows, rows);
    }
    return out;
}

fn uploadTree(session: anytype, destinations: []const common.Words, columns: []const ColumnEvaluation) !void {
    if (destinations.len != columns.len) return error.InvalidResidentInput;
    for (destinations, columns) |dst, col| {
        if (dst.len != col.values.len) return error.InvalidResidentInput;
        const words: [*]const u32 = @ptrCast(col.values.ptr);
        try session.context.uploadSlice(u32, dst, words[0..col.values.len]);
    }
}

fn uploadFelts(allocator: std.mem.Allocator, session: anytype, dst: common.Words, felts: []const QM31) !void {
    const words = try allocator.alloc(u32, felts.len * 4);
    defer allocator.free(words);
    for (felts, 0..) |f, i| for (f.toM31Array(), 0..) |x, k| {
        words[4 * i + k] = x.toU32();
    };
    try session.context.uploadSlice(u32, dst, words);
}

/// Forward and inverse twiddles of the FRI input domain's half coset (as `resident_prover`).
pub const Twiddles = struct {
    allocator: std.mem.Allocator,
    tree: prover_engine.poly.twiddles.TwiddleTree([]M31),

    pub fn init(allocator: std.mem.Allocator, words: usize) !Twiddles {
        if (words == 0 or !std.math.isPowerOfTwo(words)) return error.InvalidTwiddles;
        const circle_log: u32 = @intCast(std.math.log2_int(usize, words) + 1);
        const coset = core.poly.circle.CanonicCoset.new(circle_log).circleDomain().half_coset;
        var tree = try prover_engine.poly.twiddles.precomputeM31Parallel(allocator, coset);
        errdefer prover_engine.poly.twiddles.deinitM31(allocator, &tree);
        if (tree.twiddles.len != words or tree.itwiddles.len != words) return error.InvalidTwiddles;
        return .{ .allocator = allocator, .tree = tree };
    }
    pub fn deinit(self: *Twiddles) void {
        prover_engine.poly.twiddles.deinitM31(self.allocator, &self.tree);
    }
    pub fn forwardWords(self: *const Twiddles) []const u32 {
        const p: [*]const u32 = @ptrCast(self.tree.twiddles.ptr);
        return p[0..self.tree.twiddles.len];
    }
    pub fn inverseWords(self: *const Twiddles) []const u32 {
        const p: [*]const u32 = @ptrCast(self.tree.itwiddles.ptr);
        return p[0..self.tree.itwiddles.len];
    }
};

test "cuda resident prover: the whole device schedule typechecks against the native CUDA session" {
    const entry: *const fn (std.mem.Allocator, Input) anyerror!Result = &prove;
    try std.testing.expect(@intFromPtr(entry) != 0);
}
