//! `cuda-widenode`: the wide block node (docs/design/block-rec.md § Wide nodes) on stwo-zig's resident
//! CUDA circuit prover (`circuit_cuda.resident_prover`). Two experiments:
//!
//!   cuda-widenode A <epoch dir> <from> <k>... [--fold f] [--plan-only] [--cpu] [--cpu-only]
//!     A block leaf at its natural size (k = 1: `block_rec.leafCircuitOf`, not padded; k > 1: the packed
//!     circuit `block_pack.buildPacked`), FRI fold `f` (default 1; last layer 0 at fold 1, `trace log
//!     mod f` otherwise). Does the CUDA circuit prover work at fold 1, and how fast? `--cpu-only` plans
//!     the arena, then proves and verifies with the CPU circuit prover only (any host, no GPU).
//!
//!   cuda-widenode B <epoch dir> <from> [--plan-only] [--cpu] [--cpu-node]
//!     The 8-child wide node at fold 4, last layer 0: the shared shape `block_node_k.shape(3, …)` raised
//!     to a trace log that is a multiple of 4 (2^24). The 8 block leaves `<from> … <from+7>` are proved
//!     at that shape on the GPU and turned into `block_rec.Proved` children (the verifier proof, request
//!     and circuit hash a `leaf.CircuitProof` holds, from the verified device proof); then the node
//!     circuit over them is proved on the GPU. Its output digest must be `block_node_k.expected`'s.
//!
//! Every GPU proof is verified twice natively: `resident_verifier.verify` (the device proof) and
//! `leaf.verifyCircuit` (stwo-zig's circuit verifier on the serialized verifier proof, the one the node
//! verifies in-circuit). `--cpu` also proves every circuit with the CPU circuit prover
//! (`leaf.proveCircuit`) and requires byte-identical proofs, the same circuit hash and preprocessed
//! root; in B, `--cpu-node` does that for the node only. `--plan-only` stops after host planning and
//! prints the planned device arena (no GPU: links against the stubs); in B it plans the leaves and the
//! node's topology (no child proofs needed).
//!
//! Links stwo-zig's circuit archive (its own `circuit_eval` set), not ours: `-Dcuda-circuit-archive`.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const cuda = @import("stwo_circuit_cuda_integration");
const cuda_backend = @import("stwo_cuda_backend");

const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const finalize = circuit.common.finalize;
const preprocessed = circuit.common.preprocessed;
const component_list = circuit.common.component_list;
const Context = circuit.builder.Context;
const NoValue = circuit.builder.NoValue;
const ComponentSizes = finalize.ComponentSizes;
const PF = sb.block.proof_file;
const bs = sb.block.system;
const leaf = sb.recursion.leaf;
const br = sb.recursion.block_rec;
const wk = sb.recursion.block_node_k;

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

fn gib(n: usize) f64 {
    return @as(f64, @floatFromInt(n)) / (1 << 30);
}

fn log2(n: usize) u32 {
    return if (n <= 1) 0 else std.math.log2_int_ceil(usize, n);
}

/// Host peak RSS in GiB (getrusage: KiB on Linux, bytes on macOS).
fn rssGib() f64 {
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    const raw: usize = @intCast(ru.maxrss);
    const bytes = if (@import("builtin").os.tag == .macos) raw else raw * 1024;
    return gib(bytes);
}

fn sha(bytes: []const u8) [64]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return std.fmt.bytesToHex(d, .lower);
}

fn traceLogOf(target: ComponentSizes) !u32 {
    const layout = try preprocessed.ColumnLayout.fromComponentSizes(target);
    return layout.traceLogSize();
}

/// The device arena `resident_prover.prove` would plan for `input` (its own planning steps, standalone
/// session: no static retention).
fn plannedArena(allocator: std.mem.Allocator, input: cuda.resident_prover.Input) !usize {
    const layout = input.preprocessed.layout();
    var geometry = try cuda.geometry.Geometry.init(allocator, &layout, input.air, input.catalog, input.config);
    defer geometry.deinit();
    const blowup = input.config.fri_config.log_blowup_factor;
    _ = try cuda.resident_witness.Plan.init(&layout, input.preprocessed.first_permutation_row);
    const interaction_plan = try cuda.resident_interaction.Plan.init(&layout);
    var composition_plan = try cuda.resident_composition.Plan.init(allocator, &layout, input.air, input.catalog);
    defer composition_plan.deinit();
    var commit_plans: [4]cuda.resident_commit.Plan = undefined;
    var commit_count: usize = 0;
    defer for (commit_plans[0..commit_count]) |*plan| plan.deinit();
    for (geometry.trees, &commit_plans) |tree, *plan| {
        plan.* = try cuda.resident_commit.Plan.init(allocator, tree, blowup);
        commit_count += 1;
    }
    var oods_plan = try cuda.resident_oods.Plan.init(allocator, input.air, &geometry, blowup);
    defer oods_plan.deinit();
    var quotient_topology = try cuda.resident_quotient.derive(allocator, input.air, &geometry, &oods_plan, blowup);
    defer quotient_topology.deinit();
    const twiddle_words = @as(usize, 1) << @intCast(geometry.fri_input_log - 1);
    var fri_plan = try cuda.resident_fri.Plan.init(allocator, &geometry, input.config, twiddle_words);
    defer fri_plan.deinit();
    var decommit_plan = try cuda.resident_decommit.Plan.init(allocator, &geometry, input.config);
    defer decommit_plan.deinit();
    const terminal_layout = try cuda.resident_terminal_bundle.Layout.init(&geometry, &oods_plan, input.config);
    var terminal_bundle = try cuda.resident_terminal_bundle.Bundle.init(allocator, terminal_layout, .{ .capacity_words = decommit_plan.topology.assembly_capacity_words });
    defer terminal_bundle.deinit(allocator);
    var memory_plan = try cuda.resident_memory_plan.Plan.init(allocator, .{
        .value_count = input.values.len,
        .twiddle_words = twiddle_words,
        .retain_static = false,
        .commitments = &commit_plans,
        .interaction = &interaction_plan,
        .composition = &composition_plan,
        .oods = &oods_plan,
        .quotient = &quotient_topology,
        .fri = &fri_plan,
        .decommit = &decommit_plan,
        .terminal = &terminal_bundle,
    });
    defer memory_plan.deinit();
    return memory_plan.bytes();
}

/// Shared GPU state: the AIR template (bound per circuit) and the AOT catalog.
const Gpu = struct {
    template: cpu.air.Bundle,
    catalog: cuda.air_aot.Catalog,
    tables: *leaf.Tables,
    plan_only: bool,

    fn init(gpa: std.mem.Allocator, plan_only: bool) !Gpu {
        var template = try cpu.air.parse(gpa, leaf.bundle_bytes);
        errdefer template.deinit();
        var catalog = try cuda.air_aot.build(gpa, leaf.bundle_bytes);
        errdefer catalog.deinit();
        return .{ .template = template, .catalog = catalog, .tables = try leaf.Tables.init(gpa), .plan_only = plan_only };
    }

    fn deinit(self: *Gpu, gpa: std.mem.Allocator) void {
        self.tables.deinit(gpa);
        self.catalog.deinit();
        self.template.deinit();
    }
};

/// The FRI configuration: fixed (a shape's), or a fold step with the last layer chosen from the trace
/// log (0 at fold 1; `trace log mod fold` otherwise, so every CUDA fold is a full one).
const FriChoice = union(enum) {
    fixed: FriConfigV2,
    fold: u32,

    fn resolve(self: FriChoice, trace_log: u32) !FriConfigV2 {
        return switch (self) {
            .fixed => |f| f,
            .fold => |fold| try FriConfigV2.init(26, if (fold == 1) 0 else trace_log % fold, 1, 70, fold),
        };
    }
};

/// What one GPU proof took.
const Stats = struct {
    trace_log: u32 = 0,
    planned: usize = 0,
    preprocess_s: f64 = 0,
    prove_s: f64 = 0,
    gpu_verify_s: f64 = 0,
    convert_s: f64 = 0,
    native_verify_s: f64 = 0,
    peak_device: usize = 0,
    bytes: usize = 0,
};

fn printStages(result: *const cuda.resident_prover.Result) void {
    for (cuda_backend.runtime.telemetry.all_stages) |stage| {
        const c = result.verdict.counters.stages[stage.index()];
        if (c.kernel_launches == 0 and c.h2d_bytes == 0) continue;
        std.debug.print("    stage {s}: {d:.3}s device, {d} launches, h2d {d} MiB\n", .{ @tagName(stage), secs(c.device_elapsed_ns), c.kernel_launches, c.h2d_bytes >> 20 });
    }
}

/// Pads `ctx` to `target` (when given), proves it on the GPU, verifies the device proof natively,
/// converts it to the verifier proof a node verifies in-circuit (`leaf.CircuitProof`, as
/// `leaf.proveCircuit` returns it from the CPU prover; `circuit_cuda.recursion_source` does the same
/// conversion), and verifies that with stwo-zig's circuit verifier. Null under `--plan-only`.
/// The result's bytes and request live in `a`.
fn gpuProve(gpa: std.mem.Allocator, a: std.mem.Allocator, g: *Gpu, label: []const u8, ctx: *Context(QM31), target: ?ComponentSizes, fri_choice: FriChoice, stats: *Stats) !?leaf.CircuitProof {
    var timer = try std.time.Timer.start();
    if (target) |t| try finalize.padToTargets(QM31, ctx, t);
    if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
    var pp = try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, ctx);
    defer pp.deinit(gpa);
    const layout = pp.layout();
    const log_sizes = try component_list.circuitComponentLogSizes(&layout);
    var air = try cpu.air.bind(gpa, &g.template, log_sizes, &layout);
    defer air.deinit();
    stats.trace_log = pp.traceLogSize();
    const fri = try fri_choice.resolve(stats.trace_log);
    const config = PcsConfigV2.fromFriAndTraceSize(fri, stats.trace_log);
    const input = cuda.resident_prover.Input{ .values = ctx.values(), .preprocessed = &pp, .air = &air, .catalog = &g.catalog, .config = config, .profile = .internal };
    stats.planned = try plannedArena(gpa, input);
    stats.preprocess_s = secs(timer.lap());
    const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
    std.debug.print("{s}: {d} vars, trace log {d} (eq {d} qm31_ops {d} m31_to_u32 {d} triple_xor {d} blake_g {d}), fri fold {d} last layer {d}, planned arena {d:.2} GiB, pad+check+preprocess {d:.1}s, host peak RSS {d:.1} GiB\n", .{
        label,                    ctx.circuit.n_vars, stats.trace_log, log2(sz.eq), log2(sz.qm31_ops), log2(sz.m31_to_u32), log2(sz.triple_xor), log2(sz.blake_g_gate),
        fri.fold_step,            fri.log_last_layer_degree_bound,
        gib(stats.planned),       stats.preprocess_s, rssGib(),
    });
    if (g.plan_only) return null;

    _ = timer.lap();
    var result = try cuda.resident_prover.prove(gpa, input);
    defer result.deinit();
    stats.prove_s = secs(timer.lap());
    stats.peak_device = result.verdict.counters.peak_live_bytes;
    if (!result.verdict.isResident() or result.verdict.counters.cpu_fallback_attempts != 0) return error.NonresidentCircuitProof;
    var verified = cuda.resident_verifier.verify(gpa, input, &result) catch |err| {
        std.debug.print("{s}: GPU proof REJECTED by the native verifier: {s}\n", .{ label, @errorName(err) });
        return err;
    };
    defer verified.deinit();
    stats.gpu_verify_s = secs(timer.lap());

    const dec = result.terminal_proof.decoded;
    const claim_words = dec.words[dec.layout.interaction_claim.start..dec.layout.interaction_claim.end];
    if (claim_words.len != component_list.N_COMPONENTS * 4) return error.InvalidCircuitResidentClaim;
    var claims: [component_list.N_COMPONENTS]QM31 = undefined;
    for (&claims, 0..) |*out, i| {
        const w = claim_words[i * 4 ..][0..4];
        out.* = QM31.fromU32Unchecked(w[0], w[1], w[2], w[3]);
    }
    var prepared = try cpu.verifier_proof.fromVerifiedCapture(gpa, &result.stark, &verified.capture, try cpu.verifier_proof.proofConfig(pp.columns.len, config), &claims, dec.interactionNonce(), 0);
    errdefer prepared.deinit();
    const pp_root = result.stark.commitment_scheme_proof.commitments.items[0];
    const circuit_hash = try circuit.common.circuit_hash.hostCircuitHash(log_sizes, fri.log_blowup_factor, pp_root);
    // The outputs follow the `u` wire; the last 8 are the digest (`leaf.finish`).
    const output_start = circuit.witness.trace.U_VAR_IDX + 1;
    if (pp.n_outputs != 8 or output_start + 8 > ctx.values().len) return error.InvalidCircuitResidentOutput;
    var digest: [8]u32 = undefined;
    for (&digest, ctx.values()[output_start..][0..8]) |*w, value| {
        const limbs = circuit.builder.ivalue.limbs(value);
        if (limbs[2] != 0 or limbs[3] != 0 or limbs[0] > 0xffff or limbs[1] > 0xffff) return error.InvalidCircuitResidentOutput;
        w.* = limbs[0] | (limbs[1] << 16);
    }
    const cp: leaf.CircuitProof = .{
        .bytes = try prepared.serialize(a),
        .prepared = prepared,
        .circuit_hash = core.vcs.blake2_hash.digestToU32s(circuit_hash),
        .request = .{
            .pcs_config = config,
            .preprocessed_column_log_sizes = try leaf.requestColumns(a, &pp),
            .preprocessed_root = core.vcs.blake2_hash.digestToU32s(pp_root),
            .output_digest = digest,
        },
    };
    stats.convert_s = secs(timer.lap());
    try circuitVerify(gpa, g, label, &cp);
    stats.native_verify_s = secs(timer.lap());
    stats.bytes = cp.bytes.len;
    const hex = sha(cp.bytes);
    std.debug.print("{s}: GPU proved in {d:.2}s, device proof verified {d:.2}s, converted {d:.2}s, circuit verifier {d:.2}s; proof {d} bytes sha256 {s}; peak device {d:.2} GiB; host peak RSS {d:.1} GiB\n", .{
        label, stats.prove_s, stats.gpu_verify_s, stats.convert_s, stats.native_verify_s, cp.bytes.len, hex[0..16], gib(stats.peak_device), rssGib(),
    });
    printStages(&result);
    return cp;
}

/// stwo-zig's circuit verifier on a circuit proof. It replays the in-circuit verifier, which needs the
/// last FRI layer to be 0 (`stark_verifier/fri.zig`): with another last layer it is skipped (such a
/// proof is for timing only; it cannot be a child).
fn circuitVerify(gpa: std.mem.Allocator, g: *Gpu, label: []const u8, cp: *const leaf.CircuitProof) !void {
    if (cp.request.pcs_config.fri_config.log_last_layer_degree_bound != 0) {
        std.debug.print("{s}: circuit verifier skipped (last layer {d}; it needs 0)\n", .{ label, cp.request.pcs_config.fri_config.log_last_layer_degree_bound });
        return;
    }
    _ = try leaf.verifyCircuit(gpa, g.tables, cp);
}

/// Proves the (already padded and preprocessed) `ctx` with the CPU circuit prover and requires the GPU
/// proof `gp` to be the same, byte for byte, with the same circuit hash and preprocessed root.
fn cpuCompare(gpa: std.mem.Allocator, a: std.mem.Allocator, label: []const u8, ctx: *Context(QM31), fri: FriConfigV2, gp: *const leaf.CircuitProof) !void {
    var timer = try std.time.Timer.start();
    var cp = try leaf.proveCircuit(gpa, a, ctx, null, fri);
    defer cp.deinit();
    const same = std.mem.eql(u8, cp.bytes, gp.bytes) and
        std.mem.eql(u32, &cp.circuit_hash, &gp.circuit_hash) and
        std.mem.eql(u32, &cp.request.preprocessed_root, &gp.request.preprocessed_root) and
        std.mem.eql(u32, &cp.request.output_digest, &gp.request.output_digest);
    const hex = sha(cp.bytes);
    std.debug.print("{s}: CPU proved in {d:.2}s, {d} bytes sha256 {s}: {s}; host peak RSS {d:.1} GiB\n", .{ label, secs(timer.lap()), cp.bytes.len, hex[0..16], if (same) "BYTE-IDENTICAL" else "MISMATCH", rssGib() });
    if (!same) return error.GpuCpuMismatch;
}

fn loadFiles(a: std.mem.Allocator, dir: []const u8, from: u32, n: usize) ![]PF.File {
    const files = try a.alloc(PF.File, n);
    for (files, 0..) |*f, i| {
        const path = try std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ dir, from + @as(u32, @intCast(i)) });
        f.* = try PF.decode(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
    }
    return files;
}

const Opts = struct { plan_only: bool = false, cpu: bool = false, cpu_node: bool = false, cpu_only: bool = false, fold: u32 = 1 };

/// Experiment A: a leaf (k = 1) or packed circuit (k > 1) at its natural size.
fn experimentA(gpa: std.mem.Allocator, dir: []const u8, from: u32, ks: []const usize, opts: Opts) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    var max_k: usize = 1;
    for (ks) |k| max_k = @max(max_k, k);
    const files = try loadFiles(a, dir, from, max_k);
    var g = try Gpu.init(gpa, opts.plan_only);
    defer g.deinit(gpa);
    for (ks) |k| {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        var timer = try std.time.Timer.start();
        var ctx = if (k == 1)
            try br.leafCircuitOf(gpa, scratch.allocator(), &airs, &files[0], PF.productionFri())
        else
            try sb.recursion.block_pack.buildPacked(gpa, scratch.allocator(), &airs, files[0..k], PF.productionFri());
        defer ctx.deinit();
        const label = try std.fmt.allocPrint(scratch.allocator(), "A k={d} (blocks {d}..{d}) fold {d}", .{ k, from, from + k - 1, opts.fold });
        std.debug.print("{s}: block proofs verified natively and circuit built in {d:.1}s\n", .{ label, secs(timer.lap()) });
        var stats: Stats = .{};
        const maybe = try gpuProve(gpa, scratch.allocator(), &g, label, &ctx, null, .{ .fold = opts.fold }, &stats);
        if (opts.cpu_only) {
            // The CPU leg alone (any host): the CPU circuit prover at this FRI configuration, and the
            // circuit verifier on its proof.
            _ = timer.lap();
            var cp = try leaf.proveCircuit(gpa, scratch.allocator(), &ctx, null, try (FriChoice{ .fold = opts.fold }).resolve(stats.trace_log));
            defer cp.deinit();
            const prove_s = secs(timer.lap());
            try circuitVerify(gpa, &g, label, &cp);
            const hex = sha(cp.bytes);
            std.debug.print("{s}: CPU proved in {d:.2}s, circuit verifier {d:.2}s, {d} bytes sha256 {s}; host peak RSS {d:.1} GiB\n", .{ label, prove_s, secs(timer.lap()), cp.bytes.len, hex[0..16], rssGib() });
            continue;
        }
        var gp = maybe orelse continue;
        defer gp.deinit();
        if (k == 1) {
            const want = leaf.pubsDigest(leaf.zero_key, &br.leafSummary(&files[0].pubs));
            if (!std.mem.eql(u32, &want, &gp.request.output_digest)) return error.LeafDigestMismatch;
            std.debug.print("{s}: output digest = the leaf summary's digest\n", .{label});
        }
        if (opts.cpu) try cpuCompare(gpa, scratch.allocator(), label, &ctx, try (FriChoice{ .fold = opts.fold }).resolve(stats.trace_log), &gp);
    }
}

/// The 8-child shared shape at fold 4 with a trace log that is a multiple of 4 (`block_pack.shapes`).
fn shapeB(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, start: ComponentSizes) !br.Shape {
    const fold: u32 = 4;
    const fri = try FriConfigV2.init(26, 0, 1, 70, fold);
    var target = start;
    while (true) {
        target.blake_g_gate = @max(target.blake_g_gate, @as(usize, 1) << @intCast((try traceLogOf(target) + fold - 1) / fold * fold));
        var shp = try wk.shape(gpa, table, 3, target, fri);
        const tl = try traceLogOf(shp.target);
        if (tl % fold == 0) return shp;
        target = shp.target;
        shp.deinit(gpa);
    }
}

/// Experiment B: 8 block leaves at the shared 2^24 shape and the wide node over them, all on the GPU.
fn experimentB(gpa: std.mem.Allocator, dir: []const u8, from: u32, opts: Opts) !void {
    const n = 8;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const files = try loadFiles(a, dir, from, n);
    var g = try Gpu.init(gpa, opts.plan_only);
    defer g.deinit(gpa);
    var total = try std.time.Timer.start();
    var timer = try std.time.Timer.start();

    // The leaf circuits (block proofs verified natively), their padded sizes, the shared shape.
    var ctxs: [n]?Context(QM31) = @splat(null);
    defer for (&ctxs) |*c| if (c.*) |*x| x.deinit();
    var start: ComponentSizes = undefined;
    for (files, &ctxs, 0..) |*f, *c, i| {
        c.* = try br.leafCircuitOf(gpa, a, &airs, f, PF.productionFri());
        const sz = finalize.computePaddedSizes(.fromBuilder(&c.*.?.circuit));
        start = if (i == 0) sz else start.elementwiseMax(sz);
        std.debug.print("block {d}: L {d} {s}, leaf {d} vars, natural trace log {d}\n", .{ from + i, f.log_size, @tagName(f.profile), c.*.?.circuit.n_vars, try traceLogOf(sz) });
    }
    const build_s = secs(timer.lap());
    var shp = try shapeB(gpa, &g.tables.table, start);
    defer shp.deinit(gpa);
    const tl = try traceLogOf(shp.target);
    std.debug.print("B: 8 block proofs verified natively and leaf circuits built in {d:.1}s; shared shape (8 children, fold 4, last layer 0): trace log {d}, found in {d:.1}s\n", .{ build_s, tl, secs(timer.lap()) });
    if (tl % 4 != 0 or shp.fri.log_last_layer_degree_bound != 0 or shp.fri.fold_step != 4) return error.ShapeNotAligned;

    // The leaves on the GPU, at the shape.
    var leaves: [n]br.Proved = undefined;
    var n_leaves: usize = 0;
    defer for (leaves[0..n_leaves]) |*l| l.proof.deinit();
    var leaf_prove_s: f64 = 0;
    var leaf_peak: usize = 0;
    for (files, &ctxs, 0..) |*f, *c, i| {
        const label = try std.fmt.allocPrint(a, "B leaf {d} (block {d})", .{ i, from + i });
        var stats: Stats = .{};
        const maybe = try gpuProve(gpa, a, &g, label, &c.*.?, shp.target, .{ .fixed = shp.fri }, &stats);
        if (maybe) |cp| {
            leaves[i] = .{ .proof = cp, .key = leaf.zero_key, .sum = br.leafSummary(&f.pubs) };
            n_leaves += 1;
            if (!std.mem.eql(u32, &leaves[i].digest(), &cp.request.output_digest)) return error.LeafDigestMismatch;
            leaf_prove_s += stats.prove_s;
            leaf_peak = @max(leaf_peak, stats.peak_device);
            if (opts.cpu) try cpuCompare(gpa, a, label, &c.*.?, shp.fri, &leaves[i].proof);
        }
        c.*.?.deinit();
        c.* = null;
    }
    if (!opts.plan_only) std.debug.print("B: 8 leaves GPU-proved in {d:.2}s total ({d:.2}s per leaf), peak device {d:.2} GiB; elapsed {d:.1}s\n", .{ leaf_prove_s, leaf_prove_s / n, gib(leaf_peak), secs(total.read()) });

    if (opts.plan_only) {
        // The node's topology at the shape (no child proofs): the plan needs only the layout and the
        // number of values (an untouched mapping of that length).
        var topo = try wk.topology(gpa, &g.tables.table, 3, &shp.shared);
        defer topo.deinit();
        try finalize.padToTargets(NoValue, &topo, shp.target);
        var pp = try preprocessed.PreprocessedCircuit.preprocessContext(NoValue, gpa, &topo);
        defer pp.deinit(gpa);
        const layout = pp.layout();
        var air = try cpu.air.bind(gpa, &g.template, try component_list.circuitComponentLogSizes(&layout), &layout);
        defer air.deinit();
        const fake = try std.heap.page_allocator.alloc(QM31, topo.circuit.n_vars);
        defer std.heap.page_allocator.free(fake);
        const config = PcsConfigV2.fromFriAndTraceSize(shp.fri, pp.traceLogSize());
        const planned = try plannedArena(gpa, .{ .values = fake, .preprocessed = &pp, .air = &air, .catalog = &g.catalog, .config = config, .profile = .internal });
        std.debug.print("B node (8 children, topology): {d} vars, trace log {d}, planned arena {d:.2} GiB, host peak RSS {d:.1} GiB\n", .{ topo.circuit.n_vars, pp.traceLogSize(), gib(planned), rssGib() });
        return;
    }

    // The node over them, on the GPU.
    var refs: [n]*const br.Proved = undefined;
    for (&refs, &leaves) |*r, *l| r.* = l;
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    _ = timer.lap();
    var node_ctx = try wk.circuitOf(gpa, scratch.allocator(), g.tables, 3, &shp, &refs);
    defer node_ctx.deinit();
    const want = try wk.expected(scratch.allocator(), &refs);
    const want_digest = leaf.pubsDigest(want.key, &want.sum);
    std.debug.print("B node: circuit over the 8 GPU leaf proofs built in {d:.1}s ({d} vars); host peak RSS {d:.1} GiB\n", .{ secs(timer.lap()), node_ctx.circuit.n_vars, rssGib() });
    var stats: Stats = .{};
    var node = (try gpuProve(gpa, scratch.allocator(), &g, "B node", &node_ctx, shp.target, .{ .fixed = shp.fri }, &stats)).?;
    defer node.deinit();
    if (!std.mem.eql(u32, &node.request.output_digest, &want_digest)) return error.NodeDigestMismatch;
    std.debug.print("B node: output digest = block_node_k.expected's (blocks {d}..{d}, key {x:0>8}…)\n", .{ want.sum[0].toU32(), want.sum[0].toU32() + want.sum[1].toU32() - 1, want.key[0] });
    std.debug.print("B: 8 leaves + node GPU-proved in {d:.2}s ({d:.2}s per block); node peak device {d:.2} GiB; end to end {d:.1}s; host peak RSS {d:.1} GiB\n", .{
        leaf_prove_s + stats.prove_s, (leaf_prove_s + stats.prove_s) / n, gib(stats.peak_device), secs(total.read()), rssGib(),
    });
    if (opts.cpu or opts.cpu_node) try cpuCompare(gpa, scratch.allocator(), "B node", &node_ctx, shp.fri, &node);
}

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    const usage = "usage: cuda-widenode A <epoch dir> <from> <k>... [--fold f] [--plan-only] [--cpu] [--cpu-only]\n       cuda-widenode B <epoch dir> <from> [--plan-only] [--cpu] [--cpu-node]\n";
    if (args.len < 4) {
        std.debug.print("{s}", .{usage});
        return error.Usage;
    }
    var opts: Opts = .{};
    var ks: std.ArrayList(usize) = .empty;
    defer ks.deinit(gpa);
    var i: usize = 4;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        if (std.mem.eql(u8, x, "--plan-only")) opts.plan_only = true else if (std.mem.eql(u8, x, "--cpu")) opts.cpu = true else if (std.mem.eql(u8, x, "--cpu-node")) opts.cpu_node = true else if (std.mem.eql(u8, x, "--cpu-only")) {
            opts.cpu_only = true;
            opts.plan_only = true;
        } else if (std.mem.eql(u8, x, "--fold")) {
            i += 1;
            if (i >= args.len) return error.Usage;
            opts.fold = try std.fmt.parseInt(u32, args[i], 10);
        } else try ks.append(gpa, try std.fmt.parseInt(usize, x, 10));
    }
    const dir = args[2];
    const from = try std.fmt.parseInt(u32, args[3], 10);
    if (std.mem.eql(u8, args[1], "A")) {
        if (ks.items.len == 0) try ks.append(gpa, 1);
        return experimentA(gpa, dir, from, ks.items, opts);
    }
    if (std.mem.eql(u8, args[1], "B")) return experimentB(gpa, dir, from, opts);
    std.debug.print("{s}", .{usage});
    return error.Usage;
}
