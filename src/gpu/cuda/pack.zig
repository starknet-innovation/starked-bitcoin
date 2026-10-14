//! `cuda-pack <epoch dir> <from> <k>... [--plan-only] [--cpu]`: the leaf-packing spike on CUDA
//! (`recursion/block_pack.zig`). For each k, the k block proofs `<dir>/proofs/<from..>.sbblock` are
//! verified in one circuit, which is proved with stwo-zig's resident CUDA circuit prover
//! (`circuit_cuda.resident_prover`, fold step 4, 70 queries, 26 PoW bits, last layer below) and verified natively.
//!
//! `--plan-only` stops after the host planning and prints the planned device arena (no GPU needed:
//! links against the stubs). `--cpu` also proves the circuit with the CPU circuit prover and checks
//! that the two serialized proofs are byte-identical.
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
const PF = sb.block.proof_file;
const bs = sb.block.system;
const leaf = sb.recursion.leaf;

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

fn log2(n: usize) u32 {
    return if (n <= 1) 0 else std.math.log2_int_ceil(usize, n);
}

/// The device arena `resident_prover.prove` would plan for `input` (its own planning steps).
fn plannedArena(allocator: std.mem.Allocator, input: cuda.resident_prover.Input) !usize {
    const layout = input.preprocessed.layout();
    var geometry = try cuda.geometry.Geometry.init(allocator, &layout, input.air, input.catalog, input.config);
    defer geometry.deinit();
    const blowup = input.config.fri_config.log_blowup_factor;
    const witness_plan = try cuda.resident_witness.Plan.init(&layout, input.preprocessed.first_permutation_row);
    _ = witness_plan;
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

fn sha(bytes: []const u8) [64]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return std.fmt.bytesToHex(d, .lower);
}

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len < 4) return error.Usage;
    var ks: std.ArrayList(usize) = .empty;
    defer ks.deinit(gpa);
    var plan_only = false;
    var with_cpu = false;
    for (args[3..]) |x| {
        if (std.mem.eql(u8, x, "--plan-only")) plan_only = true else if (std.mem.eql(u8, x, "--cpu")) with_cpu = true else try ks.append(gpa, try std.fmt.parseInt(usize, x, 10));
    }
    const dir = args[1];
    const from = try std.fmt.parseInt(u32, args[2], 10);

    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const fri = PF.productionFri();
    var max_k: usize = 0;
    for (ks.items) |k| max_k = @max(max_k, k);
    const files = try a.alloc(PF.File, max_k);
    for (files, 0..) |*f, i| {
        const path = try std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ dir, from + @as(u32, @intCast(i)) });
        f.* = try PF.decode(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
    }
    var template = try cpu.air.parse(gpa, leaf.bundle_bytes);
    defer template.deinit();
    var catalog = try cuda.air_aot.build(gpa, leaf.bundle_bytes);
    defer catalog.deinit();

    for (ks.items) |k| {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        var timer = try std.time.Timer.start();
        var ctx = try sb.recursion.block_pack.buildPacked(gpa, scratch.allocator(), &airs, files[0..k], fri);
        defer ctx.deinit();
        if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
        var pp = try circuit.common.preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, &ctx);
        defer pp.deinit(gpa);
        const layout = pp.layout();
        var air = try cpu.air.bind(gpa, &template, try circuit.common.component_list.circuitComponentLogSizes(&layout), &layout);
        defer air.deinit();
        // The FRI folds (trace log + blowup) - (last layer + blowup) rows by 4 per layer, the last layer
        // taking the remainder. Only fold step 4 is qualified on CUDA (a remainder of 1 fails to
        // verify), so the last-layer degree bound is the smallest that makes every fold a 4.
        const last_layer: u32 = if (std.posix.getenv("PACK_LAST_LAYER")) |v| try std.fmt.parseInt(u32, v, 10) else pp.traceLogSize() % 4;
        const config = PcsConfigV2.fromFriAndTraceSize(try FriConfigV2.init(26, last_layer, 1, 70, 4), pp.traceLogSize());
        const input = cuda.resident_prover.Input{ .values = ctx.values(), .preprocessed = &pp, .air = &air, .catalog = &catalog, .config = config, .profile = .internal };
        const build_s = secs(timer.lap());
        const planned = try plannedArena(gpa, input);
        const sz = circuit.common.finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        std.debug.print("k={d} blocks {d}..{d}: {d} vars, trace log {d} (eq {d} qm31_ops {d} m31_to_u32 {d} triple_xor {d} blake_g {d}), last layer {d}, built {d:.1}s, planned arena {d:.2} GiB\n", .{
            k, from, from + k - 1, ctx.circuit.n_vars, pp.traceLogSize(),
            log2(sz.eq), log2(sz.qm31_ops), log2(sz.m31_to_u32), log2(sz.triple_xor), log2(sz.blake_g_gate),
            last_layer, build_s, @as(f64, @floatFromInt(planned)) / (1 << 30),
        });
        if (plan_only) continue;
        _ = timer.lap();
        var result = try cuda.resident_prover.prove(gpa, input);
        defer result.deinit();
        const prove_s = secs(timer.lap());
        var verified = try cuda.resident_verifier.verify(gpa, input, &result);
        defer verified.deinit();
        const verify_s = secs(timer.lap());
        const dec = result.terminal_proof.decoded;
        const claim_words = dec.words[dec.layout.interaction_claim.start..dec.layout.interaction_claim.end];
        var claims: [circuit.common.component_list.N_COMPONENTS]QM31 = undefined;
        for (&claims, 0..) |*out, i| {
            const w = claim_words[i * 4 ..][0..4];
            out.* = QM31.fromU32Unchecked(w[0], w[1], w[2], w[3]);
        }
        var recursive = try cpu.verifier_proof.fromVerifiedCapture(gpa, &result.stark, &verified.capture, try cpu.verifier_proof.proofConfig(pp.columns.len, config), &claims, dec.interactionNonce(), 0);
        defer recursive.deinit();
        const wire = try recursive.serialize(gpa);
        defer gpa.free(wire);
        const hex = sha(wire);
        std.debug.print("k={d}: GPU proved in {d:.2}s ({d:.3}s per block), verified {d:.2}s, proof {d} bytes sha256 {s}, peak device {d:.2} GiB, resident {}\n", .{
            k, prove_s, prove_s / @as(f64, @floatFromInt(k)), verify_s, wire.len, hex[0..16],
            @as(f64, @floatFromInt(result.verdict.counters.peak_live_bytes)) / (1 << 30), result.verdict.isResident(),
        });
        for (cuda_backend.runtime.telemetry.all_stages) |stage| {
            const c = result.verdict.counters.stages[stage.index()];
            if (c.kernel_launches == 0 and c.h2d_bytes == 0) continue;
            std.debug.print("  stage {s}: {d:.3}s device, {d} launches, h2d {d} MiB\n", .{ @tagName(stage), secs(c.device_elapsed_ns), c.kernel_launches, c.h2d_bytes >> 20 });
        }
        if (!with_cpu) continue;
        _ = timer.lap();
        var bundle = try cpu.air.parse(gpa, leaf.bundle_bytes);
        defer bundle.deinit();
        var proof = try cpu.Internal.prove(gpa, ctx.values(), &pp, &bundle, config, .{}, {});
        defer proof.deinit();
        var prepared = try cpu.verifier_proof.prepare(gpa, &proof);
        defer prepared.deinit();
        const cpu_wire = try prepared.serialize(gpa);
        defer gpa.free(cpu_wire);
        const cpu_hex = sha(cpu_wire);
        std.debug.print("k={d}: CPU proved in {d:.2}s, sha256 {s}: {s}\n", .{ k, secs(timer.lap()), cpu_hex[0..16], if (std.mem.eql(u8, wire, cpu_wire)) "BYTE-IDENTICAL" else "MISMATCH" });
        if (!std.mem.eql(u8, wire, cpu_wire)) return error.GpuCpuMismatch;
    }
}
