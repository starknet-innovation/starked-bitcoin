//! BLOCK-REC, first step: a block proof (the 15-component block system) verified by the plain
//! in-circuit verifier, as a block leaf would. `measure` builds that circuit for a sample block and
//! reports its size and validity, and optionally proves it (stwo-zig's circuit prover) to measure
//! time and memory. The leaf's public-input handling (binding, digest) is not decided yet
//! (docs/design/block-rec.md); here the circuit outputs the digest of the block's public inputs.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const pv = @import("plain_verifier.zig");
const leaf = @import("leaf.zig");
const ir = @import("../air/ir.zig");
const component = @import("../air/component.zig");
const system = @import("../air/system.zig");
const rec = @import("../air/prove_rec.zig");
const bs = @import("../block/system.zig");
const PF = @import("../block/proof_file.zig");
const checks = @import("../block/checks.zig");

const builder = circuit.builder;
const Context = builder.Context;
const Var = builder.Var;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;

/// The plain-verifier configuration of a block proof at `log_size`.
pub fn config(a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, log_size: u32, fri: FriConfigV2) !pv.PlainConfig {
    const parts = try a.alloc(pv.PartConfig, bs.N_COMP);
    for (parts, airs) |*p, *air| p.* = .{
        .n_preprocessed = air.n_preprocessed,
        .main_offsets = try pv.mainOffsets(a, air.*),
        .n_inter = 4 * component.nBatches(air.*),
    };
    return .{ .log_trace_size = log_size, .fri = rec.Config.fromFriAndTraceSize(fri, log_size).fri_config, .system = true, .parts = parts };
}

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

/// Builds (and with `prove`, proves) the plain verifier of a block-170 proof.
pub fn measure(gpa: std.mem.Allocator, weak: bool, prove: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const fri = if (weak) PF.testFri() else PF.productionFri();
    const airs = try bs.parseAirs(a);
    const s = checks.samples_small[1];
    var timer = try std.time.Timer.start();
    const b = try bs.buildU(a, s.raw, s.undo, s.ctx);
    var proof = try PF.prove(a, &airs, &b, fri);
    std.debug.print("block {d}: trace 2^{d}, proved natively in {d:.1}s ({s})\n", .{ s.ctx.height, b.log_size, secs(timer.lap()), if (weak) "test strength" else "70 queries, 26 PoW bits" });
    const parts = bs.parts(&airs, &b);
    const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
    var capture: core.verifier.ProofCapture(rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &parts, &.{}, &proof, &capture);
    const pc = try config(a, &airs, b.log_size, fri);
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    const values = try pv.fromCapture(a, rec.Hasher, &proof.stark, &capture, pc, proof.claimed_sums);

    var ctx = try Context(QM31).init(gpa, circuit.common.component_list.N_RESERVED);
    defer ctx.deinit();
    const g = try pv.guess(QM31, &ctx, &values);
    const pub_vars = try a.alloc(Var, bs.N_PUB);
    for (pub_vars, b.pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
    const st_parts = try a.alloc(pv.PartStatement, bs.N_COMP);
    for (st_parts, &airs, 0..) |*p, *air, i| p.* = .{ .air = air, .digest = try air.digest(a), .pubs = pub_vars[0..bs.n_pubs[i]] };
    const st = pv.PlainStatement{ .parts = st_parts, .preprocessed_root = pre_root };
    try pv.verifyPlain(QM31, &ctx, &g, pc, &st);
    try leaf.finish(QM31, &ctx, try leaf.pubsDigestVars(QM31, &ctx, try zeroKey(&ctx), pub_vars));
    const valid = try ctx.isCircuitValid();
    const st_ = ctx.stats;
    std.debug.print("circuit built in {d:.1}s: {d} vars; add {d}, sub {d}, mul {d}, pointwise_mul {d}, eq {d}, blake updates {d}, m31_to_u32 {d}; valid {}\n", .{
        secs(timer.lap()), ctx.circuit.n_vars, st_.add, st_.sub, st_.mul, st_.pointwise_mul, st_.equals, st_.blake_updates, st_.m31_to_u32, valid,
    });
    if (!valid) return error.CircuitUnsatisfied;
    if (!prove) return;
    const cp = try leaf.proveCircuit(gpa, a, &ctx, null, try FriConfigV2.init(26, 0, 1, 70, 1));
    std.debug.print("circuit proved in {d:.1}s: proof {d} bytes\n", .{ secs(timer.lap()), cp.bytes.len });
}

fn zeroKey(ctx: *Context(QM31)) ![8]builder.wrappers.U32Wrapper(Var) {
    var key: [8]builder.wrappers.U32Wrapper(Var) = undefined;
    for (&key) |*k| k.* = try builder.wrappers.constU32(QM31, ctx, 0);
    return key;
}
