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
const coin = @import("../block/coin.zig");
const glue = @import("glue.zig");

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
    try leafChecks(&ctx, pub_vars);
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

/// The block leaf's own checks (`Circuit/BlockLeaf.lean`, `checks_pub`): `αₖ = α₁ᵏ` and the BIP30 flag
/// from the height. Hook 0 binds the height, the flag, and the 104 weight limbs.
pub fn leafChecks(ctx: *Context(QM31), pub_vars: []const Var) !void {
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:block_leaf_checks"));
    const ins = try ctx.scratch().alloc(Var, 106);
    ins[0] = pub_vars[2];
    ins[1] = pub_vars[coin.PUB_LOST];
    @memcpy(ins[2..], pub_vars[coin.PUB_ALPHA .. coin.PUB_ALPHA + 104]);
    const Hooks = struct {
        inputs: []const Var,
        pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
            return if (id == 0) self.inputs else error.UnknownHook;
        }
    };
    _ = try glue.run(QM31, ctx, &prog, &.{}, Hooks{ .inputs = ins });
}

/// The block's seed leaf `Blake2s(hash ‖ C_h)` (`Circuit/BlockLeaf.lean`, `seedLeaf_sound`): 16 limbs,
/// from the block hash's public limbs (25–40) and the commitment's (9–24).
pub fn seedLeafVars(ctx: *Context(QM31), pub_vars: []const Var) ![16]Var {
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:seed_leaf"));
    const ins = try ctx.scratch().alloc(Var, 32);
    @memcpy(ins[0..16], pub_vars[bs.PUB_HASH .. bs.PUB_HASH + 16]);
    @memcpy(ins[16..32], pub_vars[9..25]);
    const Hooks = struct {
        inputs: []const Var,
        pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
            return if (id == 0) self.inputs else error.UnknownHook;
        }
    };
    const res = try glue.run(QM31, ctx, &prog, &.{}, Hooks{ .inputs = ins });
    var out: [16]Var = undefined;
    @memcpy(&out, res);
    return out;
}

/// The leaf's height-derived context (`Circuit/BlockCtx.lean`, `ctx_sound`): the BIP34, CSV and segwit
/// flags (inputs 4–6) and the subsidy's limbs (159–160) are the height's. Hook 0 binds them, height first.
pub fn leafCtx(ctx: *Context(QM31), pub_vars: []const Var) !void {
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:block_leaf_ctx"));
    const ins = [6]Var{ pub_vars[2], pub_vars[4], pub_vars[5], pub_vars[6], pub_vars[coin.PUB_SUBL], pub_vars[coin.PUB_SUBH] };
    const Hooks = struct {
        inputs: []const Var,
        pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
            return if (id == 0) self.inputs else error.UnknownHook;
        }
    };
    _ = try glue.run(QM31, ctx, &prog, &.{}, Hooks{ .inputs = &ins });
}

test "block leaf context: the height's flags and subsidy pass, a wrong one fails" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    for ([_]u32{ 0, 170, 227930, 227931, 419328, 481824, 629999, 630000, 840000, 8000000 }) |height| for (0..4) |tamper| {
        var pubs: [bs.N_PUB]M31 = @splat(M31.zero());
        const want = checks.pubs(&.{}, 0, .{ .height = height, .prev_mtp = 0 });
        @memcpy(pubs[0..8], &want);
        const sub = coin.subsidy(height);
        pubs[coin.PUB_SUBL] = M31.fromCanonical(@intCast(sub & 0xffffff));
        pubs[coin.PUB_SUBH] = M31.fromCanonical(@intCast(sub >> 24));
        if (tamper == 1) pubs[4] = M31.one().sub(pubs[4]);
        if (tamper == 2) pubs[6] = M31.one().sub(pubs[6]);
        if (tamper == 3) pubs[coin.PUB_SUBL] = pubs[coin.PUB_SUBL].add(M31.one());
        var ctx = try Context(QM31).init(a, 0);
        defer ctx.deinit();
        const vars = try a.alloc(Var, bs.N_PUB);
        for (vars, pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
        try leafCtx(&ctx, vars);
        try std.testing.expectEqual(tamper == 0, try ctx.isCircuitValid());
    };
}

test "block seed leaf: the circuit's limbs are the native epoch.seedLeaf's" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const epoch = @import("../block/epoch.zig");
    const HT = @import("../btc/header_tree.zig");
    var prng = std.Random.DefaultPrng.init(31);
    const r = prng.random();
    for (0..4) |_| {
        var hash: [32]u8 = undefined;
        var c: [32]u8 = undefined;
        r.bytes(&hash);
        r.bytes(&c);
        var pubs: [bs.N_PUB]M31 = @splat(M31.zero());
        @memcpy(pubs[bs.PUB_HASH..][0..16], &bs.hashLimbsOf(hash));
        for (0..8) |w| {
            const word = std.mem.readInt(u32, c[4 * w ..][0..4], .little);
            pubs[9 + 2 * w] = M31.fromCanonical(word & 0xffff);
            pubs[10 + 2 * w] = M31.fromCanonical(word >> 16);
        }
        var ctx = try Context(QM31).init(a, 0);
        defer ctx.deinit();
        const vars = try a.alloc(Var, bs.N_PUB);
        for (vars, pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
        const out = try seedLeafVars(&ctx, vars);
        const want = HT.limbs(epoch.seedLeaf(hash, c));
        for (out, want) |v, w| try std.testing.expect(ctx.get(v).eql(QM31.fromBase(w)));
        try std.testing.expect(try ctx.isCircuitValid());
    }
}

test "block leaf checks: honest public inputs pass, a wrong BIP30 flag or weight fails" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const ch = @import("../block/epoch.zig").challenge(@splat(7));
    for ([_]u32{ 170, 91722 }) |height| for (0..3) |tamper| {
        var pubs: [bs.N_PUB]M31 = @splat(M31.zero());
        pubs[2] = M31.fromCanonical(height);
        const want = coin.pubs(ch, QM31.zero(), 0, bs.lostHeight(height), height);
        @memcpy(pubs[41..], &want);
        if (tamper == 1) pubs[coin.PUB_LOST] = M31.one().sub(pubs[coin.PUB_LOST]);
        if (tamper == 2) pubs[coin.PUB_ALPHA + 4 * 7] = pubs[coin.PUB_ALPHA + 4 * 7].add(M31.one());
        var ctx = try Context(QM31).init(a, 0);
        defer ctx.deinit();
        const vars = try a.alloc(Var, bs.N_PUB);
        for (vars, pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
        try leafChecks(&ctx, vars);
        try std.testing.expectEqual(tamper == 0, try ctx.isCircuitValid());
    };
}

fn zeroKey(ctx: *Context(QM31)) ![8]builder.wrappers.U32Wrapper(Var) {
    var key: [8]builder.wrappers.U32Wrapper(Var) = undefined;
    for (&key) |*k| k.* = try builder.wrappers.constU32(QM31, ctx, 0);
    return key;
}
