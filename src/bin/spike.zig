//! Spike CLI: prove an AIR on CPU or Metal and verify on CPU.
//!   spike <log_size> <cpu|metal> [lean]   add32-chain (Zig-built or Lean-exported)
//!   spike sha <log_size> <cpu|metal>      SHA-256 compressions (Lean-exported)

const std = @import("std");
const sb = @import("starked_bitcoin");
const pcs_core = @import("stwo_core").pcs;
const FriConfig = @import("stwo_core").fri.FriConfig;
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const metal = @import("stwo_metal_backend");
const proof_wire = @import("stwo_proof_wire");

pub fn main() !void {
    var gpa: std.heap.DebugAllocator(.{}) = .init;
    defer _ = gpa.deinit();
    var arena = std.heap.ArenaAllocator.init(gpa.allocator());
    defer arena.deinit();
    const a = arena.allocator();

    const args = try std.process.argsAlloc(a);
    if (args.len == 4 and std.mem.eql(u8, args[1], "sha")) return sha(a, try std.fmt.parseInt(u32, args[2], 10), std.mem.eql(u8, args[3], "metal"));
    if (args.len == 4 and std.mem.eql(u8, args[1], "headers")) return headers(a, try std.fmt.parseInt(u32, args[2], 10), std.mem.eql(u8, args[3], "metal"));
    if (args.len != 3 and args.len != 4) return error.Usage;
    const log_size = try std.fmt.parseInt(u32, args[1], 10);
    const use_metal = std.mem.eql(u8, args[2], "metal");
    // `lean` as 3rd arg: use the AIR exported from the Lean definition.
    const from_lean = args.len == 4 and std.mem.eql(u8, args[3], "lean");

    const n = @as(usize, 1) << @intCast(log_size);
    const air = if (from_lean)
        (try sb.air.ir.Air.parseJson(a, sb.air.add32_chain.lean_json)).value
    else
        try sb.air.add32_chain.build(a, true);
    var prng = std.Random.DefaultPrng.init(42);
    const ys = try a.alloc(u32, n);
    for (ys) |*y| y.* = prng.random().int(u32);
    const w = try sb.air.add32_chain.witness(a, log_size, 0, ys);
    const statement = sb.air.prove.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };
    // 96 queries at log blowup 1 with 26 PoW bits (~122 bits by the usual heuristic), as stwo-zig's "secure" profile uses 70 queries + 26 bits.
    const config = pcs_core.PcsConfig{ .pow_bits = 26, .fri_config = try FriConfig.init(0, 1, 70) };

    if (use_metal) try metal.MetalProverEngine.initializeRuntime(a, .source_jit);
    var timer = try std.time.Timer.start();
    const prepared = try sb.air.prove.prepare(a, statement, @ptrCast(w.main));
    const proof = if (use_metal)
        try sb.air.prove.prove(metal.MetalProverEngine, a, config, prepared)
    else
        try sb.air.prove.prove(sb.air.prove.Engine(CpuBackend), a, config, prepared);
    const prove_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const bytes = try proof_wire.encodeProofBytes(a, proof);
    try sb.air.prove.verify(a, config, air, log_size, &.{}, proof);
    const verify_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const digest = try air.digest(a);
    var proof_hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &proof_hash, .{});
    std.debug.print(
        "source={s} air={s} digest={x}... rows=2^{d} cols={d} constraints={d} backend={s} prove={d:.3}s verify={d:.3}s proof={d}B proof_sha256={x}...\n",
        .{ if (from_lean) "lean" else "zig", air.name, digest[0..8], log_size, air.n_main + air.n_preprocessed, air.constraints.len, args[2], prove_s, verify_s, bytes.len, proof_hash[0..8] },
    );
}

fn sha(a: std.mem.Allocator, log_size: u32, use_metal: bool) !void {
    const W = sb.sha256_witness;
    const air = (try sb.air.ir.Air.parseJson(a, W.lean_json)).value;
    const count = W.capacity(log_size);
    var prng = std.Random.DefaultPrng.init(7);
    const cs = try a.alloc(W.Compression, count);
    for (cs) |*c| {
        for (&c.input) |*x| x.* = prng.random().int(u32);
        for (&c.block) |*x| x.* = prng.random().int(u32);
    }
    const config = pcs_core.PcsConfig{ .pow_bits = 26, .fri_config = try FriConfig.init(0, 1, 70) };
    if (use_metal) try metal.MetalProverEngine.initializeRuntime(a, .source_jit);
    var timer = try std.time.Timer.start();
    const wit = try W.generate(a, log_size, cs);
    const witness_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const statement = sb.air.prove.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };
    const prepared = try sb.air.prove.prepare(a, statement, @ptrCast(wit.main));
    const proof = if (use_metal)
        try sb.air.prove.prove(metal.MetalProverEngine, a, config, prepared)
    else
        try sb.air.prove.prove(sb.air.prove.Engine(CpuBackend), a, config, prepared);
    const prove_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const bytes = try proof_wire.encodeProofBytes(a, proof);
    try sb.air.prove.verify(a, config, air, log_size, &.{}, proof);
    const verify_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    std.debug.print(
        "sha256_compress rows=2^{d} compressions={d} backend={s} witness={d:.3}s prove={d:.3}s verify={d:.3}s proof={d}B => {d:.0} compressions/s ({d:.0} headers/s)\n",
        .{ log_size, count, if (use_metal) "metal" else "cpu", witness_s, prove_s, verify_s, bytes.len, @as(f64, @floatFromInt(count)) / prove_s, @as(f64, @floatFromInt(count)) / prove_s / 3 },
    );
}

/// Synthetic linked chain (no proof-of-work yet): header i+1's prev-hash is header i's hash.
fn headers(a: std.mem.Allocator, log_size: u32, use_metal: bool) !void {
    const H = sb.header_chain;
    const air = (try sb.air.ir.Air.parseJson(a, H.lean_json)).value;
    const count = (@as(usize, 1) << @intCast(log_size)) / H.PERIOD;
    const hs = try a.alloc(H.Header, count);
    var prng = std.Random.DefaultPrng.init(11);
    var prev = [_]u8{0} ** 32;
    for (hs) |*h| {
        prng.random().bytes(h);
        @memcpy(h[4..36], &prev);
        prev = sb.sha256.stateToBytes(sb.sha256.headerHash(h));
    }
    const config = pcs_core.PcsConfig{ .pow_bits = 26, .fri_config = try FriConfig.init(0, 1, 70) };
    if (use_metal) try metal.MetalProverEngine.initializeRuntime(a, .source_jit);
    var timer = try std.time.Timer.start();
    const wit = try H.generate(a, log_size, hs);
    const witness_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const statement = sb.air.prove.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .pubs = &wit.pubs, .air = &air, .allocator = a };
    const prepared = try sb.air.prove.prepare(a, statement, @ptrCast(wit.main));
    const proof = if (use_metal)
        try sb.air.prove.prove(metal.MetalProverEngine, a, config, prepared)
    else
        try sb.air.prove.prove(sb.air.prove.Engine(CpuBackend), a, config, prepared);
    const prove_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    const bytes = try proof_wire.encodeProofBytes(a, proof);
    try sb.air.prove.verify(a, config, air, log_size, &wit.pubs, proof);
    const verify_s = @as(f64, @floatFromInt(timer.lap())) / 1e9;
    std.debug.print(
        "header_chain rows=2^{d} headers={d} backend={s} witness={d:.3}s prove={d:.3}s verify={d:.3}s proof={d}B => {d:.0} headers/s\n",
        .{ log_size, count, if (use_metal) "metal" else "cpu", witness_s, prove_s, verify_s, bytes.len, @as(f64, @floatFromInt(count)) / prove_s },
    );
}
