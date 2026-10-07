//! Spike CLI: prove an AIR on CPU or Metal and verify on CPU.
//!   spike <log_size> <cpu|metal> [lean]   add32-chain (Zig-built or Lean-exported)
//!   spike sha <log_size> <cpu|metal>      SHA-256 compressions (Lean-exported)
//!   spike headers <log_size> <cpu|metal> <headers.hex>   header chain v2 (Lean-exported)

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
    if (args.len == 5 and std.mem.eql(u8, args[1], "headers")) return headers(a, try std.fmt.parseInt(u32, args[2], 10), std.mem.eql(u8, args[3], "metal"), args[4]);
    if (args.len >= 5 and std.mem.eql(u8, args[1], "fullrun")) return fullrun(
        gpa.allocator(),
        try std.fmt.parseInt(u32, args[2], 10),
        args[3],
        args[4],
        if (args.len > 5) try std.fmt.parseInt(usize, args[5], 10) else 0,
        if (args.len > 6) try std.fmt.parseInt(usize, args[6], 10) else std.math.maxInt(usize),
    );
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

/// Real mainnet headers from a hex file (one 80-byte header per line), from height 0.
fn headers(a: std.mem.Allocator, log_size: u32, use_metal: bool, path: []const u8) !void {
    const H = sb.header_chain;
    const air = (try sb.air.ir.Air.parseJson(a, H.lean_json)).value;
    const count = (@as(usize, 1) << @intCast(log_size)) / H.PERIOD;
    const all = try H.loadHeaders(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
    if (all.len < count) return error.NotEnoughHeaders;
    const hs = all[0..count];
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

fn word(h: *const sb.header_chain.Header, t: usize) u32 {
    return std.mem.readInt(u32, h[4 * t ..][0..4], .big);
}

/// HC-FULLRUN: walk a binary header file (80 bytes per header, by height) in segments of
/// 2^log_size / 256 headers. For each segment, derive the start state from the chain itself,
/// generate the witness, and either check it against the Lean-exported AIR (`check`) or prove
/// and verify it (`cpu` / `metal`). Also checks that each segment's public outputs equal the next
/// segment's public inputs (what aggregation will enforce).
fn fullrun(gpa: std.mem.Allocator, log_size: u32, mode: []const u8, path: []const u8, from: usize, to_req: usize) !void {
    const H = sb.header_chain;
    const R = sb.retarget;
    const M31T = @import("stwo_core").fields.m31.M31;
    var arena0 = std.heap.ArenaAllocator.init(gpa);
    defer arena0.deinit();
    const a0 = arena0.allocator();
    const raw = try std.fs.cwd().readFileAlloc(a0, path, 1 << 31);
    if (raw.len % 80 != 0) return error.BadHeaderFile;
    const all: []const H.Header = @as([*]const H.Header, @ptrCast(raw.ptr))[0 .. raw.len / 80];
    const to = @min(to_req, all.len);
    const air = (try sb.air.ir.Air.parseJson(a0, H.lean_json)).value;
    const digest = try air.digest(a0);
    const use_metal = std.mem.eql(u8, mode, "metal");
    const prove = use_metal or std.mem.eql(u8, mode, "cpu");
    const config = pcs_core.PcsConfig{ .pow_bits = 26, .fri_config = try FriConfig.init(0, 1, 70) };
    if (use_metal) try metal.MetalProverEngine.initializeRuntime(a0, .source_jit);

    // Chainwork before `from`.
    var work: u256 = 0;
    for (all[0..from]) |*h| work += sb.work.blockProof(R.compactValue(R.le(word(h, 18))));

    var prev_pubs: ?[H.N_PUB]M31T = null;
    var h0 = from;
    var segments: usize = 0;
    var failures: usize = 0;
    var timer = try std.time.Timer.start();
    var prove_ns: u64 = 0;
    var proof_bytes: usize = 0;
    while (h0 < to) {
        var ls = log_size;
        while (ls > 8 and (@as(usize, 1) << @intCast(ls - 8)) > to - h0) ls -= 1;
        const n = @as(usize, 1) << @intCast(ls - 8);
        if (n > to - h0) break;
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const a = arena.allocator();
        const seg = all[h0 .. h0 + n];
        var start = H.genesis_start;
        if (h0 > 0) {
            var prev: [11]u32 = undefined;
            const k = @min(h0, 11);
            for (0..k) |i| prev[i] = word(&all[h0 - 1 - i], 17);
            const p = (h0 - 1) - (h0 - 1) % 2016;
            start = .{ .height = @intCast(h0), .prev_nbits_word = word(&all[h0 - 1], 18),
                .prev_pst_word = word(&all[p], 17), .window = H.windowFrom(prev[0..k]), .work = work };
        }
        const wit = H.generateFrom(a, ls, seg, start) catch |e| {
            std.debug.print("FAIL witness at segment {d}..{d}: {s}\n", .{ h0, h0 + n - 1, @errorName(e) });
            failures += 1;
            for (seg) |*h| work += sb.work.blockProof(R.compactValue(R.le(word(h, 18))));
            h0 += n;
            prev_pubs = null;
            continue;
        };
        // Chaining: outputs of the previous segment = inputs of this one.
        if (prev_pubs) |pp| {
            const pairs = [_][3]usize{ .{ 16, 0, 16 }, .{ 40, 34, 2 }, .{ 42, 36, 2 }, .{ 46, 44, 2 }, .{ 68, 48, 20 }, .{ 98, 88, 10 } };
            for (pairs) |pr| for (0..pr[2]) |i| {
                if (pp[pr[0] + i].toU32() != wit.pubs[pr[1] + i].toU32()) {
                    std.debug.print("FAIL chaining at height {d}: out pub {d} != in pub {d}\n", .{ h0, pr[0] + i, pr[1] + i });
                    failures += 1;
                }
            };
            const out_h = pp[38].toU32() | (pp[39].toU32() << 16);
            const in_h = wit.pubs[32].toU32() | (wit.pubs[33].toU32() << 16);
            if (out_h + 1 != in_h) {
                std.debug.print("FAIL chaining heights at {d}\n", .{h0});
                failures += 1;
            }
        }
        if (prove) {
            const t0 = timer.read();
            const statement = sb.air.prove.AirStatement{ .log_size = ls, .digest = digest, .pubs = &wit.pubs, .air = &air, .allocator = a };
            const prepared = try sb.air.prove.prepare(a, statement, @ptrCast(wit.main));
            const proof = if (use_metal)
                try sb.air.prove.prove(metal.MetalProverEngine, a, config, prepared)
            else
                try sb.air.prove.prove(sb.air.prove.Engine(CpuBackend), a, config, prepared);
            prove_ns += timer.read() - t0;
            proof_bytes += (try proof_wire.encodeProofBytes(a, proof)).len;
            sb.air.prove.verify(a, config, air, ls, &wit.pubs, proof) catch |e| {
                std.debug.print("FAIL verify at segment {d}: {s}\n", .{ h0, @errorName(e) });
                failures += 1;
            };
        } else {
            const t = sb.air.interp.RowTrace{ .log_size = ls, .pubs = &wit.pubs,
                .preprocessed = @ptrCast(try air.genPreprocessed(a, ls)), .main = @ptrCast(wit.main) };
            if (try sb.air.interp.firstViolation(a, air, t)) |v| {
                std.debug.print("FAIL constraint {d} at row {d} (segment {d})\n", .{ v.constraint, v.row, h0 });
                failures += 1;
            }
        }
        for (seg) |*h| work += sb.work.blockProof(R.compactValue(R.le(word(h, 18))));
        prev_pubs = wit.pubs;
        segments += 1;
        h0 += n;
        if (segments % 16 == 0) std.debug.print("  ... height {d} ({d:.0}s)\n", .{ h0 - 1, @as(f64, @floatFromInt(timer.read())) / 1e9 });
    }
    const total_s = @as(f64, @floatFromInt(timer.read())) / 1e9;
    std.debug.print("fullrun {s}: heights {d}..{d} in {d} segments, failures={d}, total={d:.1}s", .{ mode, from, h0 - 1, segments, failures, total_s });
    if (prove) std.debug.print(" prove={d:.1}s proofs={d}B", .{ @as(f64, @floatFromInt(prove_ns)) / 1e9, proof_bytes });
    std.debug.print(" final_work=0x{x}\n", .{work});
    if (failures != 0) return error.FullRunFailures;
}
