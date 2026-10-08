//! Spike CLI: prove an AIR on CPU or Metal and verify on CPU.
//!   spike <log_size> <cpu|metal> [lean]   add32-chain (Zig-built or Lean-exported)
//!   spike sha <log_size> <cpu|metal>      SHA-256 compressions (Lean-exported)
//!   spike headers <log_size> <cpu|metal> <headers.hex>   header chain v2 (Lean-exported)
//!   spike leaf <log_size> <n_queries> <pow_bits> <headers.bin>   REC-LEAF: wrap one segment (CPU)
//!   spike chain <log_size> <n_queries> <pow_bits> <headers.bin> [to]   AGG: all headers [0, to)
//!       (segments as in fullrun) folded to one root, checked by the outer verifier (CPU)
//!   spike agg <log_size> <n_leaves> <n_queries> <pow_bits> <headers.bin>   AGG: leaves from genesis,
//!       folded to one root, checked by the outer verifier (CPU)

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
    if (args.len == 6 and std.mem.eql(u8, args[1], "leaf")) return leaf(
        gpa.allocator(),
        a,
        try std.fmt.parseInt(u32, args[2], 10),
        try std.fmt.parseInt(u32, args[3], 10),
        try std.fmt.parseInt(u32, args[4], 10),
        args[5],
    );
    if (args.len >= 6 and std.mem.eql(u8, args[1], "chain")) return chain(
        gpa.allocator(),
        a,
        try std.fmt.parseInt(u32, args[2], 10),
        try std.fmt.parseInt(u32, args[3], 10),
        try std.fmt.parseInt(u32, args[4], 10),
        args[5],
        if (args.len > 6) try std.fmt.parseInt(usize, args[6], 10) else std.math.maxInt(usize),
    );
    if (args.len == 7 and std.mem.eql(u8, args[1], "agg")) return agg(
        gpa.allocator(),
        a,
        try std.fmt.parseInt(u32, args[2], 10),
        try std.fmt.parseInt(usize, args[3], 10),
        try std.fmt.parseInt(u32, args[4], 10),
        try std.fmt.parseInt(u32, args[5], 10),
        args[6],
    );
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
fn leaf(gpa: std.mem.Allocator, a: std.mem.Allocator, log_size: u32, n_queries: u32, pow_bits: u32, path: []const u8) !void {
    const H = sb.header_chain;
    const raw = try std.fs.cwd().readFileAlloc(a, path, 1 << 31);
    const n = @as(usize, 1) << @intCast(log_size - 8);
    if (raw.len < 80 * n) return error.BadHeaderFile;
    const segment: []const H.Header = @as([*]const H.Header, @ptrCast(raw.ptr))[0..n];
    const fri = try @import("stwo_core").pcs.config_v2.FriConfigV2.init(pow_bits, 0, 1, n_queries, 1);
    const tables = try sb.recursion.leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    var r = try sb.recursion.leaf.wrapSegment(gpa, a, tables, log_size, segment, sb.header_chain.genesis_start, null, fri);
    defer r.proof.deinit();
    const t = r.timings;
    const s = struct {
        fn f(ns: u64) f64 {
            return @as(f64, @floatFromInt(ns)) / 1e9;
        }
    }.f;
    std.debug.print("leaf log={d} headers={d} queries={d} pow={d}: segment {d:.2}s, circuit {d} vars built {d:.2}s, leaf prove {d:.2}s, verify {d:.2}s, proof {d} bytes\n", .{ log_size, n, n_queries, pow_bits, s(t.segment_ns), t.n_vars, s(t.build_ns), s(t.prove_ns), s(t.verify_ns), r.proof.bytes.len });
}

fn secs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e9;
}

fn agg(gpa: std.mem.Allocator, a: std.mem.Allocator, log_size: u32, n_leaves: usize, n_queries: u32, pow_bits: u32, path: []const u8) !void {
    const H = sb.header_chain;
    const L = sb.recursion.leaf;
    const N = sb.recursion.node;
    const raw = try std.fs.cwd().readFileAlloc(a, path, 1 << 31);
    const all: []const H.Header = @as([*]const H.Header, @ptrCast(raw.ptr))[0 .. raw.len / 80];
    const per = @as(usize, 1) << @intCast(log_size - 8);
    if (all.len < per * n_leaves) return error.BadHeaderFile;
    const fri = try @import("stwo_core").pcs.config_v2.FriConfigV2.init(pow_bits, 0, 1, n_queries, 1);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();

    var first = try L.buildSegmentLeaf(gpa, a, log_size, all[0..per], H.genesis_start);
    var shape = try N.Shape.init(gpa, &tables.table, first.paddedSizes(), fri);
    defer shape.deinit(gpa);
    const node_id = try N.nodeIdentity(gpa, &tables.table, &shape);
    std.debug.print("shape and node identity: {d:.1}s\n", .{secs(timer.lap())});

    const items = try a.alloc(N.Proved, n_leaves);
    const leaf_hashes = try a.alloc([8]u32, n_leaves);
    for (items, leaf_hashes, 0..) |*it, *lh, i| {
        const h0 = i * per;
        var sl = if (i == 0) first else try L.buildSegmentLeaf(gpa, a, log_size, all[h0 .. h0 + per], sb.segments.startAt(all, h0, sb.segments.workBefore(all, h0)));
        const lf = try L.proveSegmentLeaf(gpa, a, tables, &sl, shape.target, fri);
        it.* = .{ .proof = lf.proof, .key = L.zero_key, .pubs = lf.pubs };
        lh.* = lf.proof.circuit_hash;
        std.debug.print("leaf {d}: segment {d:.1}s, leaf prove {d:.1}s\n", .{ i, secs(lf.timings.segment_ns), secs(lf.timings.prove_ns) });
    }
    const t_leaves = timer.lap();
    var root = try N.foldAll(gpa, a, tables, &shape, items);
    defer root.proof.deinit();
    const t_fold = timer.lap();
    const vk_leaf = (try L.leafIdentity(gpa, log_size, all, shape.target, fri.log_blowup_factor)).hash;
    for (leaf_hashes) |*h| {
        if (!std.mem.eql(u32, h, &vk_leaf)) return error.LeafIdentityMismatch;
        h.* = vk_leaf;
    }
    try N.verifyRoot(gpa, a, tables, .{ .node = node_id, .leaf_hashes = leaf_hashes }, &root.proof, root.pubs);
    std.debug.print("agg log={d} leaves={d} headers={d} queries={d} pow={d}: leaves {d:.1}s, fold {d} nodes {d:.1}s, root verified {d:.2}s, root proof {d} bytes, tip height {d}\n", .{ log_size, n_leaves, per * n_leaves, n_queries, pow_bits, secs(t_leaves), n_leaves - 1, secs(t_fold), secs(timer.lap()), root.proof.bytes.len, root.pubs[38].toU32() | (root.pubs[39].toU32() << 16) });
}

/// Segments of `all[0..to)`: `2^(log-8)` headers each, shrinking (by powers of two) at the end.
fn plan(a: std.mem.Allocator, log_size: u32, to: usize) ![]const [2]usize {
    var segs: std.ArrayList([2]usize) = .empty;
    var h0: usize = 0;
    while (h0 < to) {
        var ls = log_size;
        while (ls > 8 and (@as(usize, 1) << @intCast(ls - 8)) > to - h0) ls -= 1;
        const n = @as(usize, 1) << @intCast(ls - 8);
        if (n > to - h0) break;
        try segs.append(a, .{ h0, ls });
        h0 += n;
    }
    return segs.items;
}

fn chain(gpa: std.mem.Allocator, a: std.mem.Allocator, log_size: u32, n_queries: u32, pow_bits: u32, path: []const u8, to_req: usize) !void {
    const L = sb.recursion.leaf;
    const N = sb.recursion.node;
    const raw = try std.fs.cwd().readFileAlloc(a, path, 1 << 31);
    const all: []const sb.header_chain.Header = @as([*]const sb.header_chain.Header, @ptrCast(raw.ptr))[0 .. raw.len / 80];
    const to = @min(to_req, all.len);
    const segs = try plan(a, log_size, to);
    const fri = try @import("stwo_core").pcs.config_v2.FriConfigV2.init(pow_bits, 0, 1, n_queries, 1);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();
    const t_all = timer.read();

    // Chainwork before each segment.
    const works = try a.alloc(u256, segs.len);
    {
        var w: u256 = 0;
        var h: usize = 0;
        for (segs, works) |seg, *wk| {
            w += sb.segments.workBefore(all[h..seg[0]], seg[0] - h);
            h = seg[0];
            wk.* = w;
        }
    }

    // The shape covers the first leaf of every segment size.
    var start: ?L.ComponentSizes = null;
    var seen = [_]bool{false} ** 32;
    for (segs, works) |seg, wk| {
        if (seen[seg[1]]) continue;
        seen[seg[1]] = true;
        var tmp = std.heap.ArenaAllocator.init(gpa);
        defer tmp.deinit();
        const n = @as(usize, 1) << @intCast(seg[1] - 8);
        var sl = try L.buildSegmentLeaf(gpa, tmp.allocator(), @intCast(seg[1]), all[seg[0] .. seg[0] + n], sb.segments.startAt(all, seg[0], wk));
        defer sl.ctx.deinit();
        const p = sl.paddedSizes();
        start = if (start) |s0| s0.elementwiseMax(p) else p;
    }
    var shape = try N.Shape.init(gpa, &tables.table, start.?, fri);
    defer shape.deinit(gpa);
    const node_id = try N.nodeIdentity(gpa, &tables.table, &shape);
    // The verifier's leaf identities, from public data (the first segment of each size).
    var size_hash: [32][8]u32 = undefined;
    @memset(&seen, false);
    for (segs) |seg| if (!seen[seg[1]]) {
        seen[seg[1]] = true;
        size_hash[seg[1]] = (try L.leafIdentity(gpa, @intCast(seg[1]), all, shape.target, fri.log_blowup_factor)).hash;
    };
    const vk_leaf_hashes = try a.alloc([8]u32, segs.len);
    for (segs, vk_leaf_hashes) |seg, *h| h.* = size_hash[seg[1]];
    std.debug.print("chain: {d} headers in {d} segments; shape and VK (node + leaf identities) {d:.1}s\n", .{ to, segs.len, secs(timer.lap()) });

    const items = try a.alloc(N.Proved, segs.len);
    const leaf_hashes = try a.alloc([8]u32, segs.len);
    for (segs, works, items, leaf_hashes, 0..) |seg, wk, *it, *lh, i| {
        var tmp = std.heap.ArenaAllocator.init(gpa);
        defer tmp.deinit();
        const n = @as(usize, 1) << @intCast(seg[1] - 8);
        var sl = try L.buildSegmentLeaf(gpa, tmp.allocator(), @intCast(seg[1]), all[seg[0] .. seg[0] + n], sb.segments.startAt(all, seg[0], wk));
        const lf = try L.proveSegmentLeaf(gpa, a, tables, &sl, shape.target, fri);
        it.* = .{ .proof = lf.proof, .key = L.zero_key, .pubs = lf.pubs };
        lh.* = lf.proof.circuit_hash;
        if (i % 8 == 0 or i + 1 == segs.len)
            std.debug.print("  leaf {d}/{d} (heights {d}..{d}): segment {d:.1}s, leaf {d:.1}s, elapsed {d:.0}s\n", .{ i + 1, segs.len, seg[0], seg[0] + n - 1, secs(lf.timings.segment_ns), secs(lf.timings.prove_ns), secs(timer.read() - t_all) });
    }
    const t_leaves = timer.lap();
    var root = try N.foldAll(gpa, a, tables, &shape, items);
    defer root.proof.deinit();
    const t_fold = timer.lap();
    for (leaf_hashes, vk_leaf_hashes, 0..) |got, want, i| if (!std.mem.eql(u32, &got, &want)) {
        std.debug.print("leaf {d}: circuit hash differs from the VK\n", .{i});
        return error.LeafIdentityMismatch;
    };
    try N.verifyRoot(gpa, a, tables, .{ .node = node_id, .leaf_hashes = vk_leaf_hashes }, &root.proof, root.pubs);
    var tip: [8]u32 = undefined;
    for (&tip, 0..) |*w, k| w.* = root.pubs[16 + 2 * k].toU32() | (root.pubs[17 + 2 * k].toU32() << 16);
    var work: u256 = 0;
    for (0..10) |l| work |= @as(u256, root.pubs[98 + l].toU32()) << @intCast(16 * l);
    std.debug.print("chain ROOT VERIFIED: headers 0..{d}, {d} leaves, {d} nodes; leaves {d:.0}s, fold {d:.0}s, verify {d:.2}s; root proof {d} bytes\n", .{ to - 1, segs.len, segs.len - 1, secs(t_leaves), secs(t_fold), secs(timer.lap()), root.proof.bytes.len });
    std.debug.print("  tip height {d}, chainwork 0x{x}, tip state words", .{ root.pubs[38].toU32() | (root.pubs[39].toU32() << 16), work });
    for (tip) |w| std.debug.print(" {x:0>8}", .{w});
    std.debug.print("\n", .{});
}

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
        const start = sb.segments.startAt(all, h0, work);
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
