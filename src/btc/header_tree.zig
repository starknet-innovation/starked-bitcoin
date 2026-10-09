//! Header commitment tree (HC-HASHTREE, D-033): witnesses for the `header_chain_v7` and
//! `blake2s_tree` components (Lean: `Gadgets/HeaderTree.lean`) and the native tree functions.
//! A segment of `2^K` headers commits to the perfect Blake2s tree over its block hashes; the
//! verifier contributes the public entry `node(K, 0, root)`.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const H = @import("header_chain.zig");
const B = @import("../hash/blake2s_air.zig");
const system = @import("../air/system.zig");

pub const header_json = @embedFile("air:header_chain_v7");
pub const tree_json = @embedFile("air:blake2s_tree");
pub const REL_NODE: u32 = 2;
pub const TREE_N_MAIN: usize = 309;
const LVL = 300;
const LVLB = 301;
const LVL_INV = 306;
const POS = 307;
const TMULT = 308;
const HMULT = 124;

pub const Words = [8]u32;

/// The standard Blake2s-256 chaining value (IV with the parameter block).
pub fn h0() Words {
    var h = B.IV;
    h[0] ^= 0x01010020;
    return h;
}

/// A tree node: Blake2s of `l ‖ r` (one 64-byte block, final).
pub fn node(l: Words, r: Words) Words {
    var m: [16]u32 = undefined;
    @memcpy(m[0..8], &l);
    @memcpy(m[8..16], &r);
    return B.compress(.{ .h = h0(), .m = m, .t = 64, .f = true });
}

/// Root of the perfect tree over `leaves` (a power of two).
pub fn root(leaves: []const Words) Words {
    if (leaves.len == 1) return leaves[0];
    const half = leaves.len / 2;
    return node(root(leaves[0..half]), root(leaves[half..]));
}

/// A peak of an MMR stack: a folded item and the number of leaves it covers.
pub fn Peak(comptime E: type) type {
    return struct { e: E, n: usize };
}

/// Pushes `e` (covering `n` leaves) onto the peak stack, merging the top two while their counts
/// are equal (PROOF-STORE: the stack is what a stored chain proof keeps, so it can be extended).
pub fn pushPeak(comptime E: type, a: std.mem.Allocator, stack: *std.ArrayList(Peak(E)), e: E, n: usize, ctx: anytype, comptime merge: fn (@TypeOf(ctx), E, E) anyerror!E) !void {
    try stack.append(a, .{ .e = e, .n = n });
    while (stack.items.len >= 2 and stack.items[stack.items.len - 1].n == stack.items[stack.items.len - 2].n) {
        const r = stack.pop().?;
        const l = stack.pop().?;
        try stack.append(a, .{ .e = try merge(ctx, l.e, r.e), .n = l.n + r.n });
    }
}

/// Bags the peaks right to left into one item, leaving `peaks` unchanged (a single peak is
/// returned as is).
pub fn bagPeaks(comptime E: type, peaks: []const Peak(E), ctx: anytype, comptime merge: fn (@TypeOf(ctx), E, E) anyerror!E) !E {
    if (peaks.len == 0) return error.NothingToFold;
    var acc = peaks[peaks.len - 1].e;
    var i = peaks.len - 1;
    while (i > 0) {
        i -= 1;
        acc = try merge(ctx, peaks[i].e, acc);
    }
    return acc;
}

/// **MMR order** (D-033): `items` (with leaf counts `sizes`) left to right, merging the top two
/// while their counts are equal, then the remaining peaks right to left ("bagging"). Every merge
/// joins adjacent ranges, left before right.
pub fn mmrFold(comptime E: type, a: std.mem.Allocator, items: []const E, sizes: []const usize, ctx: anytype, comptime merge: fn (@TypeOf(ctx), E, E) anyerror!E) !E {
    if (items.len == 0) return error.NothingToFold;
    var stack = std.ArrayList(Peak(E)).empty;
    defer stack.deinit(a);
    for (items, sizes) |e, n| try pushPeak(E, a, &stack, e, n, ctx, merge);
    return bagPeaks(E, stack.items, ctx, merge);
}

/// Segment sizes, as log sizes of the segment AIR: `2^(log − 8)` headers. 2 (`log = 9`) is the
/// minimum (a 1-header segment has no tree node); 4096 (`log = 20`) the largest we prove.
pub const MIN_SEG_LOG: u32 = 9;
pub const MAX_SEG_LOG: u32 = 20;

pub fn segHeaders(log: u32) usize {
    return @as(usize, 1) << @intCast(log - 8);
}

/// The next segment at height `h0` with `remaining` headers left: the largest log size in
/// `[MIN_SEG_LOG, max_log]` whose segment fits and stays aligned (`n ≤ lowbit(h0)` for `h0 > 0`).
/// Then every peak is an aligned perfect subtree and the fold is the canonical MMR (`mmrRoot`),
/// however the chain is cut. From `h0 = 0` this is the greedy largest-first plan.
pub fn nextSegment(start: usize, remaining: usize, max_log: u32) ?u32 {
    var ls = max_log;
    while (ls >= MIN_SEG_LOG) : (ls -= 1) {
        const n = segHeaders(ls);
        if (n <= remaining and (start == 0 or n <= (start & (~start + 1)))) return ls;
    }
    return null;
}

/// Segments `(h0, log)` covering `[from, to)` after `from` (as many as fit; an odd last header is
/// left out).
pub fn planSegments(a: std.mem.Allocator, from: usize, to: usize, max_log: u32) ![]const [2]usize {
    var segs: std.ArrayList([2]usize) = .empty;
    var at = from;
    while (at < to) {
        const ls = nextSegment(at, to - at, max_log) orelse break;
        try segs.append(a, .{ at, ls });
        at += segHeaders(ls);
    }
    return segs.toOwnedSlice(a);
}

/// The verifier's check of a segment list (log sizes, chain order from height 0): every size in
/// range and every segment aligned, so the fold's root is the canonical MMR root.
pub fn validPlan(logs: []const u32, max_log: u32) bool {
    var at: usize = 0;
    for (logs) |ls| {
        if (ls < MIN_SEG_LOG or ls > max_log) return false;
        const n = segHeaders(ls);
        if (at != 0 and n > (at & (~at + 1))) return false;
        at += n;
    }
    return logs.len > 0;
}

/// The depth of leaf 0 in the MMR over `n` leaves: the first peak's height, plus one if there are
/// other peaks (bagging joins the first peak once, on the left).
pub fn leftmostDepth(n: usize) usize {
    const first = std.math.log2_int(usize, n);
    return first + @intFromBool(n != (@as(usize, 1) << @intCast(first)));
}

/// Checks that `steps` is the inclusion path of leaf 0 in an MMR over `n` leaves with root `t`:
/// every sibling on the right, of the depth `n` implies.
pub fn verifyLeftmost(leaf: Words, steps: []const Step, n: usize, t: Words) bool {
    if (steps.len != leftmostDepth(n)) return false;
    for (steps) |s| if (s.left) return false;
    return verifyInclusion(leaf, steps, t);
}

fn nodeMerge(_: void, l: Words, r: Words) anyerror!Words {
    return node(l, r);
}

/// The MMR root over block hashes `leaves` (in height order).
pub fn mmrRoot(a: std.mem.Allocator, leaves: []const Words) !Words {
    const ones = try a.alloc(usize, leaves.len);
    defer a.free(ones);
    @memset(ones, 1);
    return mmrFold(Words, a, leaves, ones, {}, nodeMerge);
}

/// One step of an inclusion proof: hash with `sibling`, which sits on the left if `left`.
pub const Step = struct { sibling: Words, left: bool };

/// The inclusion proof of leaf `h` in `mmrRoot(leaves)`, leaf to root.
pub fn inclusionProof(a: std.mem.Allocator, leaves: []const Words, h: usize) ![]Step {
    if (h >= leaves.len) return error.OutOfRange;
    const E = struct { w: Words, has: bool };
    const Ctx = struct {
        a: std.mem.Allocator,
        steps: *std.ArrayList(Step),
        fn merge(c: @This(), l: E, r: E) anyerror!E {
            if (l.has) try c.steps.append(c.a, .{ .sibling = r.w, .left = false });
            if (r.has) try c.steps.append(c.a, .{ .sibling = l.w, .left = true });
            return .{ .w = node(l.w, r.w), .has = l.has or r.has };
        }
    };
    const items = try a.alloc(E, leaves.len);
    defer a.free(items);
    for (items, leaves, 0..) |*e, l, i| e.* = .{ .w = l, .has = i == h };
    const ones = try a.alloc(usize, leaves.len);
    defer a.free(ones);
    @memset(ones, 1);
    var steps = std.ArrayList(Step).empty;
    errdefer steps.deinit(a);
    _ = try mmrFold(E, a, items, ones, Ctx{ .a = a, .steps = &steps }, Ctx.merge);
    return steps.toOwnedSlice(a);
}

/// Checks an inclusion proof of `leaf` against the root `t`.
pub fn verifyInclusion(leaf: Words, steps: []const Step, t: Words) bool {
    var x = leaf;
    for (steps) |s| x = if (s.left) node(s.sibling, x) else node(x, s.sibling);
    return std.mem.eql(u32, &x, &t);
}

/// A header's block hash (SHA256d) as the 8 SHA-256 state words (the leaves' encoding).
pub fn blockHash(header: *const H.Header) Words {
    const Sha = std.crypto.hash.sha2.Sha256;
    var d: [32]u8 = undefined;
    Sha.hash(std.mem.asBytes(header), &d, .{});
    Sha.hash(&d, &d, .{});
    var w: Words = undefined;
    for (&w, 0..) |*x, i| x.* = std.mem.readInt(u32, d[4 * i ..][0..4], .big);
    return w;
}

/// The 16 limbs of a word tuple, lo/hi interleaved (the lookups' encoding).
pub fn limbs(w: Words) [16]M31 {
    var out: [16]M31 = undefined;
    for (w, 0..) |x, i| {
        out[2 * i] = M31.fromCanonical(x & 0xffff);
        out[2 * i + 1] = M31.fromCanonical(x >> 16);
    }
    return out;
}

/// The public entry for a segment of `2^k` headers with root `r`.
pub fn rootEntry(a: std.mem.Allocator, k: u32, r: Words) !system.PubEntry {
    const vals = try a.alloc(M31, 18);
    vals[0] = M31.fromCanonical(k);
    vals[1] = M31.zero();
    @memcpy(vals[2..], &limbs(r));
    return .{ .rel = REL_NODE, .vals = vals, .mult = M31.zero().sub(M31.one()) };
}

pub const Witness = struct {
    header_main: [][]M31,
    tree_main: [][]M31,
    root: Words,
};

/// Witnesses for a segment: the header-chain witness `hw` (2^log_size rows) gains the leaf
/// multiplicity column; the tree component computes every node, then repeats the root.
pub fn generate(a: std.mem.Allocator, log_size: u32, hw: H.Witness) !Witness {
    const n = @as(usize, 1) << @intCast(log_size);
    const n_leaves = hw.hashes.len;
    const k: u32 = std.math.log2_int(usize, n_leaves);
    if (@as(usize, 1) << @intCast(k) != n_leaves) return error.NotAPowerOfTwo;
    const leaves = try a.alloc(Words, n_leaves);
    for (leaves, hw.hashes) |*l, h| l.* = h;

    // Nodes by level: level 0 = leaves.
    const levels = try a.alloc([]Words, k + 1);
    levels[0] = leaves;
    for (1..k + 1) |l| {
        levels[l] = try a.alloc(Words, levels[l - 1].len / 2);
        for (levels[l], 0..) |*x, p| x.* = node(levels[l - 1][2 * p], levels[l - 1][2 * p + 1]);
    }
    const r = levels[k][0];

    // Tree periods: every internal node once, then the root repeated (K = 0: no internal node,
    // the periods still need a consistent node, so they recompute nothing and are inactive in
    // lookups only through multiplicity 0 — see below).
    const n_periods = (n + B.PERIOD - 1) / B.PERIOD;
    const Item = struct { l: u32, p: u32 };
    var items = std.ArrayList(Item).empty;
    for (1..k + 1) |l| for (0..levels[l].len) |p| try items.append(a, .{ .l = @intCast(l), .p = @intCast(p) });
    if (items.items.len == 0) return error.SegmentTooSmall; // a 1-header segment needs no tree; not supported yet
    const inputs = try a.alloc(B.Input, n_periods);
    const per = try a.alloc(Item, n_periods);
    for (inputs, per, 0..) |*in, *it, i| {
        it.* = items.items[@min(i, items.items.len - 1)];
        var m: [16]u32 = undefined;
        @memcpy(m[0..8], &levels[it.l - 1][2 * it.p]);
        @memcpy(m[8..16], &levels[it.l - 1][2 * it.p + 1]);
        in.* = .{ .h = h0(), .m = m, .t = 64, .f = true };
    }
    const tree = try a.alloc([]M31, TREE_N_MAIN);
    for (tree) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    for (0..n_periods) |i| B.fillPeriod(tree[0..B.N_MAIN], i * B.PERIOD, n, inputs[i]);

    // Uses per (level, position): the children of every period whose row 0 is in the trace,
    // and the public root entry. Yields: the first period computing a node carries its count.
    var uses = std.AutoHashMap(u64, u32).init(a);
    const key = struct {
        fn f(l: u32, p: u32) u64 {
            return (@as(u64, l) << 32) | p;
        }
    }.f;
    for (per) |it| {
        (try uses.getOrPutValue(key(it.l - 1, 2 * it.p), 0)).value_ptr.* += 1;
        (try uses.getOrPutValue(key(it.l - 1, 2 * it.p + 1), 0)).value_ptr.* += 1;
    }
    (try uses.getOrPutValue(key(k, 0), 0)).value_ptr.* += 1;
    var yielded = std.AutoHashMap(u64, void).init(a);
    for (per, 0..) |it, i| {
        const base = i * B.PERIOD;
        for (0..B.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            tree[LVL][row] = M31.fromCanonical(it.l);
            for (0..5) |b| tree[LVLB + b][row] = M31.fromCanonical((it.l >> @intCast(b)) & 1);
            tree[LVL_INV][row] = try M31.fromCanonical(it.l).inv();
            tree[POS][row] = M31.fromCanonical(it.p);
        }
        if (base + 87 < n) {
            const kk = key(it.l, it.p);
            if (!yielded.contains(kk)) {
                try yielded.put(kk, {});
                tree[TMULT][base + 87] = M31.fromCanonical(uses.get(kk) orelse 0);
            }
        }
    }

    // Header component: the header witness plus the leaf multiplicities (at row 215 of each header).
    const hm = try a.alloc([]M31, HMULT + 1);
    @memcpy(hm[0..HMULT], hw.main);
    hm[HMULT] = try a.alloc(M31, n);
    @memset(hm[HMULT], M31.zero());
    for (0..n_leaves) |j| hm[HMULT][256 * j + 215] = M31.fromCanonical(uses.get(key(0, @intCast(j))) orelse 0);
    return .{ .header_main = hm, .tree_main = tree, .root = r };
}

test "header tree: a 16-header segment proves with its Blake2s root; a wrong root is rejected" {
    const ir = @import("../air/ir.zig");
    const rec = @import("../air/prove_rec.zig");
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const headers_air = (try ir.Air.parseJson(a, header_json)).value;
    const tree_air = (try ir.Air.parseJson(a, tree_json)).value;
    const hdrs = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const log_size: u32 = 12;
    const hw = try H.generate(a, log_size, hdrs);
    const w = try generate(a, log_size, hw);

    // The root equals Blake2s over the leaves' words (little-endian bytes), recomputed with std.
    var lb: [64]u8 = undefined;
    for (hw.hashes[0], 0..) |x, i| std.mem.writeInt(u32, lb[4 * i ..][0..4], x, .little);
    for (hw.hashes[1], 0..) |x, i| std.mem.writeInt(u32, lb[32 + 4 * i ..][0..4], x, .little);
    var d: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&lb, &d, .{});
    const n01 = node(hw.hashes[0], hw.hashes[1]);
    for (n01, 0..) |x, i| try std.testing.expectEqual(std.mem.readInt(u32, d[4 * i ..][0..4], .little), x);

    for (hdrs, hw.hashes) |*hd, hh| try std.testing.expectEqualSlices(u32, &hh, &blockHash(hd));
    try std.testing.expectEqualSlices(u32, &w.root, &try mmrRoot(a, hw.hashes));

    // Each component's constraints hold.
    const tt = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(try tree_air.genPreprocessed(a, log_size)), .main = @ptrCast(w.tree_main) };
    try std.testing.expect(try interp.firstViolation(a, tree_air, tt) == null);
    const ht = interp.RowTrace{ .log_size = log_size, .pubs = &hw.pubs, .preprocessed = @ptrCast(try headers_air.genPreprocessed(a, log_size)), .main = @ptrCast(w.header_main) };
    try std.testing.expect(try interp.firstViolation(a, headers_air, ht) == null);

    const parts = [_]system.Part{
        .{ .air = &headers_air, .log_size = log_size, .pubs = &hw.pubs },
        .{ .air = &tree_air, .log_size = log_size },
    };
    const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const mains = [_][]const []const M31{ @ptrCast(w.header_main), @ptrCast(w.tree_main) };
    const ext = [_]system.PubEntry{try rootEntry(a, 4, w.root)};
    try system.verifyExt(a, cfg, &parts, &ext, try system.prove(E, a, cfg, &parts, &mains));

    var bad_root = w.root;
    bad_root[0] ^= 1;
    const bad = [_]system.PubEntry{try rootEntry(a, 4, bad_root)};
    try std.testing.expectError(error.LookupsUnbalanced, system.verifyExt(a, cfg, &parts, &bad, try system.prove(E, a, cfg, &parts, &mains)));
}

test "header tree: MMR root and inclusion proofs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var leaves: [13]Words = undefined;
    for (&leaves, 0..) |*l, i| l.* = .{ @intCast(i), 1, 2, 3, 4, 5, 6, 7 };
    // 13 = 8 + 4 + 1: peaks root(0..8), root(8..12), leaf 12, bagged right to left.
    const t = try mmrRoot(a, &leaves);
    try std.testing.expectEqualSlices(u32, &node(root(leaves[0..8]), node(root(leaves[8..12]), leaves[12])), &t);
    for (0..13) |h| {
        const steps = try inclusionProof(a, &leaves, h);
        try std.testing.expect(verifyInclusion(leaves[h], steps, t));
        try std.testing.expect(!verifyInclusion(leaves[(h + 1) % 13], steps, t));
    }
    // Segment-wise folding (aligned, non-increasing powers of two) gives the same root.
    const segs = [_]Words{ root(leaves[0..4]), root(leaves[4..8]), root(leaves[8..12]), leaves[12] };
    try std.testing.expectEqualSlices(u32, &t, &try mmrFold(Words, a, &segs, &.{ 4, 4, 4, 1 }, {}, nodeMerge));
}

test "header tree: incremental peaks, aligned plans and the leftmost path" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var leaves: [100]Words = undefined;
    for (&leaves, 0..) |*l, i| l.* = .{ @intCast(i), 9, 8, 7, 6, 5, 4, 3 };
    // Cut 0..52 one way, then extend to 100 from the stored peaks: the root is the MMR root.
    for ([_]usize{ 52, 64, 2, 98 }) |cut| {
        var stack = std.ArrayList(Peak(Words)).empty;
        for ([_][2]usize{ .{ 0, cut }, .{ cut, 100 } }) |range| {
            for (try planSegments(a, range[0], range[1], 12)) |s| {
                const n = segHeaders(@intCast(s[1]));
                try pushPeak(Words, a, &stack, root(leaves[s[0] .. s[0] + n]), n, {}, nodeMerge);
            }
        }
        try std.testing.expectEqualSlices(u32, &try mmrRoot(a, &leaves), &try bagPeaks(Words, stack.items, {}, nodeMerge));
    }
    // Plans: from 0 greedy; after 52 = 32 + 16 + 4, segments of at most 4 until aligned.
    const p = try planSegments(a, 52, 100, 12);
    try std.testing.expectEqual(@as(usize, 52), p[0][0]);
    try std.testing.expectEqual(@as(usize, 10), p[0][1]);
    try std.testing.expect(validPlan(&.{ 12, 12, 12, 11, 10, 10, 9 }, 12));
    try std.testing.expect(!validPlan(&.{ 10, 11 }, 12)); // 8 headers at height 4: misaligned
    try std.testing.expect(!validPlan(&.{ 13, 12 }, 12)); // above the maximum
    try std.testing.expect(!validPlan(&.{ 8, 9 }, 12)); // below the minimum
    // Leaf 0's path is the leftmost one, of the expected depth, for every size.
    for ([_]usize{ 2, 3, 13, 64, 100 }) |n| {
        const t = try mmrRoot(a, leaves[0..n]);
        const steps = try inclusionProof(a, leaves[0..n], 0);
        try std.testing.expect(verifyLeftmost(leaves[0], steps, n, t));
        try std.testing.expect(!verifyLeftmost(leaves[1], steps, n, t));
        if (n > 2) {
            const other = try inclusionProof(a, leaves[0..n], 1);
            try std.testing.expect(!verifyLeftmost(leaves[1], other, n, t));
        }
    }
}
