//! Block Merkle tree (M3a.4 `BLK-MERKLE`): the witness for the `block_merkle` component (Lean:
//! `Block/Merkle.lean`). One row per internal node of the txid tree, level by level, then the root
//! row. Node `k` has id `NB + k`; its message (the children's digests) is hashed by the SHA
//! component as a `NODE` block, an `NPAD` block and the second hash.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const spec = @import("../sha256/spec.zig");
const bsha = @import("sha.zig");
const msg = @import("msg.zig");

pub const json = @embedFile("air:block_merkle");
pub const N_MAIN = 41;
pub const NB: u32 = 1 << 27;

const ACTN = 0;
const RT = 1;
const FIRSTL = 2;
const LAST = 3;
const LINV = 4;
const I = 5;
const CNT = 6;
const PCNT = 7;
const ODD = 8;
const BASE = 9;
const PBASE = 10;
const L1 = 11;
const RIX = 12;
const LEFT = 13;
const RIGHT = 14;
const DUP = 15;
const C1 = 16;
const C1INV = 17;
const RN = 18;
const PINV = 19;
const NM = 20;
const MMC = 21;
const RIDC = 22;
const NF = 23;
const FS = 24;
const RL0 = 25;

pub const Node = struct {
    id: u32,
    left: u32,
    right: u32,
    dup: bool,
    first: bool,
    i: u32,
    cnt: u32,
    pcnt: u32,
    base: u32,
    pbase: u32,
    l1: bool,
};

/// The internal nodes over `ntx` txid leaves (message ids `1 + 2j`), level by level.
pub fn tree(a: std.mem.Allocator, ntx: u32) ![]Node {
    var out = std.ArrayList(Node).empty;
    var pcnt = ntx;
    var pbase: u32 = 0;
    var l1 = true;
    while (pcnt > 1) {
        const cnt = (pcnt + 1) / 2;
        const base: u32 = @intCast(out.items.len);
        for (0..cnt) |ii| {
            const i: u32 = @intCast(ii);
            const dup = 2 * i + 1 == pcnt;
            const left: u32 = if (l1) 1 + 4 * i else NB + pbase + 2 * i;
            const right: u32 = if (dup) left else left + @as(u32, if (l1) 2 else 1);
            try out.append(a, .{ .id = NB + base + i, .left = left, .right = right, .dup = dup, .first = i == 0, .i = i, .cnt = cnt, .pcnt = pcnt, .base = base, .pbase = pbase, .l1 = l1 });
        }
        pbase = base;
        pcnt = cnt;
        l1 = false;
    }
    return out.toOwnedSlice(a);
}

pub fn rootId(nodes: []const Node) u32 {
    return if (nodes.len == 0) 1 else nodes[nodes.len - 1].id;
}

/// Appends each node's three compressions to the plan and sets the digest yields' multiplicities
/// (children of nodes and the root). Returns the root digest.
pub fn extendPlan(a: std.mem.Allocator, pl: *bsha.Plan, nodes: []const Node) !spec.State {
    var comps = std.ArrayList(@import("../sha256/witness.zig").Compression).empty;
    try comps.appendSlice(a, pl.compressions);
    var meta = std.ArrayList(bsha.Meta).empty;
    try meta.appendSlice(a, pl.meta);
    const nd = try a.alloc(spec.State, nodes.len);
    const Ctx = struct {
        msgd: []const spec.State,
        nd: []const spec.State,
        fn of(c: @This(), id: u32) spec.State {
            return if (id >= NB) c.nd[id - NB] else c.msgd[id];
        }
    };
    for (nodes, 0..) |node, k| {
        const ctx = Ctx{ .msgd = pl.digests, .nd = nd };
        var block: spec.Block = undefined;
        @memcpy(block[0..8], &ctx.of(node.left));
        @memcpy(block[8..16], &ctx.of(node.right));
        try comps.append(a, .{ .input = spec.IV, .block = block });
        try meta.append(a, .{ .mid = node.id, .blk = 0, .fst = false, .dbl = false, .node = true, .lid = node.left, .rid = node.right, .dup = node.dup });
        const h1 = spec.compress(spec.IV, block);
        var npad: spec.Block = [_]u32{0} ** 16;
        npad[0] = 0x80000000;
        npad[15] = 512;
        try comps.append(a, .{ .input = h1, .block = npad });
        try meta.append(a, .{ .mid = node.id, .blk = 1, .fst = false, .dbl = false, .npad = true, .lid = node.left, .rid = node.right, .dup = node.dup });
        const h2 = spec.compress(h1, npad);
        var block2: spec.Block = undefined;
        @memcpy(block2[0..8], &h2);
        block2[8] = 0x80000000;
        @memset(block2[9..15], 0);
        block2[15] = 256;
        try comps.append(a, .{ .input = spec.IV, .block = block2 });
        try meta.append(a, .{ .mid = node.id, .blk = 2, .fst = false, .dbl = true });
        nd[k] = spec.compress(spec.IV, block2);
    }
    // Digest uses: each node reads its children; the root row reads the root.
    var uses = std.AutoHashMap(u32, u32).init(a);
    for (nodes) |node| {
        (try uses.getOrPutValue(node.left, 0)).value_ptr.* += 1;
        (try uses.getOrPutValue(node.right, 0)).value_ptr.* += 1;
    }
    (try uses.getOrPutValue(rootId(nodes), 0)).value_ptr.* += 1;
    for (meta.items) |*m| if (m.dbl) {
        m.ym = uses.get(m.mid) orelse 0;
    };
    pl.compressions = try comps.toOwnedSlice(a);
    pl.meta = try meta.toOwnedSlice(a);
    return if (nodes.len == 0) pl.digests[1] else nd[nodes.len - 1];
}

/// The root row reads the header's Merkle field as the header message's words 9..16.
pub fn addHeaderUses(msg_cols: [][]M31) void {
    for (0..8) |w| msg_cols[msg.WM][39 + 4 * w] = msg_cols[msg.WM][39 + 4 * w].add(M31.one());
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

/// Main columns in `2^log_size` rows.
pub fn generate(a: std.mem.Allocator, log_size: u32, ntx: u32, nodes: []const Node, root: spec.State) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (nodes.len + 2 > n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    const one = M31.one();
    for (0..n) |r| {
        cols[RIX][r] = f(r);
        if (r < nodes.len) {
            const nd = nodes[r];
            cols[ACTN][r] = one;
            if (nd.first) cols[FIRSTL][r] = one;
            cols[I][r] = f(nd.i);
            cols[CNT][r] = f(nd.cnt);
            cols[PCNT][r] = f(nd.pcnt);
            if (nd.pcnt % 2 == 1) cols[ODD][r] = one;
            cols[BASE][r] = f(nd.base);
            cols[PBASE][r] = f(nd.pbase);
            if (nd.l1) cols[L1][r] = one;
            cols[PINV][r] = try f(nd.pcnt).sub(one).inv();
            cols[NM][r] = one;
            cols[MMC][r] = one;
        } else if (r == nodes.len) {
            cols[RT][r] = one;
            cols[RIDC][r] = f(rootId(nodes));
            for (root, 0..) |w, k| {
                cols[RL0 + 2 * k][r] = f(w & 0xffff);
                cols[RL0 + 2 * k + 1][r] = f(w >> 16);
            }
        }
        if (r == 0) {
            // Level 1 starts at row 0 (also when row 0 is the root row).
            cols[FIRSTL][r] = one;
            cols[L1][r] = one;
            cols[PCNT][r] = f(ntx);
        }
        // Is-zero flags, the root node, duplicates and children (on every row).
        const e = cols[I][r].sub(cols[CNT][r]).add(one);
        if (e.eql(M31.zero())) cols[LAST][r] = one else cols[LINV][r] = try e.inv();
        const g = cols[CNT][r].sub(one);
        if (g.eql(M31.zero())) cols[C1][r] = one else cols[C1INV][r] = try g.inv();
        cols[RN][r] = cols[LAST][r].mul(cols[C1][r]);
        cols[DUP][r] = cols[ODD][r].mul(cols[LAST][r]);
        const l1 = cols[L1][r];
        cols[LEFT][r] = l1.mul(f(4).mul(cols[I][r]).add(one)).add(one.sub(l1).mul(f(NB).add(cols[PBASE][r]).add(f(2).mul(cols[I][r]))));
        cols[RIGHT][r] = cols[LEFT][r].add(one.sub(cols[DUP][r]).mul(l1.add(one)));
        cols[NF][r] = cols[ACTN][r].mul(one.sub(cols[FIRSTL][r]));
        cols[FS][r] = cols[ACTN][r].mul(cols[FIRSTL][r]);
    }
    return cols;
}

test "block merkle: (bytes, fields, msg, sha, merkle) prove for small blocks; tampering is rejected" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    const bytes = @import("bytes.zig");
    const fields = @import("fields.zig");
    const shaw = @import("../sha256/witness.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const merkle_air = (try ir.Air.parseJson(a, json)).value;
    const sha_air = (try ir.Air.parseJson(a, bsha.json)).value;
    const msg_air = (try ir.Air.parseJson(a, msg.json)).value;
    const fields_air = (try ir.Air.parseJson(a, fields.json)).value;
    const bytes_air = (try ir.Air.parseJson(a, bytes.json)).value;
    const samples = [_][]const u8{ @embedFile("testdata:block_0"), @embedFile("testdata:block_170"), @embedFile("testdata:block_91812") };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const ntx: u32 = @intCast(rows[0].val);
        const txs = try msg.txRanges(a, rows);
        const msgs = try msg.messages(a, txs);
        var pl = try bsha.plan(a, raw, msgs);
        const nodes = try tree(a, ntx);
        const root = try extendPlan(a, &pl, nodes);
        try std.testing.expectEqualSlices(u8, raw[36..68], &bsha.digestBytes(root));
        const need = @max(msg.rowsNeeded(msgs), raw.len + 1, rows.len + 1, (pl.compressions.len + 1) * shaw.PERIOD, nodes.len + 2);
        const log_size: u32 = std.math.log2_int_ceil(usize, need);
        const pubs = [_]M31{ f(raw.len), f(ntx) };
        var reads = std.ArrayList(u32).empty;
        const mm = try msg.generate(a, log_size, raw, msgs, &reads);
        msg.setUses(mm);
        addHeaderUses(mm);
        const sm = try bsha.generate(a, log_size, pl);
        const km = try generate(a, log_size, ntx, nodes, root);
        // Each AIR on its own first (clear failures).
        inline for (.{ .{ sha_air, sm, "sha" }, .{ merkle_air, km, "merkle" } }) |t| {
            const tr = interp.RowTrace{ .log_size = log_size, .pubs = &pubs, .preprocessed = @ptrCast(try t[0].genPreprocessed(a, log_size)), .main = @ptrCast(t[1]) };
            if (try interp.firstViolation(a, t[0], tr)) |v| {
                std.debug.print("block of {d} bytes: {s} row {d} violates constraint {d}\n", .{ raw.len, t[2], v.row, v.constraint });
                return error.TestUnexpectedResult;
            }
        }
        const fm = try fields.generate(a, log_size, raw, rows);
        fields.setTxUses(fm, rows, 2);
        try reads.appendSlice(a, try fields.reads(a, rows));
        const bm = try bytes.generate(a, log_size, raw, reads.items);
        const parts = [_]system.Part{
            .{ .air = &bytes_air, .log_size = log_size, .pubs = pubs[0..1] },
            .{ .air = &fields_air, .log_size = log_size, .pubs = &pubs },
            .{ .air = &msg_air, .log_size = log_size },
            .{ .air = &sha_air, .log_size = log_size },
            .{ .air = &merkle_air, .log_size = log_size, .pubs = &pubs },
        };
        const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
        const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(fm), @ptrCast(mm), @ptrCast(sm), @ptrCast(km) };
        try system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains));
        std.debug.print("block of {d} bytes, {d} txs: {d} nodes, {d} compressions, log {d}: proved and verified\n", .{ raw.len, ntx, nodes.len, pl.compressions.len, log_size });
        // A wrong root limb in the Merkle row: the header words no longer match.
        if (nodes.len > 0) {
            const km2 = try a.alloc([]M31, km.len);
            for (km2, km) |*d, s| d.* = try a.dupe(M31, s);
            km2[RL0][nodes.len] = km2[RL0][nodes.len].add(M31.one());
            const mains2 = [_][]const []const M31{ @ptrCast(bm), @ptrCast(fm), @ptrCast(mm), @ptrCast(sm), @ptrCast(km2) };
            try std.testing.expectError(error.LookupsUnbalanced, system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains2)));
        }
    }
}

test "block merkle: large segwit samples satisfy the SHA and Merkle AIRs (run with ReleaseFast)" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const fields = @import("fields.zig");
    const shaw = @import("../sha256/witness.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const merkle_air = (try ir.Air.parseJson(a, json)).value;
    const sha_air = (try ir.Air.parseJson(a, bsha.json)).value;
    const samples = [_][]const u8{ @embedFile("testdata:block_481824"), @embedFile("testdata:block_709632") };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const ntx: u32 = @intCast(rows[0].val);
        const msgs = try msg.messages(a, try msg.txRanges(a, rows));
        var pl = try bsha.plan(a, raw, msgs);
        const nodes = try tree(a, ntx);
        const root = try extendPlan(a, &pl, nodes);
        try std.testing.expectEqualSlices(u8, raw[36..68], &bsha.digestBytes(root));
        const pubs = [_]M31{ f(raw.len), f(ntx) };
        const ls: u32 = std.math.log2_int_ceil(usize, (pl.compressions.len + 1) * shaw.PERIOD);
        const lm: u32 = std.math.log2_int_ceil(usize, nodes.len + 2);
        const sm = try bsha.generate(a, ls, pl);
        const km = try generate(a, lm, ntx, nodes, root);
        inline for (.{ .{ sha_air, sm, "sha", ls }, .{ merkle_air, km, "merkle", lm } }) |t| {
            const tr = interp.RowTrace{ .log_size = t[3], .pubs = &pubs, .preprocessed = @ptrCast(try t[0].genPreprocessed(a, t[3])), .main = @ptrCast(t[1]) };
            if (try interp.firstViolation(a, t[0], tr)) |v| {
                std.debug.print("block of {d} bytes: {s} row {d} violates constraint {d}\n", .{ raw.len, t[2], v.row, v.constraint });
                return error.TestUnexpectedResult;
            }
        }
        std.debug.print("block of {d} bytes, {d} txs: {d} nodes, {d} compressions: SHA and Merkle constraints hold\n", .{ raw.len, ntx, nodes.len, pl.compressions.len });
    }
}

test "block merkle: a duplicated transaction (CVE-2012-2459) is rejected by the mutation check" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const fields = @import("fields.zig");
    const shaw = @import("../sha256/witness.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const sha_air = (try ir.Air.parseJson(a, bsha.json)).value;
    // Block 0's coinbase twice; the header carries the (mutated) tree's root.
    const b0 = @embedFile("testdata:block_0");
    const tx = b0[81..];
    var raw = std.ArrayList(u8).empty;
    try raw.appendSlice(a, b0[0..80]);
    try raw.append(a, 2);
    try raw.appendSlice(a, tx);
    try raw.appendSlice(a, tx);
    const rows = try fields.tokenize(a, raw.items);
    const msgs = try msg.messages(a, try msg.txRanges(a, rows));
    var pl0 = try bsha.plan(a, raw.items, msgs);
    const nodes = try tree(a, 2);
    const root = try extendPlan(a, &pl0, nodes);
    @memcpy(raw.items[36..68], &bsha.digestBytes(root));
    // Re-plan with the patched header (its hash changed); the root is unchanged.
    var pl = try bsha.plan(a, raw.items, msgs);
    _ = try extendPlan(a, &pl, nodes);
    const ls: u32 = std.math.log2_int_ceil(usize, (pl.compressions.len + 1) * shaw.PERIOD);
    const sm = try bsha.generate(a, ls, pl);
    const tr = interp.RowTrace{ .log_size = ls, .preprocessed = @ptrCast(try sha_air.genPreprocessed(a, ls)), .main = @ptrCast(sm) };
    const v = (try interp.firstViolation(a, sha_air, tr)) orelse return error.TestUnexpectedResult;
    // The node block is the period after the messages; its row 19 holds the check.
    const node_period = pl.meta.len - 3;
    try std.testing.expectEqual(node_period * shaw.PERIOD + 19, v.row);
}
