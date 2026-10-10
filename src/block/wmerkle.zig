//! Witness tree and commitment node (M3a.5e, D-035): the witness for the `block_wmerkle` component
//! (Lean: `Block/WMerkle.lean`). The txid tree's layout over `[0^32, wtxid(tx 1), …]`, then the
//! commitment row hashing the root with the coinbase nonce.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const spec = @import("../sha256/spec.zig");
const bsha = @import("sha.zig");
const merkle = @import("merkle.zig");
const ctxw = @import("ctx.zig");

pub const json = @embedFile("air:block_wmerkle");
pub const N_MAIN = 27;
pub const NBW: u32 = (1 << 27) + (1 << 26);

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
const WON = 25;
const LRAW = 26;

/// The internal nodes over `ntx` witness leaves (leaf 0 `ZERO_ID`, leaf `j ≥ 1` the wtxid message
/// `2 + 2j`), level by level.
pub fn tree(a: std.mem.Allocator, ntx: u32) ![]merkle.Node {
    var out = std.ArrayList(merkle.Node).empty;
    var pcnt = ntx;
    var pbase: u32 = 0;
    var l1 = true;
    while (pcnt > 1) {
        const cnt = (pcnt + 1) / 2;
        const base: u32 = @intCast(out.items.len);
        for (0..cnt) |ii| {
            const i: u32 = @intCast(ii);
            const dup = 2 * i + 1 == pcnt;
            const raw_left: u32 = if (l1) 2 + 4 * i else NBW + pbase + 2 * i;
            const left: u32 = if (l1 and i == 0) ctxw.ZERO_ID else raw_left;
            const right: u32 = if (dup) left else raw_left + @as(u32, if (l1) 2 else 1);
            try out.append(a, .{ .id = NBW + base + i, .left = left, .right = right, .dup = dup, .first = i == 0, .i = i, .cnt = cnt, .pcnt = pcnt, .base = base, .pbase = pbase, .l1 = l1 });
        }
        pbase = base;
        pcnt = cnt;
        l1 = false;
    }
    return out.toOwnedSlice(a);
}

pub fn rootId(nodes: []const merkle.Node) u32 {
    return if (nodes.len == 0) ctxw.ZERO_ID else nodes[nodes.len - 1].id;
}

/// The commitment node's id: the row after the tree's nodes.
pub fn commitId(nodes: []const merkle.Node) u32 {
    return NBW + @as(u32, @intCast(nodes.len));
}

fn stateOfBytes(b: [32]u8) spec.State {
    var s: spec.State = undefined;
    for (&s, 0..) |*w, i| w.* = std.mem.readInt(u32, b[4 * i ..][0..4], .big);
    return s;
}

/// Appends the witness tree's nodes and the commitment node to the plan (as `merkle.extendPlan`) and
/// adds their digest uses to the yields. Returns the commitment node's digest.
pub fn extendPlan(a: std.mem.Allocator, pl: *bsha.Plan, nodes: []const merkle.Node, nonce: [32]u8) !spec.State {
    var comps = std.ArrayList(@import("../sha256/witness.zig").Compression).empty;
    try comps.appendSlice(a, pl.compressions);
    var meta = std.ArrayList(bsha.Meta).empty;
    try meta.appendSlice(a, pl.meta);
    const nd = try a.alloc(spec.State, nodes.len + 1);
    const zero = [_]u32{0} ** 8;
    const nonce_s = stateOfBytes(nonce);
    var all = std.ArrayList(merkle.Node).empty;
    try all.appendSlice(a, nodes);
    try all.append(a, .{ .id = commitId(nodes), .left = rootId(nodes), .right = ctxw.NONCE_ID, .dup = true, .first = false, .i = 0, .cnt = 0, .pcnt = 0, .base = 0, .pbase = 0, .l1 = false });
    const Of = struct {
        msgd: []const spec.State,
        nd: []const spec.State,
        zero: spec.State,
        nonce: spec.State,
        fn of(c: @This(), id: u32) spec.State {
            if (id == ctxw.ZERO_ID) return c.zero;
            if (id == ctxw.NONCE_ID) return c.nonce;
            return if (id >= NBW) c.nd[id - NBW] else c.msgd[id];
        }
    };
    var uses = std.AutoHashMap(u32, u32).init(a);
    for (all.items, 0..) |node, k| {
        const o = Of{ .msgd = pl.digests, .nd = nd, .zero = zero, .nonce = nonce_s };
        var block: spec.Block = undefined;
        @memcpy(block[0..8], &o.of(node.left));
        @memcpy(block[8..16], &o.of(node.right));
        (try uses.getOrPutValue(node.left, 0)).value_ptr.* += 1;
        (try uses.getOrPutValue(node.right, 0)).value_ptr.* += 1;
        // Every witness-tree node skips the mutation check (tuple entry 4 is 1).
        try comps.append(a, .{ .input = spec.IV, .block = block });
        try meta.append(a, .{ .mid = node.id, .blk = 0, .fst = false, .dbl = false, .node = true, .lid = node.left, .rid = node.right, .dup = true });
        const h1 = spec.compress(spec.IV, block);
        var npad: spec.Block = [_]u32{0} ** 16;
        npad[0] = 0x80000000;
        npad[15] = 512;
        try comps.append(a, .{ .input = h1, .block = npad });
        try meta.append(a, .{ .mid = node.id, .blk = 1, .fst = false, .dbl = false, .npad = true, .lid = node.left, .rid = node.right, .dup = true });
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
    // The context component reads the commitment node's digest.
    (try uses.getOrPutValue(commitId(nodes), 0)).value_ptr.* += 1;
    for (meta.items) |*m| if (m.dbl) {
        if (uses.get(m.mid)) |u| m.ym += u;
    };
    pl.compressions = try comps.toOwnedSlice(a);
    pl.meta = try meta.toOwnedSlice(a);
    return nd[nodes.len];
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

/// Main columns in `2^log_size` rows; all inactive (`won` false) when there is no commitment.
pub fn generate(a: std.mem.Allocator, log_size: u32, ntx: u32, nodes: []const merkle.Node, won: bool) ![][]M31 {
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
        if (won) cols[WON][r] = one;
        if (won and r < nodes.len) {
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
        } else if (won and r == nodes.len) {
            cols[RT][r] = one;
            cols[RIDC][r] = f(rootId(nodes));
            cols[NM][r] = one;
            cols[MMC][r] = one;
        }
        if (r == 0) {
            cols[FIRSTL][r] = one;
            cols[L1][r] = one;
            cols[PCNT][r] = f(ntx);
        }
        const e = cols[I][r].sub(cols[CNT][r]).add(one);
        if (e.eql(M31.zero())) cols[LAST][r] = one else cols[LINV][r] = try e.inv();
        const g = cols[CNT][r].sub(one);
        if (g.eql(M31.zero())) cols[C1][r] = one else cols[C1INV][r] = try g.inv();
        cols[RN][r] = cols[LAST][r].mul(cols[C1][r]);
        cols[DUP][r] = cols[ODD][r].mul(cols[LAST][r]);
        const l1 = cols[L1][r];
        cols[LRAW][r] = l1.mul(f(4).mul(cols[I][r]).add(f(2))).add(one.sub(l1).mul(f(NBW).add(cols[PBASE][r]).add(f(2).mul(cols[I][r]))));
        if (cols[RT][r].eql(one)) {
            cols[LEFT][r] = cols[RIDC][r];
            cols[RIGHT][r] = f(ctxw.NONCE_ID);
        } else {
            const zfix = if (r == 0) f(ctxw.ZERO_ID - 2) else M31.zero();
            cols[LEFT][r] = cols[LRAW][r].add(zfix);
            cols[RIGHT][r] = cols[LRAW][r].add(one.sub(cols[DUP][r]).mul(l1.add(one)));
        }
        cols[NF][r] = cols[ACTN][r].mul(one.sub(cols[FIRSTL][r]));
        cols[FS][r] = cols[ACTN][r].mul(cols[FIRSTL][r]);
    }
    return cols;
}
