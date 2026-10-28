//! The coin-set pass segment system (docs/design/set-pass.md § The segment system; Lean:
//! `lean/StarkedAir/SetPass/`): witnesses for one segment of a set file, a run of whole records, from
//! the carried state before it. Components in proof order: `block_bytes` (the segment's bytes),
//! `block_tables`, `set_pend`, `set_rec`, `block_fpwalk`, `set_b2w`, `set_b2c`, `set_tmsg`,
//! `set_shac`. `build` also returns the state after the segment, which `set_pass.zig`'s native model
//! cross-checks.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const QM31 = @import("stwo_core").fields.qm31.QM31;
const ir = @import("../air/ir.zig");
const system = @import("../air/system.zig");
const bytes = @import("bytes.zig");
const checks = @import("checks.zig");
const coin = @import("coin.zig");
const commit = @import("commit.zig");
const b2 = @import("../hash/blake2s_air.zig");
const shaw = @import("../sha256/witness.zig");
const shs = @import("../sha256/spec.zig");

pub const N_COMP = 12;
pub const jsons = [N_COMP][]const u8{ bytes.json, checks.tables_json, @embedFile("air:set_pend"), @embedFile("air:set_rec"), coin.fpwalk_json, @embedFile("air:set_b2w"), @embedFile("air:set_b2c"), @embedFile("air:set_tmsg"), @embedFile("air:set_shac"), @embedFile("air:set_lw"), @embedFile("air:set_lc"), @embedFile("air:set_mt") };
pub const names = [N_COMP][]const u8{ "bytes", "tables", "pend", "rec", "fpwalk", "b2w", "b2c", "tmsg", "shac", "lw", "lc", "mt" };
pub const C = struct {
    pub const bytes = 0;
    pub const tables = 1;
    pub const pend = 2;
    pub const rec = 3;
    pub const fpwalk = 4;
    pub const b2w = 5;
    pub const b2c = 6;
    pub const tmsg = 7;
    pub const shac = 8;
    pub const lw = 9;
    pub const lc = 10;
    pub const mt = 11;
};

/// Public inputs (Lean `SetPass/Layout.lean`).
pub const N_PUB = 567;
pub const PUB_LEN = 0;
pub const PUB_I_IN = 1;
pub const PUB_I_OUT = 2;
pub const PUB_HASLAST = 3;
pub const PUB_LAST_IN = 4;
pub const PUB_MAXH_IN = 40;
pub const PUB_G = 41;
pub const PUB_Z = 45;
pub const PUB_ALPHA = 49;
pub const PUB_SUM_IN = 153;
pub const PUB_SUM_OUT = 157;
pub const PUB_MAXH_OUT = 161;
pub const PUB_AMT_IN = 162;
pub const PUB_AMT_OUT = 174;
pub const PUB_LAST_OUT = 186;
pub const B2_IN = 222;
pub const B2_OUT = 304;
pub const SHA_IN = 386;
pub const SHA_OUT = 468;
/// The segment's Merkle root (16 limbs) and the tree's half width (D-050).
pub const PUB_ROOT = 550;
pub const PUB_HALF = 566;

const REL_PB2I = 26;
const REL_PB2O = 27;
const REL_PSHI = 28;
const REL_PSHO = 29;

/// A record's fixed part.
pub const HEAD = 49;
/// The largest height and `ser` length the circuit accepts (`set_rec`).
pub const MAX_HEIGHT: u32 = 1 << 24;
pub const MAX_LEN: u32 = 1 << 24;

/// A streamed hash: chaining value, blocks compressed, pending bytes.
pub const HashSt = struct {
    h: [8]u32,
    nb: u32 = 0,
    plen: u8 = 0,
    pend: [64]u8 = @splat(0),

    fn pendSlice(self: *const HashSt) []const u8 {
        return self.pend[0..self.plen];
    }
};

/// The carried state (Lean `SetFile.St`, with `t = 64·nb` and `len = 64·nb + plen`; `n` and `ok` are the
/// verifier's).
pub const State = struct {
    i: u32 = 0,
    last: ?[36]u8 = null,
    max_h: u32 = 0,
    sum: QM31 = QM31.zero(),
    amount: u128 = 0,
    b2: HashSt,
    sha: HashSt,
};

/// The pass's start (`SetFile.begin`): the file's count bytes are Blake2s's pending bytes.
pub fn begin(count: [4]u8) State {
    var st: State = .{ .b2 = .{ .h = commit.H0 }, .sha = .{ .h = shs.IV } };
    st.b2.plen = 4;
    @memcpy(st.b2.pend[0..4], &count);
    return st;
}

/// The pass's end (`SetFile.finish`, the hashes): Blake2s's last block, SHA-256's padding, SHA256d
/// reversed.
pub fn finish(st: State) struct { digest: [32]u8, hash: [32]u8 } {
    var blk: [64]u8 = @splat(0);
    @memcpy(blk[0..st.b2.plen], st.b2.pendSlice());
    var m: [16]u32 = undefined;
    for (0..16) |k| m[k] = std.mem.readInt(u32, blk[4 * k ..][0..4], .little);
    const h = b2.compress(.{ .h = st.b2.h, .m = m, .t = 64 * @as(u64, st.b2.nb) + st.b2.plen, .f = true });
    var digest: [32]u8 = undefined;
    for (0..8) |w| std.mem.writeInt(u32, digest[4 * w ..][0..4], h[w], .little);
    // SHA-256: the pending bytes, 0x80, zeros, the bit length.
    const len: u64 = 64 * @as(u64, st.sha.nb) + st.sha.plen;
    var tail: [128]u8 = @splat(0);
    @memcpy(tail[0..st.sha.plen], st.sha.pendSlice());
    tail[st.sha.plen] = 0x80;
    const tl: usize = if (st.sha.plen < 56) 64 else 128;
    std.mem.writeInt(u64, tail[tl - 8 ..][0..8], 8 * len, .big);
    var H = st.sha.h;
    var off: usize = 0;
    while (off < tl) : (off += 64) H = shs.compress(H, shs.blockFromBytes(tail[off..][0..64]));
    const h1 = shs.stateToBytes(H);
    var hash: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(&h1, &hash, .{});
    std.mem.reverse(u8, &hash);
    return .{ .digest = digest, .hash = hash };
}

/// A parsed record of the segment.
pub const Rec = struct {
    start: u32,
    head: *const [HEAD]u8,
    ser: []const u8,

    fn height(r: Rec) u32 {
        return std.mem.readInt(u32, r.head[36..40], .little);
    }
    fn cb(r: Rec) u8 {
        return r.head[40];
    }
    fn code(r: Rec) u32 {
        return 2 * r.height() + r.cb();
    }
    fn key(r: Rec) [36]u8 {
        var k: [36]u8 = undefined;
        @memcpy(k[0..32], r.head[0..32]);
        for (0..4) |i| k[32 + i] = r.head[35 - i];
        return k;
    }
};

/// The segment's records, checked as `set_rec` checks them.
pub fn parse(a: std.mem.Allocator, seg: []const u8) ![]Rec {
    var out: std.ArrayList(Rec) = .empty;
    var at: usize = 0;
    while (at < seg.len) {
        if (seg.len - at < HEAD) return error.EndOfStream;
        const head = seg[at..][0..HEAD];
        const l = std.mem.readInt(u32, head[45..49], .little);
        if (l < 8 or l >= MAX_LEN) return error.CoinOutOfRange;
        if (head[40] > 1) return error.BadCoinbaseFlag;
        if (std.mem.readInt(u32, head[36..40], .little) >= MAX_HEIGHT) return error.CoinOutOfRange;
        if (seg.len - at - HEAD < l) return error.EndOfStream;
        try out.append(a, .{ .start = @intCast(at), .head = head, .ser = seg[at + HEAD ..][0..l] });
        at += HEAD + l;
    }
    if (out.items.len == 0) return error.EmptySegment;
    if (seg.len >= MAX_LEN) return error.SegmentTooLong;
    return out.items;
}

/// The `TxOutSer` bytes of a record.
fn txOutSer(a: std.mem.Allocator, r: Rec) ![]u8 {
    const out = try a.alloc(u8, 40 + r.ser.len);
    @memcpy(out[0..36], r.head[0..36]);
    std.mem.writeInt(u32, out[36..40], r.code(), .little);
    @memcpy(out[40..], r.ser);
    return out;
}

pub const Built = struct {
    logs: [N_COMP]u32,
    /// The segment's Merkle root (D-050).
    root: [8]u32 = @splat(0),
    pubs: [N_PUB]M31,
    mains: [N_COMP][][]M31,
    out: State,
    recs: usize,
};

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

fn invOrZero(x: M31) M31 {
    return x.inv() catch M31.zero();
}

fn zeros(a: std.mem.Allocator, n_cols: usize, n: usize) ![][]M31 {
    const cols = try a.alloc([]M31, n_cols);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    return cols;
}

fn setQ(cols: [][]M31, base: usize, r: usize, x: QM31) void {
    for (x.toM31Array(), 0..) |v, j| cols[base + j][r] = v;
}

fn logFor(rows: usize, min: u32) u32 {
    return @max(min, std.math.log2_int_ceil(usize, @max(rows, 2)));
}

fn setHash(pubs: *[N_PUB]M31, base: usize, s: HashSt) void {
    for (0..8) |w| {
        pubs[base + 2 * w] = f(s.h[w] & 0xffff);
        pubs[base + 2 * w + 1] = f(s.h[w] >> 16);
    }
    pubs[base + 16] = f(s.nb);
    pubs[base + 17] = f(s.plen);
    for (0..64) |j| pubs[base + 18 + j] = f(s.pend[j]);
}

/// The challenge and the incoming state `in` as public inputs (everything else zero).
pub fn statePubsIn(pubs: *[N_PUB]M31, ch: coin.Challenge, in: State) void {
    @memset(pubs, M31.zero());
    pubs[PUB_I_IN] = f(in.i);
    if (in.last) |k| {
        pubs[PUB_HASLAST] = M31.one();
        for (0..36) |j| pubs[PUB_LAST_IN + j] = f(k[j]);
    }
    pubs[PUB_MAXH_IN] = f(in.max_h);
    for (ch.gamma.toM31Array(), 0..) |v, j| pubs[PUB_G + j] = v;
    for (ch.z.toM31Array(), 0..) |v, j| pubs[PUB_Z + j] = v;
    for (ch.alpha, 0..) |al, i| for (al.toM31Array(), 0..) |v, j| {
        pubs[PUB_ALPHA + 4 * i + j] = v;
    };
    for (in.sum.toM31Array(), 0..) |v, j| pubs[PUB_SUM_IN + j] = v;
    for (0..12) |j| pubs[PUB_AMT_IN + j] = f(@as(u8, @truncate(in.amount >> @intCast(8 * j))));
    setHash(pubs, B2_IN, in.b2);
    setHash(pubs, SHA_IN, in.sha);
}

fn setPubs(pubs: *[N_PUB]M31, len: usize, ch: coin.Challenge, in: State, out: State) void {
    statePubsIn(pubs, ch, in);
    pubs[PUB_LEN] = f(len);
    pubs[PUB_I_OUT] = f(out.i);
    for (out.sum.toM31Array(), 0..) |v, j| pubs[PUB_SUM_OUT + j] = v;
    pubs[PUB_MAXH_OUT] = f(out.max_h);
    for (0..12) |j| pubs[PUB_AMT_OUT + j] = f(@as(u8, @truncate(out.amount >> @intCast(8 * j))));
    for (0..36) |j| pubs[PUB_LAST_OUT + j] = f(out.last.?[j]);
    setHash(pubs, B2_OUT, out.b2);
    setHash(pubs, SHA_OUT, out.sha);
}

/// Pending-table reads (`set_pend`'s multiplicities), per table and index.
const PendReads = [4][64]u32;

/// The witnesses of one segment `seg` (whole records) from state `in`.
pub fn build(a: std.mem.Allocator, ch: coin.Challenge, in: State, seg: []const u8) !Built {
    return buildAt(a, ch, in, seg, null);
}

/// The component logs a segment needs (each at its floor or above), from its byte length, record
/// count, `ser` bytes and the incoming pending lengths.
pub fn minLogs(seg_len: usize, n_recs: usize, ser_len: usize, b2p: usize, shap: usize, leaf_blocks: usize) [N_COMP]u32 {
    const xs = b2p + seg_len;
    const m_b2 = if (xs > 64) (xs + 63) / 64 - 1 else 0;
    const ys = shap + 40 * n_recs + ser_len;
    const m_sha = ys / 64;
    const rec_log = logFor(n_recs + 1, 6);
    return .{
        logFor(seg_len, 6),
        8,
        6,
        logFor(n_recs + 1, 6),
        logFor(ser_len + 1, 6),
        logFor(16 * (m_b2 + 1) + 1, 6),
        logFor(b2.PERIOD * m_b2, 8),
        logFor(ys + 1, 6),
        logFor(shaw.PERIOD * m_sha, 8),
        logFor(16 * leaf_blocks + 1, 6),
        logFor(b2.PERIOD * leaf_blocks, 8),
        treeLog(rec_log),
    };
}

/// A record's Merkle leaf message length (`key(r − 1) ‖ record`) and blocks.
pub fn leafLen(ser_len: usize) usize {
    return 36 + HEAD + ser_len;
}
pub fn leafBlocks(ser_len: usize) usize {
    return (leafLen(ser_len) + 63) / 64;
}

/// The tree component's log for a segment whose records fit `2^rec_log` slots (`HALF = 2^(rec_log − 1)`).
pub fn treeLog(rec_log: u32) u32 {
    return logFor(b2.PERIOD * ((@as(usize, 1) << @intCast(rec_log)) - 1), 8);
}

fn fitsIn(need: [N_COMP]u32, logs: [N_COMP]u32) bool {
    for (need, logs) |n, l| if (n > l) return false;
    return true;
}

/// Cuts a set file's records into segments that fit `logs` (with full pending buffers, so whatever the
/// incoming state): greedy, each segment as long as fits. Returns each segment's end offset.
pub fn cut(a: std.mem.Allocator, file: []const u8, logs: [N_COMP]u32) ![]usize {
    var ends: std.ArrayList(usize) = .empty;
    var at: usize = 4;
    while (at < file.len) {
        var end = at;
        var n: usize = 0;
        var ser: usize = 0;
        var lb: usize = 0;
        while (end < file.len) {
            if (file.len - end < HEAD) return error.Truncated;
            const l = std.mem.readInt(u32, file[end + 45 ..][0..4], .little);
            const next = end + HEAD + l;
            if (next > file.len) return error.Truncated;
            if (!fitsIn(minLogs(next - at, n + 1, ser + l, 64, 63, lb + leafBlocks(l)), logs)) break;
            end = next;
            n += 1;
            ser += l;
            lb += leafBlocks(l);
        }
        if (n == 0) return error.RecordTooLarge;
        try ends.append(a, end);
        at = end;
    }
    return ends.toOwnedSlice(a);
}

/// `build` at fixed component logs `fixed` (a pass's leaves share one shape), when given: the segment
/// must fit them.
pub fn buildAt(a: std.mem.Allocator, ch: coin.Challenge, in: State, seg: []const u8, fixed: ?[N_COMP]u32) !Built {
    const recs = try parse(a, seg);
    var out = in;
    var reads: std.ArrayList(u32) = .empty;
    var ranges: std.ArrayList(u32) = .empty;
    var pend_reads: PendReads = @splat(@splat(0));
    var b: Built = undefined;
    b.recs = recs.len;

    // The TxOutSer stream and the native state after the segment.
    var tos: std.ArrayList(u8) = .empty;
    for (recs) |r| try tos.appendSlice(a, try txOutSer(a, r));
    var fracs = try a.alloc(QM31, recs.len);
    for (recs, 0..) |r, i| {
        const k = r.key();
        if (out.last) |p| if (std.mem.order(u8, &p, &k) != .lt) return error.SetNotSorted;
        out.last = k;
        fracs[i] = try coin.coinFrac(ch, r.head[0..32].*, std.mem.readInt(u32, r.head[32..36], .little), r.height(), r.cb() == 1, r.ser, std.mem.readInt(u32, r.head[41..45], .little));
        out.sum = out.sum.add(fracs[i]);
        out.amount += std.mem.readInt(u64, r.ser[0..8], .little);
        out.max_h = @max(out.max_h, r.height());
    }
    out.i = in.i + @as(u32, @intCast(recs.len));
    if (out.amount >= @as(u128, 1) << 96) return error.AmountOverflow;

    // Blake2s over P_in ‖ seg: every block but the last compressed.
    const xs = try std.mem.concat(a, u8, &.{ in.b2.pendSlice(), seg });
    if (xs.len <= 64) return error.SegmentTooShort;
    const m_b2 = (xs.len + 63) / 64 - 1;
    const b2_blocks = try a.alloc([16]u32, m_b2);
    const b2_hs = try a.alloc([8]u32, m_b2);
    {
        var h = in.b2.h;
        for (0..m_b2) |blk| {
            for (0..16) |k| b2_blocks[blk][k] = std.mem.readInt(u32, xs[64 * blk + 4 * k ..][0..4], .little);
            h = b2.compress(.{ .h = h, .m = b2_blocks[blk], .t = 64 * (@as(u64, in.b2.nb) + blk + 1), .f = false });
            b2_hs[blk] = h;
        }
        out.b2 = .{ .h = h, .nb = in.b2.nb + @as(u32, @intCast(m_b2)), .plen = @intCast(xs.len - 64 * m_b2) };
        @memcpy(out.b2.pend[0..out.b2.plen], xs[64 * m_b2 ..]);
    }
    // SHA-256 over Q_in ‖ TxOutSer: every whole block compressed.
    const ys = try std.mem.concat(a, u8, &.{ in.sha.pendSlice(), tos.items });
    const m_sha = ys.len / 64;
    if (m_sha == 0) return error.SegmentTooShort;
    const sha_comps = try a.alloc(shaw.Compression, m_sha);
    {
        var H = in.sha.h;
        for (0..m_sha) |blk| {
            sha_comps[blk] = .{ .input = H, .block = shs.blockFromBytes(ys[64 * blk ..][0..64]) };
            H = shs.compress(H, sha_comps[blk].block);
        }
        out.sha = .{ .h = H, .nb = in.sha.nb + @as(u32, @intCast(m_sha)), .plen = @intCast(ys.len - 64 * m_sha) };
        @memcpy(out.sha.pend[0..out.sha.plen], ys[64 * m_sha ..]);
    }
    setPubs(&b.pubs, seg.len, ch, in, out);

    var ser_len: usize = 0;
    for (recs) |r| ser_len += r.ser.len;
    var leaf_blocks: usize = 0;
    for (recs) |r| leaf_blocks += leafBlocks(r.ser.len);
    b.logs = minLogs(seg.len, recs.len, ser_len, in.b2.plen, in.sha.plen, leaf_blocks);
    if (fixed) |fx| {
        if (!fitsIn(b.logs, fx) or fx[C.mt] < treeLog(fx[C.rec])) return error.SegmentTooLarge;
        b.logs = fx;
    }

    b.mains[C.rec] = try recColumns(a, b.logs[C.rec], ch, in, recs, fracs, &reads, &ranges);
    var segs = try a.alloc(coin.Seg, recs.len);
    for (recs, 0..) |r, i| segs[i] = .{ .str = 0, .sid = @intCast(i), .start = r.start + HEAD, .len = @intCast(r.ser.len) };
    var no_undo: std.ArrayList(u32) = .empty;
    b.mains[C.fpwalk] = try coin.fpwalkColumns(a, b.logs[C.fpwalk], seg, &.{}, segs, ch.gamma, &reads, &no_undo);
    b.mains[C.b2w] = try b2wColumns(a, b.logs[C.b2w], in.b2, out.b2, seg.len, xs, m_b2, &reads, &pend_reads);
    b.mains[C.b2c] = try b2cColumns(a, b.logs[C.b2c], in.b2, b2_blocks, b2_hs);
    b.mains[C.tmsg] = try tmsgColumns(a, b.logs[C.tmsg], in.sha, recs, ys, m_sha, &reads, &pend_reads);
    b.mains[C.shac] = try shacColumns(a, b.logs[C.shac], sha_comps);
    // The Merkle root (D-050): leaves, the heap tree over `2·HALF` slots, its three components.
    const half: usize = @as(usize, 1) << @intCast(b.logs[C.rec] - 1);
    if (recs.len > 2 * half) return error.TooManyRecords;
    const leaves = try leafHashes(a, in, recs);
    const tree = try treeNodes(a, leaves, half);
    for (0..8) |w| {
        b.pubs[PUB_ROOT + 2 * w] = f(tree[1][w] & 0xffff);
        b.pubs[PUB_ROOT + 2 * w + 1] = f(tree[1][w] >> 16);
    }
    b.pubs[PUB_HALF] = f(half);
    b.root = tree[1];
    b.mains[C.lw] = try lwColumns(a, b.logs[C.lw], recs, leaves, &reads);
    b.mains[C.lc] = try lcColumns(a, b.logs[C.lc], leaves);
    b.mains[C.mt] = try mtColumns(a, b.logs[C.mt], leaves, tree, half, &ranges);
    b.mains[C.pend] = try pendColumns(a, b.logs[C.pend], &pend_reads);
    b.mains[C.tables] = try checks.tables(a, b.logs[C.tables], ranges.items, &.{});
    b.mains[C.bytes] = try bytes.generate(a, b.logs[C.bytes], seg, reads.items);
    b.out = out;
    return b;
}

fn pendColumns(a: std.mem.Allocator, log_size: u32, pr: *const PendReads) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 4, n);
    for (0..4) |t| for (0..64) |j| {
        cols[t][j] = f(pr[t][j]);
    };
    return cols;
}

fn recColumns(a: std.mem.Allocator, log_size: u32, ch: coin.Challenge, in: State, recs: []const Rec, fracs: []const QM31, reads: *std.ArrayList(u32), ranges: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const LST = 1;
    const IDX = 2;
    const START = 3;
    const HB = 4;
    const AB = 53;
    const LENC = 61;
    const CC = 62;
    const K = 65;
    const D = 69;
    const SB = 72;
    const FC = 75;
    const ACC = 79;
    const AM = 83;
    const AC = 94;
    const PMX = 106;
    const MX = 107;
    const GT = 108;
    const MD = 109;
    const DIFF = 112;
    const PREV = 148;
    const DELTA = 184;
    const FH = 185;
    const n = @as(usize, 1) << @intCast(log_size);
    if (recs.len + 1 > n) return error.RecordsDoNotFit;
    const cols = try zeros(a, 189, n);
    var acc = in.sum;
    var amount = in.amount;
    var mx = in.max_h;
    var prev_key: [36]u8 = if (in.last) |k| k else @splat(0);
    for (0..n) |r| {
        const on = r < recs.len;
        // The previous key: the incoming one on row 0, else the previous row's key bytes.
        for (0..36) |j| cols[PREV + j][r] = f(prev_key[j]);
        const cmp = on and (r > 0 or in.last != null);
        var key: [36]u8 = @splat(0);
        if (on) {
            const rc = recs[r];
            key = rc.key();
            cols[ON][r] = M31.one();
            cols[LST][r] = if (r + 1 == recs.len) M31.one() else M31.zero();
            cols[IDX][r] = f(r);
            cols[START][r] = f(rc.start);
            for (0..HEAD) |j| {
                cols[HB + j][r] = f(rc.head[j]);
                try reads.append(a, rc.start + @as(u32, @intCast(j)));
            }
            for (0..8) |j| {
                cols[AB + j][r] = f(rc.ser[j]);
                try reads.append(a, rc.start + HEAD + @as(u32, @intCast(j)));
            }
            const len: u32 = @intCast(rc.ser.len);
            cols[LENC][r] = f(len);
            const code = rc.code();
            var carry: u32 = rc.cb();
            for (0..4) |i| {
                const v = 2 * @as(u32, rc.head[36 + i]) + carry;
                cols[CC + i][r] = f(v & 0xff);
                carry = v >> 8;
                if (i < 3) cols[K + 1 + i][r] = f(carry);
            }
            for (0..3) |i| {
                cols[D + i][r] = f(((len - 8) >> @intCast(8 * i)) & 0xff);
                cols[SB + i][r] = f((rc.start >> @intCast(8 * i)) & 0xff);
                try ranges.append(a, (len - 8) >> @intCast(8 * i) & 0xff);
                try ranges.append(a, (rc.start >> @intCast(8 * i)) & 0xff);
                try ranges.append(a, (code >> @intCast(8 * i)) & 0xff);
            }
            setQ(cols, FC, r, fracs[r]);
            acc = acc.add(fracs[r]);
            // The amount: 12 bytes with carries.
            const add = std.mem.readInt(u64, rc.ser[0..8], .little);
            var c: u32 = 0;
            for (0..12) |j| {
                const pv: u32 = @as(u8, @truncate(amount >> @intCast(8 * j)));
                const av: u32 = if (j < 8) @as(u8, @truncate(add >> @intCast(8 * j))) else 0;
                const s = pv + av + c;
                c = s >> 8;
                if (j < 11) cols[AC + j + 1][r] = f(c);
            }
            amount += add;
            // The highest height.
            const h = rc.height();
            cols[PMX][r] = f(mx);
            const gt = h > mx;
            cols[GT][r] = if (gt) M31.one() else M31.zero();
            const md: u32 = if (gt) h - mx - 1 else mx - h;
            for (0..3) |i| {
                cols[MD + i][r] = f((md >> @intCast(8 * i)) & 0xff);
                try ranges.append(a, (md >> @intCast(8 * i)) & 0xff);
            }
            if (gt) mx = h;
            // The key comparison.
            if (cmp) {
                var d: usize = 0;
                while (d < 36 and key[d] == prev_key[d]) d += 1;
                if (d == 36 or key[d] < prev_key[d]) return error.SetNotSorted;
                cols[DIFF + d][r] = M31.one();
                cols[DELTA][r] = f(key[d] - prev_key[d] - 1);
                try ranges.append(a, key[d] - prev_key[d] - 1);
            }
            setQ(cols, FH, r, coin.horner(ch.gamma, rc.ser));
        } else {
            cols[PMX][r] = f(mx);
        }
        setQ(cols, ACC, r, acc);
        for (0..12) |j| {
            const v: u8 = @truncate(amount >> @intCast(8 * j));
            cols[AM + j][r] = f(v);
            try ranges.append(a, v);
        }
        cols[MX][r] = f(mx);
        prev_key = key;
    }
    return cols;
}

fn b2wColumns(a: std.mem.Allocator, log_size: u32, in: HashSt, out: HashSt, len: usize, xs: []const u8, m: usize, reads: *std.ArrayList(u32), pr: *PendReads) ![][]M31 {
    const ON = 0;
    const BLK = 1;
    const POS = 2;
    const B = 3;
    const A = 7;
    const N = 11;
    const HELD = 15;
    const CNT = 16;
    const PCNT = 17;
    const HINV = 18;
    const SM = 19;
    const END = 20;
    const UW = 21;
    _ = len;
    _ = out;
    const n = @as(usize, 1) << @intCast(log_size);
    const rows = 16 * (m + 1);
    if (rows + 1 > n) return error.B2DoesNotFit;
    const cols = try zeros(a, 22, n);
    const mf = f(m);
    var cnt: u32 = 0;
    var pcnt: u32 = 0;
    for (0..n) |r| {
        const kw = r % 16;
        if (kw == 0) {
            cnt = 0;
            pcnt = 0;
        }
        const on = r < rows;
        const blk: usize = if (on) r / 16 else 0;
        const held = on and blk == m;
        cols[BLK][r] = f(blk);
        cols[POS][r] = f(64 * blk + 4 * kw);
        cols[HELD][r] = if (held) M31.one() else M31.zero();
        cols[HINV][r] = invOrZero(f(blk).sub(mf));
        if (on) {
            cols[ON][r] = M31.one();
            cols[SM][r] = if (r > 0) M31.one() else M31.zero();
            cols[END][r] = if (r + 1 == rows) M31.one() else M31.zero();
            cols[UW][r] = if (held) M31.zero() else M31.one();
            for (0..4) |j| {
                const x = 64 * blk + 4 * kw + j;
                if (x >= xs.len) continue;
                cols[A + j][r] = M31.one();
                cols[B + j][r] = f(xs[x]);
                cnt += 1;
                if (x < in.plen) {
                    cols[N + j][r] = M31.one();
                    pcnt += 1;
                    pr[0][x] += 1;
                } else try reads.append(a, @intCast(x - in.plen));
                if (held) pr[1][4 * kw + j] += 1;
            }
        }
        cols[CNT][r] = f(cnt);
        cols[PCNT][r] = f(pcnt);
    }
    return cols;
}

fn b2cColumns(a: std.mem.Allocator, log_size: u32, in: HashSt, blocks: []const [16]u32, hs: []const [8]u32) ![][]M31 {
    const BLKI = 300;
    const NIL = 301;
    const LASTU = 302;
    const WLO = 303;
    const WHI = 304;
    const CHN = 305;
    const USEW = 306;
    const MU = 307;
    const LINV = 308;
    const n = @as(usize, 1) << @intCast(log_size);
    const m = blocks.len;
    if (b2.PERIOD * m > n) return error.B2DoesNotFit;
    const cols = try zeros(a, 309, n);
    var p: usize = 0;
    while (p * b2.PERIOD < n) : (p += 1) {
        const used = p < m;
        const input: b2.Input = if (used) .{ .h = if (p == 0) in.h else hs[p - 1], .m = blocks[p], .t = 64 * (@as(u64, in.nb) + p + 1), .f = false } else .{ .h = commit.H0, .m = @splat(0), .t = 0, .f = false };
        const base = p * b2.PERIOD;
        b2.fillPeriod(cols, base, n, input);
        for (0..b2.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            if (!used) {
                cols[NIL][row] = M31.one();
                continue;
            }
            cols[BLKI][row] = f(p);
            cols[LASTU][row] = if (p + 1 == m) M31.one() else M31.zero();
            cols[CHN][row] = if (p > 0) M31.one() else M31.zero();
            cols[USEW][row] = M31.one();
            cols[MU][row] = if (q < 16) M31.one() else M31.zero();
            cols[LINV][row] = invOrZero(f(p).sub(f(m - 1)));
            if (q < 16) {
                cols[WLO][row] = f(input.m[q] & 0xffff);
                cols[WHI][row] = f(input.m[q] >> 16);
            }
        }
    }
    return cols;
}

fn tmsgColumns(a: std.mem.Allocator, log_size: u32, in: HashSt, recs: []const Rec, ys: []const u8, m: usize, reads: *std.ArrayList(u32), pr: *PendReads) ![][]M31 {
    const ON = 0;
    const Y = 1;
    const B = 2;
    const PND = 3;
    const P0 = 4;
    const PC = 5;
    const PS = 6;
    const NEW = 7;
    const FR = 8;
    const ENDR = 9;
    const R = 10;
    const O = 11;
    const RST = 12;
    const RLEN = 13;
    const TAIL = 14;
    const NT = 15;
    const ENDS = 16;
    const SB = 17;
    const n = @as(usize, 1) << @intCast(log_size);
    if (ys.len + 1 > n) return error.ShaDoesNotFit;
    const cols = try zeros(a, 18, n);
    for (0..n) |r| {
        cols[Y][r] = f(r);
        cols[SB][r] = f(r / 64);
    }
    var y: usize = 0;
    while (y < in.plen) : (y += 1) {
        cols[ON][y] = M31.one();
        cols[PND][y] = M31.one();
        cols[B][y] = f(ys[y]);
        pr[2][y] += 1;
    }
    for (recs, 0..) |rc, ri| {
        const tl = 40 + rc.ser.len;
        for (0..tl) |o| {
            cols[ON][y] = M31.one();
            cols[B][y] = f(ys[y]);
            cols[R][y] = f(ri);
            cols[O][y] = f(o);
            cols[RST][y] = f(rc.start);
            cols[RLEN][y] = f(rc.ser.len);
            if (o == 0) cols[NEW][y] = M31.one();
            if (o == 0 and ri == 0) cols[FR][y] = M31.one();
            if (o + 1 == tl) cols[ENDR][y] = M31.one();
            if (o < 36) {
                cols[P0][y] = M31.one();
                try reads.append(a, rc.start + @as(u32, @intCast(o)));
            } else if (o < 40) {
                cols[PC][y] = M31.one();
            } else {
                cols[PS][y] = M31.one();
                try reads.append(a, rc.start + 9 + @as(u32, @intCast(o)));
            }
            y += 1;
        }
    }
    std.debug.assert(y == ys.len);
    for (0..ys.len) |r| {
        const tail = r >= 64 * m;
        if (tail) {
            cols[TAIL][r] = M31.one();
            pr[3][r % 64] += 1;
        } else cols[NT][r] = M31.one();
    }
    cols[ENDS][ys.len - 1] = M31.one();
    return cols;
}

fn shacColumns(a: std.mem.Allocator, log_size: u32, comps: []const shaw.Compression) ![][]M31 {
    const BLKI = 124;
    const NIL = 125;
    const LASTS = 126;
    const USEW = 127;
    const CHN = 128;
    const LINV = 129;
    const n = @as(usize, 1) << @intCast(log_size);
    const m = comps.len;
    const w = try shaw.generate(a, log_size, comps);
    const cols = try a.alloc([]M31, 130);
    for (cols[0..shaw.N_MAIN], w.main) |*c, x| c.* = x;
    for (cols[shaw.N_MAIN..]) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    for (0..n) |row| {
        const p = row / shaw.PERIOD;
        if (p >= m) {
            cols[NIL][row] = M31.one();
            continue;
        }
        cols[BLKI][row] = f(p);
        cols[LASTS][row] = if (p + 1 == m) M31.one() else M31.zero();
        cols[USEW][row] = M31.one();
        cols[CHN][row] = if (p > 0) M31.one() else M31.zero();
        cols[LINV][row] = invOrZero(f(p).sub(f(m - 1)));
    }
    return cols;
}

pub fn parseAirs(a: std.mem.Allocator) ![N_COMP]ir.Air {
    var out: [N_COMP]ir.Air = undefined;
    for (&out, jsons) |*x, j| x.* = (try ir.Air.parseJson(a, j)).value;
    return out;
}

pub fn parts(airs: *const [N_COMP]ir.Air, b: *const Built) [N_COMP]system.Part {
    var out: [N_COMP]system.Part = undefined;
    for (&out, 0..) |*p, i| p.* = .{ .air = &airs[i], .log_size = b.logs[i], .pubs = b.pubs[0..airs[i].n_pub] };
    return out;
}

/// The first violated constraint of any component, for diagnostics.
pub fn firstViolation(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !?struct { comp: usize, row: usize, constraint: usize } {
    const interp = @import("../air/interp.zig");
    for (0..N_COMP) |i| {
        const tr = interp.RowTrace{ .log_size = b.logs[i], .pubs = b.pubs[0..airs[i].n_pub], .preprocessed = @ptrCast(try airs[i].genPreprocessed(a, b.logs[i])), .main = @ptrCast(b.mains[i]) };
        if (try interp.firstViolation(a, airs[i], tr)) |v| return .{ .comp = i, .row = v.row, .constraint = v.constraint };
    }
    return null;
}

/// LogUp balance without proving, at fixed random challenges: the first unbalanced relation, or null.
pub fn unbalanced(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !?u32 {
    const interp = @import("../air/interp.zig");
    const z = QM31.fromU32Unchecked(123456789, 987654321, 192837465, 564738291);
    const alpha = QM31.fromU32Unchecked(1029384756, 1122334455, 99887766, 13572468);
    var sums = [_]QM31{QM31.zero()} ** 64;
    for (0..N_COMP) |i| {
        const air = airs[i];
        if (air.lookups.len == 0) continue;
        var t = interp.RowTrace{ .log_size = b.logs[i], .pubs = b.pubs[0..air.n_pub], .preprocessed = @ptrCast(try air.genPreprocessed(a, b.logs[i])), .main = @ptrCast(b.mains[i]) };
        const scratch = try a.alloc(M31, air.exprs.len);
        const out = try a.alloc(M31, air.constraints.len);
        const n = @as(usize, 1) << @intCast(b.logs[i]);
        for (0..n) |row| {
            t.row = row;
            interp.evalConstraints(M31, air, t.pubs, scratch, &t, out);
            for (air.lookups) |l| {
                const m = scratch[l.mult];
                if (m.isZero()) continue;
                var fp = QM31.fromBase(M31.fromCanonical(l.rel));
                var pw = alpha;
                for (l.vals) |v| {
                    fp = fp.add(pw.mulM31(scratch[v]));
                    pw = pw.mul(alpha);
                }
                sums[l.rel] = sums[l.rel].add(QM31.fromBase(m).mul(try z.sub(fp).inv()));
            }
        }
    }
    for (sums, 0..) |s, rel| if (!s.isZero()) return @intCast(rel);
    return null;
}

pub fn proveVerify(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !void {
    const rec = @import("../air/prove_rec.zig");
    const ps = parts(airs, b);
    var L: u32 = 0;
    for (b.logs) |l| L = @max(L, l);
    const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), L);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var mains: [N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    try system.verifyExt(a, cfg, &ps, &.{}, try system.prove(E, a, cfg, &ps, &mains));
}

const set_pass = @import("set_pass.zig");
const EP = @import("epoch.zig");

/// Segments of `per` records over a whole set file; checks each segment's constraints and balance
/// (and proves the first `prove` of them), and returns the facts from the chained public states.
fn runSegments(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, file: []const u8, ch: coin.Challenge, per: usize, prove: usize) !struct { digest: [32]u8, hash: [32]u8, st: State } {
    var st = begin(file[0..4].*);
    var at: usize = 4;
    const n = std.mem.readInt(u32, file[0..4], .little);
    var k: usize = 0;
    while (st.i < n) : (k += 1) {
        // `per` records from `at`.
        var end = at;
        var c: usize = 0;
        while (c < per and end < file.len) : (c += 1) end += HEAD + std.mem.readInt(u32, file[end + 45 ..][0..4], .little);
        const b = try build(a, ch, st, file[at..end]);
        if (try firstViolation(a, airs, &b)) |v| {
            std.debug.print("segment {d}: {s} row {d} violates constraint {d}\n", .{ k, names[v.comp], v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        if (try unbalanced(a, airs, &b)) |rel| {
            std.debug.print("segment {d}: relation {d} unbalanced\n", .{ k, rel });
            return error.TestUnexpectedResult;
        }
        if (k < prove) try proveVerify(a, airs, &b);
        st = b.out;
        at = end;
    }
    if (at != file.len) return error.TrailingBytes;
    const fin = finish(st);
    return .{ .digest = fin.digest, .hash = fin.hash, .st = st };
}

test "set segments: every segment of the sets after blocks 170 and 1000 satisfies and balances; the chained states give the native facts" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    const ch = EP.challenge(@splat(7));
    for ([_][]const u8{ "data/epoch/set-170.bin", "data/epoch/set-1000.bin" }, [_]usize{ 3, 40 }) |path, per| {
        const file = std.fs.cwd().readFileAlloc(a, path, 1 << 30) catch return error.SkipZigTest;
        const want = try set_pass.run(file, &.{ch}, std.math.maxInt(u32));
        const got = try runSegments(a, &airs, file, ch, per, 1);
        try std.testing.expectEqualSlices(u8, &want.digest, &got.digest);
        try std.testing.expectEqualSlices(u8, &want.hash, &got.hash);
        try std.testing.expectEqual(want.count, got.st.i);
        try std.testing.expectEqual(@as(u128, want.amount), got.st.amount);
        try std.testing.expectEqual(want.max_height, got.st.max_h);
        try std.testing.expect(want.sums[0].eql(got.st.sum));
    }
}

test "set segments: a tampered outgoing value is rejected (each carried part)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    const ch = EP.challenge(@splat(7));
    const file = std.fs.cwd().readFileAlloc(a, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    var end: usize = 4;
    for (0..3) |_| end += HEAD + std.mem.readInt(u32, file[end + 45 ..][0..4], .little);
    const b = try build(a, ch, begin(file[0..4].*), file[4..end]);
    std.debug.print("segment: {d} records, logs {any}, b2 plen {d}, sha plen {d}\n", .{ b.recs, b.logs, b.out.b2.plen, b.out.sha.plen });
    try std.testing.expect(try firstViolation(a, &airs, &b) == null);
    try std.testing.expect(try unbalanced(a, &airs, &b) == null);
    const cases = [_]usize{
        PUB_I_OUT,         PUB_SUM_OUT + 2,          PUB_MAXH_OUT,             PUB_AMT_OUT + 4,           PUB_LAST_OUT + 35,
        PUB_LAST_OUT + 3,  B2_OUT + 5,               B2_OUT + 16,              B2_OUT + 17,               B2_OUT + 18,
        SHA_OUT + 9,       SHA_OUT + 16,             SHA_OUT + 17,             SHA_OUT + 18,              PUB_LEN,
        B2_IN + 3,         SHA_IN + 12,              PUB_SUM_IN,               PUB_AMT_IN,                PUB_MAXH_IN,
        PUB_I_IN,          PUB_ROOT + 3,             PUB_ROOT + 14,            PUB_HALF,
    };
    for (cases) |i| {
        var t = b;
        t.pubs[i] = t.pubs[i].add(M31.one());
        const bad = (try firstViolation(a, &airs, &t)) != null or (try unbalanced(a, &airs, &t)) != null;
        if (!bad) std.debug.print("public input {d} tampered: not rejected\n", .{i});
        try std.testing.expect(bad);
    }
}

// ---------------------------------------------------------------------------------------------
// The Merkle root (D-050)

/// A record's Merkle leaf: its message `key(r − 1) ‖ record`, the message blocks, the chaining value
/// before each block, and the digest.
pub const Leaf = struct {
    msg: []const u8,
    blocks: []const [16]u32,
    ins: []const [8]u32,
    digest: [8]u32,
};

fn leafT(msg_len: usize, b: usize, nb: usize) u64 {
    return if (b + 1 == nb) msg_len else 64 * (@as(u64, b) + 1);
}

/// The segment's leaves, from the incoming state's last key (36 zero bytes before the set's first record).
pub fn leafHashes(a: std.mem.Allocator, in: State, recs: []const Rec) ![]Leaf {
    const out = try a.alloc(Leaf, recs.len);
    var prev: [36]u8 = in.last orelse @splat(0);
    for (recs, out) |r, *lf| {
        const msg = try a.alloc(u8, leafLen(r.ser.len));
        @memcpy(msg[0..36], &prev);
        @memcpy(msg[36..][0..HEAD], r.head);
        @memcpy(msg[36 + HEAD ..], r.ser);
        const nb = leafBlocks(r.ser.len);
        const blocks = try a.alloc([16]u32, nb);
        const ins = try a.alloc([8]u32, nb);
        var h = commit.H0;
        for (blocks, ins, 0..) |*bw, *hin, bi| {
            var buf: [64]u8 = @splat(0);
            const lo = 64 * bi;
            const hi = @min(msg.len, lo + 64);
            @memcpy(buf[0 .. hi - lo], msg[lo..hi]);
            for (bw, 0..) |*w, k| w.* = std.mem.readInt(u32, buf[4 * k ..][0..4], .little);
            hin.* = h;
            h = b2.compress(.{ .h = h, .m = bw.*, .t = leafT(msg.len, bi, nb), .f = bi + 1 == nb });
        }
        lf.* = .{ .msg = msg, .blocks = blocks, .ins = ins, .digest = h };
        prev = r.key();
    }
    return out;
}

/// A node: Blake2s-256 of `left ‖ right` (one block).
pub fn nodeHash(l: [8]u32, r: [8]u32) [8]u32 {
    var m: [16]u32 = undefined;
    @memcpy(m[0..8], &l);
    @memcpy(m[8..16], &r);
    return b2.compress(.{ .h = commit.H0, .m = m, .t = 64, .f = true });
}

fn slotDigest(leaves: []const Leaf, s: usize) [8]u32 {
    return if (s < leaves.len) leaves[s].digest else @splat(0);
}

/// The heap tree's nodes `1 … 2·HALF − 1` (index 0 unused): node `j < HALF` hashes nodes `2j`, `2j + 1`,
/// node `j ≥ HALF` slots `2(j − HALF)`, `2(j − HALF) + 1`.
pub fn treeNodes(a: std.mem.Allocator, leaves: []const Leaf, half: usize) ![][8]u32 {
    const nodes = try a.alloc([8]u32, 2 * half);
    nodes[0] = @splat(0);
    var j = 2 * half - 1;
    while (j >= 1) : (j -= 1) {
        nodes[j] = if (j >= half)
            nodeHash(slotDigest(leaves, 2 * (j - half)), slotDigest(leaves, 2 * (j - half) + 1))
        else
            nodeHash(nodes[2 * j], nodes[2 * j + 1]);
    }
    return nodes;
}

fn lwColumns(a: std.mem.Allocator, log_size: u32, recs: []const Rec, leaves: []const Leaf, reads: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const RI = 1;
    const BLK = 2;
    const B = 3;
    const A = 7;
    const CNT = 11;
    const LASTF = 12;
    const T = 13;
    const SM = 14;
    const ENDR = 15;
    const NEWR = 16;
    const START = 17;
    const M = 18;
    const F0 = 19;
    const PKU = 20;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 21, n);
    var row: usize = 0;
    for (recs, leaves, 0..) |r, lf, ri| {
        const nb = lf.blocks.len;
        var cnt: usize = 0;
        for (0..nb) |bi| for (0..16) |k| {
            if (row + 1 >= n) return error.LeafWordsDoNotFit;
            const last = bi + 1 == nb;
            const newr = bi == 0 and k == 0;
            const pku = bi == 0 and k < 9;
            cols[ON][row] = M31.one();
            cols[RI][row] = f(ri);
            cols[BLK][row] = f(bi);
            for (0..4) |j| {
                const pos = 64 * bi + 4 * k + j;
                if (pos < lf.msg.len) {
                    cols[B + j][row] = f(lf.msg[pos]);
                    cols[A + j][row] = M31.one();
                    cnt += 1;
                    if (!pku) try reads.append(a, @intCast(r.start + pos - 36));
                }
            }
            cols[CNT][row] = f(cnt);
            cols[LASTF][row] = if (last) M31.one() else M31.zero();
            cols[T][row] = f(leafT(lf.msg.len, bi, nb));
            cols[SM][row] = if (row > 0 and !newr) M31.one() else M31.zero();
            cols[ENDR][row] = if (k == 15 and last) M31.one() else M31.zero();
            cols[NEWR][row] = if (newr) M31.one() else M31.zero();
            cols[START][row] = f(r.start);
            cols[M][row] = f(lf.msg.len);
            cols[F0][row] = if (bi == 0) M31.one() else M31.zero();
            cols[PKU][row] = if (pku) M31.one() else M31.zero();
            row += 1;
        };
    }
    // Off rows: block 0, not last: the counter constraint gives 64.
    while (row < n) : (row += 1) cols[T][row] = f(64);
    return cols;
}

fn lcColumns(a: std.mem.Allocator, log_size: u32, leaves: []const Leaf) ![][]M31 {
    const BLKI = 300;
    const FST = 301;
    const NIL = 302;
    const LASTF = 303;
    const T = 304;
    const WLO = 305;
    const WHI = 306;
    const CHN = 307;
    const USEW = 308;
    const YD = 309;
    const MU0 = 310;
    const MU1 = 311;
    const RI = 312;
    const n = @as(usize, 1) << @intCast(log_size);
    var total: usize = 0;
    for (leaves) |lf| total += lf.blocks.len;
    if (b2.PERIOD * total > n) return error.LeafBlocksDoNotFit;
    const cols = try zeros(a, 313, n);
    var p: usize = 0;
    for (leaves, 0..) |lf, ri| for (lf.blocks, lf.ins, 0..) |bw, hin, bi| {
        const nb = lf.blocks.len;
        const last = bi + 1 == nb;
        const input: b2.Input = .{ .h = hin, .m = bw, .t = leafT(lf.msg.len, bi, nb), .f = last };
        const base = p * b2.PERIOD;
        b2.fillPeriod(cols, base, n, input);
        for (0..b2.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            cols[BLKI][row] = f(bi);
            cols[FST][row] = if (bi == 0) M31.one() else M31.zero();
            cols[LASTF][row] = if (last) M31.one() else M31.zero();
            cols[T][row] = f(input.t);
            cols[CHN][row] = if (bi > 0) M31.one() else M31.zero();
            cols[USEW][row] = M31.one();
            cols[YD][row] = if (last) M31.one() else M31.zero();
            cols[MU0][row] = if (q < 16) M31.one() else M31.zero();
            cols[MU1][row] = if (q == 0) M31.one() else M31.zero();
            cols[RI][row] = f(ri);
            if (q < 16) {
                cols[WLO][row] = f(bw[q] & 0xffff);
                cols[WHI][row] = f(bw[q] >> 16);
            }
        }
        p += 1;
    };
    while (p * b2.PERIOD < n) : (p += 1) {
        const base = p * b2.PERIOD;
        b2.fillPeriod(cols, base, n, .{ .h = commit.H0, .m = @splat(0), .t = 0, .f = false });
        for (0..b2.PERIOD) |q| {
            if (base + q >= n) break;
            cols[NIL][base + q] = M31.one();
        }
    }
    return cols;
}

fn bytes3(x: usize) [3]u32 {
    return .{ @intCast(x & 0xff), @intCast((x >> 8) & 0xff), @intCast((x >> 16) & 0xff) };
}

fn mtColumns(a: std.mem.Allocator, log_size: u32, leaves: []const Leaf, tree: []const [8]u32, half: usize, ranges: *std.ArrayList(u32)) ![][]M31 {
    const ID = 300;
    const NIL = 301;
    const USEW = 302;
    const LEAFL = 303;
    const USEL = 304;
    const USER = 305;
    const WLO = 306;
    const WHI = 307;
    const CK = 308;
    const LU = 309;
    const USEROW = 310;
    const ZW = 311;
    const MUN = 312;
    const MUL = 313;
    const DD = 314;
    const UL = 317;
    const UR = 320;
    const EB = 323;
    const HB = 326;
    const n = @as(usize, 1) << @intCast(log_size);
    const nodes = 2 * half - 1;
    const cnt = leaves.len;
    if (b2.PERIOD * nodes > n) return error.TreeDoesNotFit;
    if (cnt > 2 * half or 2 * half - cnt >= 1 << 24) return error.TooManyRecords;
    if (half == 0 or half - 1 >= 1 << 24) return error.TreeOutOfRange;
    const cols = try zeros(a, 329, n);
    var p: usize = 0;
    while (p * b2.PERIOD < n) : (p += 1) {
        const base = p * b2.PERIOD;
        const used = p < nodes;
        const j = p + 1;
        const leafl = used and j >= half;
        var m: [16]u32 = @splat(0);
        if (used) {
            const l = if (leafl) slotDigest(leaves, 2 * (j - half)) else tree[2 * j];
            const r = if (leafl) slotDigest(leaves, 2 * (j - half) + 1) else tree[2 * j + 1];
            @memcpy(m[0..8], &l);
            @memcpy(m[8..16], &r);
        }
        b2.fillPeriod(cols, base, n, if (used) .{ .h = commit.H0, .m = m, .t = 64, .f = true } else .{ .h = commit.H0, .m = @splat(0), .t = 0, .f = false });
        const slot_l = if (leafl) 2 * (j - half) else 0;
        const use_l = leafl and slot_l < cnt;
        const use_r = leafl and slot_l + 1 < cnt;
        const dd = if (!used) 0 else if (leafl) j - half else half - 1 - j;
        const ul: usize = if (!leafl) 0 else if (use_l) cnt - 1 - slot_l else slot_l - cnt;
        const ur: usize = if (!leafl) 0 else if (use_r) cnt - 1 - (slot_l + 1) else slot_l + 1 - cnt;
        if (dd >= 1 << 24 or ul >= 1 << 24 or ur >= 1 << 24) return error.TreeOutOfRange;
        if (used) {
            for (bytes3(dd)) |x| try ranges.append(a, x);
            if (leafl) for ([_]usize{ ul, ur }) |v| for (bytes3(v)) |x| try ranges.append(a, x);
        }
        for (0..b2.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            const lt8 = q < 8;
            const lt16 = q < 16;
            const userow = if (lt8) use_l else use_r;
            if (!used) {
                cols[NIL][row] = M31.one();
            } else {
                cols[ID][row] = f(j);
                cols[USEW][row] = M31.one();
            }
            cols[LEAFL][row] = if (leafl) M31.one() else M31.zero();
            cols[USEL][row] = if (use_l) M31.one() else M31.zero();
            cols[USER][row] = if (use_r) M31.one() else M31.zero();
            const ck = f(2 * (if (used) j else 0) + @intFromBool(!lt8)).sub(f(if (leafl) 2 * half else 0));
            cols[CK][row] = ck;
            cols[LU][row] = if (leafl) M31.one() else M31.zero();
            cols[USEROW][row] = if (userow) M31.one() else M31.zero();
            cols[ZW][row] = if (leafl and !userow) M31.one() else M31.zero();
            cols[MUN][row] = if (used and lt16 and !leafl) M31.one() else M31.zero();
            cols[MUL][row] = if (lt16 and leafl and userow) M31.one() else M31.zero();
            for (bytes3(dd), 0..) |x, i| cols[DD + i][row] = f(x);
            for (bytes3(ul), 0..) |x, i| cols[UL + i][row] = f(x);
            for (bytes3(ur), 0..) |x, i| cols[UR + i][row] = f(x);
            if (lt16) {
                cols[WLO][row] = f(m[q] & 0xffff);
                cols[WHI][row] = f(m[q] >> 16);
            }
        }
    }
    for (bytes3(2 * half - cnt), 0..) |x, i| {
        cols[EB + i][0] = f(x);
        try ranges.append(a, x);
    }
    for (bytes3(half - 1), 0..) |x, i| {
        cols[HB + i][0] = f(x);
        try ranges.append(a, x);
    }
    return cols;
}

test "set segments: Merkle leaves are Blake2s-256 of key(r - 1) ‖ record; the root is the heap tree's" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const file = std.fs.cwd().readFileAlloc(a, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    const recs = try parse(a, file[4..]);
    const leaves = try leafHashes(a, begin(file[0..4].*), recs);
    for (recs, leaves, 0..) |r, lf, i| {
        var want: [32]u8 = undefined;
        var msg: std.ArrayList(u8) = .empty;
        const prev: [36]u8 = if (i == 0) @splat(0) else recs[i - 1].key();
        try msg.appendSlice(a, &prev);
        try msg.appendSlice(a, r.head);
        try msg.appendSlice(a, r.ser);
        std.crypto.hash.blake2.Blake2s256.hash(msg.items, &want, .{});
        var got: [32]u8 = undefined;
        for (lf.digest, 0..) |w, k| std.mem.writeInt(u32, got[4 * k ..][0..4], w, .little);
        try std.testing.expectEqualSlices(u8, &want, &got);
    }
    // A node is Blake2s-256 of the two 32-byte children.
    const tree = try treeNodes(a, leaves, 64);
    var lr: [64]u8 = undefined;
    for (tree[2], 0..) |w, k| std.mem.writeInt(u32, lr[4 * k ..][0..4], w, .little);
    for (tree[3], 0..) |w, k| std.mem.writeInt(u32, lr[32 + 4 * k ..][0..4], w, .little);
    var want: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&lr, &want, .{});
    var got: [32]u8 = undefined;
    for (tree[1], 0..) |w, k| std.mem.writeInt(u32, got[4 * k ..][0..4], w, .little);
    try std.testing.expectEqualSlices(u8, &want, &got);
}
