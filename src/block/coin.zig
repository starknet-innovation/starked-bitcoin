//! M3b coin events (D-040): witnesses for `block_fpwalk`, `block_urec` and `block_coin` (Lean:
//! `Block/FpWalk.lean`, `Block/URec.lean`, `Block/Coin.lean`). The challenge `(γ, z, α)` is public; in
//! production it is drawn from the epoch's commitments (docs/design/utxo.md), here it is a parameter.

const std = @import("std");
const core = @import("stwo_core");
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const fields = @import("fields.zig");

pub const fpwalk_json = @embedFile("air:block_fpwalk");
pub const urec_json = @embedFile("air:block_urec");
pub const coin_json = @embedFile("air:block_coin");

pub const W = 26;
pub const PUB_G = 41;
pub const PUB_Z = 45;
pub const PUB_ALPHA = 49;
pub const PUB_S = 153;
pub const PUB_NIN = 157;
pub const PUB_LOST = 158;
pub const PUB_SUBL = 159;
pub const PUB_SUBH = 160;
pub const N_PUB = 161;
/// The coin component's `CTX` column (Lean `Coin.CTX`).
pub const CTX_COL = 80;

pub const MAX_MONEY: u64 = 21_000_000 * 100_000_000;

/// The block subsidy at `height` (Core's `GetBlockSubsidy`).
pub fn subsidy(height: u32) u64 {
    const halvings = height / 210000;
    return if (halvings >= 64) 0 else @as(u64, 5_000_000_000) >> @intCast(halvings);
}

pub const Challenge = struct {
    gamma: QM31,
    z: QM31,
    alpha: [W]QM31,

    /// A fixed test challenge (not secure: production derives it from the epoch's commitments).
    pub fn testing() Challenge {
        // Powers of one α, as in production (`epoch.challenge`).
        var al: [W]QM31 = undefined;
        var x = QM31.one();
        for (&al) |*v| {
            v.* = x;
            x = x.mul(QM31.fromU32Unchecked(1000003, 17, 19, 23));
        }
        return .{ .gamma = QM31.fromU32Unchecked(12345, 678, 9101, 1121), .z = QM31.fromU32Unchecked(31415926, 27182818, 14142135, 17320508), .alpha = al };
    }
};

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

fn neg(x: M31) M31 {
    return M31.zero().sub(x);
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

/// A fingerprint segment: stream (0 raw, 1 undo), id, start, length.
pub const Seg = struct { str: u1, sid: u32, start: u32, len: u32 };

/// Horner over the bytes with `γ`.
pub fn horner(gamma: QM31, bytes: []const u8) QM31 {
    var h = QM31.zero();
    for (bytes) |b| h = h.mul(gamma).add(QM31.fromBase(f(b)));
    return h;
}

/// `block_fpwalk`: one row per segment byte; appends its byte reads to `raw_reads` and `undo_reads`.
pub fn fpwalkColumns(a: std.mem.Allocator, log_size: u32, raw: []const u8, undo: []const u8, segs: []const Seg, gamma: QM31, raw_reads: *std.ArrayList(u32), undo_reads: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const STR = 1;
    const SID = 2;
    const POS = 3;
    const B = 4;
    const FST = 5;
    const LST = 6;
    const REM = 7;
    const LINV = 8;
    const LEN = 9;
    const H = 10;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 14, n);
    var r: usize = 0;
    for (segs) |s| {
        const data = if (s.str == 0) raw else undo;
        var h = QM31.zero();
        for (0..s.len) |q| {
            if (r + 1 >= n) return error.FingerprintsDoNotFit;
            const pos = s.start + q;
            const b = data[pos];
            h = h.mul(gamma).add(QM31.fromBase(f(b)));
            const rem = s.len - q;
            cols[ON][r] = M31.one();
            cols[STR][r] = f(s.str);
            cols[SID][r] = f(s.sid);
            cols[POS][r] = f(pos);
            cols[B][r] = f(b);
            cols[FST][r] = if (q == 0) M31.one() else M31.zero();
            cols[LST][r] = if (rem == 1) M31.one() else M31.zero();
            cols[REM][r] = f(rem);
            cols[LINV][r] = invOrZero(f(rem).sub(M31.one()));
            cols[LEN][r] = f(s.len);
            setQ(cols, H, r, h);
            try (if (s.str == 0) raw_reads else undo_reads).append(a, @intCast(pos));
            r += 1;
        }
    }
    return cols;
}

/// An undo record's parts.
pub const Rec = struct { start: u32, tl: u32, code: u32, value: u64, ctx: u32 };

/// A record's header in the in-circuit stream: the 4-byte code, the creating transaction's index (3
/// bytes), and the `serTxOut` length (2 bytes). The index and the length are committed with the code: the
/// epoch challenge is drawn after the commitment, and the LogUp bound holds only for claims fixed before
/// it, so neither a claim's index nor the records' boundaries may be trace choices (D-041).
pub const UHDR = 9;

fn parseRecs(a: std.mem.Allocator, undo: []const u8, hdr: usize) ![]Rec {
    if (undo.len == 0 or undo[0] != 1) return error.BadUndoStream;
    var out = std.ArrayList(Rec).empty;
    var p: usize = 1;
    while (p < undo.len) {
        if (p + hdr + 9 > undo.len) return error.BadUndoStream;
        const code = std.mem.readInt(u32, undo[p..][0..4], .little);
        const cx: u32 = if (hdr == UHDR) std.mem.readInt(u24, undo[p + 4 ..][0..3], .little) else 0;
        const tl_hdr: ?u16 = if (hdr == UHDR) std.mem.readInt(u16, undo[p + 7 ..][0..2], .little) else null;
        const value = std.mem.readInt(u64, undo[p + hdr ..][0..8], .little);
        const c = undo[p + hdr + 8];
        const sl: struct { v: usize, h: usize } = switch (c) {
            0...252 => .{ .v = c, .h = 1 },
            253 => blk: {
                if (p + hdr + 11 > undo.len) return error.BadUndoStream;
                break :blk .{ .v = std.mem.readInt(u16, undo[p + hdr + 9 ..][0..2], .little), .h = 3 };
            },
            else => return error.BadUndoStream,
        };
        const tl = 8 + sl.h + sl.v;
        if (p + hdr + tl > undo.len) return error.BadUndoStream;
        if (tl_hdr) |x| if (x != tl) return error.BadUndoStream;
        try out.append(a, .{ .start = @intCast(p), .tl = @intCast(tl), .code = code, .value = value, .ctx = cx });
        p += hdr + tl;
    }
    return out.toOwnedSlice(a);
}

/// The records of the in-circuit undo stream (`0x01`, then per record a 4-byte code, a 3-byte creating
/// transaction index and a `serTxOut`).
pub fn records(a: std.mem.Allocator, undo: []const u8) ![]Rec {
    return parseRecs(a, undo, UHDR);
}

/// The in-circuit undo stream from a fetched one (`0x01`, per record a 4-byte code and a `serTxOut`) and
/// the creating transactions' indices (`ctx`, per record; 0 when absent). A same-block creator's index is
/// found by txid.
pub fn undoStream(a: std.mem.Allocator, fetched: []const u8, ctx: ?[]const u32, raw: []const u8, rows: []const fields.Row, txids: []const [32]u8, height: u32) ![]u8 {
    const recs = try parseRecs(a, fetched, 4);
    if (ctx) |c| if (c.len != recs.len) return error.CtxCountMismatch;
    var out = std.ArrayList(u8).empty;
    try out.append(a, 1);
    var txi: u32 = 0;
    var j: usize = 0;
    for (rows) |tok| {
        if (tok.kind == fields.K_LOCK) {
            txi += 1;
            continue;
        }
        if (tok.kind != fields.K_IN or txi == 0) continue;
        if (j >= recs.len) return error.MissingUndoRecord;
        const rc = recs[j];
        var cv: u32 = if (ctx) |c| c[j] else 0;
        if (rc.code >> 1 == height) {
            cv = for (txids[0..txi], 0..) |t, i| {
                if (std.mem.eql(u8, &t, raw[tok.start..][0..32])) break @intCast(i);
            } else return error.SameBlockCreatorNotFound;
        }
        if (cv >= 1 << 24) return error.RangeOverflow;
        if (rc.tl >= 1 << 16) return error.RangeOverflow;
        var hdr: [UHDR]u8 = undefined;
        std.mem.writeInt(u32, hdr[0..4], rc.code, .little);
        std.mem.writeInt(u24, hdr[4..7], @intCast(cv), .little);
        std.mem.writeInt(u16, hdr[7..9], @intCast(rc.tl), .little);
        try out.appendSlice(a, &hdr);
        try out.appendSlice(a, fetched[rc.start + 4 ..][0..rc.tl]);
        j += 1;
    }
    if (j != recs.len) return error.ExtraUndoRecords;
    return out.toOwnedSlice(a);
}

/// `block_urec`: one row per record; appends its reads to `undo_reads`.
pub fn urecColumns(a: std.mem.Allocator, log_size: u32, undo: []const u8, recs: []const Rec, undo_reads: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const J = 1;
    const S = 2;
    const TL = 3;
    const n = @as(usize, 1) << @intCast(log_size);
    if (recs.len + 1 > n) return error.RecordsDoNotFit;
    const cols = try zeros(a, 21, n);
    cols[S][0] = M31.one();
    try undo_reads.append(a, 0);
    for (recs, 0..) |rc, r| {
        cols[ON][r] = M31.one();
        cols[J][r] = f(r);
        cols[S][r] = f(rc.start);
        cols[TL][r] = f(rc.tl);
        for (0..4) |i| {
            cols[4 + i][r] = f(undo[rc.start + i]);
            try undo_reads.append(a, @intCast(rc.start + i));
        }
        for (0..8) |i| {
            cols[8 + i][r] = f(undo[rc.start + UHDR + i]);
            try undo_reads.append(a, @intCast(rc.start + UHDR + i));
        }
        for (0..5) |i| {
            cols[16 + i][r] = f(undo[rc.start + 4 + i]);
            try undo_reads.append(a, @intCast(rc.start + 4 + i));
        }
    }
    return cols;
}

/// What the coin component needs from the rest of the block system.
pub const CoinInput = struct {
    raw: []const u8,
    undo: []const u8,
    rows: []const fields.Row,
    height: u32,
    /// Txid of each transaction (internal byte order).
    txids: []const [32]u8,
    recs: []const Rec,
    lost: bool = false,
    chal: Challenge,
};

pub const CoinOut = struct {
    cols: [][]M31,
    /// Txid digest uses per transaction (one per output).
    digest_uses: []u32,
    sum: QM31,
    nin: u32,
};

fn txidLimbs(t: [32]u8) [16]M31 {
    var out: [16]M31 = undefined;
    for (0..8) |w| {
        const word = std.mem.readInt(u32, t[4 * w ..][0..4], .big);
        out[2 * w] = f(word & 0xffff);
        out[2 * w + 1] = f(word >> 16);
    }
    return out;
}

/// The output segments of the block (for `block_fpwalk`, stream 0, id = start).
pub fn outputSegs(a: std.mem.Allocator, rows: []const fields.Row) ![]Seg {
    var out = std.ArrayList(Seg).empty;
    for (rows) |r| if (r.kind == fields.K_OUT) try out.append(a, .{ .str = 0, .sid = r.start, .start = r.start, .len = r.len });
    return out.toOwnedSlice(a);
}

pub fn undoSegs(a: std.mem.Allocator, recs: []const Rec) ![]Seg {
    const out = try a.alloc(Seg, recs.len);
    for (out, recs, 0..) |*s, rc, j| s.* = .{ .str = 1, .sid = @intCast(j), .start = rc.start + UHDR, .len = rc.tl };
    return out;
}

/// `block_coin`: one row per input and output token, in order. Appends raw reads and range values.
pub fn coinColumns(a: std.mem.Allocator, log_size: u32, in: CoinInput, raw_reads: *std.ArrayList(u32), ranges: *std.ArrayList(u32)) !CoinOut {
    const KO = 0;
    const KI = 1;
    const CBI = 2;
    const TXI = 3;
    const START = 4;
    const LEN = 5;
    const SSC = 6;
    const SVAL = 7;
    const D0 = 8;
    const VOUT = 11;
    const VLO = 12;
    const VHI = 13;
    const VB0 = 14;
    const J = 16;
    const ZI = 17;
    const CBO = 18;
    const PB0 = 19;
    const TLB0 = 55;
    const CLO = 71;
    const CHI = 72;
    const CB0 = 73;
    const HC = 75;
    const CBC = 76;
    const HB0 = 77;
    const CTX = 80;
    const ORD = 81;
    const OB0 = 82;
    const MB0 = 85;
    const FH = 88;
    const SLEN = 92;
    const SB = 93;
    const ZS = 94;
    const SINV = 95;
    const U6A = 96;
    const INVB = 97;
    const BIG = 98;
    const GB0 = 99;
    const UNSP = 102;
    const U6Z = 103;
    const MM = 104;
    const FC = 105;
    const ACC = 109;
    const SIDC = 113;
    const VL = 114;
    const VH = 115;
    const INL = 116;
    const INH = 117;
    const OUL = 118;
    const OUH = 119;
    const CY = 120;
    const FEL = 121;
    const FEH = 122;
    const FCY = 123;
    const CBL = 124;
    const CBH = 125;
    const TEND = 126;
    const Q1 = 127;
    const H1 = 130;
    const BR1 = 134;
    const NB = 135;
    const FB = 138;
    const Q2 = 141;
    const H2 = 144;
    const KP = 148;
    const KN = 149;
    const MNB = 150;
    const MC1 = 151;
    const MLO = 152;
    const H1C = 153;
    const H2C = 154;
    const Q3 = 155;
    const H3 = 158;
    const BR3 = 162;
    const H3C = 163;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 164, n);
    // Amounts: per row the coin's value; the token order is the block's.
    const M24: u64 = 1 << 24;
    var in_sum: u64 = 0;
    var out_sum: u64 = 0;
    var fees: u64 = 0;
    var cb_out: u64 = 0;
    var prev_kind: u8 = 0; // 0 none/CBI, 1 KI, 2 KO
    const putN = struct {
        fn bytes(c: [][]M31, base: usize, row: usize, v: u64, nb: usize, rg: *std.ArrayList(u32), al: std.mem.Allocator) !void {
            if (v >= @as(u64, 1) << @intCast(8 * nb)) return error.RangeOverflow;
            for (0..nb) |i| {
                const byte: u32 = @intCast((v >> @intCast(8 * i)) & 0xff);
                c[base + i][row] = f(byte);
                try rg.append(al, byte);
            }
        }
    };
    const ch = in.chal;
    const digest_uses = try a.alloc(u32, in.txids.len);
    @memset(digest_uses, 0);
    // Transaction index per token row, and the ordered input/output tokens.
    var txi: u32 = 0;
    var r: usize = 0;
    var j: u32 = 0;
    var vout: u32 = 0;
    var prev_ko = false;
    var prev_start: u32 = 0;
    var acc = QM31.zero();
    const b3 = struct {
        fn put(c: [][]M31, base: usize, row: usize, v: u32, rg: *std.ArrayList(u32), al: std.mem.Allocator) !void {
            if (v >= 1 << 24) return error.RangeOverflow;
            for (0..3) |i| {
                const byte = (v >> @intCast(8 * i)) & 0xff;
                c[base + i][row] = f(byte);
                try rg.append(al, byte);
            }
        }
    };
    for (in.rows) |tok| {
        if (tok.kind == fields.K_LOCK) {
            txi += 1;
            continue;
        }
        if (tok.kind != fields.K_IN and tok.kind != fields.K_OUT) continue;
        if (r + 1 >= n) return error.CoinsDoNotFit;
        const is_out = tok.kind == fields.K_OUT;
        const is_cb = txi == 0;
        cols[TXI][r] = f(txi);
        cols[START][r] = f(tok.start);
        cols[ZI][r] = invOrZero(f(txi));
        cols[CBO][r] = if (is_cb) M31.one() else M31.zero();
        if (r > 0) try b3.put(cols, D0, r, tok.start - prev_start - 1, ranges, a);
        cols[J][r] = f(j);
        var tuple: [W]M31 = [_]M31{M31.zero()} ** W;
        var m: i2 = 0;
        if (is_out) {
            cols[KO][r] = M31.one();
            cols[LEN][r] = f(tok.len);
            const ssc = tok.start + tok.off + tok.pref;
            cols[SSC][r] = f(ssc);
            cols[SVAL][r] = f(tok.val);
            vout = if (prev_ko) vout + 1 else 0;
            cols[VOUT][r] = f(vout);
            const vlo = vout & 0xffff;
            const vhi = vout >> 16;
            if (vhi >= 256) return error.RangeOverflow;
            cols[VLO][r] = f(vlo);
            cols[VHI][r] = f(vhi);
            cols[VB0][r] = f(vlo & 0xff);
            cols[VB0 + 1][r] = f(vlo >> 8);
            try ranges.appendSlice(a, &.{ vlo & 0xff, vlo >> 8, vhi });
            const code: u32 = 2 * in.height + @intFromBool(is_cb);
            cols[CLO][r] = f(code & 0xffff);
            cols[CHI][r] = f(code >> 16);
            cols[CB0][r] = f(code & 0xff);
            cols[CB0 + 1][r] = f((code >> 8) & 0xff);
            try ranges.appendSlice(a, &.{ code & 0xff, (code >> 8) & 0xff, code >> 16 });
            cols[CTX][r] = f(txi);
            cols[SLEN][r] = f(tok.len);
            const limbs = txidLimbs(in.txids[txi]);
            for (0..16) |i| cols[TLB0 + i][r] = limbs[i];
            digest_uses[txi] += 1;
            const fh = horner(ch.gamma, in.raw[tok.start .. tok.start + tok.len]);
            setQ(cols, FH, r, fh);
            // Unspendable?
            const zs = tok.val == 0;
            cols[ZS][r] = if (zs) M31.one() else M31.zero();
            cols[SINV][r] = invOrZero(f(tok.val));
            const sb: u8 = if (zs) 0 else in.raw[ssc];
            if (!zs) try raw_reads.append(a, ssc);
            cols[SB][r] = f(sb);
            const u6a = sb == 0x6a;
            cols[U6A][r] = if (u6a) M31.one() else M31.zero();
            cols[INVB][r] = if (u6a) M31.zero() else (f(sb).sub(f(0x6a))).inv() catch unreachable;
            const u6z = u6a and !zs;
            cols[U6Z][r] = if (u6z) M31.one() else M31.zero();
            const big = tok.val > 10000;
            cols[BIG][r] = if (big) M31.one() else M31.zero();
            try b3.put(cols, GB0, r, if (big) tok.val - 10001 else 10000 - tok.val, ranges, a);
            const unsp = u6z or big;
            cols[UNSP][r] = if (unsp) M31.one() else M31.zero();
            if (!unsp and !(is_cb and in.lost)) m = 1;
            cols[SIDC][r] = f(tok.start);
            for (0..16) |i| tuple[i] = limbs[i];
            tuple[16] = f(vlo);
            tuple[17] = f(vhi);
            tuple[18] = f(code & 0xffff);
            tuple[19] = f(code >> 16);
            const fa = fh.toM31Array();
            for (0..4) |i| tuple[20 + i] = fa[i];
            tuple[24] = f(tok.len);
            tuple[25] = f(txi);
            prev_ko = true;
        } else if (is_cb) {
            cols[CBI][r] = M31.one();
            // The coinbase input: its token only (no event).
            cols[ZS][r] = M31.one();
            cols[INVB][r] = (f(0).sub(f(0x6a))).inv() catch unreachable;
            prev_ko = false;
        } else {
            cols[KI][r] = M31.one();
            if (j >= in.recs.len) return error.MissingUndoRecord;
            const rc = in.recs[j];
            for (0..36) |i| {
                cols[PB0 + i][r] = f(in.raw[tok.start + i]);
                try raw_reads.append(a, tok.start + @as(u32, @intCast(i)));
            }
            var prev: [32]u8 = undefined;
            @memcpy(&prev, in.raw[tok.start..][0..32]);
            const limbs = txidLimbs(prev);
            for (0..16) |i| cols[TLB0 + i][r] = limbs[i];
            const pv = std.mem.readInt(u32, in.raw[tok.start + 32 ..][0..4], .little);
            cols[VLO][r] = f(pv & 0xffff);
            cols[VHI][r] = f(pv >> 16);
            cols[CLO][r] = f(rc.code & 0xffff);
            cols[CHI][r] = f(rc.code >> 16);
            const hc = rc.code >> 1;
            const cbc = rc.code & 1;
            cols[HC][r] = f(hc);
            cols[CBC][r] = f(cbc);
            try b3.put(cols, HB0, r, hc, ranges, a);
            // The creating transaction: the record's claim (same block: its index here).
            const ctxv: u32 = rc.ctx;
            if (hc == in.height) {
                const want: u32 = for (in.txids[0..txi], 0..) |t, i| {
                    if (std.mem.eql(u8, &t, &prev)) break @intCast(i);
                } else return error.SameBlockCreatorNotFound;
                if (ctxv != want) return error.SameBlockCreatorMismatch;
            }
            cols[CTX][r] = f(ctxv);
            const ord = hc < in.height;
            cols[ORD][r] = if (ord) M31.one() else M31.zero();
            try b3.put(cols, OB0, r, if (ord) in.height - 1 - hc else txi - 1 - ctxv, ranges, a);
            if (cbc == 1) {
                if (in.height < hc + 100) return error.ImmatureCoinbaseSpend;
                try b3.put(cols, MB0, r, in.height - hc - 100, ranges, a);
            }
            const fh = horner(ch.gamma, in.undo[rc.start + UHDR .. rc.start + UHDR + rc.tl]);
            setQ(cols, FH, r, fh);
            cols[SLEN][r] = f(rc.tl);
            cols[ZS][r] = M31.one();
            cols[INVB][r] = (f(0).sub(f(0x6a))).inv() catch unreachable;
            cols[SIDC][r] = f(j);
            m = -1;
            for (0..16) |i| tuple[i] = limbs[i];
            tuple[16] = f(pv & 0xffff);
            tuple[17] = f(pv >> 16);
            tuple[18] = f(rc.code & 0xffff);
            tuple[19] = f(rc.code >> 16);
            const fa = fh.toM31Array();
            for (0..4) |i| tuple[20 + i] = fa[i];
            tuple[24] = f(rc.tl);
            tuple[25] = f(ctxv);
            j += 1;
            prev_ko = false;
        }
        // Amounts.
        {
            const is_ki = cols[KI][r].eql(M31.one());
            const value: u64 = if (is_out) std.mem.readInt(u64, in.raw[tok.start..][0..8], .little) else if (is_ki) in.recs[j - 1].value else 0;
            if (is_out or is_ki) {
                cols[VL][r] = f(value & (M24 - 1));
                cols[VH][r] = f(value >> 24);
                cols[MNB][r] = M31.one();
            }
            if (is_ki) {
                const base: u64 = if (prev_kind == 1) in_sum else 0;
                const lo = (base & (M24 - 1)) + (value & (M24 - 1));
                in_sum = base + value;
                if (in_sum > MAX_MONEY) return error.InputsOutOfRange;
                cols[CY][r] = if (lo >= M24) M31.one() else M31.zero();
                cols[INL][r] = f(in_sum & (M24 - 1));
                cols[INH][r] = f(in_sum >> 24);
                try putN.bytes(cols, NB, r, in_sum & (M24 - 1), 3, ranges, a);
                // MAX_MONEY − inputs ≥ 0
                const br = (MAX_MONEY & (M24 - 1)) < (in_sum & (M24 - 1));
                cols[BR1][r] = if (br) M31.one() else M31.zero();
                const d = MAX_MONEY - in_sum;
                try putN.bytes(cols, Q1, r, d & (M24 - 1), 3, ranges, a);
                try putN.bytes(cols, H1, r, d >> 24, 4, ranges, a);
                cols[MC1][r] = M31.one();
                prev_kind = 1;
            } else if (is_out) {
                cols[INL][r] = f(in_sum & (M24 - 1));
                cols[INH][r] = f(in_sum >> 24);
                const base: u64 = if (prev_kind == 2) out_sum else 0;
                const lo = (base & (M24 - 1)) + (value & (M24 - 1));
                out_sum = base + value;
                cols[CY][r] = if (lo >= M24) M31.one() else M31.zero();
                cols[OUL][r] = f(out_sum & (M24 - 1));
                cols[OUH][r] = f(out_sum >> 24);
                try putN.bytes(cols, NB, r, out_sum & (M24 - 1), 3, ranges, a);
                prev_kind = 2;
            } else {
                // The coinbase input: no value; the coinbase's outputs carry a zero input sum.
                in_sum = 0;
                prev_kind = 0;
            }
        }
        const mv: M31 = switch (m) {
            0 => M31.zero(),
            1 => M31.one(),
            -1 => neg(M31.one()),
            else => unreachable,
        };
        cols[MM][r] = mv;
        var phi = QM31.zero();
        for (ch.alpha, tuple) |al, t| phi = phi.add(al.mulM31(t));
        const fr = if (m == 0) QM31.zero() else (try ch.z.sub(phi).inv()).mulM31(mv);
        acc = acc.add(fr);
        setQ(cols, FC, r, fr);
        setQ(cols, ACC, r, acc);
        prev_start = tok.start;
        r += 1;
    }
    if (j != in.recs.len) return error.ExtraUndoRecords;
    // Second pass: transaction ends, fees, the coinbase's outputs, the block's check.
    const n_on = r;
    {
        var fe: u64 = 0;
        var cbo: u64 = 0;
        for (0..n) |q| {
            const ko = q < n_on and cols[KO][q].eql(M31.one());
            const next_ko = q + 1 < n_on and cols[KO][q + 1].eql(M31.one());
            const tend = ko and !next_ko;
            const is_cb = cols[CBO][q].eql(M31.one()) and q < n_on;
            cols[TEND][q] = if (tend) M31.one() else M31.zero();
            const inl = cols[INL][q].toU32();
            const inh = cols[INH][q].toU32();
            const oul = cols[OUL][q].toU32();
            const ouh = cols[OUH][q].toU32();
            const in_v = @as(u64, inh) * M24 + inl;
            const out_v = @as(u64, ouh) * M24 + oul;
            var fcy = false;
            if (tend and !is_cb) {
                if (in_v < out_v) return error.InputsBelowOutputs;
                const fee = in_v - out_v;
                const br = inl < oul;
                cols[BR1][q] = if (br) M31.one() else M31.zero();
                try putN.bytes(cols, Q1, q, fee & (M24 - 1), 3, ranges, a);
                try putN.bytes(cols, H1, q, fee >> 24, 4, ranges, a);
                cols[MC1][q] = M31.one();
                fcy = (fe & (M24 - 1)) + (fee & (M24 - 1)) >= M24;
                fe += fee;
                // The accumulated fees within MAX_MONEY (Core: bad-txns-accumulated-fee-outofrange).
                if (fe > MAX_MONEY) return error.AccumulatedFeesOutOfRange;
                const d3 = MAX_MONEY - fe;
                cols[BR3][q] = if ((MAX_MONEY & (M24 - 1)) < (fe & (M24 - 1))) M31.one() else M31.zero();
                for (0..3) |i| cols[Q3 + i][q] = f(((d3 & (M24 - 1)) >> @intCast(8 * i)) & 0xff);
                for (0..4) |i| cols[H3 + i][q] = f(((d3 >> 24) >> @intCast(8 * i)) & 0xff);
            }
            if (tend and is_cb) cbo = out_v;
            cols[FEL][q] = f(fe & (M24 - 1));
            cols[FEH][q] = f(fe >> 24);
            cols[FCY][q] = if (fcy) M31.one() else M31.zero();
            // The fee sum's bytes on every row (range-checked on on rows only).
            if (q < n_on) try putN.bytes(cols, FB, q, fe & (M24 - 1), 3, ranges, a) else {
                for (0..3) |i| cols[FB + i][q] = f((fe >> @intCast(8 * i)) & 0xff);
            }
            cols[CBL][q] = f(cbo & (M24 - 1));
            cols[CBH][q] = f(cbo >> 24);
            if (q + 1 == n_on) {
                const sub = subsidy(in.height);
                if (cbo > sub + fe) return error.CoinbaseTooLarge;
                const d = sub + fe - cbo;
                const t: i64 = @as(i64, @intCast(sub & (M24 - 1))) + @as(i64, @intCast(fe & (M24 - 1))) - @as(i64, @intCast(cbo & (M24 - 1)));
                const dlo: i64 = @intCast(d & (M24 - 1));
                const kk = @divExact(t - dlo, @as(i64, @intCast(M24)));
                cols[KP][q] = if (kk == 1) M31.one() else M31.zero();
                cols[KN][q] = if (kk == -1) M31.one() else M31.zero();
                try putN.bytes(cols, Q2, q, d & (M24 - 1), 3, ranges, a);
                try putN.bytes(cols, H2, q, d >> 24, 4, ranges, a);
                cols[MLO][q] = M31.one();
            }
        }
        fees = fe;
        cb_out = cbo;
    }
    _ = &out_sum;
    _ = &fees;
    _ = &cb_out;
    // The comparators' top bytes are at most 7: `H1C = 7 − H1 3`, `H2C = 7 − H2 3` on every row,
    // range-checked where the comparator is (MC1, MLO).
    for (0..n) |q| {
        cols[H1C][q] = f(7).sub(cols[H1 + 3][q]);
        cols[H2C][q] = f(7).sub(cols[H2 + 3][q]);
        cols[H3C][q] = f(7).sub(cols[H3 + 3][q]);
        if (cols[MC1][q].eql(M31.one())) {
            try ranges.append(a, cols[H1C][q].toU32());
            for (0..3) |i| try ranges.append(a, cols[Q3 + i][q].toU32());
            for (0..4) |i| try ranges.append(a, cols[H3 + i][q].toU32());
            try ranges.append(a, cols[H3C][q].toU32());
        }
        if (cols[MLO][q].eql(M31.one())) try ranges.append(a, cols[H2C][q].toU32());
    }
    // Off rows: the coinbase flag and is-zero helpers, the record count and the accumulator carried.
    while (r < n) : (r += 1) {
        cols[CBO][r] = M31.one();
        cols[ZS][r] = M31.one();
        cols[INVB][r] = (f(0).sub(f(0x6a))).inv() catch unreachable;
        cols[J][r] = f(j);
        setQ(cols, ACC, r, acc);
    }
    return .{ .cols = cols, .digest_uses = digest_uses, .sum = acc, .nin = j };
}

/// The public inputs 41–158 for a challenge and a block's sum.
pub fn pubs(ch: Challenge, sum: QM31, nin: u32, lost: bool, height: u32) [N_PUB - 41]M31 {
    var out: [N_PUB - 41]M31 = undefined;
    @memcpy(out[0..4], &ch.gamma.toM31Array());
    @memcpy(out[4..8], &ch.z.toM31Array());
    for (ch.alpha, 0..) |al, k| @memcpy(out[8 + 4 * k ..][0..4], &al.toM31Array());
    @memcpy(out[PUB_S - 41 ..][0..4], &sum.toM31Array());
    out[PUB_NIN - 41] = f(nin);
    out[PUB_LOST - 41] = if (lost) M31.one() else M31.zero();
    const sub = subsidy(height);
    out[PUB_SUBL - 41] = f(sub & 0xffffff);
    out[PUB_SUBH - 41] = f(sub >> 24);
    return out;
}

/// The fraction `1/(z − φ)` of a coin created by output `vout` of transaction `ctx` (txid `txid`) of a
/// block at `height`, with `ser` its `serTxOut` bytes.
pub fn coinFrac(ch: Challenge, txid: [32]u8, vout: u32, height: u32, cb: bool, ser: []const u8, ctx: u32) !QM31 {
    var t: [W]M31 = undefined;
    const limbs = txidLimbs(txid);
    for (0..16) |i| t[i] = limbs[i];
    t[16] = f(vout & 0xffff);
    t[17] = f(vout >> 16);
    const code: u32 = 2 * height + @intFromBool(cb);
    t[18] = f(code & 0xffff);
    t[19] = f(code >> 16);
    const fa = horner(ch.gamma, ser).toM31Array();
    for (0..4) |i| t[20 + i] = fa[i];
    t[24] = f(ser.len);
    t[25] = f(ctx);
    var phi = QM31.zero();
    for (ch.alpha, t) |al, v| phi = phi.add(al.mulM31(v));
    return ch.z.sub(phi).inv();
}

test "coin events: blocks 9 and 170 balance (block 170 spends block 9's coinbase); a tampered undo record, index or length does not" {
    const bsys = @import("system.zig");
    const checks = @import("checks.zig");
    const pf = @import("proof_file.zig");
    const H = @import("../btc/header_chain.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const raw9 = @embedFile("testdata:block_9");
    const s170 = checks.samples_small[1];
    const b9 = try bsys.buildU(a, raw9, &.{1}, .{ .height = 9, .prev_mtp = pf.prevMtp(headers, 9) });
    const b170 = try bsys.buildU(a, s170.raw, s170.undo, s170.ctx);
    for ([_]*const bsys.Built{ &b9, &b170 }) |b| {
        try std.testing.expect(try bsys.firstViolation(a, &airs, b) == null);
        try std.testing.expect(try bsys.unbalanced(a, &airs, b) == null);
    }
    try std.testing.expectEqual(@as(u32, 0), b9.nin);
    try std.testing.expectEqual(@as(u32, 1), b170.nin);
    // The final set: block 170's coinbase output and its second transaction's two outputs.
    const ch = Challenge.testing();
    const rows = try fields.tokenize(a, s170.raw);
    var txids: [2][32]u8 = undefined;
    {
        var txi: usize = 0;
        var start: usize = 0;
        for (rows) |r| {
            if (r.kind == fields.K_TXH) start = r.start;
            if (r.kind == fields.K_LOCK) {
                // Non-segwit: the txid is SHA256d of the transaction's bytes.
                const tx = s170.raw[start .. r.start + 4];
                var h1: [32]u8 = undefined;
                std.crypto.hash.sha2.Sha256.hash(tx, &h1, .{});
                std.crypto.hash.sha2.Sha256.hash(&h1, &txids[txi], .{});
                txi += 1;
            }
        }
    }
    var final = QM31.zero();
    var txi: u32 = 0;
    var vout: u32 = 0;
    var prev_out = false;
    for (rows) |r| {
        if (r.kind == fields.K_LOCK) txi += 1;
        if (r.kind == fields.K_OUT) {
            vout = if (prev_out) vout + 1 else 0;
            final = final.add(try coinFrac(ch, txids[txi], vout, 170, txi == 0, s170.raw[r.start .. r.start + r.len], txi));
            prev_out = true;
        } else if (r.kind != fields.K_LOCK) prev_out = false;
    }
    try std.testing.expect(b9.coin_sum.add(b170.coin_sum).eql(final));
    // A tampered amount in block 170's undo record: the block still proves alone, but the epoch fails.
    const bad = try a.dupe(u8, s170.undo);
    bad[5] ^= 1;
    const b170x = try bsys.buildU(a, s170.raw, bad, s170.ctx);
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b170x) == null);
    try std.testing.expect(!b9.coin_sum.add(b170x.coin_sum).eql(final));
    // The creating transaction's index is the undo record's, which the commitment holds: a coin row's
    // other `CTX` leaves the record lookup unbalanced, and another index is another commitment.
    const b170c = try bsys.buildU(a, s170.raw, s170.undo, s170.ctx);
    const cm = b170c.mains[14];
    const r_in = for (0..cm[1].len) |r| {
        if (cm[1][r].eql(M31.one())) break r;
    } else unreachable;
    cm[CTX_COL][r_in] = cm[CTX_COL][r_in].add(M31.one());
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b170c) != null);
    const b170d = try bsys.buildFull(a, s170.raw, s170.undo, s170.ctx, .{ .ctx = &.{5} });
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b170d) == null);
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b170d) == null);
    try std.testing.expect(!std.mem.eql(u32, &b170d.commitment_words, &b170.commitment_words));
    // The record boundaries are committed too: a record length other than its length bytes is rejected.
    const b170t = try bsys.buildU(a, s170.raw, s170.undo, s170.ctx);
    b170t.mains[13][3][0] = b170t.mains[13][3][0].add(M31.one());
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b170t) != null);
}

test "amounts: a coinbase above subsidy plus fees is rejected (block 170, subsidy one satoshi lower)" {
    const bsys = @import("system.zig");
    const checks = @import("checks.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const s = checks.samples_small[1];
    var b = try bsys.buildU(a, s.raw, s.undo, s.ctx);
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b) == null);
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
    // Block 170: coinbase 50 BTC, the subsidy, and no fees: one satoshi less subsidy breaks the check.
    try std.testing.expectEqual(@as(u64, 5_000_000_000), subsidy(170));
    b.pubs[PUB_SUBL] = b.pubs[PUB_SUBL].sub(M31.one());
    const bad_c = try bsys.firstViolation(a, &airs, &b);
    const bad_l = try bsys.unbalanced(a, &airs, &b);
    try std.testing.expect(bad_c != null or bad_l != null);
}

test "amounts: a wrapped high comparator cannot hide a coinbase above subsidy plus fees (the 7 − H2 3 bound)" {
    const bsys = @import("system.zig");
    const checks = @import("checks.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const s = checks.samples_small[1];
    var b = try bsys.buildU(a, s.raw, s.undo, s.ctx);
    const COIN = 14;
    const TABLES = 5;
    const Q2 = 141;
    const H2 = 144;
    const KP = 148;
    const KN = 149;
    const MLO = 152;
    const H2C = 154;
    const cc = b.mains[COIN];
    const rg = b.mains[TABLES][0];
    var q: usize = 0;
    while (!cc[MLO][q].eql(M31.one())) q += 1;
    // Block 170: subsidy 50 BTC, no fees, coinbase 50 BTC. Lower the subsidy by one satoshi: the honest
    // difference is −1. The attack writes it wrapped: the low limb borrows (`KN = 1`), so the low
    // comparator is `2^24 − 1` and the high one `−1 ≡ P − 1 = 0x7FFFFFFE`, four valid bytes.
    b.pubs[PUB_SUBL] = b.pubs[PUB_SUBL].sub(M31.one());
    const drop = struct {
        fn f(t: []M31, v: M31) void {
            t[v.toU32()] = t[v.toU32()].sub(M31.one());
        }
        fn add(t: []M31, v: u32) void {
            t[v] = t[v].add(M31.one());
        }
    };
    for (0..3) |i| drop.f(rg, cc[Q2 + i][q]);
    for (0..4) |i| drop.f(rg, cc[H2 + i][q]);
    drop.f(rg, cc[H2C][q]);
    cc[KN][q] = M31.one();
    cc[KP][q] = M31.zero();
    const lo = [3]u32{ 0xff, 0xff, 0xff };
    const hi = [4]u32{ 0xfe, 0xff, 0xff, 0x7f };
    for (lo, 0..) |v, i| {
        cc[Q2 + i][q] = f(v);
        drop.add(rg, v);
    }
    for (hi, 0..) |v, i| {
        cc[H2 + i][q] = f(v);
        drop.add(rg, v);
    }
    // With the bound column consistent (`7 − 0x7f`, not a byte), the range lookup cannot balance.
    cc[H2C][q] = f(7).sub(f(0x7f));
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b) == null);
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b) != null);
    // With a byte there instead, everything balances and only the bound's constraint fails: without the
    // bound, this coinbase would have been accepted.
    cc[H2C][q] = f(7);
    drop.add(rg, 7);
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b) != null);
}
