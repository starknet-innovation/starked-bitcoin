//! Block context (M3a.5c and the commitment half of M3a.5e, D-035): the witness for the `block_ctx`
//! component (Lean: `Block/Ctx.lean`). One row per read, laid out by the preprocessed role columns
//! (period 256): the coinbase's input count, null prevout and scriptSig length; the BIP34 height push;
//! the header time (finality cutoff); the coinbase witness nonce and the commitment output; and byte
//! decompositions for the commitment length, the weight and sigop limits and the previous MTP.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const checks = @import("checks.zig");
const msg = @import("msg.zig");

pub const json = @embedFile("air:block_ctx");
pub const N_MAIN = 41;
pub const ZERO_ID: u32 = 1 << 28;
pub const NONCE_ID: u32 = (1 << 28) + 1;

const ADDR = 0;
const B = 1;
const ACTR = 2;
const ACC = 3;
const RA = 4;
const PACC = 5;
const LG0 = 6;
const A0 = 22;
const SEG0 = 23;
const W0 = 24;
const L0 = 25;
const WT = 26;
const NSEG = 27;
const HASC = 28;
const SIGS = 29;
const CPOS = 30;
const CLEN = 31;
const CLO = 32;
const CHI = 33;
const TL16 = 34;
const TH16 = 35;
const MLO = 36;
const MHI = 37;
const HC = 38;
const CID = 39;
const MZ = 40;

const Role = struct {
    base: u8 = 0,
    off: u32 = 0,
    exp: ?u8 = null,
    rst: bool = false,
    wgt: u32 = 0,
    src_b: bool = false,
    src_r: bool = false,
    sc1: bool = false,
    sc2: bool = false,
    flip: bool = false,
    hi: bool = false,
    lo: bool = false,
    cap_t0: bool = false,
    cap_t1: bool = false,
    cap_m0: bool = false,
    cap_m1: bool = false,
};

fn pow256(e: u32) u32 {
    return @as(u32, 1) << @intCast(8 * e);
}

/// The role of row `r` of a period (as `Ctx.role`).
fn role(r: u32) Role {
    if (r == 0) return .{ .base = 2, .off = 4, .exp = 1, .rst = true };
    if (r <= 32) return .{ .base = 2, .off = 4 + r, .exp = 0 };
    if (r <= 36) return .{ .base = 2, .off = 4 + r, .exp = 0xff };
    if (r == 37) return .{ .base = 2, .off = 41, .sc1 = true };
    if (r == 38) return .{ .base = 3, .off = 42, .exp = 3, .sc2 = true };
    if (r <= 41) return .{ .base = 3, .off = r + 4, .rst = r == 39, .wgt = pow256(r - 39), .src_b = true };
    if (r <= 45) return .{ .base = 1, .off = r + 26, .rst = r == 42 or r == 44, .wgt = pow256((r - 42) % 2), .src_b = true, .cap_t0 = r == 43, .cap_t1 = r == 45 };
    if (r == 46) return .{ .base = 4, .off = 0, .exp = 1 };
    if (r == 47) return .{ .base = 4, .off = 1, .exp = 0x20 };
    if (r <= 79) return .{ .base = 4, .off = r - 46, .hi = r % 2 == 0, .lo = r % 2 == 1 };
    if (r <= 85) return .{ .base = 5, .off = r - 80, .exp = checks.PATTERN[r - 80] };
    if (r <= 117) return .{ .base = 5, .off = r - 80, .hi = r % 2 == 0, .lo = r % 2 == 1 };
    if (r <= 121) return .{ .rst = r == 118, .wgt = pow256(r - 118), .src_r = true };
    if (r == 122) return .{ .flip = true };
    if (r <= 125) return .{ .rst = r == 123, .wgt = pow256(r - 123), .src_r = true };
    if (r <= 127) return .{ .rst = r == 126, .wgt = pow256(r - 126), .src_r = true };
    if (r <= 131) return .{ .rst = r == 128 or r == 130, .wgt = pow256((r - 128) % 2), .src_r = true, .cap_m0 = r == 129, .cap_m1 = r == 131 };
    return .{};
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

pub const In = struct {
    raw: []const u8,
    ctx: checks.Ctx,
    /// Transaction 0's tuple: start, segwit flag, witness-section start, lock-time start.
    tx0: msg.TxRange,
    chk: checks.Out,
    sigops: u32,
    /// The commitment node's digest id (when the commitment is checked).
    cid: u32,
};

pub const Out = struct {
    cols: [][]M31,
    reads: []u32,
    ranges: []u32,
    /// Whether the commitment is checked (`segwit · HASC`), and the nonce bytes.
    hc: bool,
    nonce: [32]u8,
};

pub fn generate(a: std.mem.Allocator, log_size: u32, in: In) !Out {
    const n = @as(usize, 1) << @intCast(log_size);
    if (n < 256) return error.TooSmall;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    var reads = std.ArrayList(u32).empty;
    var ranges = std.ArrayList(u32).empty;
    const raw = in.raw;
    const bip34 = in.ctx.bip34();
    const hc = in.ctx.segwit() and in.chk.commit != null;
    const cpos: u32 = if (in.chk.commit) |c| c[0] else 0;
    const clen: u32 = if (in.chk.commit) |c| c[1] else 0;
    const a0 = in.tx0.a;
    const seg0: u32 = @intFromBool(in.tx0.seg);
    const cutoff = in.chk.cutoff;
    const time = std.mem.readInt(u32, raw[68..72], .little);
    const mtp = in.ctx.prev_mtp;
    const force = in.ctx.force;
    if (4 * raw.len > 4000000 + 3 * @as(usize, in.chk.w) and !force) return error.BlockTooHeavy;
    const weight_d: u32 = 4000000 +% 3 *% in.chk.w -% 4 *% @as(u32, @intCast(raw.len));
    if (in.sigops > 20000 and !force) return error.TooManySigops;
    const sig_d: u32 = 20000 -% in.sigops;
    const clen_d: u32 = if (hc) clen -% 38 else 0;
    var nonce: [32]u8 = [_]u8{0} ** 32;
    if (hc) @memcpy(&nonce, raw[in.tx0.w + 2 ..][0..32]);
    const consts = [_]struct { c: usize, v: u32 }{
        .{ .c = A0, .v = a0 },                      .{ .c = SEG0, .v = seg0 },               .{ .c = W0, .v = in.tx0.w },
        .{ .c = L0, .v = in.tx0.l },                .{ .c = WT, .v = in.chk.w },             .{ .c = NSEG, .v = in.chk.nseg },
        .{ .c = HASC, .v = @intFromBool(in.chk.commit != null) }, .{ .c = SIGS, .v = in.sigops }, .{ .c = CPOS, .v = cpos },
        .{ .c = CLEN, .v = clen },                  .{ .c = CLO, .v = cutoff & 0xffff },     .{ .c = CHI, .v = cutoff >> 16 },
        .{ .c = TL16, .v = time & 0xffff },         .{ .c = TH16, .v = time >> 16 },         .{ .c = MLO, .v = mtp & 0xffff },
        .{ .c = MHI, .v = mtp >> 16 },              .{ .c = HC, .v = @intFromBool(hc) },     .{ .c = CID, .v = if (hc) in.cid else 0 },
    };
    var acc: u64 = 0;
    var pacc: u32 = 0;
    var lg = [_]u32{0} ** 16;
    var prev_b: u32 = 0;
    var prev_ra: u32 = 0;
    for (0..n) |rr| {
        const ro = role(@intCast(rr % 256));
        for (consts) |c| cols[c.c][rr] = f(c.v);
        if (rr == 0) cols[MZ][rr] = f(@intFromBool(hc));
        const base: u32 = switch (ro.base) {
            1 => 0,
            2, 3 => a0 + 2 * seg0,
            4 => in.tx0.w,
            5 => cpos,
            else => 0,
        };
        const addr = base + ro.off;
        cols[ADDR][rr] = f(addr);
        const actr = switch (ro.base) {
            1, 2 => true,
            3 => bip34,
            4, 5 => hc,
            else => false,
        };
        cols[ACTR][rr] = f(@intFromBool(actr));
        const b: u32 = if (ro.base != 0 and addr < raw.len) raw[addr] else 0;
        cols[B][rr] = f(b);
        if (actr) {
            try reads.append(a, addr);
            if (ro.exp) |e| if (b != e and !force) return error.ContextCheck;
        }
        // The range slot.
        const q = rr % 256;
        var ra: u32 = 0;
        if (ro.sc1) {
            const lo: u32 = 2 + 2 * @as(u32, @intFromBool(bip34));
            if ((b < lo or b > 100) and !force) return error.CoinbaseLength;
            ra = (b -% lo) & 0xff;
        } else if (ro.sc2) {
            ra = (100 -% prev_b) & 0xff;
        } else if (ro.flip) {
            ra = (1 -% prev_ra) & 0xff;
        } else if (ro.src_r) {
            ra = switch (q) {
                118...121 => (clen_d >> @intCast(8 * (q - 118))) & 0xff,
                123...125 => (weight_d >> @intCast(8 * (q - 123))) & 0xff,
                126...127 => (sig_d >> @intCast(8 * (q - 126))) & 0xff,
                128, 129 => (mtp & 0xffff) >> @intCast(8 * (q - 128)) & 0xff,
                130, 131 => (mtp >> 16) >> @intCast(8 * (q - 130)) & 0xff,
                else => 0,
            };
        }
        cols[RA][rr] = f(ra);
        try ranges.append(a, ra);
        // The accumulator.
        const v: u64 = (if (ro.src_b) @as(u64, b) else 0) + (if (ro.src_r) @as(u64, ra) else 0);
        acc = (if (ro.rst) 0 else acc) + @as(u64, ro.wgt) * v;
        cols[ACC][rr] = M31.fromU64(acc);
        // The digest register.
        if (ro.hi) pacc = 256 * b;
        if (ro.lo) {
            pacc += b;
            for (0..15) |j| lg[j] = lg[j + 1];
            lg[15] = pacc;
        }
        cols[PACC][rr] = if (ro.hi or ro.lo) f(pacc) else M31.zero();
        if (rr == 0) lg = [_]u32{0} ** 16;
        for (0..16) |j| cols[LG0 + j][rr] = f(lg[j]);
        prev_b = b;
        prev_ra = ra;
    }
    return .{ .cols = cols, .reads = try reads.toOwnedSlice(a), .ranges = try ranges.toOwnedSlice(a), .hc = hc, .nonce = nonce };
}
