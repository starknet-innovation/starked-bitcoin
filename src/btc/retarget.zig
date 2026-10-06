//! Witness for the difficulty-retarget constraints (lean/StarkedAir/Gadgets/Retarget.lean):
//! the scratch words of rows 220..228 of a header, plus two carry-column bits in row 222.

const std = @import("std");

pub const POW_LIMIT: u256 = (@as(u256, 1) << 224) - 1;
const TIMESPAN: u64 = 1209600;

/// Little-endian numeric value of a field stored as a raw big-endian header word
/// (nBits, time): byte-swap.
pub fn le(word: u32) u32 {
    return @byteSwap(word);
}

/// `arith_uint256::SetCompact` value (ignoring validity flags).
pub fn compactValue(n: u32) u256 {
    const size = n >> 24;
    const word: u256 = n & 0x7fffff;
    return if (size <= 3) word >> @intCast(8 * (3 - size)) else word << @intCast(8 * (size - 3));
}

/// `arith_uint256::GetCompact` for a non-negative value.
pub fn getCompact(t: u256) u32 {
    var size: u32 = @intCast((256 - @clz(t) + 7) / 8);
    var c: u32 = if (size <= 3) @intCast(t << @intCast(8 * (3 - size))) else @intCast(t >> @intCast(8 * (size - 3)));
    if (c & 0x00800000 != 0) {
        c >>= 8;
        size += 1;
    }
    return c | (size << 24);
}

/// `GetNextWorkRequired` (mainnet) at a period boundary.
pub fn nextWork(prev_nbits: u32, prev_time: u32, pst: u32) u32 {
    const span = std.math.clamp(@as(i64, prev_time) - @as(i64, pst), 302400, 4838400);
    const t = compactValue(prev_nbits) * @as(u256, @intCast(span)) / TIMESPAN;
    return getCompact(@min(t, POW_LIMIT));
}

pub const Scratch = struct {
    /// Words (a, e, w) for rows 221..228 (index 0 = row 221).
    a: [8]u32 = [_]u32{0} ** 8,
    e: [8]u32 = [_]u32{0} ** 8,
    w: [8]u32 = [_]u32{0} ** 8,
    /// Row-222 carry-column bits: col 108 (= v bit 32) and col 114 (mid-branch carry).
    v32: u32 = 0,
    mid_carry: u32 = 0,
};

fn bytesOf(comptime n: usize, x: u256) [n]u32 {
    var out: [n]u32 = undefined;
    for (0..n) |i| out[i] = @intCast((x >> @intCast(8 * i)) & 0xff);
    return out;
}

fn pack(bytes: []const u32, width: u5) u32 {
    var x: u32 = 0;
    for (bytes, 0..) |b, i| x |= b << @intCast(@as(u32, width) * @as(u32, @intCast(i)));
    return x;
}

const div_bytes = [3][5]u32{ .{ 0x00, 0x75, 0x12, 0, 0 }, .{ 0x00, 0x00, 0x75, 0x12, 0 }, .{ 0x00, 0x00, 0x00, 0x75, 0x12 } };
const div_m1_bytes = [3][5]u32{ .{ 0xff, 0x74, 0x12, 0, 0 }, .{ 0xff, 0xff, 0x74, 0x12, 0 }, .{ 0xff, 0xff, 0xff, 0x74, 0x12 } };
const cap_thr = [2][6]u32{ .{ 0, 0, 0, 0, 0x75, 0x12 }, .{ 0, 0, 0, 0x75, 0x12, 0 } };

/// `prev_nb_word`, `prev_time_word`, `prev_pst_word`, `own_nb_word` are raw header words.
pub fn scratch(height: u32, prev_nb_word: u32, prev_time_word: u32, prev_pst_word: u32, own_nb_word: u32) !Scratch {
    var s = Scratch{};
    const q = height / 2016;
    const nz: u32 = @intFromBool(q >= 1);
    const rt: u32 = @intFromBool(height % 2016 == 0 and q >= 1);
    if (nz == 1) s.w[6] = q - 1; // row 227 w

    // Previous mantissa bytes: always present in the row-220 copy, so the (ungated) product
    // P0 = mant_prev · span uses them even when span = 0.
    const prev_nb = le(prev_nb_word);
    const mant_prev: u32 = prev_nb & 0x7fffff;
    var span: u32 = 0;
    var flags: u32 = rt | (nz << 1);

    if (rt == 1) {
        const exp_prev = prev_nb >> 24;
        if (exp_prev < 3 or exp_prev > 29) return error.UnsupportedTargetEncoding;
        const s_prev = exp_prev - 3;
        s.a[0] = @as(u32, 1) << @intCast(s_prev);

        const t_prev: i64 = le(prev_time_word);
        const pst: i64 = le(prev_pst_word);
        const raw_span = t_prev - pst;
        const t_lo: u32 = @intCast(t_prev & 0xffff);
        const t_hi: u32 = @intCast(t_prev >> 16);
        const p_lo: u32 = @intCast(pst & 0xffff);
        const p_hi: u32 = @intCast(pst >> 16);
        _ = t_hi;
        _ = p_hi;
        if (raw_span < 302400) {
            span = 302400;
            flags |= 1 << 2;
            const v: u64 = @intCast(pst + 302399 - t_prev);
            s.w[1] = @truncate(v);
            s.v32 = @intCast(v >> 32);
            const diff: i64 = @as(i64, p_lo) + (302399 % 65536) - @as(i64, t_lo) - @as(i64, @intCast(v & 0xffff));
            if (diff >= 0) flags |= @as(u32, @intCast(@divExact(diff, 65536))) << 9 else flags |= @as(u32, @intCast(@divExact(-diff, 65536))) << 10;
        } else if (raw_span > 4838400) {
            span = 4838400;
            flags |= 1 << 4;
            const v: u64 = @intCast(t_prev - pst - 4838401);
            s.w[1] = @truncate(v);
            s.v32 = @intCast(v >> 32);
            // AIR: pst.lo + K_lo + v.lo + 2^16·kn = t.lo + 2^16·kp.
            const diff: i64 = @as(i64, p_lo) + (4838401 % 65536) + @as(i64, @intCast(v & 0xffff)) - @as(i64, t_lo);
            if (diff >= 0) flags |= @as(u32, @intCast(@divExact(diff, 65536))) << 9 else flags |= @as(u32, @intCast(@divExact(-diff, 65536))) << 10;
        } else {
            span = @intCast(raw_span);
            flags |= 1 << 3;
            s.mid_carry = (p_lo + (span & 0xffff)) >> 16;
            s.a[1] = span - 302400;
            s.e[1] = 4838400 - span;
        }
    }
    s.e[0] = span;

    // P0 = mant_prev · span, byte columns 0..5.
    const a_b = [3]u32{ mant_prev & 0xff, (mant_prev >> 8) & 0xff, mant_prev >> 16 };
    const b_b = [3]u32{ span & 0xff, (span >> 8) & 0xff, span >> 16 };
    var p0b: [6]u32 = undefined;
    var mc: [5]u32 = undefined;
    var carry: u32 = 0;
    for (0..6) |k| {
        var sum: u32 = carry;
        for (0..3) |i| for (0..3) |j| if (i + j == k) {
            sum += a_b[i] * b_b[j];
        };
        if (k < 5) {
            p0b[k] = sum & 0xff;
            mc[k] = sum >> 8;
            carry = mc[k];
        } else {
            if (sum > 0xff) return error.ProductOverflow;
            p0b[k] = sum;
        }
    }
    s.a[2] = pack(p0b[0..4], 8);
    s.e[2] = pack(p0b[4..6], 8);
    s.a[3] = pack(mc[0..3], 10);
    s.e[3] = pack(mc[3..5], 10);
    const p0: u64 = @as(u64, mant_prev) * span;

    if (rt == 1) {
        const expected = nextWork(prev_nb, le(prev_time_word), le(prev_pst_word));
        const own = le(own_nb_word);
        if (own != expected) return error.RetargetMismatch;
        const s_prev = (prev_nb >> 24) - 3;
        const t_new = compactValue(prev_nb) * span / TIMESPAN;
        if (t_new > POW_LIMIT) {
            flags |= 1 << 8; // cap
            if (s_prev != 25 and s_prev != 26) return error.UnexpectedCap;
            const thr = cap_thr[s_prev - 25];
            var thr_v: u64 = 0;
            for (thr, 0..) |b, k| thr_v |= @as(u64, b) << @intCast(8 * k);
            const tau = p0 - thr_v;
            const tb = bytesOf(6, tau);
            var cc: [6]u32 = [_]u32{0} ** 6;
            var cin: u32 = 0;
            for (0..6) |k| {
                const sum = thr[k] + tb[k] + cin;
                if ((sum & 0xff) != p0b[k]) return error.CapColumnMismatch;
                cc[k] = sum >> 8;
                cin = cc[k];
            }
            s.a[7] = pack(tb[0..4], 8);
            s.e[7] = pack(tb[4..6], 8);
            s.w[7] = pack(cc[0..6], 4);
        } else {
            const s_own: i64 = @as(i64, own >> 24) - 3;
            const d = s_own - @as(i64, s_prev);
            if (d < -1 or d > 1) return error.ExponentJumpTooLarge;
            const di: usize = @intCast(d + 1);
            flags |= @as(u32, 1) << @intCast(5 + di);
            const mant_own: u32 = own & 0x7fffff;
            if (mant_own < 0x8000) return error.NonCanonicalTarget;
            s.e[6] = mant_own - 0x8000;
            var divisor: u64 = 0;
            for (div_bytes[di], 0..) |b, k| divisor |= @as(u64, b) << @intCast(8 * k);
            const n: u64 = p0 * 256;
            if (n / divisor != mant_own) return error.RetargetMismatch;
            const rho = n % divisor;
            const sigma = divisor - 1 - rho;
            const rb = bytesOf(5, rho);
            const sb = bytesOf(5, sigma);
            const cb = [3]u32{ mant_own & 0xff, (mant_own >> 8) & 0xff, mant_own >> 16 };
            const nb = bytesOf(8, @as(u256, n));
            var dc: [8]u32 = [_]u32{0} ** 8;
            var cin: u32 = 0;
            for (0..8) |k| {
                var sum: u32 = cin + (if (k < 5) rb[k] else 0);
                for (0..5) |i| for (0..3) |j| if (i + j == k) {
                    sum += div_bytes[di][i] * cb[j];
                };
                if (sum < nb[k] or (sum - nb[k]) % 256 != 0) return error.DivisionColumnMismatch;
                dc[k] = (sum - nb[k]) / 256;
                if (dc[k] > 0xff) return error.CarryTooLarge;
                cin = dc[k];
            }
            if (dc[7] != 0) return error.DivisionColumnMismatch;
            var sc: [5]u32 = [_]u32{0} ** 5;
            cin = 0;
            for (0..5) |k| {
                const sum = rb[k] + sb[k] + cin;
                if ((sum & 0xff) != div_m1_bytes[di][k]) return error.RemainderColumnMismatch;
                sc[k] = sum >> 8;
                cin = sc[k];
            }
            if (sc[4] != 0) return error.RemainderColumnMismatch;
            s.a[4] = pack(rb[0..4], 8);
            s.e[4] = rb[4];
            s.w[4] = pack(sb[0..4], 8);
            s.a[5] = sb[4];
            s.e[5] = pack(dc[0..4], 8);
            s.w[5] = pack(dc[4..8], 8);
            s.a[6] = pack(sc[0..5], 2);
        }
    }
    s.w[0] = flags;
    return s;
}

test "retarget reference matches mainnet" {
    // Height 32256: first difficulty change. Height 2016: capped at powLimit.
    try std.testing.expectEqual(@as(u32, 0x1d00d86a), nextWork(0x1d00ffff, 1262152739, 1261130161));
    try std.testing.expectEqual(@as(u32, 0x1d00ffff), nextWork(0x1d00ffff, 1233061996, 1231006505));
}
