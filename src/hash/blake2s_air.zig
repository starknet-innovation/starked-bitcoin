//! Witness generation for the Blake2s compression AIR (Lean: `Gadgets/Blake2s.lean`; layout in
//! that file's header). One compression per 88-row period; a final partial period repeats the
//! last compression so that every row's constraints hold.

const std = @import("std");
const ir = @import("../air/ir.zig");
const M31 = @import("stwo_core").fields.m31.M31;

pub const lean_json = @embedFile("air:blake2s_compress");
pub const PERIOD: usize = 88;
pub const N_MAIN: usize = 300;

pub const IV = [8]u32{ 0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19 };
const SIGMA = [10][16]u8{
    .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
    .{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
    .{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
    .{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
    .{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
    .{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
    .{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
    .{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
    .{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
    .{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
};
pub const G_IDX = [8][4]u8{ .{ 0, 4, 8, 12 }, .{ 1, 5, 9, 13 }, .{ 2, 6, 10, 14 }, .{ 3, 7, 11, 15 }, .{ 0, 5, 10, 15 }, .{ 1, 6, 11, 12 }, .{ 2, 7, 8, 13 }, .{ 3, 4, 9, 14 } };
/// Output word slot of role a, b, c, d.
const OUT_W = [4]usize{ 4, 7, 6, 5 };

pub const Input = struct {
    h: [8]u32,
    m: [16]u32,
    t: u64,
    f: bool,
};

/// The RFC 7693 compression function (reference for tests).
pub fn compress(in: Input) [8]u32 {
    var v: [16]u32 = undefined;
    @memcpy(v[0..8], &in.h);
    @memcpy(v[8..16], &IV);
    v[12] ^= @truncate(in.t);
    v[13] ^= @truncate(in.t >> 32);
    if (in.f) v[14] ^= 0xffffffff;
    for (0..10) |r| for (0..8) |g| {
        const ix = G_IDX[g];
        const o = mix(v[ix[0]], v[ix[1]], v[ix[2]], v[ix[3]], in.m[SIGMA[r][2 * g]], in.m[SIGMA[r][2 * g + 1]]);
        v[ix[0]] = o.a2;
        v[ix[1]] = o.b2;
        v[ix[2]] = o.c2;
        v[ix[3]] = o.d2;
    };
    var out: [8]u32 = undefined;
    for (&out, 0..) |*w, i| w.* = in.h[i] ^ v[i] ^ v[i + 8];
    return out;
}

const Mix = struct { a1: u32, d1: u32, c1: u32, b1: u32, a2: u32, d2: u32, c2: u32, b2: u32 };

fn mix(a: u32, b: u32, c: u32, d: u32, x: u32, y: u32) Mix {
    const a1 = a +% b +% x;
    const d1 = std.math.rotr(u32, d ^ a1, 16);
    const c1 = c +% d1;
    const b1 = std.math.rotr(u32, b ^ c1, 12);
    const a2 = a1 +% b1 +% y;
    const d2 = std.math.rotr(u32, d1 ^ a2, 8);
    const c2 = c1 +% d2;
    const b2 = std.math.rotr(u32, b1 ^ c2, 7);
    return .{ .a1 = a1, .d1 = d1, .c1 = c1, .b1 = b1, .a2 = a2, .d2 = d2, .c2 = c2, .b2 = b2 };
}

fn setWord(cols: [][]M31, row: usize, slot: usize, w: u32) void {
    for (0..32) |i| cols[32 * slot + i][row] = M31.fromCanonical((w >> @intCast(i)) & 1);
}

fn setBits(cols: [][]M31, row: usize, base: usize, v: u32, n: usize) void {
    for (0..n) |i| cols[base + i][row] = M31.fromCanonical((v >> @intCast(i)) & 1);
}

/// Carries of `Σ terms` over 16-bit limbs: (lo carry, hi carry).
fn carries(terms: []const u32) [2]u32 {
    var lo: u32 = 0;
    var hi: u32 = 0;
    for (terms) |t| {
        lo += t & 0xffff;
        hi += t >> 16;
    }
    const clo = lo >> 16;
    return .{ clo, (hi + clo) >> 16 };
}

/// Fills one period starting at `base` (rows past `n` are skipped).
pub fn fillPeriod(cols: [][]M31, base: usize, n: usize, in: Input) void {
    const put = struct {
        fn word(c: [][]M31, nn: usize, row: usize, slot: usize, w: u32) void {
            if (row < nn) setWord(c, row, slot, w);
        }
    }.word;
    for (0..PERIOD) |p| {
        const row = base + p;
        if (row >= n) break;
        for (0..16) |k| {
            cols[256 + 2 * k][row] = M31.fromCanonical(in.m[k] & 0xffff);
            cols[256 + 2 * k + 1][row] = M31.fromCanonical(in.m[k] >> 16);
        }
    }
    var v: [16]u32 = undefined;
    @memcpy(v[0..8], &in.h);
    @memcpy(v[8..16], &IV);
    v[12] ^= @truncate(in.t);
    v[13] ^= @truncate(in.t >> 32);
    if (in.f) v[14] ^= 0xffffffff;
    // Init rows: the state in diagonal layout; row 0 also t_lo, t_hi, f.
    for (0..4) |k| for (0..4) |role| put(cols, n, base + k, OUT_W[role], v[G_IDX[4 + k][role]]);
    put(cols, n, base, 0, @truncate(in.t));
    put(cols, n, base, 1, @truncate(in.t >> 32));
    put(cols, n, base, 2, @intFromBool(in.f));
    // G rows.
    for (0..80) |j| {
        const r = j / 8;
        const g = j % 8;
        const row = base + 4 + j;
        const ix = G_IDX[g];
        const x = in.m[SIGMA[r][2 * g]];
        const y = in.m[SIGMA[r][2 * g + 1]];
        const a = v[ix[0]];
        const b = v[ix[1]];
        const c = v[ix[2]];
        const o = mix(a, b, c, v[ix[3]], x, y);
        v[ix[0]] = o.a2;
        v[ix[1]] = o.b2;
        v[ix[2]] = o.c2;
        v[ix[3]] = o.d2;
        if (row >= n) continue;
        for ([8]u32{ o.a1, o.d1, o.c1, o.b1, o.a2, o.d2, o.c2, o.b2 }, 0..) |w, slot| setWord(cols, row, slot, w);
        const ca1 = carries(&.{ a, b, x });
        const cc1 = carries(&.{ c, o.d1 });
        const ca2 = carries(&.{ o.a1, o.b1, y });
        const cc2 = carries(&.{ o.c1, o.d2 });
        setBits(cols, row, 288, ca1[0], 2);
        setBits(cols, row, 290, ca1[1], 2);
        setBits(cols, row, 292, cc1[0], 1);
        setBits(cols, row, 293, cc1[1], 1);
        setBits(cols, row, 294, ca2[0], 2);
        setBits(cols, row, 296, ca2[1], 2);
        setBits(cols, row, 298, cc2[0], 1);
        setBits(cols, row, 299, cc2[1], 1);
    }
    // Final rows: words k and b(4+k).
    for (0..4) |k| {
        const bk = G_IDX[4 + k][1];
        put(cols, n, base + 84 + k, 2, in.h[k] ^ v[k]);
        put(cols, n, base + 84 + k, 0, in.h[k] ^ v[k] ^ v[k + 8]);
        put(cols, n, base + 84 + k, 3, in.h[bk] ^ v[bk]);
        put(cols, n, base + 84 + k, 1, in.h[bk] ^ v[bk] ^ v[bk + 8]);
    }
}

/// Main trace (natural row order) for `inputs`, one per period, the last repeated to fill
/// `2^log_size` rows.
pub fn generate(allocator: std.mem.Allocator, log_size: u32, inputs: []const Input) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (inputs.len == 0 or inputs.len * PERIOD > n) return error.TooManyCompressions;
    const cols = try allocator.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try allocator.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    var p: usize = 0;
    while (p * PERIOD < n) : (p += 1) fillPeriod(cols, p * PERIOD, n, inputs[@min(p, inputs.len - 1)]);
    return cols;
}

/// Output words of period `p`.
pub fn outputAt(cols: []const []const M31, p: usize) [8]u32 {
    var out: [8]u32 = undefined;
    for (0..4) |k| {
        const bk = G_IDX[4 + k][1];
        out[k] = wordAt(cols, p * PERIOD + 84 + k, 0);
        out[bk] = wordAt(cols, p * PERIOD + 84 + k, 1);
    }
    return out;
}

fn wordAt(cols: []const []const M31, row: usize, slot: usize) u32 {
    var w: u32 = 0;
    for (0..32) |i| w |= cols[32 * slot + i][row].toU32() << @intCast(i);
    return w;
}

test "Blake2s AIR (Lean export): the witness satisfies it and outputs RFC 7693 compressions" {
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;

    // A 64-byte message hashed in one block: h = IV ^ params, t = 64, final.
    var msg: [64]u8 = undefined;
    for (&msg, 0..) |*b, i| b.* = @intCast(i);
    var h0 = IV;
    h0[0] ^= 0x01010020;
    var m: [16]u32 = undefined;
    for (&m, 0..) |*w, i| w.* = std.mem.readInt(u32, msg[4 * i ..][0..4], .little);
    var prng = std.Random.DefaultPrng.init(3);
    var other: Input = .{ .h = undefined, .m = undefined, .t = prng.random().int(u64), .f = false };
    for (&other.h) |*w| w.* = prng.random().int(u32);
    for (&other.m) |*w| w.* = prng.random().int(u32);
    const inputs = [_]Input{ .{ .h = h0, .m = m, .t = 64, .f = true }, other };

    const log_size: u32 = 8;
    const cols = try generate(a, log_size, &inputs);
    const trace = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)), .main = @ptrCast(cols) };
    if (try interp.firstViolation(a, air, trace)) |v| {
        std.debug.print("violation: row {d} (period row {d}), constraint {d}\n", .{ v.row, v.row % PERIOD, v.constraint });
        return error.ConstraintViolated;
    }
    // Period 0 is Blake2s-256 of the message (the digest is the output words, little-endian).
    var want: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&msg, &want, .{});
    const got = outputAt(@ptrCast(cols), 0);
    for (got, 0..) |w, i| try std.testing.expectEqual(std.mem.readInt(u32, want[4 * i ..][0..4], .little), w);
    try std.testing.expectEqualSlices(u32, &compress(other), &outputAt(@ptrCast(cols), 1));

    // A flipped output bit, or a flipped message limb, violates the AIR.
    cols[3][84] = M31.one().sub(cols[3][84]);
    try std.testing.expect(try interp.firstViolation(a, air, trace) != null);
    cols[3][84] = M31.one().sub(cols[3][84]);
    cols[256][10] = cols[256][10].add(M31.one());
    try std.testing.expect(try interp.firstViolation(a, air, trace) != null);
    cols[256][10] = cols[256][10].sub(M31.one());

    // It proves and verifies (recursion profile, test-strength FRI).
    const prove_base = @import("../air/prove.zig");
    const prove_rec = @import("../air/prove_rec.zig");
    const cfg = prove_rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const statement = prove_base.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    try prove_rec.verify(a, cfg, air, log_size, &.{}, try prove_rec.prove(E, a, cfg, statement, @ptrCast(cols)));
}
