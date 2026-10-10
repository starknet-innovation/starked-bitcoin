//! Block commitment (M3a.6 `BLK-COMMIT`, D-038 as amended): witnesses for the `block_undo`,
//! `block_b2msg` and `block_b2s` components (Lean: `Block/Undo.lean`, `Block/B2Msg.lean`,
//! `Block/B2s.lean`). `C = blake2s(undo)`, with `undo = 0x01 ++ records`; the raw block is bound by
//! the public block hash.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const bytes = @import("bytes.zig");
const b2 = @import("../hash/blake2s_air.zig");

pub const undo_json = @embedFile("air:block_undo");
pub const msg_json = @embedFile("air:block_b2msg");
pub const b2s_json = @embedFile("air:block_b2s");

/// Blake2s's initial chaining value (IV with the parameter block for a 32-byte digest).
pub const H0 = blk: {
    var h = b2.IV;
    h[0] ^= 0x01010020;
    break :blk h;
};

/// One stream's blocks: message words, counter, last flag.
pub const Block = struct { m: [16]u32, t: u64, last: bool };

pub fn blocks(a: std.mem.Allocator, data: []const u8) ![]Block {
    const nb = @max(1, (data.len + 63) / 64);
    const out = try a.alloc(Block, nb);
    for (out, 0..) |*b, i| {
        var buf = [_]u8{0} ** 64;
        const lo = 64 * i;
        const hi = @min(data.len, lo + 64);
        if (hi > lo) @memcpy(buf[0 .. hi - lo], data[lo..hi]);
        for (0..16) |k| b.m[k] = std.mem.readInt(u32, buf[4 * k ..][0..4], .little);
        b.last = i + 1 == nb;
        b.t = if (b.last) data.len else 64 * (i + 1);
    }
    return out;
}

/// The chaining values after each block (index `i`: after block `i`).
fn chain(a: std.mem.Allocator, bs: []const Block) ![][8]u32 {
    const hs = try a.alloc([8]u32, bs.len);
    var h = H0;
    for (bs, 0..) |b, i| {
        h = b2.compress(.{ .h = h, .m = b.m, .t = b.t, .f = b.last });
        hs[i] = h;
    }
    return hs;
}

pub fn digest(a: std.mem.Allocator, data: []const u8) ![8]u32 {
    const hs = try chain(a, try blocks(a, data));
    return hs[hs.len - 1];
}

/// The commitment's words: `blake2s(undo)`.
pub fn commitment(a: std.mem.Allocator, undo: []const u8) ![8]u32 {
    return digest(a, undo);
}

/// Public inputs 9–24: the commitment's 16-bit limbs (word `w` low limb first).
pub fn pubLimbs(c: [8]u32) [16]M31 {
    var out: [16]M31 = undefined;
    for (0..8) |w| {
        out[2 * w] = M31.fromCanonical(c[w] & 0xffff);
        out[2 * w + 1] = M31.fromCanonical(c[w] >> 16);
    }
    return out;
}

fn zeros(a: std.mem.Allocator, n_cols: usize, n: usize) ![][]M31 {
    const cols = try a.alloc([]M31, n_cols);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    return cols;
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

pub fn rowsNeeded(undo_len: usize) usize {
    const nb = @max(1, (undo_len + 63) / 64);
    return @max(16 * nb + 1, b2.PERIOD * (nb + 1));
}

/// The walker's columns; appends the undo positions it reads to `undo_reads`.
pub fn msgColumns(a: std.mem.Allocator, log_size: u32, undo: []const u8, undo_reads: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const BLK = 1;
    const POS = 2;
    const B0 = 3;
    const A0 = 7;
    const CNT = 11;
    const LASTF = 12;
    const T = 13;
    const SM = 14;
    const END = 15;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 16, n);
    const nb = @max(1, (undo.len + 63) / 64);
    var r: usize = 0;
    var cnt: usize = 0;
    for (0..nb) |blk| for (0..16) |kw| {
        if (r + 1 >= n) return error.CommitDoesNotFit;
        const pos = 64 * blk + 4 * kw;
        cols[ON][r] = M31.one();
        cols[BLK][r] = f(blk);
        cols[POS][r] = f(pos);
        for (0..4) |j| if (pos + j < undo.len) {
            cols[A0 + j][r] = M31.one();
            cols[B0 + j][r] = f(undo[pos + j]);
            cnt += 1;
            try undo_reads.append(a, @intCast(pos + j));
        };
        cols[CNT][r] = f(cnt);
        const last = blk + 1 == nb;
        cols[LASTF][r] = if (last) M31.one() else M31.zero();
        cols[SM][r] = if (r > 0) M31.one() else M31.zero();
        cols[END][r] = if (last and kw == 15) M31.one() else M31.zero();
        cols[T][r] = if (last) f(undo.len) else f(64 * (blk + 1));
        r += 1;
    };
    // Off rows: block 0, positions by the period, nothing active.
    while (r < n) : (r += 1) {
        cols[POS][r] = f(4 * (r % 16));
        cols[T][r] = f(64);
    }
    return cols;
}

/// The Blake2s component's columns: the stream's blocks from period 0, then unused periods.
pub fn b2sColumns(a: std.mem.Allocator, log_size: u32, undo: []const u8) ![][]M31 {
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
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 312, n);
    const bs = try blocks(a, undo);
    const hs = try chain(a, bs);
    var p: usize = 0;
    while (p * b2.PERIOD < n) : (p += 1) {
        const used = p < bs.len;
        const in: b2.Input = if (used) .{ .h = if (p == 0) H0 else hs[p - 1], .m = bs[p].m, .t = bs[p].t, .f = bs[p].last } else .{ .h = H0, .m = [_]u32{0} ** 16, .t = 0, .f = false };
        const last = used and bs[p].last;
        const base = p * b2.PERIOD;
        b2.fillPeriod(cols, base, n, in);
        for (0..b2.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            cols[BLKI][row] = if (used) f(p) else M31.zero();
            cols[FST][row] = if (used and p == 0) M31.one() else M31.zero();
            cols[NIL][row] = if (used) M31.zero() else M31.one();
            cols[LASTF][row] = if (last) M31.one() else M31.zero();
            cols[T][row] = if (used) f(bs[p].t) else M31.zero();
            cols[CHN][row] = if (used and p > 0) M31.one() else M31.zero();
            cols[USEW][row] = if (used) M31.one() else M31.zero();
            cols[YD][row] = if (last) M31.one() else M31.zero();
            cols[MU0][row] = if (used and q < 16) M31.one() else M31.zero();
            cols[MU1][row] = if (used and q == 0) M31.one() else M31.zero();
            if (q < 16) {
                cols[WLO][row] = f(in.m[q] & 0xffff);
                cols[WHI][row] = f(in.m[q] >> 16);
            }
        }
    }
    return cols;
}

/// The undo table's columns (the byte table's layout).
pub fn undoColumns(a: std.mem.Allocator, log_size: u32, undo: []const u8, reads: []const u32) ![][]M31 {
    return bytes.generate(a, log_size, undo, reads);
}

test "block commitment: the spec's commitment matches std Blake2s" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    // The empty stream, the version byte alone, an exact block and one short of it.
    const z = [_]u8{0} ** 64;
    for ([_][]const u8{ &.{}, &[_]u8{1}, &z, z[0..63], @embedFile("testdata:block_0") }) |data| {
        var d: [32]u8 = undefined;
        std.crypto.hash.blake2.Blake2s256.hash(data, &d, .{});
        const dw = try commitment(a, data);
        for (0..8) |w| try std.testing.expectEqual(std.mem.readInt(u32, d[4 * w ..][0..4], .little), dw[w]);
    }
}

test "block commitment: a 3-block undo stream satisfies and balances; a wrong public limb is rejected" {
    const bsys = @import("system.zig");
    const checks = @import("checks.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const s = checks.samples_small[1];
    var undo: [150]u8 = undefined;
    undo[0] = 1;
    for (undo[1..], 1..) |*x, i| x.* = @truncate(i *% 37 +% 11);
    var b = try bsys.buildU(a, s.raw, &undo, s.ctx);
    try std.testing.expect((try bsys.firstViolation(a, &airs, &b)) == null);
    try std.testing.expect((try bsys.unbalanced(a, &airs, &b)) == null);
    try std.testing.expectEqualSlices(u32, &(try commitment(a, &undo)), &b.commitment_words);
    // The public limbs enter by a lookup: a wrong one leaves the digest relation unbalanced.
    b.pubs[9 + 5] = b.pubs[9 + 5].add(M31.one());
    try std.testing.expect((try bsys.unbalanced(a, &airs, &b)) != null);
}
