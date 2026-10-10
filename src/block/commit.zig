//! Block commitment (M3a.6 `BLK-COMMIT`, D-038): witnesses for the `block_undo`, `block_b2msg` and
//! `block_b2s` components (Lean: `Block/Undo.lean`, `Block/B2Msg.lean`, `Block/B2s.lean`).
//! `C = blake2s(blake2s(raw) ++ blake2s(undo))`, with `undo = 0x01 ++ records`.

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

/// The commitment's words: `blake2s(blake2s(raw) ++ blake2s(undo))`.
pub fn commitment(a: std.mem.Allocator, raw: []const u8, undo: []const u8) ![8]u32 {
    const d0 = try digest(a, raw);
    const d1 = try digest(a, undo);
    var m: [16]u32 = undefined;
    @memcpy(m[0..8], &d0);
    @memcpy(m[8..16], &d1);
    return b2.compress(.{ .h = H0, .m = m, .t = 64, .f = true });
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

pub fn rowsNeeded(raw_len: usize, undo_len: usize) usize {
    const nb = @max(1, (raw_len + 63) / 64) + @max(1, (undo_len + 63) / 64);
    return @max(16 * nb + 1, b2.PERIOD * (nb + 2));
}

/// The walker's columns; appends the positions it reads to `raw_reads` and `undo_reads`.
pub fn msgColumns(a: std.mem.Allocator, log_size: u32, raw: []const u8, undo: []const u8, raw_reads: *std.ArrayList(u32), undo_reads: *std.ArrayList(u32)) ![][]M31 {
    const ON = 0;
    const STR = 1;
    const BLK = 2;
    const POS = 3;
    const B0 = 4;
    const A0 = 8;
    const CNT = 12;
    const LASTF = 13;
    const NEWS = 14;
    const T = 15;
    const SM = 16;
    const END = 17;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 18, n);
    var r: usize = 0;
    for ([2][]const u8{ raw, undo }, 0..) |data, s| {
        const nb = @max(1, (data.len + 63) / 64);
        var cnt: usize = 0;
        for (0..nb) |blk| for (0..16) |kw| {
            if (r + 1 >= n) return error.CommitDoesNotFit;
            const pos = 64 * blk + 4 * kw;
            cols[ON][r] = M31.one();
            cols[STR][r] = f(s);
            cols[BLK][r] = f(blk);
            cols[POS][r] = f(pos);
            for (0..4) |j| if (pos + j < data.len) {
                cols[A0 + j][r] = M31.one();
                cols[B0 + j][r] = f(data[pos + j]);
                cnt += 1;
                try (if (s == 0) raw_reads else undo_reads).append(a, @intCast(pos + j));
            };
            cols[CNT][r] = f(cnt);
            const last = blk + 1 == nb;
            cols[LASTF][r] = if (last) M31.one() else M31.zero();
            cols[NEWS][r] = if (s == 1 and blk == 0 and kw == 0) M31.one() else M31.zero();
            cols[SM][r] = if (r > 0 and !(s == 1 and blk == 0 and kw == 0)) M31.one() else M31.zero();
            cols[END][r] = if (last and kw == 15) M31.one() else M31.zero();
            cols[T][r] = if (last) f(data.len) else f(64 * (blk + 1));
            r += 1;
        };
    }
    // Off rows: stream 1, block 0, positions by the period, nothing active.
    while (r < n) : (r += 1) {
        cols[STR][r] = M31.one();
        cols[POS][r] = f(4 * (r % 16));
        cols[T][r] = f(64);
    }
    return cols;
}

/// The Blake2s component's columns: period 0 is the outer hash, then stream 0's and stream 1's
/// blocks, then unused periods.
pub fn b2sColumns(a: std.mem.Allocator, log_size: u32, raw: []const u8, undo: []const u8) ![][]M31 {
    const STR = 300;
    const BLKI = 301;
    const FST = 302;
    const NIL = 303;
    const LASTF = 304;
    const T = 305;
    const WLO = 306;
    const WHI = 307;
    const CHN = 308;
    const USEW = 309;
    const YD = 310;
    const TV = 311;
    const FV = 312;
    const OQ = 313;
    const MU0 = 314;
    const MU1 = 315;
    const MU2 = 316;
    const n = @as(usize, 1) << @intCast(log_size);
    const cols = try zeros(a, 317, n);
    const Per = struct { in: b2.Input, str: u32, blki: u32, fst: bool, nil: bool, last: bool, t: u64, outer: bool };
    var pers = std.ArrayList(Per).empty;
    const s0 = try blocks(a, raw);
    const s1 = try blocks(a, undo);
    const h0s = try chain(a, s0);
    const h1s = try chain(a, s1);
    var m: [16]u32 = undefined;
    @memcpy(m[0..8], &h0s[h0s.len - 1]);
    @memcpy(m[8..16], &h1s[h1s.len - 1]);
    try pers.append(a, .{ .in = .{ .h = H0, .m = m, .t = 64, .f = true }, .str = 0, .blki = 0, .fst = false, .nil = false, .last = false, .t = 0, .outer = true });
    for ([2][]const Block{ s0, s1 }, [2][][8]u32{ h0s, h1s }, 0..) |bs, hs, s| for (bs, 0..) |b, i| {
        const h = if (i == 0) H0 else hs[i - 1];
        try pers.append(a, .{ .in = .{ .h = h, .m = b.m, .t = b.t, .f = b.last }, .str = @intCast(s), .blki = @intCast(i), .fst = i == 0, .nil = false, .last = b.last, .t = b.t, .outer = false });
    };
    const nil: Per = .{ .in = .{ .h = H0, .m = [_]u32{0} ** 16, .t = 0, .f = false }, .str = 0, .blki = 0, .fst = false, .nil = true, .last = false, .t = 0, .outer = false };
    var p: usize = 0;
    while (p * b2.PERIOD < n) : (p += 1) {
        const x = if (p < pers.items.len) pers.items[p] else nil;
        const base = p * b2.PERIOD;
        b2.fillPeriod(cols, base, n, x.in);
        const usew = !x.nil and !x.outer;
        for (0..b2.PERIOD) |q| {
            const row = base + q;
            if (row >= n) break;
            cols[STR][row] = f(x.str);
            cols[BLKI][row] = f(x.blki);
            cols[FST][row] = if (x.fst) M31.one() else M31.zero();
            cols[NIL][row] = if (x.nil) M31.one() else M31.zero();
            cols[LASTF][row] = if (x.last) M31.one() else M31.zero();
            cols[T][row] = f(x.t);
            cols[CHN][row] = if (usew and !x.fst) M31.one() else M31.zero();
            cols[USEW][row] = if (usew) M31.one() else M31.zero();
            cols[YD][row] = if (usew and x.last) M31.one() else M31.zero();
            cols[TV][row] = if (x.outer) f(64) else f(x.t);
            cols[FV][row] = if (x.outer or x.last) M31.one() else M31.zero();
            cols[OQ][row] = if (p == 0) M31.one() else M31.zero();
            cols[MU0][row] = if (usew and q < 16) M31.one() else M31.zero();
            cols[MU1][row] = if (x.outer and q < 16) M31.one() else M31.zero();
            cols[MU2][row] = if (usew and q == 0) M31.one() else M31.zero();
            if (q < 16) {
                cols[WLO][row] = f(x.in.m[q] & 0xffff);
                cols[WHI][row] = f(x.in.m[q] >> 16);
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
    const raw = @embedFile("testdata:block_0");
    const undo = [_]u8{1};
    var d0: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(raw, &d0, .{});
    var d1: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&undo, &d1, .{});
    var both: [64]u8 = undefined;
    @memcpy(both[0..32], &d0);
    @memcpy(both[32..64], &d1);
    var c: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&both, &c, .{});
    const words = try commitment(a, raw, &undo);
    for (0..8) |w| try std.testing.expectEqual(std.mem.readInt(u32, c[4 * w ..][0..4], .little), words[w]);
    // The empty stream and a 64-byte stream (exact block) as well.
    const z = [_]u8{0} ** 64;
    for ([_][]const u8{ &.{}, &z, z[0..63] }) |data| {
        var d: [32]u8 = undefined;
        std.crypto.hash.blake2.Blake2s256.hash(data, &d, .{});
        const dw = try digest(a, data);
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
    try std.testing.expectEqualSlices(u32, &(try commitment(a, s.raw, &undo)), &b.commitment_words);
    b.pubs[9 + 5] = b.pubs[9 + 5].add(M31.one());
    const v = (try bsys.firstViolation(a, &airs, &b)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 11), v.comp);
}
