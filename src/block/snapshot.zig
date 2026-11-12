//! Bitcoin Core's UTXO snapshot files (`dumptxoutset`, loaded by `loadtxoutset`), read coin by coin so a
//! mainnet snapshot (~9 GB, ~165 M coins) is never held in memory. The format is Core's
//! (`node/utxo_snapshot.h`, `rpc/blockchain.cpp` `WriteUTXOSnapshot`, `validation.cpp`
//! `PopulateAndValidateSnapshot`, `compressor.cpp`):
//!
//!   metadata: "utxo" 0xff, version (LE16, = 2), network magic (4), base block hash (32), coin count (LE64)
//!   then groups: txid (32), CompactSize n, n × (CompactSize vout, Coin)
//!   Coin: VARINT(height·2 + coinbase), VARINT(CompressAmount(value)), compressed script
//!
//! `scan` decompresses each coin and computes what the set's proven facts are compared with: the count, the
//! total amount and Core's `hash_serialized` (SHA256d over each coin's `TxOutSer`, as `set_file.scan`).
//! It also applies the loader's checks (no coin above the base height, `vout` below 2^32 − 1, values in
//! money range, the count as announced, no trailing bytes) and requires the coins strictly sorted by
//! (txid, vout), which is the order `dumptxoutset` writes (the coins database's key order).

const std = @import("std");
const Sha256 = std.crypto.hash.sha2.Sha256;
const Secp256k1 = std.crypto.ecc.Secp256k1;

pub const magic = [5]u8{ 'u', 't', 'x', 'o', 0xff };
pub const version: u16 = 2;
pub const mainnet_magic = [4]u8{ 0xf9, 0xbe, 0xb4, 0xd9 };
const max_money: u64 = 21_000_000 * 100_000_000;
const max_script_size = 10_000;
const n_special = 6;

pub const Meta = struct { network: [4]u8, base: [32]u8, count: u64 };
pub const Info = struct { meta: Meta, count: u64, amount: u64, hash: [32]u8, max_height: u32 };

pub const Error = error{ BadMagic, UnsupportedVersion, BadVarInt, BadCompactSize, CountMismatch, TrailingBytes, CoinAboveBase, BadVout, BadAmount, NotSorted };

const In = *std.Io.Reader;

fn varInt(r: In) !u64 {
    // Core's VARINT (serialize.h ReadVarInt): base 128, most significant group first, each continuation adds 1.
    var n: u64 = 0;
    while (true) {
        const b = try r.takeByte();
        if (n > (std.math.maxInt(u64) >> 7)) return error.BadVarInt;
        n = (n << 7) | (b & 0x7f);
        if (b & 0x80 == 0) return n;
        if (n == std.math.maxInt(u64)) return error.BadVarInt;
        n += 1;
    }
}

fn compactSize(r: In) !u64 {
    const b = try r.takeByte();
    const n: u64 = switch (b) {
        0xfd => try r.takeInt(u16, .little),
        0xfe => try r.takeInt(u32, .little),
        0xff => try r.takeInt(u64, .little),
        else => return b,
    };
    // Canonical encodings only (ReadCompactSize's "non-canonical" errors), and Core's MAX_SIZE.
    const min: u64 = switch (b) {
        0xfd => 0xfd,
        0xfe => 0x10000,
        else => 0x100000000,
    };
    if (n < min or n > 0x02000000) return error.BadCompactSize;
    return n;
}

/// Core's `DecompressAmount`.
pub fn decompressAmount(x0: u64) u64 {
    if (x0 == 0) return 0;
    var x = x0 - 1;
    var e = x % 10;
    x /= 10;
    var n: u64 = undefined;
    if (e < 9) {
        const d = (x % 9) + 1;
        x /= 9;
        n = x *% 10 +% d;
    } else n = x +% 1;
    while (e > 0) : (e -= 1) n *%= 10;
    return n;
}

/// Core's `CompressAmount` (for writing test snapshots).
pub fn compressAmount(n0: u64) u64 {
    if (n0 == 0) return 0;
    var n = n0;
    var e: u64 = 0;
    while (n % 10 == 0 and e < 9) : (e += 1) n /= 10;
    if (e < 9) {
        const d = n % 10;
        n /= 10;
        return 1 + (n * 9 + d - 1) * 10 + e;
    }
    return 1 + (n - 1) * 10 + 9;
}

/// Appends a coin's script, decompressed as Core's `ScriptCompression::Unser` does, to `out` (after the
/// CompactSize of its length).
fn readScript(r: In, out: *std.ArrayListUnmanaged(u8), gpa: std.mem.Allocator) !void {
    const n = try varInt(r);
    var s: [67]u8 = undefined;
    var script: []const u8 = undefined;
    if (n < n_special) {
        var v: [32]u8 = undefined;
        const len: usize = if (n < 2) 20 else 32;
        try r.readSliceAll(v[0..len]);
        switch (n) {
            0 => {
                s[0..3].* = .{ 0x76, 0xa9, 20 };
                @memcpy(s[3..23], v[0..20]);
                s[23..25].* = .{ 0x88, 0xac };
                script = s[0..25];
            },
            1 => {
                s[0..2].* = .{ 0xa9, 20 };
                @memcpy(s[2..22], v[0..20]);
                s[22] = 0x87;
                script = s[0..23];
            },
            2, 3 => {
                s[0..2].* = .{ 33, @intCast(n) };
                @memcpy(s[2..34], &v);
                s[34] = 0xac;
                script = s[0..35];
            },
            else => {
                var c: [33]u8 = undefined;
                c[0] = @intCast(n - 2);
                @memcpy(c[1..], &v);
                // Core leaves the script empty when the point does not decompress (never written so:
                // `CompressScript` takes this form only for a fully valid key).
                if (Secp256k1.fromSec1(&c)) |p| {
                    s[0] = 65;
                    s[1..66].* = p.toUncompressedSec1();
                    s[66] = 0xac;
                    script = s[0..67];
                } else |_| script = s[0..0];
            },
        }
        try appendScript(out, gpa, script);
        return;
    }
    const len = n - n_special;
    if (len > max_script_size) {
        // Core: "Overly long script, replace with a short invalid one".
        try r.discardAll64(len);
        try appendScript(out, gpa, &.{0x6a});
        return;
    }
    var hdr: [9]u8 = undefined;
    const h = putCompactSize(&hdr, len);
    try out.appendSlice(gpa, h);
    const at = out.items.len;
    try out.resize(gpa, at + len);
    try r.readSliceAll(out.items[at..]);
}

fn putCompactSize(buf: *[9]u8, n: u64) []const u8 {
    if (n < 0xfd) {
        buf[0] = @intCast(n);
        return buf[0..1];
    } else if (n <= 0xffff) {
        buf[0] = 0xfd;
        std.mem.writeInt(u16, buf[1..3], @intCast(n), .little);
        return buf[0..3];
    } else if (n <= 0xffffffff) {
        buf[0] = 0xfe;
        std.mem.writeInt(u32, buf[1..5], @intCast(n), .little);
        return buf[0..5];
    }
    buf[0] = 0xff;
    std.mem.writeInt(u64, buf[1..9], n, .little);
    return buf[0..9];
}

fn appendScript(out: *std.ArrayListUnmanaged(u8), gpa: std.mem.Allocator, script: []const u8) !void {
    var hdr: [9]u8 = undefined;
    try out.appendSlice(gpa, putCompactSize(&hdr, script.len));
    try out.appendSlice(gpa, script);
}

pub fn readMeta(r: In) !Meta {
    var m: [5]u8 = undefined;
    try r.readSliceAll(&m);
    if (!std.mem.eql(u8, &m, &magic)) return error.BadMagic;
    if (try r.takeInt(u16, .little) != version) return error.UnsupportedVersion;
    var meta: Meta = undefined;
    try r.readSliceAll(&meta.network);
    try r.readSliceAll(&meta.base);
    meta.count = try r.takeInt(u64, .little);
    return meta;
}

/// Reads a whole snapshot from `r`: the metadata, then every coin, checked and hashed. `base_height` is
/// the height of the block the snapshot is after (Core rejects a coin above it).
pub fn scanReader(gpa: std.mem.Allocator, r: In, base_height: u32) !Info {
    const meta = try readMeta(r);
    var hs = Sha256.init(.{});
    var ser: std.ArrayListUnmanaged(u8) = .empty;
    defer ser.deinit(gpa);
    var left = meta.count;
    var amount: u64 = 0;
    var max_height: u32 = 0;
    var prev: ?struct { txid: [32]u8, vout: u32 } = null;
    while (left > 0) {
        var txid: [32]u8 = undefined;
        try r.readSliceAll(&txid);
        const n = try compactSize(r);
        if (n > left) return error.CountMismatch;
        for (0..n) |_| {
            const vout64 = try compactSize(r);
            if (vout64 >= std.math.maxInt(u32)) return error.BadVout;
            const vout: u32 = @intCast(vout64);
            const code = try varInt(r);
            if (code > std.math.maxInt(u32)) return error.BadVarInt;
            const height: u32 = @intCast(code >> 1);
            if (height > base_height) return error.CoinAboveBase;
            const value = decompressAmount(try varInt(r));
            if (value > max_money) return error.BadAmount;
            if (prev) |p| {
                const o = std.mem.order(u8, &p.txid, &txid);
                if (!(o == .lt or (o == .eq and p.vout < vout))) return error.NotSorted;
            }
            prev = .{ .txid = txid, .vout = vout };
            ser.clearRetainingCapacity();
            var vb: [8]u8 = undefined;
            std.mem.writeInt(u64, &vb, value, .little);
            try ser.appendSlice(gpa, &vb);
            try readScript(r, &ser, gpa);
            var b: [8]u8 = undefined;
            hs.update(&txid);
            std.mem.writeInt(u32, b[0..4], vout, .little);
            std.mem.writeInt(u32, b[4..8], @intCast(code), .little);
            hs.update(&b);
            hs.update(ser.items);
            amount += value;
            max_height = @max(max_height, height);
        }
        left -= n;
    }
    if (r.takeByte()) |_| return error.TrailingBytes else |e| if (e != error.EndOfStream) return e;
    var info = Info{ .meta = meta, .count = meta.count, .amount = amount, .hash = undefined, .max_height = max_height };
    var h1: [32]u8 = undefined;
    hs.final(&h1);
    Sha256.hash(&h1, &info.hash, .{});
    std.mem.reverse(u8, &info.hash);
    return info;
}

pub fn scan(gpa: std.mem.Allocator, path: []const u8, base_height: u32) !Info {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const buf = try gpa.alloc(u8, 1 << 20);
    defer gpa.free(buf);
    var fr = file.reader(buf);
    return scanReader(gpa, &fr.interface, base_height);
}

/// The metadata only (the base block hash names the height the caller must check against).
pub fn readMetaFile(path: []const u8) !Meta {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    var buf: [64]u8 = undefined;
    var fr = file.reader(&buf);
    return readMeta(&fr.interface);
}

// ---- writing (tests): a set file's coins as a snapshot, scripts stored uncompressed ----

fn putVarInt(w: *std.ArrayListUnmanaged(u8), gpa: std.mem.Allocator, n0: u64) !void {
    var tmp: [10]u8 = undefined;
    var len: usize = 0;
    var n = n0;
    while (true) : (len += 1) {
        tmp[len] = @as(u8, @truncate(n & 0x7f)) | (if (len > 0) @as(u8, 0x80) else 0);
        if (n <= 0x7f) break;
        n = (n >> 7) - 1;
    }
    var i = len + 1;
    while (i > 0) : (i -= 1) try w.append(gpa, tmp[i - 1]);
}

pub const TestCoin = struct { txid: [32]u8, vout: u32, height: u32, cb: bool, ser: []const u8 };

/// A snapshot of `coins` (sorted by (txid, vout)), each script in Core's raw form (`nSize = len + 6`).
pub fn encode(gpa: std.mem.Allocator, network: [4]u8, base: [32]u8, coins: []const TestCoin) ![]u8 {
    var w: std.ArrayListUnmanaged(u8) = .empty;
    errdefer w.deinit(gpa);
    try w.appendSlice(gpa, &magic);
    var b: [8]u8 = undefined;
    std.mem.writeInt(u16, b[0..2], version, .little);
    try w.appendSlice(gpa, b[0..2]);
    try w.appendSlice(gpa, &network);
    try w.appendSlice(gpa, &base);
    std.mem.writeInt(u64, &b, coins.len, .little);
    try w.appendSlice(gpa, &b);
    var i: usize = 0;
    while (i < coins.len) {
        var j = i;
        while (j < coins.len and std.mem.eql(u8, &coins[j].txid, &coins[i].txid)) j += 1;
        try w.appendSlice(gpa, &coins[i].txid);
        var hdr: [9]u8 = undefined;
        try w.appendSlice(gpa, putCompactSize(&hdr, j - i));
        for (coins[i..j]) |c| {
            try w.appendSlice(gpa, putCompactSize(&hdr, c.vout));
            try putVarInt(&w, gpa, 2 * @as(u64, c.height) + @intFromBool(c.cb));
            try putVarInt(&w, gpa, compressAmount(std.mem.readInt(u64, c.ser[0..8], .little)));
            // The script after its CompactSize length.
            var fr = std.Io.Reader.fixed(c.ser[8..]);
            const len = try compactSize(&fr);
            try putVarInt(&w, gpa, len + n_special);
            try w.appendSlice(gpa, c.ser[8 + fr.seek ..][0..len]);
        }
        i = j;
    }
    return w.toOwnedSlice(gpa);
}

const testing = std.testing;

test "snapshot: amount compression round-trips and matches Core's examples" {
    // compressor_tests.cpp: CompressAmount(0) = 0, 1 → 0x1, CENT → 0x7, COIN → 0x9, 50 BTC → 0x32, 21M BTC → 0x1406f40.
    const cases = [_][2]u64{ .{ 0, 0 }, .{ 1, 1 }, .{ 1_000_000, 7 }, .{ 100_000_000, 9 }, .{ 5_000_000_000, 0x32 }, .{ max_money, 0x1406f40 } };
    for (cases) |c| {
        try testing.expectEqual(c[1], compressAmount(c[0]));
        try testing.expectEqual(c[0], decompressAmount(c[1]));
    }
    var x: u64 = 1;
    while (x < max_money) : (x = x * 7 + 3) try testing.expectEqual(x, decompressAmount(compressAmount(x)));
}

test "snapshot: VARINT matches Core's encoding" {
    // serialize_tests.cpp varints: 0 → 00, 127 → 7f, 128 → 80 00, 255 → 80 7f, 16383 → fe 7f, 16384 → ff 00.
    const cases = .{ .{ 0, "\x00" }, .{ 127, "\x7f" }, .{ 128, "\x80\x00" }, .{ 255, "\x80\x7f" }, .{ 16383, "\xfe\x7f" }, .{ 16384, "\xff\x00" } };
    inline for (cases) |c| {
        var w: std.ArrayListUnmanaged(u8) = .empty;
        defer w.deinit(testing.allocator);
        try putVarInt(&w, testing.allocator, c[0]);
        try testing.expectEqualSlices(u8, c[1], w.items);
        var r = std.Io.Reader.fixed(c[1]);
        try testing.expectEqual(@as(u64, c[0]), try varInt(&r));
    }
}

test "snapshot: special scripts decompress to Core's templates" {
    const a = testing.allocator;
    var out: std.ArrayListUnmanaged(u8) = .empty;
    defer out.deinit(a);
    // P2PKH
    var r0 = std.Io.Reader.fixed("\x00" ++ "\x11" ** 20);
    try readScript(&r0, &out, a);
    try testing.expectEqualSlices(u8, "\x19\x76\xa9\x14" ++ "\x11" ** 20 ++ "\x88\xac", out.items);
    out.clearRetainingCapacity();
    // P2SH
    var r1 = std.Io.Reader.fixed("\x01" ++ "\x22" ** 20);
    try readScript(&r1, &out, a);
    try testing.expectEqualSlices(u8, "\x17\xa9\x14" ++ "\x22" ** 20 ++ "\x87", out.items);
    out.clearRetainingCapacity();
    // Uncompressed P2PK of the generator G (x = 79be…, y even → type 4).
    const gx = Secp256k1.basePoint.affineCoordinates().x.toBytes(.big);
    var r4 = std.Io.Reader.fixed("\x04" ++ gx);
    try readScript(&r4, &out, a);
    try testing.expectEqual(@as(usize, 68), out.items.len);
    try testing.expectEqualSlices(u8, "\x43\x41\x04", out.items[0..3]);
    try testing.expectEqualSlices(u8, &Secp256k1.basePoint.toUncompressedSec1(), out.items[2..67]);
    try testing.expectEqual(@as(u8, 0xac), out.items[67]);
    out.clearRetainingCapacity();
    // Raw script: nSize = len + 6.
    var rr = std.Io.Reader.fixed("\x09\x51\x52\x53");
    try readScript(&rr, &out, a);
    try testing.expectEqualSlices(u8, "\x03\x51\x52\x53", out.items);
}

test "snapshot: a set file written as a snapshot scans to the set file's facts; tampering is rejected" {
    const SF = @import("set_file.zig");
    const a = testing.allocator;
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const aa = arena.allocator();
    const path = "data/epoch/set-1000.bin";
    const want = SF.scan(a, path, null) catch return error.SkipZigTest;
    var rd: SF.Reader = undefined;
    try rd.init(a, path);
    defer rd.deinit();
    var coins: std.ArrayListUnmanaged(TestCoin) = .empty;
    var max_h: u32 = 0;
    while (try rd.next()) |c| {
        try coins.append(aa, .{ .txid = c.txid, .vout = c.vout, .height = c.height, .cb = c.cb, .ser = try aa.dupe(u8, c.ser) });
        max_h = @max(max_h, c.height);
    }
    const base: [32]u8 = @splat(7);
    const snap = try encode(aa, mainnet_magic, base, coins.items);
    var r = std.Io.Reader.fixed(snap);
    const got = try scanReader(a, &r, 1000);
    try testing.expectEqual(want.count, got.count);
    try testing.expectEqual(want.amount, got.amount);
    try testing.expectEqualSlices(u8, &want.hash, &got.hash);
    try testing.expectEqualSlices(u8, &base, &got.meta.base);
    try testing.expectEqual(max_h, got.max_height);
    // A coin above the base height, a trailing byte, a short count, swapped coins.
    var r2 = std.Io.Reader.fixed(snap);
    try testing.expectError(error.CoinAboveBase, scanReader(a, &r2, max_h - 1));
    const extra = try std.mem.concat(aa, u8, &.{ snap, "\x00" });
    var r3 = std.Io.Reader.fixed(extra);
    try testing.expectError(error.TrailingBytes, scanReader(a, &r3, 1000));
    const short = try aa.dupe(u8, snap);
    std.mem.writeInt(u64, short[43..51], coins.items.len - 1, .little);
    var r4 = std.Io.Reader.fixed(short);
    try testing.expect(std.meta.isError(scanReader(a, &r4, 1000)));
    std.mem.swap(TestCoin, &coins.items[0], &coins.items[coins.items.len - 1]);
    const unsorted = try encode(aa, mainnet_magic, base, coins.items);
    var r5 = std.Io.Reader.fixed(unsorted);
    try testing.expectError(error.NotSorted, scanReader(a, &r5, 1000));
}
