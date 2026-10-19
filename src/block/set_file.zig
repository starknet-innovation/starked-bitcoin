//! Coin set files (`epoch.encodeSet`'s format) read coin by coin, so a set of ~165 M coins (~14 GB) is
//! never held in memory: `epoch.decodeSet`'s checks (coinbase flag, ranges, no trailing bytes) plus strict
//! sortedness, and the digest (`epoch.setDigest`, Blake2s of the file's bytes) computed on the way.
//! `scan` gives what a set's header facts need (count, amount, Core's `hash_serialized`, digest); `sum`
//! gives its fractions under a challenge (`epoch.finalSum`), a second pass once the challenge is known.

const std = @import("std");
const EP = @import("epoch.zig");
const coin = @import("coin.zig");
const QM31 = @import("stwo_core").fields.qm31.QM31;
const Sha256 = std.crypto.hash.sha2.Sha256;
const Blake2s = std.crypto.hash.blake2.Blake2s256;

pub const Info = struct { count: u64, amount: u64, hash: [32]u8, digest: [32]u8 };

/// Reads a set file coin by coin. Initialize in place (`init`), then `next` until null; `next`'s coin's
/// `ser` is valid until the following call.
pub const Reader = struct {
    gpa: std.mem.Allocator,
    file: std.fs.File,
    buf: []u8,
    fr: std.fs.File.Reader,
    n: u32 = 0,
    i: u32 = 0,
    prev: ?struct { txid: [32]u8, vout: u32 } = null,
    b2: Blake2s = Blake2s.init(.{}),
    ser: std.ArrayListUnmanaged(u8) = .empty,
    done: bool = false,

    pub fn init(self: *Reader, gpa: std.mem.Allocator, path: []const u8) !void {
        const file = try std.fs.cwd().openFile(path, .{});
        errdefer file.close();
        const buf = try gpa.alloc(u8, 1 << 20);
        self.* = .{ .gpa = gpa, .file = file, .buf = buf, .fr = file.reader(buf) };
        var nb: [4]u8 = undefined;
        try self.fr.interface.readSliceAll(&nb);
        self.b2.update(&nb);
        self.n = std.mem.readInt(u32, &nb, .little);
    }

    pub fn deinit(self: *Reader) void {
        self.ser.deinit(self.gpa);
        self.gpa.free(self.buf);
        self.file.close();
    }

    pub fn next(self: *Reader) !?EP.Coin {
        const r = &self.fr.interface;
        if (self.i == self.n) {
            if (!self.done) {
                if (r.takeByte()) |_| return error.TrailingBytes else |e| if (e != error.EndOfStream) return e;
                self.done = true;
            }
            return null;
        }
        self.i += 1;
        var head: [32 + 4 + 4 + 1 + 4 + 4]u8 = undefined;
        try r.readSliceAll(&head);
        self.b2.update(&head);
        var c: EP.Coin = undefined;
        @memcpy(&c.txid, head[0..32]);
        c.vout = std.mem.readInt(u32, head[32..36], .little);
        c.height = std.mem.readInt(u32, head[36..40], .little);
        const cb = head[40];
        if (cb > 1) return error.BadCoinbaseFlag;
        c.cb = cb == 1;
        c.txi = std.mem.readInt(u32, head[41..45], .little);
        const l = std.mem.readInt(u32, head[45..49], .little);
        // `WFE` (CoinEpochSound.lean): the code `2·height + cb` below 2^32, the script length below P.
        if (c.height >= 1 << 31 or l >= 0x7fffffff) return error.CoinOutOfRange;
        if (self.prev) |p| {
            const o = std.mem.order(u8, &p.txid, &c.txid);
            if (!(o == .lt or (o == .eq and p.vout < c.vout))) return error.SetNotSorted;
        }
        self.prev = .{ .txid = c.txid, .vout = c.vout };
        try self.ser.resize(self.gpa, l);
        try r.readSliceAll(self.ser.items);
        self.b2.update(self.ser.items);
        c.ser = self.ser.items;
        return c;
    }

    /// The digest of the whole file (`epoch.setDigest`), once `next` has returned null.
    pub fn digest(self: *Reader) ![32]u8 {
        if (!self.done) return error.NotAtEnd;
        var d: [32]u8 = undefined;
        self.b2.final(&d);
        return d;
    }
};

/// Count, amount, Core's `hash_serialized` and the digest of the set file at `path`; with `before`, every
/// coin must be created before that block (an epoch's initial set).
pub fn scan(gpa: std.mem.Allocator, path: []const u8, before: ?u32) !Info {
    var rd: Reader = undefined;
    try rd.init(gpa, path);
    defer rd.deinit();
    var hs = Sha256.init(.{});
    var amount: u64 = 0;
    while (try rd.next()) |c| {
        if (before) |b| if (c.height >= b) return error.PrevSetTooNew;
        if (c.ser.len < 8) return error.CoinOutOfRange;
        var b: [8]u8 = undefined;
        hs.update(&c.txid);
        std.mem.writeInt(u32, b[0..4], c.vout, .little);
        std.mem.writeInt(u32, b[4..8], 2 * c.height + @intFromBool(c.cb), .little);
        hs.update(&b);
        hs.update(c.ser);
        amount += std.mem.readInt(u64, c.ser[0..8], .little);
    }
    var info = Info{ .count = rd.n, .amount = amount, .hash = undefined, .digest = try rd.digest() };
    var h1: [32]u8 = undefined;
    hs.final(&h1);
    Sha256.hash(&h1, &info.hash, .{});
    std.mem.reverse(u8, &info.hash);
    return info;
}

/// The set's fractions under `ch` (`epoch.finalSum`), and its digest (to check it is the set scanned).
pub fn sum(gpa: std.mem.Allocator, path: []const u8, ch: coin.Challenge) !struct { sum: QM31, digest: [32]u8 } {
    var rd: Reader = undefined;
    try rd.init(gpa, path);
    defer rd.deinit();
    var s = QM31.zero();
    while (try rd.next()) |c| s = s.add(try coin.coinFrac(ch, c.txid, c.vout, c.height, c.cb, c.ser, c.txi));
    return .{ .sum = s, .digest = try rd.digest() };
}

test "set_file: scan and sum equal the in-memory decode on epoch sets" {
    const a = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const aa = arena.allocator();
    const path = "data/epoch/set-1000.bin";
    const bytes = std.fs.cwd().readFileAlloc(aa, path, 1 << 30) catch return error.SkipZigTest;
    const set = try EP.decodeSet(aa, bytes);
    const info = try scan(a, path, 1001);
    try std.testing.expectEqual(@as(u64, set.len), info.count);
    try std.testing.expectEqual(EP.totalAmount(set), info.amount);
    try std.testing.expectEqualSlices(u8, &EP.hashSerialized(set), &info.hash);
    try std.testing.expectEqualSlices(u8, &(try EP.setDigest(aa, set)), &info.digest);
    try std.testing.expectError(error.PrevSetTooNew, scan(a, path, 1000));
    const ch = EP.challenge(@splat(7));
    const s = try sum(a, path, ch);
    try std.testing.expect(s.sum.eql(try EP.finalSum(ch, set)));
}

test "set_file: malformed files are rejected (unsorted, trailing bytes, coinbase flag, truncated)" {
    const a = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const aa = arena.allocator();
    const bytes = std.fs.cwd().readFileAlloc(aa, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    const set = try EP.decodeSet(aa, bytes);
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const dir_path = try tmp.dir.realpathAlloc(aa, ".");
    const path = try std.fs.path.join(aa, &.{ dir_path, "s.bin" });
    // Two coins swapped.
    const swapped = try aa.dupe(EP.Coin, set);
    std.mem.swap(EP.Coin, &swapped[3], &swapped[4]);
    try tmp.dir.writeFile(.{ .sub_path = "s.bin", .data = try EP.encodeSet(aa, swapped) });
    try std.testing.expectError(error.SetNotSorted, scan(a, path, null));
    // A trailing byte.
    try tmp.dir.writeFile(.{ .sub_path = "s.bin", .data = try std.mem.concat(aa, u8, &.{ bytes, &.{0} }) });
    try std.testing.expectError(error.TrailingBytes, scan(a, path, null));
    // A coinbase flag of 2 (the first coin's: offset 4 + 40).
    const bad = try aa.dupe(u8, bytes);
    bad[4 + 40] = 2;
    try tmp.dir.writeFile(.{ .sub_path = "s.bin", .data = bad });
    try std.testing.expectError(error.BadCoinbaseFlag, scan(a, path, null));
    // Truncated.
    try tmp.dir.writeFile(.{ .sub_path = "s.bin", .data = bytes[0 .. bytes.len - 1] });
    try std.testing.expectError(error.EndOfStream, scan(a, path, null));
    // The untouched file scans to the in-memory facts.
    try tmp.dir.writeFile(.{ .sub_path = "s.bin", .data = bytes });
    try std.testing.expectEqual(@as(u64, set.len), (try scan(a, path, null)).count);
}
