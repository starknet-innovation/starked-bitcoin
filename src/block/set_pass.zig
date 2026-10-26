//! The coin-set pass, native model (docs/design/set-pass.md): a set file's facts (its digest, Core's
//! `hash_serialized`, count, amount, highest coin, and its fractions under given challenges) computed
//! over the file's bytes in segments of whole records, with everything a segment hands the next held in
//! `State`. The segment circuit will prove `step` record by record; this model fixes the carried state
//! and is tested to give `set_file.scan`/`sum`'s values for any segmentation.

const std = @import("std");
const coin = @import("coin.zig");
const QM31 = @import("stwo_core").fields.qm31.QM31;
const Sha256 = std.crypto.hash.sha2.Sha256;
const Blake2s = std.crypto.hash.blake2.Blake2s256;

/// Challenges per pass: 1 for a chain's end sets, 2 for a set between two epochs.
pub const MAX_K = 2;

/// A record's fixed part: txid 32, vout 4, height 4, cb 1, txi 4, len 4.
pub const HEAD = 49;

pub const Outpoint = struct { txid: [32]u8, vout: u32 };

/// What one segment hands the next.
pub const State = struct {
    /// The file's record count (its first 4 bytes) and the records consumed.
    n: u32,
    i: u32 = 0,
    /// Blake2s over the file's bytes (`epoch.setDigest`): its words, counter and pending bytes.
    b2: Blake2s,
    /// SHA-256 over the `TxOutSer` stream (`hash_serialized`'s inner hash): its words, length, pending bytes.
    sha: Sha256 = Sha256.init(.{}),
    k: u8,
    sums: [MAX_K]QM31 = @splat(QM31.zero()),
    amount: u64 = 0,
    max_height: u32 = 0,
    /// The last outpoint (sortedness across a boundary).
    last: ?Outpoint = null,
    /// Totals for sizing: TxOutSer bytes hashed.
    sha_bytes: u64 = 0,
};

pub const Facts = struct {
    count: u64,
    amount: u64,
    /// Core's `hash_serialized` (SHA256d, byte-reversed).
    hash: [32]u8,
    /// Blake2s of the file (`epoch.setDigest`).
    digest: [32]u8,
    max_height: u32,
    sums: [MAX_K]QM31,
    /// Sizing: the file's bytes, the TxOutSer bytes, and the compressions each hash makes.
    file_bytes: u64,
    sha_bytes: u64,
    b2_blocks: u64,
    sha_blocks: u64,
};

/// The first segment's start: the file's 4-byte count.
pub fn begin(header: *const [4]u8, k: u8) !State {
    if (k == 0 or k > MAX_K) return error.BadChallengeCount;
    var st: State = .{ .n = std.mem.readInt(u32, header, .little), .b2 = Blake2s.init(.{}), .k = k };
    st.b2.update(header);
    return st;
}

/// One record (`bytes` from its first byte; returns its length): the reader's checks, then every
/// carried value advanced.
pub fn step(st: *State, chs: []const coin.Challenge, bytes: []const u8) !usize {
    if (chs.len != st.k) return error.BadChallengeCount;
    if (st.i == st.n) return error.TrailingBytes;
    if (bytes.len < HEAD) return error.EndOfStream;
    const h = bytes[0..HEAD];
    var txid: [32]u8 = undefined;
    @memcpy(&txid, h[0..32]);
    const vout = std.mem.readInt(u32, h[32..36], .little);
    const height = std.mem.readInt(u32, h[36..40], .little);
    const cb = h[40];
    if (cb > 1) return error.BadCoinbaseFlag;
    const txi = std.mem.readInt(u32, h[41..45], .little);
    const l = std.mem.readInt(u32, h[45..49], .little);
    if (height >= 1 << 31 or l >= 0x7fffffff) return error.CoinOutOfRange;
    if (bytes.len - HEAD < l) return error.EndOfStream;
    const ser = bytes[HEAD .. HEAD + l];
    if (st.last) |p| {
        const o = std.mem.order(u8, &p.txid, &txid);
        if (!(o == .lt or (o == .eq and p.vout < vout))) return error.SetNotSorted;
    }
    st.last = .{ .txid = txid, .vout = vout };
    st.b2.update(bytes[0 .. HEAD + l]);
    // TxOutSer: the outpoint, 2·height + cb, the output.
    if (l < 8) return error.CoinOutOfRange;
    var b: [8]u8 = undefined;
    st.sha.update(&txid);
    std.mem.writeInt(u32, b[0..4], vout, .little);
    std.mem.writeInt(u32, b[4..8], 2 * height + cb, .little);
    st.sha.update(&b);
    st.sha.update(ser);
    st.sha_bytes += 40 + l;
    st.amount += std.mem.readInt(u64, ser[0..8], .little);
    st.max_height = @max(st.max_height, height);
    for (chs, st.sums[0..st.k]) |ch, *s| s.* = s.add(try coin.coinFrac(ch, txid, vout, height, cb == 1, ser, txi));
    st.i += 1;
    return HEAD + l;
}

/// A segment: `count` records from `bytes[off..]`; returns the offset after them.
pub fn segment(st: *State, chs: []const coin.Challenge, bytes: []const u8, off: usize, count: u32) !usize {
    var at = off;
    for (0..count) |_| at += try step(st, chs, bytes[at..]);
    return at;
}

/// The last segment's end: every record consumed, no byte after, the hashes finalized.
pub fn finish(st: *State, file_bytes: u64) !Facts {
    if (st.i != st.n) return error.EndOfStream;
    var f: Facts = .{
        .count = st.n,
        .amount = st.amount,
        .hash = undefined,
        .digest = undefined,
        .max_height = st.max_height,
        .sums = st.sums,
        .file_bytes = file_bytes,
        .sha_bytes = st.sha_bytes,
        .b2_blocks = @max(1, (file_bytes + 63) / 64),
        .sha_blocks = (st.sha_bytes + 9 + 63) / 64 + 1,
    };
    var b2 = st.b2;
    b2.final(&f.digest);
    var sha = st.sha;
    var h1: [32]u8 = undefined;
    sha.final(&h1);
    Sha256.hash(&h1, &f.hash, .{});
    std.mem.reverse(u8, &f.hash);
    return f;
}

/// The whole file in segments of `per` records (the last may be shorter).
pub fn run(bytes: []const u8, chs: []const coin.Challenge, per: u32) !Facts {
    if (bytes.len < 4 or per == 0) return error.EndOfStream;
    var st = try begin(bytes[0..4], @intCast(chs.len));
    var at: usize = 4;
    while (st.i < st.n) at = try segment(&st, chs, bytes, at, @min(per, st.n - st.i));
    if (at != bytes.len) return error.TrailingBytes;
    return finish(&st, bytes.len);
}

/// The same over a file, streamed in segments of `per` records (a 14 GB set never in memory).
pub fn runFile(gpa: std.mem.Allocator, path: []const u8, chs: []const coin.Challenge, per: u32) !Facts {
    const file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    const buf = try gpa.alloc(u8, 1 << 20);
    defer gpa.free(buf);
    var fr = file.reader(buf);
    const r = &fr.interface;
    var header: [4]u8 = undefined;
    try r.readSliceAll(&header);
    var st = try begin(&header, @intCast(chs.len));
    var rec: std.ArrayListUnmanaged(u8) = .empty;
    defer rec.deinit(gpa);
    var size: u64 = 4;
    var in_segment: u32 = 0;
    while (st.i < st.n) {
        try rec.resize(gpa, HEAD);
        try r.readSliceAll(rec.items[0..HEAD]);
        const l = std.mem.readInt(u32, rec.items[45..49], .little);
        if (l >= 0x7fffffff) return error.CoinOutOfRange;
        try rec.resize(gpa, HEAD + l);
        try r.readSliceAll(rec.items[HEAD..]);
        // A segment boundary: `st` is all that crosses it (a proof's public values in and out).
        if (in_segment == per) in_segment = 0;
        size += try step(&st, chs, rec.items);
        in_segment += 1;
    }
    if (r.takeByte()) |_| return error.TrailingBytes else |e| if (e != error.EndOfStream) return e;
    return finish(&st, size);
}

const EP = @import("epoch.zig");
const SF = @import("set_file.zig");

fn expectFacts(gpa: std.mem.Allocator, path: []const u8, f: Facts, chs: []const coin.Challenge) !void {
    const info = try SF.scan(gpa, path, null);
    try std.testing.expectEqual(info.count, f.count);
    try std.testing.expectEqual(info.amount, f.amount);
    try std.testing.expectEqualSlices(u8, &info.hash, &f.hash);
    try std.testing.expectEqualSlices(u8, &info.digest, &f.digest);
    for (chs, 0..) |ch, j| try std.testing.expect(f.sums[j].eql((try SF.sum(gpa, path, ch)).sum));
}

test "set_pass: any segmentation gives set_file's facts (sets after blocks 170 and 1000, two challenges)" {
    const a = std.testing.allocator;
    const chs = [_]coin.Challenge{ EP.challenge(@splat(7)), EP.challenge(@splat(9)) };
    for ([_][]const u8{ "data/epoch/set-170.bin", "data/epoch/set-1000.bin" }) |path| {
        const bytes = std.fs.cwd().readFileAlloc(a, path, 1 << 30) catch return error.SkipZigTest;
        defer a.free(bytes);
        const whole = try run(bytes, &chs, std.math.maxInt(u32));
        try expectFacts(a, path, whole, &chs);
        for ([_]u32{ 1, 2, 7, 64, 1000 }) |per| {
            const f = try run(bytes, &chs, per);
            try std.testing.expectEqualDeep(whole, f);
        }
        try std.testing.expectEqualDeep(whole, try runFile(a, path, &chs, 13));
        // The highest coin is below the set's block + 1 (an epoch's start set: below its first block).
        try std.testing.expect(whole.max_height < 1001);
    }
}

test "set_pass: malformed sets are rejected as the reader rejects them" {
    const a = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const aa = arena.allocator();
    const bytes = std.fs.cwd().readFileAlloc(aa, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    const set = try EP.decodeSet(aa, bytes);
    const chs = [_]coin.Challenge{EP.challenge(@splat(7))};
    const swapped = try aa.dupe(EP.Coin, set);
    std.mem.swap(EP.Coin, &swapped[3], &swapped[4]);
    try std.testing.expectError(error.SetNotSorted, run(try EP.encodeSet(aa, swapped), &chs, 2));
    try std.testing.expectError(error.TrailingBytes, run(try std.mem.concat(aa, u8, &.{ bytes, &.{0} }), &chs, 5));
    const bad = try aa.dupe(u8, bytes);
    bad[4 + 40] = 2;
    try std.testing.expectError(error.BadCoinbaseFlag, run(bad, &chs, 5));
    try std.testing.expectError(error.EndOfStream, run(bytes[0 .. bytes.len - 1], &chs, 5));
}
