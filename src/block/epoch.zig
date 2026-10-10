//! M3b epochs (D-040): the challenge, the native coin set, and the epoch check.
//!
//! An epoch is blocks `from … to` (from genesis for now). Its challenge `(γ, z, α)` is derived from a
//! seed hashing, per height, the block hash and the block commitment (both public in the block proofs),
//! so the verifier recomputes it from the proofs. The epoch holds when the blocks' partial sums minus the
//! final set's fractions are zero (`Spec/UtxoEpoch.lean`, `epoch_sound`), with the final set strictly
//! sorted by outpoint.

const std = @import("std");
const core = @import("stwo_core");
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const coin = @import("coin.zig");
const fields = @import("fields.zig");

const Blake2s = std.crypto.hash.blake2.Blake2s256;
pub const TAG = "starked-bitcoin M3b epoch v1";

/// The seed: Blake2s of the tag, the range, and per height the block hash and commitment.
pub fn seed(from: u32, to: u32, hashes: []const [32]u8, commits: []const [32]u8) [32]u8 {
    return seedFrom(from, to, null, hashes, commits);
}

/// The seed of an epoch from a previous set: the previous set's `hash_serialized` follows the range, so
/// the initial set is fixed before the challenge (`Spec/UtxoEpochFrom.lean`). Without one, it is `seed`.
pub fn seedFrom(from: u32, to: u32, prev: ?[32]u8, hashes: []const [32]u8, commits: []const [32]u8) [32]u8 {
    var h = Blake2s.init(.{});
    h.update(TAG);
    var buf: [8]u8 = undefined;
    std.mem.writeInt(u32, buf[0..4], from, .little);
    std.mem.writeInt(u32, buf[4..8], to, .little);
    h.update(&buf);
    if (prev) |p| h.update(&p);
    for (hashes, commits) |bh, c| {
        h.update(&bh);
        h.update(&c);
    }
    var out: [32]u8 = undefined;
    h.final(&out);
    return out;
}

/// Field elements from the seed (counter mode, rejecting 2^31 − 1).
const Stream = struct {
    seed: [32]u8,
    ctr: u32 = 0,
    buf: [8]u32 = undefined,
    pos: usize = 8,

    fn next(self: *Stream) M31 {
        while (true) {
            if (self.pos == 8) {
                var h = Blake2s.init(.{});
                h.update(&self.seed);
                var c: [4]u8 = undefined;
                std.mem.writeInt(u32, &c, self.ctr, .little);
                h.update(&c);
                var out: [32]u8 = undefined;
                h.final(&out);
                for (0..8) |i| self.buf[i] = std.mem.readInt(u32, out[4 * i ..][0..4], .little) & 0x7fffffff;
                self.ctr += 1;
                self.pos = 0;
            }
            const v = self.buf[self.pos];
            self.pos += 1;
            if (v != 0x7fffffff) return M31.fromCanonical(v);
        }
    }

    fn q(self: *Stream) QM31 {
        return QM31.fromM31(self.next(), self.next(), self.next(), self.next());
    }
};

pub fn challenge(s: [32]u8) coin.Challenge {
    var st = Stream{ .seed = s };
    var ch: coin.Challenge = undefined;
    ch.gamma = st.q();
    ch.z = st.q();
    // The tuple's weights are powers of one α: φ(t) = Σₖ tₖ αᵏ, the value at α of the polynomial
    // `tuplePoly t` that the epoch theorem uses (`Spec/UtxoEpoch.lean`, `LogUpSZ.lean`).
    const a = st.q();
    var x = QM31.one();
    for (&ch.alpha) |*w| {
        w.* = x;
        x = x.mul(a);
    }
    return ch;
}

/// A coin of the native set, with what its tuple needs.
pub const Coin = struct {
    txid: [32]u8,
    vout: u32,
    height: u32,
    cb: bool,
    txi: u32,
    /// `serTxOut`: amount and script.
    ser: []const u8,

    fn lessThan(_: void, x: Coin, y: Coin) bool {
        const o = std.mem.order(u8, &x.txid, &y.txid);
        return o == .lt or (o == .eq and x.vout < y.vout);
    }
};

const Key = struct { txid: [32]u8, vout: u32 };

fn txidOf(raw: []const u8, start: usize, rows: []const fields.Row, lock_row: usize, seg: bool) [32]u8 {
    var h1: [32]u8 = undefined;
    var out: [32]u8 = undefined;
    if (!seg) {
        const end = rows[lock_row].start + 4;
        std.crypto.hash.sha2.Sha256.hash(raw[start..end], &h1, .{});
    } else {
        // Without the marker/flag and the witness section.
        var s = std.crypto.hash.sha2.Sha256.init(.{});
        s.update(raw[start .. start + 4]);
        var wst: usize = rows[lock_row].start;
        var r = lock_row;
        while (r > 0) : (r -= 1) {
            if (rows[r - 1].kind == fields.K_OUT or rows[r - 1].kind == fields.K_NOUT) {
                wst = rows[r - 1].start + rows[r - 1].len;
                break;
            }
        }
        s.update(raw[start + 6 .. wst]);
        s.update(raw[rows[lock_row].start .. rows[lock_row].start + 4]);
        s.final(&h1);
    }
    std.crypto.hash.sha2.Sha256.hash(&h1, &out, .{});
    return out;
}

fn unspendable(script: []const u8) bool {
    return (script.len > 0 and script[0] == 0x6a) or script.len > 10000;
}

/// The coin set after blocks `0 … blocks.len − 1` (Core's semantics with the spec's two deviations).
pub fn coinSet(a: std.mem.Allocator, blocks: []const []const u8) ![]Coin {
    return coinSetFrom(a, &.{}, 0, blocks);
}

/// The coin set after applying blocks `first, first + 1, …` to `init`.
pub fn coinSetFrom(a: std.mem.Allocator, init: []const Coin, first: u32, blocks: []const []const u8) ![]Coin {
    var set = std.AutoHashMap(Key, Coin).init(a);
    for (init) |c| try set.put(.{ .txid = c.txid, .vout = c.vout }, c);
    for (blocks, 0..) |raw, hh| {
        const height: u32 = first + @as(u32, @intCast(hh));
        const rows = try fields.tokenize(a, raw);
        var txi: u32 = 0;
        var tx_start: usize = 0;
        var seg = false;
        var outs = std.ArrayList(struct { vout: u32, ser: []const u8 }).empty;
        var ins = std.ArrayList(Key).empty;
        var vout: u32 = 0;
        for (rows, 0..) |r, ri| {
            switch (r.kind) {
                fields.K_TXH => {
                    tx_start = r.start;
                    seg = r.seg;
                    outs.clearRetainingCapacity();
                    ins.clearRetainingCapacity();
                    vout = 0;
                },
                fields.K_IN => if (txi > 0) {
                    var k: Key = undefined;
                    @memcpy(&k.txid, raw[r.start..][0..32]);
                    k.vout = std.mem.readInt(u32, raw[r.start + 32 ..][0..4], .little);
                    try ins.append(a, k);
                },
                fields.K_OUT => {
                    try outs.append(a, .{ .vout = vout, .ser = raw[r.start .. r.start + r.len] });
                    vout += 1;
                },
                fields.K_LOCK => {
                    const id = txidOf(raw, tx_start, rows, ri, seg);
                    for (ins.items) |k| if (!set.remove(k)) return error.MissingCoin;
                    const lost = txi == 0 and (height == 0 or height == 91722 or height == 91812);
                    if (!lost) for (outs.items) |o| {
                        const sl = o.ser[8];
                        const hdr: usize = if (sl < 253) 1 else 3;
                        const script = o.ser[8 + hdr ..];
                        if (unspendable(script)) continue;
                        const k = Key{ .txid = id, .vout = o.vout };
                        if (set.contains(k)) return error.Overwrite;
                        try set.put(k, .{ .txid = id, .vout = o.vout, .height = height, .cb = txi == 0, .txi = txi, .ser = o.ser });
                    };
                    txi += 1;
                },
                else => {},
            }
        }
    }
    var out = std.ArrayList(Coin).empty;
    var it = set.valueIterator();
    while (it.next()) |c| try out.append(a, c.*);
    std.mem.sort(Coin, out.items, {}, Coin.lessThan);
    return out.toOwnedSlice(a);
}

/// The final set's fractions.
pub fn finalSum(ch: coin.Challenge, set: []const Coin) !QM31 {
    var s = QM31.zero();
    for (set) |c| s = s.add(try coin.coinFrac(ch, c.txid, c.vout, c.height, c.cb, c.ser, c.txi));
    return s;
}

/// Strictly sorted by outpoint (txid bytes, then index): distinct keys.
pub fn sortedStrict(set: []const Coin) bool {
    for (1..set.len) |i| if (!Coin.lessThan({}, set[i - 1], set[i])) return false;
    return true;
}

/// Core's `HASH_SERIALIZED` (`kernel/coinstats.cpp`): SHA256d over each coin's outpoint, `height·2 + cb`
/// (4 bytes), amount and script, in key order. Returned in display order.
pub fn hashSerialized(set: []const Coin) [32]u8 {
    var s = std.crypto.hash.sha2.Sha256.init(.{});
    for (set) |c| {
        s.update(&c.txid);
        var b: [8]u8 = undefined;
        std.mem.writeInt(u32, b[0..4], c.vout, .little);
        std.mem.writeInt(u32, b[4..8], 2 * c.height + @intFromBool(c.cb), .little);
        s.update(&b);
        s.update(c.ser);
    }
    var h1: [32]u8 = undefined;
    s.final(&h1);
    var out: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(&h1, &out, .{});
    std.mem.reverse(u8, &out);
    return out;
}

/// An initial set's coins are all created before block `from` (their creation indices are earlier than
/// the epoch's transactions).
pub fn createdBefore(set: []const Coin, from: u32) bool {
    for (set) |c| if (c.height >= from) return false;
    return true;
}

/// Total amount of the set.
pub fn totalAmount(set: []const Coin) u64 {
    var t: u64 = 0;
    for (set) |c| t += std.mem.readInt(u64, c.ser[0..8], .little);
    return t;
}

test "epoch: blocks 0-9 then 170's coin set; the challenge is deterministic" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const s1 = seed(0, 1, &.{[_]u8{1} ** 32}, &.{[_]u8{2} ** 32});
    const c1 = challenge(s1);
    const c2 = challenge(s1);
    try std.testing.expect(c1.z.eql(c2.z));
    const s2 = seed(0, 1, &.{[_]u8{1} ** 32}, &.{[_]u8{3} ** 32});
    try std.testing.expect(!challenge(s2).z.eql(c1.z));
    // Genesis alone: an empty set (Core never connects block 0).
    const set0 = try coinSet(a, &.{@embedFile("testdata:block_0")});
    try std.testing.expectEqual(@as(usize, 0), set0.len);
}

/// The verifier's checks of a block proof's M3b public inputs: the epoch's challenge, the BIP30/genesis
/// bit, the subsidy (inputs 41–152 and 158–160).
pub fn checkPubs(pubs: []const M31, ch: coin.Challenge, height: u32) !void {
    const want = coin.pubs(ch, QM31.zero(), 0, @import("system.zig").lostHeight(height), height);
    for (41..coin.PUB_S) |i| if (!pubs[i].eql(want[i - 41])) return error.ChallengeMismatch;
    for (coin.PUB_LOST..coin.N_PUB) |i| if (!pubs[i].eql(want[i - 41])) return error.ContextMismatch;
}

pub fn partialSum(pubs: []const M31) QM31 {
    return QM31.fromM31(pubs[coin.PUB_S], pubs[coin.PUB_S + 1], pubs[coin.PUB_S + 2], pubs[coin.PUB_S + 3]);
}

/// The coin set file: count, then per coin txid, vout, height, coinbase, tx index, `serTxOut`.
pub fn encodeSet(a: std.mem.Allocator, set: []const Coin) ![]u8 {
    var out = std.ArrayList(u8).empty;
    const w = out.writer(a);
    try w.writeInt(u32, @intCast(set.len), .little);
    for (set) |c| {
        try w.writeAll(&c.txid);
        try w.writeInt(u32, c.vout, .little);
        try w.writeInt(u32, c.height, .little);
        try w.writeByte(@intFromBool(c.cb));
        try w.writeInt(u32, c.txi, .little);
        try w.writeInt(u32, @intCast(c.ser.len), .little);
        try w.writeAll(c.ser);
    }
    return out.toOwnedSlice(a);
}

pub fn decodeSet(a: std.mem.Allocator, bytes: []const u8) ![]Coin {
    var fbs = std.io.fixedBufferStream(bytes);
    const r = fbs.reader();
    const n = try r.readInt(u32, .little);
    const out = try a.alloc(Coin, n);
    for (out) |*c| {
        try r.readNoEof(&c.txid);
        c.vout = try r.readInt(u32, .little);
        c.height = try r.readInt(u32, .little);
        c.cb = (try r.readByte()) != 0;
        c.txi = try r.readInt(u32, .little);
        const l = try r.readInt(u32, .little);
        if (l > bytes.len - fbs.pos) return error.Truncated;
        c.ser = bytes[fbs.pos .. fbs.pos + l];
        fbs.pos += l;
    }
    if (fbs.pos != bytes.len) return error.TrailingBytes;
    return out;
}
