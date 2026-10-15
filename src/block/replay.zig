//! Replay (full-chain data preparation): one pass over raw blocks, in height order, keeping the coin set
//! in memory and deriving per block what `scripts/fetch_undo.py --ctx` asks the node for: the undo
//! stream and the creating transactions' indices (`.ctx`). Every coin already carries both (height,
//! coinbase, tx index and `serTxOut`, as `epoch.Coin`), so only raw blocks are needed. Each block is
//! checked against the pinned header at its height, its txid Merkle root (with Core's mutation rule) and
//! its witness commitment (Core's `CheckWitnessMalleation`), so any source of raw blocks will do.
//!
//! The semantics are `epoch.coinSetFrom`'s (tested equal): unspendable outputs are skipped, the
//! coinbases of blocks 0, 91722 and 91812 are lost (overwritten under BIP30), and an overwrite or a
//! missing coin is an error. The set after a block is written in `epoch.encodeSet`'s format, streamed and
//! sorted without copying the coins: an epoch's previous set (`--from`), and a checkpoint to resume from.
//!
//! Memory per coin: the table entry (36-byte outpoint, code, tx index, offset, length; 80 % load) and its
//! `serTxOut` in one heap, compacted when more than half of it is spent coins.

const std = @import("std");
const EP = @import("epoch.zig");
const fields = @import("fields.zig");
const Sha256 = std.crypto.hash.sha2.Sha256;
const Blake2s = std.crypto.hash.blake2.Blake2s256;

/// Segwit's activation height on mainnet: from here a witness commitment is checked when present.
pub const SEGWIT_HEIGHT: u32 = 481824;

pub const Key = extern struct { txid: [32]u8, vout: u32 };
pub const Val = struct { code: u32, txi: u32, off: u64, len: u32 };

const KeyCtx = struct {
    pub fn hash(_: KeyCtx, k: Key) u64 {
        return std.mem.readInt(u64, k.txid[0..8], .little) ^ (@as(u64, k.vout) *% 0x9E3779B97F4A7C15);
    }
    pub fn eql(_: KeyCtx, x: Key, y: Key) bool {
        return x.vout == y.vout and std.mem.eql(u8, &x.txid, &y.txid);
    }
};

fn keyLess(_: void, x: Key, y: Key) bool {
    const o = std.mem.order(u8, &x.txid, &y.txid);
    return o == .lt or (o == .eq and x.vout < y.vout);
}

/// A block's undo stream (`0x01`, then per non-coinbase input LE32 `2·height + cb` and `serTxOut`) and
/// `.ctx` (per input, LE32 the creating transaction's index in its block).
pub const Undo = struct { undo: []const u8, ctx: []const u8 };

/// A written set: what `chainproof verify-epoch` reports for it.
pub const SetInfo = struct { count: u64, amount: u64, hash: [32]u8, digest: [32]u8 };

pub const Set = struct {
    gpa: std.mem.Allocator,
    map: std.HashMapUnmanaged(Key, Val, KeyCtx, 80) = .empty,
    heap: std.ArrayListUnmanaged(u8) = .empty,
    /// Bytes of `heap` that belong to unspent coins.
    live: u64 = 0,

    pub fn init(gpa: std.mem.Allocator, capacity: u32) !Set {
        var s = Set{ .gpa = gpa };
        if (capacity > 0) try s.map.ensureTotalCapacity(gpa, capacity);
        return s;
    }

    pub fn deinit(self: *Set) void {
        self.map.deinit(self.gpa);
        self.heap.deinit(self.gpa);
    }

    pub fn count(self: *const Set) usize {
        return self.map.count();
    }

    pub fn ser(self: *const Set, v: Val) []const u8 {
        return self.heap.items[v.off..][0..v.len];
    }

    fn put(self: *Set, k: Key, code: u32, txi: u32, s: []const u8) !void {
        const off = self.heap.items.len;
        try self.heap.appendSlice(self.gpa, s);
        const gop = try self.map.getOrPut(self.gpa, k);
        if (gop.found_existing) return error.Overwrite;
        gop.value_ptr.* = .{ .code = code, .txi = txi, .off = off, .len = @intCast(s.len) };
        self.live += s.len;
    }

    /// Rewrites the heap with the unspent coins only, once spent ones are more than half of it.
    pub fn maybeCompact(self: *Set) !void {
        if (self.heap.items.len < 2 * self.live + (64 << 20)) return;
        var nh = std.ArrayListUnmanaged(u8).empty;
        try nh.ensureTotalCapacity(self.gpa, self.live + (self.live >> 3));
        var it = self.map.valueIterator();
        while (it.next()) |v| {
            const s = self.ser(v.*);
            v.off = nh.items.len;
            nh.appendSliceAssumeCapacity(s);
        }
        self.heap.deinit(self.gpa);
        self.heap = nh;
    }

    /// Applies block `height` (the semantics of `epoch.coinSetFrom`) after checking it against its
    /// pinned header. With `want`, returns its undo stream and `.ctx`, allocated in `a`.
    pub fn apply(self: *Set, a: std.mem.Allocator, raw: []const u8, header: *const [80]u8, height: u32, want: bool) !?Undo {
        if (raw.len < 80 or !std.mem.eql(u8, raw[0..80], header)) return error.HeaderMismatch;
        const rows = try fields.tokenize(a, raw);
        var undo = std.ArrayList(u8).empty;
        var ctx = std.ArrayList(u8).empty;
        if (want) try undo.append(a, 1);
        var txids = std.ArrayList([32]u8).empty;
        var wtxids = std.ArrayList([32]u8).empty;
        var any_witness = false;
        var nonce: ?[32]u8 = null;
        var cb_items: u32 = 0;
        var cb_outs = std.ArrayList([]const u8).empty;
        var txi: u32 = 0;
        var tx_start: usize = 0;
        var seg = false;
        var outs = std.ArrayList(struct { vout: u32, ser: []const u8 }).empty;
        var ins = std.ArrayList(Key).empty;
        var vout: u32 = 0;
        var in_cb_witness = false;
        for (rows, 0..) |r, ri| {
            switch (r.kind) {
                fields.K_TXH => {
                    tx_start = r.start;
                    seg = r.seg;
                    if (seg) any_witness = true;
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
                    const o = raw[r.start .. r.start + r.len];
                    try outs.append(a, .{ .vout = vout, .ser = o });
                    if (txi == 0) try cb_outs.append(a, o);
                    vout += 1;
                },
                // The coinbase has one input, so its witness is the first stack.
                fields.K_WCNT => if (txi == 0) {
                    in_cb_witness = true;
                    cb_items = r.val;
                },
                fields.K_WITEM => if (txi == 0 and in_cb_witness and r.val == 32 and cb_items == 1) {
                    nonce = raw[r.start + r.pref ..][0..32].*;
                },
                fields.K_LOCK => {
                    const id = EP.txidOf(raw, tx_start, rows, ri, seg);
                    try txids.append(a, id);
                    if (txi == 0) {
                        try wtxids.append(a, @splat(0));
                    } else if (seg) {
                        try wtxids.append(a, sha256d(raw[tx_start .. r.start + 4]));
                    } else try wtxids.append(a, id);
                    for (ins.items) |k| {
                        const kv = self.map.fetchRemove(k) orelse return error.MissingCoin;
                        self.live -= kv.value.len;
                        if (want) {
                            var b: [4]u8 = undefined;
                            std.mem.writeInt(u32, &b, kv.value.code, .little);
                            try undo.appendSlice(a, &b);
                            try undo.appendSlice(a, self.ser(kv.value));
                            std.mem.writeInt(u32, &b, kv.value.txi, .little);
                            try ctx.appendSlice(a, &b);
                        }
                    }
                    const lost = txi == 0 and (height == 0 or height == 91722 or height == 91812);
                    if (!lost) for (outs.items) |o| {
                        const sl = o.ser[8];
                        const hdr: usize = if (sl < 253) 1 else 3;
                        if (EP.unspendable(o.ser[8 + hdr ..])) continue;
                        try self.put(.{ .txid = id, .vout = o.vout }, 2 * height + @intFromBool(txi == 0), txi, o.ser);
                    };
                    txi += 1;
                    in_cb_witness = false;
                },
                else => {},
            }
        }
        var mutated = false;
        const root = try merkleRoot(a, txids.items, &mutated);
        if (mutated) return error.MutatedMerkle;
        if (!std.mem.eql(u8, &root, raw[36..68])) return error.BadMerkleRoot;
        try checkWitness(a, cb_outs.items, wtxids.items, nonce, cb_items, any_witness, height >= SEGWIT_HEIGHT);
        if (!want) return null;
        return .{ .undo = try undo.toOwnedSlice(a), .ctx = try ctx.toOwnedSlice(a) };
    }

    /// Writes the set in `epoch.encodeSet`'s format (sorted by outpoint) to `path`, atomically.
    pub fn writeFile(self: *const Set, path: []const u8) !SetInfo {
        const n = self.map.count();
        if (n > std.math.maxInt(u32)) return error.TooManyCoins;
        const Ent = struct { k: *const Key, v: *const Val };
        const ents = try self.gpa.alloc(Ent, n);
        defer self.gpa.free(ents);
        var it = self.map.iterator();
        var i: usize = 0;
        while (it.next()) |e| : (i += 1) ents[i] = .{ .k = e.key_ptr, .v = e.value_ptr };
        std.sort.pdq(Ent, ents, {}, struct {
            fn less(_: void, x: Ent, y: Ent) bool {
                return keyLess({}, x.k.*, y.k.*);
            }
        }.less);
        var tmp_buf: [std.fs.max_path_bytes]u8 = undefined;
        const tmp = try std.fmt.bufPrint(&tmp_buf, "{s}.tmp", .{path});
        const f = try std.fs.cwd().createFile(tmp, .{ .truncate = true });
        defer f.close();
        var buf: [1 << 20]u8 = undefined;
        var fw = f.writer(&buf);
        var w = HashingWriter{ .w = &fw.interface };
        var hs = Sha256.init(.{});
        var amount: u64 = 0;
        try w.int(@intCast(n));
        for (ents) |e| {
            const s = self.ser(e.v.*);
            try w.bytes(&e.k.txid);
            try w.int(e.k.vout);
            try w.int(e.v.code >> 1);
            try w.bytes(&.{@as(u8, @intCast(e.v.code & 1))});
            try w.int(e.v.txi);
            try w.int(e.v.len);
            try w.bytes(s);
            var b: [8]u8 = undefined;
            hs.update(&e.k.txid);
            std.mem.writeInt(u32, b[0..4], e.k.vout, .little);
            std.mem.writeInt(u32, b[4..8], e.v.code, .little);
            hs.update(&b);
            hs.update(s);
            amount += std.mem.readInt(u64, s[0..8], .little);
        }
        try fw.interface.flush();
        try f.sync();
        try std.fs.cwd().rename(tmp, path);
        var info = SetInfo{ .count = n, .amount = amount, .hash = undefined, .digest = undefined };
        var h1: [32]u8 = undefined;
        hs.final(&h1);
        Sha256.hash(&h1, &info.hash, .{});
        std.mem.reverse(u8, &info.hash);
        w.b2.final(&info.digest);
        return info;
    }

    /// Loads a set file (`epoch.decodeSet`'s checks, streamed): strictly sorted, every coin created
    /// before block `from`.
    pub fn loadFile(self: *Set, path: []const u8, from: u32) !SetInfo {
        const f = try std.fs.cwd().openFile(path, .{});
        defer f.close();
        var buf: [1 << 20]u8 = undefined;
        var fr = f.reader(&buf);
        const r = &fr.interface;
        var b2 = Blake2s.init(.{});
        var hs = Sha256.init(.{});
        var nb: [4]u8 = undefined;
        try r.readSliceAll(&nb);
        b2.update(&nb);
        const n = std.mem.readInt(u32, &nb, .little);
        try self.map.ensureTotalCapacity(self.gpa, n);
        var prev: ?Key = null;
        var amount: u64 = 0;
        var s_buf = std.ArrayListUnmanaged(u8).empty;
        defer s_buf.deinit(self.gpa);
        for (0..n) |_| {
            var head: [32 + 4 + 4 + 1 + 4 + 4]u8 = undefined;
            try r.readSliceAll(&head);
            b2.update(&head);
            var k: Key = undefined;
            @memcpy(&k.txid, head[0..32]);
            k.vout = std.mem.readInt(u32, head[32..36], .little);
            const height = std.mem.readInt(u32, head[36..40], .little);
            const cb = head[40];
            const txi = std.mem.readInt(u32, head[41..45], .little);
            const l = std.mem.readInt(u32, head[45..49], .little);
            if (cb > 1) return error.BadCoinbaseFlag;
            if (height >= 1 << 31 or l >= 0x7fffffff) return error.CoinOutOfRange;
            if (height >= from) return error.PrevSetTooNew;
            if (prev) |p| if (!keyLess({}, p, k)) return error.SetNotSorted;
            prev = k;
            try s_buf.resize(self.gpa, l);
            try r.readSliceAll(s_buf.items);
            b2.update(s_buf.items);
            if (l < 8) return error.CoinOutOfRange;
            const code = 2 * height + cb;
            try self.put(k, code, txi, s_buf.items);
            var hb: [8]u8 = undefined;
            hs.update(&k.txid);
            std.mem.writeInt(u32, hb[0..4], k.vout, .little);
            std.mem.writeInt(u32, hb[4..8], code, .little);
            hs.update(&hb);
            hs.update(s_buf.items);
            amount += std.mem.readInt(u64, s_buf.items[0..8], .little);
        }
        if (r.takeByte()) |_| return error.TrailingBytes else |e| if (e != error.EndOfStream) return e;
        var info = SetInfo{ .count = n, .amount = amount, .hash = undefined, .digest = undefined };
        var h1: [32]u8 = undefined;
        hs.final(&h1);
        Sha256.hash(&h1, &info.hash, .{});
        std.mem.reverse(u8, &info.hash);
        b2.final(&info.digest);
        return info;
    }
};

/// A writer that also hashes what it writes (the set's digest, `epoch.setDigest`).
const HashingWriter = struct {
    w: *std.Io.Writer,
    b2: Blake2s = Blake2s.init(.{}),

    fn bytes(self: *HashingWriter, b: []const u8) !void {
        self.b2.update(b);
        try self.w.writeAll(b);
    }

    fn int(self: *HashingWriter, x: u32) !void {
        var b: [4]u8 = undefined;
        std.mem.writeInt(u32, &b, x, .little);
        try self.bytes(&b);
    }
};

fn sha256d(b: []const u8) [32]u8 {
    var h1: [32]u8 = undefined;
    var out: [32]u8 = undefined;
    Sha256.hash(b, &h1, .{});
    Sha256.hash(&h1, &out, .{});
    return out;
}

/// Core's `ComputeMerkleRoot`: `mutated` when a level has two equal adjacent hashes (CVE-2012-2459).
pub fn merkleRoot(a: std.mem.Allocator, leaves: []const [32]u8, mutated: ?*bool) ![32]u8 {
    if (leaves.len == 0) return error.EmptyBlock;
    const hs = try a.alloc([32]u8, leaves.len + 1);
    @memcpy(hs[0..leaves.len], leaves);
    var n = leaves.len;
    while (n > 1) {
        if (mutated) |m| {
            var p: usize = 0;
            while (p + 1 < n) : (p += 2) if (std.mem.eql(u8, &hs[p], &hs[p + 1])) {
                m.* = true;
            };
        }
        if (n & 1 == 1) {
            hs[n] = hs[n - 1];
            n += 1;
        }
        for (0..n / 2) |i| {
            var pair: [64]u8 = undefined;
            @memcpy(pair[0..32], &hs[2 * i]);
            @memcpy(pair[32..64], &hs[2 * i + 1]);
            hs[i] = sha256d(&pair);
        }
        n /= 2;
    }
    return hs[0];
}

/// Core's `CheckWitnessMalleation`: with segwit active and a commitment (the coinbase's last output
/// starting `6a24aa21a9ed`), the coinbase witness is one 32-byte nonce and the commitment is
/// SHA256d(witness root ‖ nonce); otherwise no transaction has witness data.
fn checkWitness(a: std.mem.Allocator, cb_outs: []const []const u8, wtxids: []const [32]u8, nonce: ?[32]u8, cb_items: u32, any_witness: bool, active: bool) !void {
    if (active) {
        var commit: ?[]const u8 = null;
        for (cb_outs) |o| {
            const hdr: usize = switch (o[8]) {
                0...252 => 1,
                253 => 3,
                else => 5,
            };
            const script = o[8 + hdr ..];
            if (script.len >= 38 and std.mem.eql(u8, script[0..6], &.{ 0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed })) commit = script[6..38];
        }
        if (commit) |c| {
            if (cb_items != 1) return error.BadWitnessNonceSize;
            const nc = nonce orelse return error.BadWitnessNonceSize;
            const root = try merkleRoot(a, wtxids, null);
            var pair: [64]u8 = undefined;
            @memcpy(pair[0..32], &root);
            @memcpy(pair[32..64], &nc);
            if (!std.mem.eql(u8, &sha256d(&pair), c)) return error.BadWitnessMerkleMatch;
            return;
        }
    }
    if (any_witness) return error.UnexpectedWitness;
}

const testing = std.testing;

test "replay: genesis; a wrong header or Merkle root is rejected" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const raw0 = @embedFile("testdata:block_0");
    var set = try Set.init(testing.allocator, 0);
    defer set.deinit();
    var header: [80]u8 = raw0[0..80].*;
    const und0 = (try set.apply(a, raw0, &header, 0, true)).?;
    try testing.expectEqualSlices(u8, &.{1}, und0.undo);
    try testing.expectEqual(@as(usize, 0), und0.ctx.len);
    try testing.expectEqual(@as(usize, 0), set.count());
    // A wrong header, a flipped Merkle root.
    header[5] ^= 1;
    try testing.expectError(error.HeaderMismatch, set.apply(a, raw0, &header, 0, false));
    const bad = try a.dupe(u8, raw0);
    bad[40] ^= 1;
    try testing.expectError(error.BadMerkleRoot, set.apply(a, bad, bad[0..80], 0, false));
}

test "replay: merkle mutation (CVE-2012-2459)" {
    var arena = std.heap.ArenaAllocator.init(testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const l = [_][32]u8{ @splat(1), @splat(2), @splat(3) };
    const l4 = [_][32]u8{ @splat(1), @splat(2), @splat(3), @splat(3) };
    var m = false;
    const r3 = try merkleRoot(a, &l, &m);
    try testing.expect(!m);
    const r4 = try merkleRoot(a, &l4, &m);
    try testing.expect(m);
    try testing.expectEqualSlices(u8, &r3, &r4);
}
