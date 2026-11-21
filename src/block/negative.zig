//! Tests of the block system (M3a.5) on synthetic blocks: valid edge cases are accepted, and each
//! invalid block, with its witness forced through (`Ctx.force`), violates a constraint or leaves a
//! lookup unbalanced.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const checks = @import("checks.zig");
const bsys = @import("system.zig");
const walk = @import("walk.zig");

const Sha = std.crypto.hash.sha2.Sha256;

fn sha256d(data: []const u8) [32]u8 {
    var h1: [32]u8 = undefined;
    Sha.hash(data, &h1, .{});
    var h2: [32]u8 = undefined;
    Sha.hash(&h1, &h2, .{});
    return h2;
}

pub const In = struct { hash: [32]u8 = [_]u8{7} ** 32, n: u32 = 0, script: []const u8 = &.{ 0x51, 0x51 }, seq: u32 = 0xffffffff };
pub const Out = struct { value: u64 = 5000000000, script: []const u8 = &.{0x51} };
pub const Tx = struct {
    version: u32 = 1,
    ins: []const In,
    outs: []const Out,
    /// One stack per input (segwit serialization when any is non-empty).
    wit: ?[]const []const []const u8 = null,
    lock: u32 = 0,
};

const W = std.ArrayList(u8);

fn compact(a: std.mem.Allocator, w: *W, n: usize) !void {
    if (n < 253) try w.append(a, @intCast(n)) else if (n <= 0xffff) {
        try w.append(a, 253);
        try w.appendSlice(a, &std.mem.toBytes(std.mem.nativeToLittle(u16, @intCast(n))));
    } else {
        try w.append(a, 254);
        try w.appendSlice(a, &std.mem.toBytes(std.mem.nativeToLittle(u32, @intCast(n))));
    }
}

fn int(a: std.mem.Allocator, w: *W, comptime T: type, v: T) !void {
    try w.appendSlice(a, &std.mem.toBytes(std.mem.nativeToLittle(T, v)));
}

fn hasWit(tx: Tx) bool {
    const ws = tx.wit orelse return false;
    for (ws) |s| if (s.len > 0) return true;
    return false;
}

pub fn serTx(a: std.mem.Allocator, w: *W, tx: Tx, with_wit: bool) !void {
    const seg = with_wit and hasWit(tx);
    try int(a, w, u32, tx.version);
    if (seg) try w.appendSlice(a, &.{ 0, 1 });
    try compact(a, w, tx.ins.len);
    for (tx.ins) |i| {
        try w.appendSlice(a, &i.hash);
        try int(a, w, u32, i.n);
        try compact(a, w, i.script.len);
        try w.appendSlice(a, i.script);
        try int(a, w, u32, i.seq);
    }
    try compact(a, w, tx.outs.len);
    for (tx.outs) |o| {
        try int(a, w, u64, o.value);
        try compact(a, w, o.script.len);
        try w.appendSlice(a, o.script);
    }
    if (seg) for (tx.wit.?) |stack| {
        try compact(a, w, stack.len);
        for (stack) |item| {
            try compact(a, w, item.len);
            try w.appendSlice(a, item);
        }
    };
    try int(a, w, u32, tx.lock);
}

fn txHash(a: std.mem.Allocator, tx: Tx, with_wit: bool) ![32]u8 {
    var w = W.empty;
    try serTx(a, &w, tx, with_wit);
    return sha256d(w.items);
}

fn merkleRoot(a: std.mem.Allocator, leaves: []const [32]u8) ![32]u8 {
    var level = try a.dupe([32]u8, leaves);
    while (level.len > 1) {
        const next = try a.alloc([32]u8, (level.len + 1) / 2);
        for (next, 0..) |*h, i| {
            var buf: [64]u8 = undefined;
            @memcpy(buf[0..32], &level[2 * i]);
            @memcpy(buf[32..], &level[@min(2 * i + 1, level.len - 1)]);
            h.* = sha256d(&buf);
        }
        level = next;
    }
    return level[0];
}

/// The witness commitment script for `txs` (the coinbase's wtxid counts as zero) and `nonce`.
pub fn commitmentScript(a: std.mem.Allocator, txs: []const Tx, nonce: [32]u8) ![]u8 {
    const leaves = try a.alloc([32]u8, txs.len);
    leaves[0] = [_]u8{0} ** 32;
    for (txs[1..], leaves[1..]) |t, *l| l.* = try txHash(a, t, true);
    const root = try merkleRoot(a, leaves);
    var buf: [64]u8 = undefined;
    @memcpy(buf[0..32], &root);
    @memcpy(buf[32..], &nonce);
    const c = sha256d(&buf);
    const s = try a.alloc(u8, 38);
    @memcpy(s[0..6], &checks.PATTERN);
    @memcpy(s[6..], &c);
    return s;
}

/// A block: a header template with the Merkle root and time filled in, the count, the transactions.
pub fn block(a: std.mem.Allocator, txs: []const Tx, time: u32) ![]u8 {
    var w = W.empty;
    const hdr = @embedFile("testdata:block_170")[0..80];
    try w.appendSlice(a, hdr);
    const ids = try a.alloc([32]u8, txs.len);
    for (txs, ids) |t, *id| id.* = try txHash(a, t, false);
    const root = try merkleRoot(a, ids);
    @memcpy(w.items[36..68], &root);
    std.mem.writeInt(u32, w.items[68..72], time, .little);
    try compact(a, &w, txs.len);
    for (txs) |t| try serTx(a, &w, t, true);
    return w.toOwnedSlice(a);
}

const Verdict = enum { accepted, rejected };

fn judge(a: std.mem.Allocator, raw: []const u8, ctx: checks.Ctx) !Verdict {
    var c = ctx;
    c.force = true;
    const airs = try bsys.parseAirs(a);
    const b = bsys.build(a, raw, c) catch |e| {
        std.debug.print("  (witness generation failed: {s})\n", .{@errorName(e)});
        return .rejected;
    };
    if (try bsys.firstViolation(a, &airs, &b)) |v| {
        std.debug.print("  {s} row {d} violates constraint {d}\n", .{ bsys.names[v.comp], v.row, v.constraint });
        return .rejected;
    }
    if (try bsys.unbalanced(a, &airs, &b)) |rel| {
        std.debug.print("  relation {d} unbalanced\n", .{rel});
        return .rejected;
    }
    return .accepted;
}

const cb_script = [_]u8{ 0x04, 0xff, 0xff, 0x00, 0x1d };
const null_in = In{ .hash = [_]u8{0} ** 32, .n = 0xffffffff, .script = &cb_script };

fn legacy(a: std.mem.Allocator, tx1: Tx) ![]u8 {
    const txs = [_]Tx{ .{ .ins = &.{null_in}, .outs = &.{.{}} }, tx1 };
    return block(a, &txs, 1231731025);
}

const pre_ctx = checks.Ctx{ .height = 1000, .prev_mtp = 1231700000 };

test "block negative: mutated legacy blocks are rejected; the unmutated one is accepted" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const ok_tx = Tx{ .ins = &.{.{}}, .outs = &.{ .{ .value = 1000 }, .{ .value = 2000 } } };
    std.debug.print("valid legacy block\n", .{});
    try std.testing.expectEqual(Verdict.accepted, try judge(a, try legacy(a, ok_tx), pre_ctx));

    const max: u64 = 2100000000000000;
    const cases = [_]struct { name: []const u8, tx: Tx, ctx: checks.Ctx = pre_ctx }{
        .{ .name = "negative value", .tx = .{ .ins = &.{.{}}, .outs = &.{.{ .value = @bitCast(@as(i64, -1)) }} } },
        .{ .name = "value above MAX_MONEY", .tx = .{ .ins = &.{.{}}, .outs = &.{.{ .value = max + 1 }} } },
        .{ .name = "total above MAX_MONEY", .tx = .{ .ins = &.{.{}}, .outs = &.{ .{ .value = max / 2 + 1 }, .{ .value = max / 2 + 1 } } } },
        .{ .name = "value 2^51 (byte 6 = 8)", .tx = .{ .ins = &.{.{}}, .outs = &.{.{ .value = 1 << 51 }} } },
        .{ .name = "no outputs", .tx = .{ .ins = &.{.{}}, .outs = &.{} } },
        .{ .name = "second coinbase", .tx = .{ .ins = &.{null_in}, .outs = &.{.{}} } },
        .{ .name = "null prevout among inputs", .tx = .{ .ins = &.{ .{}, .{ .hash = [_]u8{0} ** 32, .n = 0xffffffff } }, .outs = &.{.{}} } },
        .{ .name = "lock time at the height (non-final)", .tx = .{ .ins = &.{.{ .seq = 0 }}, .outs = &.{.{}}, .lock = 1000 } },
        .{ .name = "lock time above the height", .tx = .{ .ins = &.{.{ .seq = 0 }}, .outs = &.{.{}}, .lock = 5000 } },
        .{ .name = "time lock at the cutoff", .tx = .{ .ins = &.{.{ .seq = 0 }}, .outs = &.{.{}}, .lock = 1231731025 } },
        .{ .name = "one non-final sequence among final ones", .tx = .{ .ins = &.{ .{}, .{ .n = 1, .seq = 0xfffffffe } }, .outs = &.{.{}}, .lock = 2000 } },
        .{ .name = "BIP34 height missing", .tx = ok_tx, .ctx = .{ .height = 300000, .prev_mtp = 1231700000 } },
    };
    for (cases) |c| {
        std.debug.print("{s}\n", .{c.name});
        const raw = try legacy(a, c.tx);
        try std.testing.expectEqual(Verdict.rejected, try judge(a, raw, c.ctx));
    }
    // Final despite a lock time: below the height, below the cutoff, or all sequences final.
    const finals = [_]Tx{
        .{ .ins = &.{.{ .seq = 0 }}, .outs = &.{.{}}, .lock = 999 },
        .{ .ins = &.{.{ .seq = 0 }}, .outs = &.{.{}}, .lock = 1231731024 },
        .{ .ins = &.{ .{}, .{ .n = 1 } }, .outs = &.{.{}}, .lock = 0xffffffff },
    };
    for (finals) |t| {
        std.debug.print("final with lock time {d}\n", .{t.lock});
        try std.testing.expectEqual(Verdict.accepted, try judge(a, try legacy(a, t), pre_ctx));
    }
}

test "block negative: sigop counting matches Core's on edge-case scripts; too many sigops are rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const scripts = [_][]const u8{
        &.{ 0x4e, 0xff, 0xff, 0xff, 0x7f, 0xac }, // truncated PUSHDATA4 (length > rest)
        &.{ 0x4e, 0x00, 0x00, 0x00, 0x02, 0xac, 0xac }, // PUSHDATA4 of 2^25 bytes (runs to the end)
        &.{ 0x4e, 0x01, 0x00, 0x00, 0x00, 0xac, 0xae }, // PUSHDATA4 of one byte, then CHECKMULTISIG
        &.{ 0x4d, 0x01 }, // truncated length bytes
        &.{ 0x4c, 0x00, 0xac, 0x4c }, // empty PUSHDATA1, CHECKSIG, truncated PUSHDATA1
        &.{ 0x02, 0xac, 0xac, 0xad, 0xaf, 0x00, 0xae }, // push over sigops, then three
        &([_]u8{ 0x4d, 0x00, 0x01 } ++ [_]u8{0xac} ** 10), // PUSHDATA2 of 256 bytes (truncated)
    };
    var outs = std.ArrayList(Out).empty;
    var want: u32 = 1; // the coinbase output's sigops (none) + this tx: computed below
    want = 0;
    for (scripts) |s| {
        try outs.append(a, .{ .value = 1, .script = s });
        want += walk.sigOps(s);
    }
    const tx = Tx{ .ins = &.{.{}}, .outs = outs.items };
    const raw = try legacy(a, tx);
    const b = try bsys.build(a, raw, pre_ctx);
    const airs = try bsys.parseAirs(a);
    try std.testing.expect(try bsys.firstViolation(a, &airs, &b) == null);
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
    try std.testing.expectEqual(want, b.sigops);
    std.debug.print("edge-case scripts: {d} sigops, as Core counts\n", .{b.sigops});

    // 1001 CHECKMULTISIGs: 20,020 sigops.
    const heavy = [_]u8{0xae} ** 1001;
    std.debug.print("20,020 sigops\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try legacy(a, .{ .ins = &.{.{}}, .outs = &.{.{ .script = &heavy }} }), pre_ctx));
    const ok = [_]u8{0xae} ** 1000;
    std.debug.print("20,000 sigops\n", .{});
    try std.testing.expectEqual(Verdict.accepted, try judge(a, try legacy(a, .{ .ins = &.{.{}}, .outs = &.{.{ .script = &ok }} }), pre_ctx));
}

/// A segwit block at `height`: a BIP34 coinbase with the witness nonce and the commitment (unless
/// `commit` is false), and a segwit spend.
fn segwitBlock(a: std.mem.Allocator, height: u32, opts: struct { commit: bool = true, decoy: bool = false, nonce_len: usize = 32, tamper: bool = false, version: u32 = 2, seq: u32 = 0xffffffff, cb_version: u32 = 1, cb_seq: u32 = 0xffffffff }) ![]u8 {
    const nonce = [_]u8{0x42} ** 32;
    var cbs = std.ArrayList(u8).empty;
    try cbs.appendSlice(a, &.{ 0x03, @intCast(height & 0xff), @intCast((height >> 8) & 0xff), @intCast(height >> 16), 0xaa, 0xbb });
    const sig = [_]u8{0x30} ** 71;
    const pk = [_]u8{0x02} ** 33;
    const stack1 = [_][]const u8{ &sig, &pk };
    const tx1 = Tx{ .version = opts.version, .ins = &.{.{ .script = &.{}, .seq = opts.seq }}, .outs = &.{.{ .value = 1000, .script = &([_]u8{ 0x00, 0x14 } ++ [_]u8{0x11} ** 20) }}, .wit = &.{&stack1} };
    const nonce_item = try a.alloc(u8, opts.nonce_len);
    @memset(nonce_item, 0x42);
    const cb_stack = [_][]const u8{nonce_item};
    var cb = Tx{ .version = opts.cb_version, .ins = &.{.{ .hash = [_]u8{0} ** 32, .n = 0xffffffff, .script = cbs.items, .seq = opts.cb_seq }}, .outs = &.{.{}}, .wit = &.{&cb_stack} };
    var txs = [_]Tx{ cb, tx1 };
    const cscript = try commitmentScript(a, &txs, nonce);
    var outs = std.ArrayList(Out).empty;
    try outs.append(a, .{ .value = 625000000, .script = &.{0x51} });
    if (opts.commit) try outs.append(a, .{ .value = 0, .script = cscript });
    if (opts.decoy) {
        const d = try a.dupe(u8, cscript);
        d[37] ^= 1;
        try outs.append(a, .{ .value = 0, .script = d });
    }
    cb.outs = outs.items;
    txs[0] = cb;
    if (opts.tamper) {
        const sig2 = try a.dupe(u8, &sig);
        sig2[5] ^= 1;
        const st = try a.alloc([]const u8, 2);
        st[0] = sig2;
        st[1] = &pk;
        const ws = try a.alloc([]const []const u8, 1);
        ws[0] = st;
        txs[1].wit = ws;
    }
    return block(a, &txs, 1700000000);
}

test "block negative: segwit commitment cases" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };
    std.debug.print("valid segwit block\n", .{});
    try std.testing.expectEqual(Verdict.accepted, try judge(a, try segwitBlock(a, 500000, .{}), ctx));
    std.debug.print("segwit block before activation (unexpected witness)\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 470000, .{}), .{ .height = 470000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") }));
    std.debug.print("no commitment output, witness present\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .commit = false }), ctx));
    std.debug.print("tampered witness (txid unchanged)\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .tamper = true }), ctx));
    std.debug.print("later decoy commitment output\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .decoy = true }), ctx));
    std.debug.print("nonce of 33 bytes\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .nonce_len = 33 }), ctx));
}

test "block negative: a CSV-era block proves and verifies with its ancestry; a wrong MTP fails" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const raw = try segwitBlock(a, 500000, .{});
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };
    const b = try bsys.build(a, raw, ctx);
    try std.testing.expect(b.log_size >= 12);
    try bsys.proveVerify(a, &airs, &b);
    std.debug.print("CSV-era block (height 500000, log {d}): proved and verified with its ancestry\n", .{b.log_size});
    // The MTP's public limb one off, the ancestry trace forced to match: rejected.
    var c = ctx;
    c.prev_mtp += 1;
    try std.testing.expectEqual(Verdict.rejected, try judge(a, raw, c));
}

test "block negative: BIP68 height-based relative locks (CONNECT-RULES step 2)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };
    // The synthetic undo's coins are from height 499,999: a lock of 1 block is met, 2 is not.
    const Case = struct { name: []const u8, version: u32 = 2, seq: u32, want: Verdict };
    const cases = [_]Case{
        .{ .name = "lock 0", .seq = 0, .want = .accepted },
        .{ .name = "lock 1", .seq = 1, .want = .accepted },
        .{ .name = "lock 2", .seq = 2, .want = .rejected },
        .{ .name = "lock 65535", .seq = 0xffff, .want = .rejected },
        .{ .name = "lock 1, the unused bits 16-21 and 23-30 set", .seq = 0x7fbf0001, .want = .accepted },
        .{ .name = "lock 2, the unused bits 16-21 and 23-30 set", .seq = 0x7fbf0002, .want = .rejected },
        .{ .name = "lock 2, disabled (bit 31)", .seq = 0x80000002, .want = .accepted },
        .{ .name = "lock 2, version 1", .version = 1, .seq = 2, .want = .accepted },
        .{ .name = "lock 2, version 0", .version = 0, .seq = 2, .want = .accepted },
        .{ .name = "lock 2, version 256", .version = 256, .seq = 2, .want = .rejected },
        .{ .name = "lock 2, version 0xffffffff (unsigned)", .version = 0xffffffff, .seq = 2, .want = .rejected },
        // A time-based lock against a claimed MTP of 0 (the default): met. Whether the claim is the
        // chain's MTP is the resolver's check, not the block's (step 4, docs/design/connect-rules.md).
        .{ .name = "time lock 2 (bit 22), claim 0", .seq = 0x00400002, .want = .accepted },
    };
    for (cases) |c| {
        std.debug.print("BIP68: {s}\n", .{c.name});
        try std.testing.expectEqual(c.want, try judge(a, try segwitBlock(a, 500000, .{ .version = c.version, .seq = c.seq }), ctx));
    }
    // The coinbase's input is not checked (Core calls SequenceLocks for non-coinbase transactions only).
    std.debug.print("BIP68: coinbase of version 2 with sequence 2\n", .{});
    try std.testing.expectEqual(Verdict.accepted, try judge(a, try segwitBlock(a, 500000, .{ .cb_version = 2, .cb_seq = 2 }), ctx));
    // Before CSV activation nothing is enforced.
    std.debug.print("BIP68: lock 2 at height 1000 (before CSV)\n", .{});
    const pre = try legacy(a, .{ .version = 2, .ins = &.{.{ .seq = 2 }}, .outs = &.{.{}} });
    try std.testing.expectEqual(Verdict.accepted, try judge(a, pre, pre_ctx));
}

fn judgeM(a: std.mem.Allocator, raw: []const u8, mtps: []const u32, ctx: checks.Ctx) !Verdict {
    var c = ctx;
    c.force = true;
    const airs = try bsys.parseAirs(a);
    const b = bsys.buildFull(a, raw, try bsys.syntheticUndo(a, raw, c.height), c, .{ .mtps = mtps }) catch |e| {
        std.debug.print("  (witness generation failed: {s})\n", .{@errorName(e)});
        return .rejected;
    };
    if (try bsys.firstViolation(a, &airs, &b)) |v| {
        std.debug.print("  {s} row {d} violates constraint {d}\n", .{ bsys.names[v.comp], v.row, v.constraint });
        return .rejected;
    }
    if (try bsys.unbalanced(a, &airs, &b)) |rel| {
        std.debug.print("  relation {d} unbalanced\n", .{rel});
        return .rejected;
    }
    return .accepted;
}

test "block negative: BIP68 time-based relative locks against the claimed MTP (CONNECT-RULES step 4)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const prev: u32 = 1231715347;
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = prev, .anc = checks.ancOf("170") };
    // Core: the lock is met when prev_mtp >= claim + 512 * lock (claim: the MTP of the block before the coin's).
    const Case = struct { name: []const u8, seq: u32, version: u32 = 2, claim: u32, want: Verdict, nclaims: usize };
    const cases = [_]Case{
        .{ .name = "lock 2, claim = prev - 1024 (exactly met)", .seq = 0x00400002, .claim = prev - 1024, .want = .accepted, .nclaims = 1 },
        .{ .name = "lock 2, claim = prev - 1023", .seq = 0x00400002, .claim = prev - 1023, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2, claim = prev", .seq = 0x00400002, .claim = prev, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2, claim = prev + 1", .seq = 0x00400002, .claim = prev + 1, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2, claim = 0xffffffff", .seq = 0x00400002, .claim = 0xffffffff, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2, claim = prev - 1024 - 65536 (other limb)", .seq = 0x00400002, .claim = prev - 1024 - 65536, .want = .accepted, .nclaims = 1 },
        .{ .name = "lock 2, claim = prev - 1024 + 65536", .seq = 0x00400002, .claim = prev - 1024 + 65536, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 1, claim = prev - 512", .seq = 0x00400001, .claim = prev - 512, .want = .accepted, .nclaims = 1 },
        .{ .name = "lock 1, claim = prev - 511", .seq = 0x00400001, .claim = prev - 511, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 65535, claim = prev - 512*65535", .seq = 0x0040ffff, .claim = prev - 512 * 65535, .want = .accepted, .nclaims = 1 },
        .{ .name = "lock 65535, claim = prev - 512*65535 + 1", .seq = 0x0040ffff, .claim = prev - 512 * 65535 + 1, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2 with the unused bits set, claim = prev - 1023", .seq = 0x7fff0002, .claim = prev - 1023, .want = .rejected, .nclaims = 1 },
        // A zero time lock is checked like any other: met by every true claim (the MTP never decreases).
        .{ .name = "lock 0, claim = prev", .seq = 0x00400000, .claim = prev, .want = .accepted, .nclaims = 1 },
        .{ .name = "lock 0, claim = prev + 1", .seq = 0x00400000, .claim = prev + 1, .want = .rejected, .nclaims = 1 },
        .{ .name = "lock 2 disabled (bit 31), claim = prev", .seq = 0x80400002, .claim = prev, .want = .accepted, .nclaims = 0 },
        .{ .name = "lock 2, version 1, claim = prev", .seq = 0x00400002, .version = 1, .claim = prev, .want = .accepted, .nclaims = 0 },
        .{ .name = "height lock 1 (no time bit), claim = prev", .seq = 1, .claim = prev, .want = .accepted, .nclaims = 0 },
    };
    for (cases) |c| {
        std.debug.print("BIP68 time: {s}\n", .{c.name});
        const raw = try segwitBlock(a, 500000, .{ .version = c.version, .seq = c.seq });
        try std.testing.expectEqual(c.want, try judgeM(a, raw, &.{c.claim}, ctx));
        if (c.want == .accepted) {
            // The claims the block adds to its public sum: one per enforced time lock.
            const b = try bsys.buildFull(a, raw, try bsys.syntheticUndo(a, raw, 500000), ctx, .{ .mtps = &.{c.claim} });
            try std.testing.expectEqual(c.nclaims, b.nclaims);
        }
    }
    // Without `force`, the witness builder refuses an unmet lock.
    const raw = try segwitBlock(a, 500000, .{ .seq = 0x00400002 });
    try std.testing.expectError(error.TimeLockNotMet, bsys.buildFull(a, raw, try bsys.syntheticUndo(a, raw, 500000), ctx, .{ .mtps = &.{prev - 1023} }));
}

test "block negative: BIP68 time claims: the honest claim is the median time past before the coin's block" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    // A chain whose header `i` has time `1000 + i`: the median of the 11 before block `c` is `1000 + c − 6`.
    const headers = try a.alloc([80]u8, 500000);
    for (headers, 0..) |*h, i| {
        @memset(h, 0);
        std.mem.writeInt(u32, h[68..72], @intCast(1000 + i), .little);
    }
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };
    const Case = struct { seq: u32, version: u32 = 2, want: u32 };
    // The synthetic undo's coins are from height 499,999.
    for ([_]Case{
        .{ .seq = 0x00400002, .want = 1000 + 499999 - 6 },
        .{ .seq = 0x00400000, .want = 1000 + 499999 - 6 },
        .{ .seq = 1, .want = 0 },
        .{ .seq = 0x80400002, .want = 0 },
        .{ .seq = 0x00400002, .version = 1, .want = 0 },
    }) |c| {
        const raw = try segwitBlock(a, 500000, .{ .version = c.version, .seq = c.seq });
        const claims = try bsys.timeClaims(a, raw, try bsys.syntheticUndo(a, raw, 500000), headers, 500000);
        try std.testing.expectEqualSlices(u32, &.{c.want}, claims);
        try std.testing.expectEqual(Verdict.accepted, try judgeM(a, raw, claims, ctx));
    }
    // Before CSV activation no claim is made.
    const pre = try legacy(a, .{ .version = 2, .ins = &.{.{ .seq = 0x00400002 }}, .outs = &.{.{}} });
    for (try bsys.timeClaims(a, pre, try bsys.syntheticUndo(a, pre, 1000), headers, 1000)) |m| try std.testing.expectEqual(@as(u32, 0), m);
}

test "block negative: BIP68: a forged lock bit is caught by the fields' constraint; a cleared one unbalances the input tuple" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const one = M31.one();
    const FIELDS = 1;
    const TABLES = 5;
    const COIN = 14;
    const C_KI = 1;
    const C_LKH = 165;
    const C_LB0 = 167;
    const F_KIN = 2;
    // A lock of 1 block on a coin from the block before: met.
    {
        var ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };
        ctx.force = false;
        const b = try bsys.build(a, try segwitBlock(a, 500000, .{ .seq = 1 }), ctx);
        try std.testing.expect(try bsys.firstViolation(a, &airs, &b) == null);
        try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
        const cm = b.mains[COIN];
        const r = for (0..cm[C_KI].len) |q| {
            if (cm[C_KI][q].eql(one)) break q;
        } else unreachable;
        try std.testing.expect(cm[C_LKH][r].eql(one));
        // The coin row drops its lock bit: its constraints hold, but its input tuple is no longer the fields'.
        cm[C_LKH][r] = M31.zero();
        try std.testing.expect(try bsys.unbalanced(a, &airs, &b) != null);
    }
    // A lock of 2 blocks: not met. The forger clears the bit on both sides and withdraws the range uses.
    {
        const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170"), .force = true };
        const b = try bsys.build(a, try segwitBlock(a, 500000, .{ .seq = 2 }), ctx);
        const v0 = (try bsys.firstViolation(a, &airs, &b)).?;
        try std.testing.expectEqual(@as(usize, COIN), v0.comp);
        const cm = b.mains[COIN];
        const fm = b.mains[FIELDS];
        const rg = b.mains[TABLES][0];
        const r = for (0..cm[C_KI].len) |q| {
            if (cm[C_KI][q].eql(one)) break q;
        } else unreachable;
        // The transaction's input row in the fields: the second input row (the first is the coinbase's).
        var seen: usize = 0;
        const fr = for (0..fm[F_KIN].len) |q| {
            if (fm[F_KIN][q].eql(one)) {
                seen += 1;
                if (seen == 2) break q;
            }
        } else unreachable;
        try std.testing.expect(fm[checks.LKH][fr].eql(one));
        cm[C_LKH][r] = M31.zero();
        for (0..3) |i| {
            const v = cm[C_LB0 + i][r].toU32();
            rg[v] = rg[v].sub(one);
            cm[C_LB0 + i][r] = M31.zero();
        }
        fm[checks.LKH][fr] = M31.zero();
        // Every lookup balances; only the fields' definition of the bit stands in the way.
        try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
        const v1 = (try bsys.firstViolation(a, &airs, &b)).?;
        try std.testing.expectEqual(@as(usize, FIELDS), v1.comp);
    }
}

// ---- CONNECT-RULES step 3: the full sigop cost ----

const rules = @import("connect_rules.zig");

/// One input of the synthetic spend: its scriptSig, its witness stack and the script it spends.
const SigIn = struct { sig: []const u8 = &.{}, wit: []const []const u8 = &.{}, spent: []const u8 };

/// A script that pushes `data` (direct push, `PUSHDATA1` or `PUSHDATA2`).
fn push(a: std.mem.Allocator, data: []const u8) ![]u8 {
    var w = W.empty;
    if (data.len < 0x4c) try w.append(a, @intCast(data.len)) else if (data.len <= 0xff) {
        try w.appendSlice(a, &.{ 0x4c, @intCast(data.len) });
    } else {
        try w.appendSlice(a, &.{ 0x4d, @intCast(data.len & 0xff), @intCast(data.len >> 8) });
    }
    try w.appendSlice(a, data);
    return w.toOwnedSlice(a);
}

const p2sh_spk = [_]u8{ 0xa9, 0x14 } ++ [_]u8{0x11} ** 20 ++ [_]u8{0x87};
const p2wpkh_spk = [_]u8{ 0x00, 0x14 } ++ [_]u8{0x11} ** 20;
const p2wsh_spk = [_]u8{ 0x00, 0x20 } ++ [_]u8{0x22} ** 32;
const p2tr_spk = [_]u8{ 0x51, 0x20 } ++ [_]u8{0x33} ** 32;

/// A segwit block at `height` (BIP34 coinbase with the witness commitment) whose second transaction
/// has the inputs `ins` followed by a taproot key spend (so the transaction always carries a witness),
/// and the fetched undo stream that gives each input its spent script (coins from the block before).
fn sigBlock(a: std.mem.Allocator, height: u32, ins: []const SigIn) !struct { raw: []u8, undo: []u8 } {
    const nonce = [_]u8{0x42} ** 32;
    const cbs = [_]u8{ 0x03, @intCast(height & 0xff), @intCast((height >> 8) & 0xff), @intCast(height >> 16), 0xaa, 0xbb };
    const sig64 = [_]u8{0x30} ** 64;
    const all = try a.alloc(SigIn, ins.len + 1);
    @memcpy(all[0..ins.len], ins);
    const key_stack = try a.dupe([]const u8, &.{&sig64});
    all[ins.len] = .{ .wit = key_stack, .spent = &p2tr_spk };
    const tins = try a.alloc(In, all.len);
    const wits = try a.alloc([]const []const u8, all.len);
    var undo = W.empty;
    try undo.append(a, 1);
    for (all, tins, wits, 0..) |x, *ti, *wi, i| {
        ti.* = .{ .n = @intCast(i), .script = x.sig };
        wi.* = x.wit;
        try int(a, &undo, u32, 2 * (height - 1));
        try int(a, &undo, u64, 1000000);
        try compact(a, &undo, x.spent.len);
        try undo.appendSlice(a, x.spent);
    }
    const tx1 = Tx{ .version = 2, .ins = tins, .outs = &.{.{ .value = 1000, .script = &p2wpkh_spk }}, .wit = wits };
    const cb_stack = try a.dupe([]const u8, &.{&nonce});
    const cb_wit = try a.dupe([]const []const u8, &.{cb_stack});
    var cb = Tx{ .version = 2, .ins = try a.dupe(In, &.{.{ .hash = [_]u8{0} ** 32, .n = 0xffffffff, .script = try a.dupe(u8, &cbs) }}), .outs = &.{.{}}, .wit = cb_wit };
    var txs = [_]Tx{ cb, tx1 };
    const cscript = try commitmentScript(a, &txs, nonce);
    cb.outs = try a.dupe(Out, &.{ .{ .value = 625000000, .script = &.{0x51} }, .{ .value = 0, .script = cscript } });
    txs[0] = cb;
    return .{ .raw = try block(a, &txs, 1700000000), .undo = try undo.toOwnedSlice(a) };
}

const sig_ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1231715347, .anc = checks.ancOf("170") };

fn judgeU(a: std.mem.Allocator, raw: []const u8, undo: []const u8, ctx: checks.Ctx) !Verdict {
    var c = ctx;
    c.force = true;
    const airs = try bsys.parseAirs(a);
    const b = bsys.buildU(a, raw, undo, c) catch |e| {
        std.debug.print("  (witness generation failed: {s})\n", .{@errorName(e)});
        return .rejected;
    };
    if (try bsys.firstViolation(a, &airs, &b)) |v| {
        std.debug.print("  {s} row {d} violates constraint {d}\n", .{ bsys.names[v.comp], v.row, v.constraint });
        return .rejected;
    }
    if (try bsys.unbalanced(a, &airs, &b)) |rel| {
        std.debug.print("  relation {d} unbalanced\n", .{rel});
        return .rejected;
    }
    return .accepted;
}

test "block negative: sigop cost: P2SH and witness sigops are counted as Core counts them (CONNECT-RULES step 3)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const sig71 = [_]u8{0x30} ** 71;
    const pk = [_]u8{0x02} ** 33;
    // Redeem and witness scripts.
    const ms15 = [_]u8{0x5f} ++ [_]u8{0x21} ++ [_]u8{0x02} ** 33 ++ [_]u8{ 0x5f, 0xae }; // 15 … 15 CHECKMULTISIG
    const ms16v = [_]u8{ 0x60, 0xaf, 0x51, 0xae, 0xae, 0xac, 0xad }; // 16, 1, then 20 (after a multisig), 1, 1
    const long = [_]u8{0xac} ** 300; // through PUSHDATA2
    const mid = [_]u8{0xae} ** 100; // through PUSHDATA1
    const wprog20 = [_]u8{ 0x00, 0x14 } ++ [_]u8{0x55} ** 20;
    const wprog32 = [_]u8{ 0x00, 0x20 } ++ [_]u8{0x66} ** 32;
    const not22 = [_]u8{ 0x00, 0x15 } ++ [_]u8{0x55} ** 20; // 22 bytes, not a program
    const v1_34 = [_]u8{ 0x51, 0x20 } ++ [_]u8{0x66} ** 32; // 34 bytes, version 1
    const wscript = [_]u8{ 0x53, 0xae, 0xac, 0x02, 0xac, 0xac, 0xad }; // 3, 1, a push over two, 1: 5
    const cases = [_]struct { name: []const u8, in: SigIn, p2sh: u32 = 0, wit: u32 = 0 }{
        .{ .name = "P2SH, 15-of-15", .in = .{ .sig = try push(a, &ms15), .spent = &p2sh_spk }, .p2sh = 15 },
        .{ .name = "P2SH, 16 then 1 then two bare multisigs", .in = .{ .sig = try push(a, &ms16v), .spent = &p2sh_spk }, .p2sh = 16 + 1 + 20 + 2 },
        .{ .name = "P2SH, 300 CHECKSIGs through PUSHDATA2", .in = .{ .sig = try push(a, &long), .spent = &p2sh_spk }, .p2sh = 300 },
        .{ .name = "P2SH, 100 multisigs through PUSHDATA1", .in = .{ .sig = try push(a, &mid), .spent = &p2sh_spk }, .p2sh = 2000 },
        .{ .name = "P2SH, two pushes: the last is the redeem script", .in = .{ .sig = try std.mem.concat(a, u8, &.{ try push(a, &ms15), try push(a, &.{ 0xac, 0xac }) }), .spent = &p2sh_spk }, .p2sh = 2 },
        .{ .name = "P2SH, scriptSig not push-only (a NOP)", .in = .{ .sig = try std.mem.concat(a, u8, &.{ &.{0x61}, try push(a, &ms15) }), .spent = &p2sh_spk } },
        .{ .name = "P2SH, scriptSig ends in a truncated push", .in = .{ .sig = &.{ 0x01, 0xac, 0x05, 0xac, 0xac }, .spent = &p2sh_spk } },
        .{ .name = "P2SH, last operation is OP_1 (empty redeem script)", .in = .{ .sig = try std.mem.concat(a, u8, &.{ try push(a, &ms15), &.{0x51} }), .spent = &p2sh_spk } },
        .{ .name = "P2SH, last operation is an empty PUSHDATA1", .in = .{ .sig = try std.mem.concat(a, u8, &.{ try push(a, &ms15), &.{ 0x4c, 0x00 } }), .spent = &p2sh_spk } },
        .{ .name = "P2SH, OP_RESERVED (0x50) is push-only", .in = .{ .sig = try std.mem.concat(a, u8, &.{ &.{0x50}, try push(a, &.{0xac}) }), .spent = &p2sh_spk }, .p2sh = 1 },
        .{ .name = "the same scriptSig, not spending P2SH", .in = .{ .sig = try push(a, &ms15), .spent = &.{ 0x76, 0xa9 } } },
        .{ .name = "P2SH-P2WPKH", .in = .{ .sig = try push(a, &wprog20), .wit = &.{ &sig71, &pk }, .spent = &p2sh_spk }, .wit = 1 },
        .{ .name = "P2SH-P2WSH", .in = .{ .sig = try push(a, &wprog32), .wit = &.{ &sig71, &wscript }, .spent = &p2sh_spk }, .wit = 5 },
        .{ .name = "P2SH, 22 bytes that are not a program", .in = .{ .sig = try push(a, &not22), .wit = &.{&wscript}, .spent = &p2sh_spk } },
        .{ .name = "P2SH, a version 1 program", .in = .{ .sig = try push(a, &v1_34), .wit = &.{&wscript}, .spent = &p2sh_spk } },
        .{ .name = "P2WPKH", .in = .{ .wit = &.{ &sig71, &pk }, .spent = &p2wpkh_spk }, .wit = 1 },
        .{ .name = "P2WPKH, empty witness", .in = .{ .spent = &p2wpkh_spk }, .wit = 1 },
        .{ .name = "P2WSH", .in = .{ .wit = &.{ &sig71, &wscript }, .spent = &p2wsh_spk }, .wit = 5 },
        .{ .name = "P2WSH, one item", .in = .{ .wit = &.{&ms16v}, .spent = &p2wsh_spk }, .wit = 16 + 1 + 20 + 2 },
        .{ .name = "P2WSH, empty stack", .in = .{ .spent = &p2wsh_spk } },
        .{ .name = "P2WSH, empty last item", .in = .{ .wit = &.{ &wscript, &.{} }, .spent = &p2wsh_spk } },
        .{ .name = "taproot script path (no sigops)", .in = .{ .wit = &.{ &wscript, &wscript }, .spent = &p2tr_spk } },
    };
    var ins = std.ArrayList(SigIn).empty;
    var p2sh: u32 = 0;
    var wit: u32 = 0;
    for (cases) |c| {
        // Each case alone: the native reference agrees with the expected counts.
        const one = try sigBlock(a, 500000, &.{c.in});
        const nat = try rules.blockRules(a, one.raw, one.undo, 500000, true);
        if (nat.sigops.p2sh != c.p2sh or nat.sigops.witness != c.wit) {
            std.debug.print("{s}: native P2SH {d} witness {d}, expected {d} and {d}\n", .{ c.name, nat.sigops.p2sh, nat.sigops.witness, c.p2sh, c.wit });
            return error.TestUnexpectedResult;
        }
        try ins.append(a, c.in);
        p2sh += c.p2sh;
        wit += c.wit;
    }
    // All of them in one transaction: the AIRs hold and count the same.
    const blk = try sigBlock(a, 500000, ins.items);
    const b = try bsys.buildU(a, blk.raw, blk.undo, sig_ctx);
    if (try bsys.firstViolation(a, &airs, &b)) |v| {
        std.debug.print("{s} row {d} violates constraint {d}\n", .{ bsys.names[v.comp], v.row, v.constraint });
        return error.TestUnexpectedResult;
    }
    try std.testing.expect(try bsys.unbalanced(a, &airs, &b) == null);
    const nat = try rules.blockRules(a, blk.raw, blk.undo, 500000, true);
    try std.testing.expectEqual(p2sh, nat.sigops.p2sh);
    try std.testing.expectEqual(wit, nat.sigops.witness);
    try std.testing.expectEqual(rules.cost(nat.sigops), b.sigop_cost);
    std.debug.print("sigop cost: {d} cases in one transaction: legacy {d}, P2SH {d}, witness {d}, cost {d}, as Core counts\n", .{ cases.len, nat.sigops.legacy, p2sh, wit, b.sigop_cost });
}

test "block negative: sigop cost: 80,000 is accepted and 80,001 rejected, through P2SH and through witness sigops" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    // 500 bare multisigs in a redeem script: 10,000 sigops, cost 40,000. The legacy count stays 0.
    const r500 = [_]u8{0xae} ** 500;
    const redeem = SigIn{ .sig = try push(a, &r500), .spent = &p2sh_spk };
    // 4,000 bare multisigs in a witness script: cost 80,000.
    const w4000 = [_]u8{0xae} ** 4000;
    const wsh = SigIn{ .wit = &.{&w4000}, .spent = &p2wsh_spk };
    const one_more = SigIn{ .spent = &p2wpkh_spk };
    const cases = [_]struct { name: []const u8, ins: []const SigIn, cost: u64, want: Verdict }{
        .{ .name = "two redeem scripts of 10,000 sigops", .ins = &.{ redeem, redeem }, .cost = 80000, .want = .accepted },
        .{ .name = "the same and a P2WPKH input", .ins = &.{ redeem, redeem, one_more }, .cost = 80001, .want = .rejected },
        .{ .name = "three redeem scripts of 10,000 sigops", .ins = &.{ redeem, redeem, redeem }, .cost = 120000, .want = .rejected },
        .{ .name = "a witness script of 80,000 sigops", .ins = &.{wsh}, .cost = 80000, .want = .accepted },
        .{ .name = "the same and a P2WPKH input", .ins = &.{ wsh, one_more }, .cost = 80001, .want = .rejected },
        .{ .name = "one redeem script and half the cost in a witness script", .ins = &.{ redeem, .{ .wit = &.{w4000[0..2000]}, .spent = &p2wsh_spk } }, .cost = 80000, .want = .accepted },
    };
    for (cases) |c| {
        const blk = try sigBlock(a, 500000, c.ins);
        const nat = try rules.blockRules(a, blk.raw, blk.undo, 500000, true);
        try std.testing.expectEqual(c.cost, rules.cost(nat.sigops));
        try std.testing.expectEqual(@as(u32, 0), nat.sigops.legacy);
        std.debug.print("sigop cost {d} (legacy 0): {s}\n", .{ c.cost, c.name });
        try std.testing.expectEqual(c.want, try judgeU(a, blk.raw, blk.undo, sig_ctx));
    }
}

test "block negative: sigop cost: a forged class, push-only flag or witness request is rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bsys.parseAirs(a);
    const one = M31.one();
    const zero = M31.zero();
    const ms = [_]u8{ 0x53, 0xae };
    const ins = [_]SigIn{
        .{ .sig = try push(a, &ms), .spent = &p2sh_spk },
        .{ .wit = &.{&ms}, .spent = &p2wsh_spk },
        .{ .spent = &p2wpkh_spk },
    };
    const blk = try sigBlock(a, 500000, &ins);
    const Forge = enum { none, urec_class, coin_class, fields_class, fields_w20, walk_po, fields_ws, walk_w4 };
    for (std.enums.values(Forge)) |fg| {
        const b = try bsys.buildU(a, blk.raw, blk.undo, sig_ctx);
        const fm = b.mains[1];
        const wm = b.mains[6];
        const um = b.mains[13];
        const cm = b.mains[14];
        // The rows: the fields' second input row (the first is the coinbase's) and so on.
        var kin = std.ArrayList(usize).empty;
        var kwc = std.ArrayList(usize).empty;
        for (0..fm[2].len) |q| {
            if (fm[2][q].eql(one)) try kin.append(a, q);
            if (fm[5][q].eql(one)) try kwc.append(a, q);
        }
        const ki0 = for (0..cm[1].len) |q| {
            if (cm[1][q].eql(one)) break q;
        } else unreachable;
        switch (fg) {
            .none => {},
            // The undo record denies the P2SH class (URec.CP).
            .urec_class => um[36][0] = zero,
            // The coin row denies it (Coin.UP): its tuple is no longer the record's.
            .coin_class => cm[170][ki0] = zero,
            // The fields' input row denies it (Fields.CP).
            .fields_class => fm[206][kin.items[1]] = zero,
            // The fields drop the P2WPKH class of the third input (Fields.CW20).
            .fields_w20 => fm[207][kin.items[3]] = zero,
            // The walker says the scriptSig is not push-only (Walk.PO), on the script's rows.
            .walk_po => for (0..wm[0].len) |q| {
                if (wm[0][q].eql(one) and wm[51][q].isZero() and wm[59][q].eql(one)) wm[59][q] = zero;
            },
            // The second input's witness stack ignores the request (Fields.WS on its rows, and WQ).
            .fields_ws => for (kwc.items[2]..kwc.items[3]) |q| {
                fm[226][q] = zero;
                fm[227][q] = zero;
            },
            // The walker counts the redeem script with weight 1 (Walk.W4).
            .walk_w4 => for (0..wm[0].len) |q| {
                wm[52][q] = zero;
            },
        }
        const viol = try bsys.firstViolation(a, &airs, &b);
        const unb = try bsys.unbalanced(a, &airs, &b);
        std.debug.print("forgery {s}: {s}\n", .{ @tagName(fg), if (viol != null) "a constraint is violated" else if (unb != null) "a lookup is unbalanced" else "accepted" });
        try std.testing.expectEqual(fg != .none, viol != null or unb != null);
    }
}
