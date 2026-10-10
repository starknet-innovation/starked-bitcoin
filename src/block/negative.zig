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
fn segwitBlock(a: std.mem.Allocator, height: u32, opts: struct { commit: bool = true, decoy: bool = false, nonce_len: usize = 32, tamper: bool = false }) ![]u8 {
    const nonce = [_]u8{0x42} ** 32;
    var cbs = std.ArrayList(u8).empty;
    try cbs.appendSlice(a, &.{ 0x03, @intCast(height & 0xff), @intCast((height >> 8) & 0xff), @intCast(height >> 16), 0xaa, 0xbb });
    const sig = [_]u8{0x30} ** 71;
    const pk = [_]u8{0x02} ** 33;
    const stack1 = [_][]const u8{ &sig, &pk };
    const tx1 = Tx{ .version = 2, .ins = &.{.{ .script = &.{} }}, .outs = &.{.{ .value = 1000, .script = &([_]u8{ 0x00, 0x14 } ++ [_]u8{0x11} ** 20) }}, .wit = &.{&stack1} };
    const nonce_item = try a.alloc(u8, opts.nonce_len);
    @memset(nonce_item, 0x42);
    const cb_stack = [_][]const u8{nonce_item};
    var cb = Tx{ .version = 1, .ins = &.{.{ .hash = [_]u8{0} ** 32, .n = 0xffffffff, .script = cbs.items }}, .outs = &.{.{}}, .wit = &.{&cb_stack} };
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
    const ctx = checks.Ctx{ .height = 500000, .prev_mtp = 1699999000 };
    std.debug.print("valid segwit block\n", .{});
    try std.testing.expectEqual(Verdict.accepted, try judge(a, try segwitBlock(a, 500000, .{}), ctx));
    std.debug.print("segwit block before activation (unexpected witness)\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 470000, .{}), .{ .height = 470000, .prev_mtp = 1699999000 }));
    std.debug.print("no commitment output, witness present\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .commit = false }), ctx));
    std.debug.print("tampered witness (txid unchanged)\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .tamper = true }), ctx));
    std.debug.print("later decoy commitment output\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .decoy = true }), ctx));
    std.debug.print("nonce of 33 bytes\n", .{});
    try std.testing.expectEqual(Verdict.rejected, try judge(a, try segwitBlock(a, 500000, .{ .nonce_len = 33 }), ctx));
}
