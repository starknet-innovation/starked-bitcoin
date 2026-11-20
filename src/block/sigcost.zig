//! CONNECT-RULES step 3, the full sigop cost: what the block's components need about each input (Lean:
//! `Fields.sigC`, `URec.classC`, `Walk.accC`). The spent script's class comes from the undo record's
//! `serTxOut`; the scriptSig's last push from the walker's automaton (`walk.spanOut`); the spans to
//! count accurately are the redeem scripts and the last witness items of version 0, 32-byte programs.

const std = @import("std");
const fields = @import("fields.zig");
const walk = @import("walk.zig");
const rules = @import("connect_rules.zig");

pub const Class = struct { p2sh: bool = false, w20: bool = false, w32: bool = false };

/// The class of a spent output from its `serTxOut` (8 amount bytes, the script's CompactSize, the
/// script), reading the bytes the `block_urec` AIR reads: 8, then 9 and 10, then 31.
pub fn classOf(ser: []const u8) Class {
    if (ser.len < 11) return .{};
    return switch (ser[8]) {
        0x16 => .{ .w20 = ser[9] == 0 and ser[10] == 0x14 },
        0x22 => .{ .w32 = ser[9] == 0 and ser[10] == 0x20 },
        0x17 => .{ .p2sh = ser[9] == 0xa9 and ser[10] == 0x14 and ser.len > 31 and ser[31] == 0x87 },
        else => .{},
    };
}

/// Per row of the fields component: the values the other components fix (zero where unused).
pub const RowSig = struct {
    /// A non-empty script's walker outputs (input and output rows).
    spo: bool = false,
    srs: u32 = 0,
    srl: u32 = 0,
    /// A non-coinbase input's spent class.
    cls: Class = .{},
    /// A witness stack row, and its item rows: the last item is a witness script to count.
    ws: bool = false,
};

pub const Out = struct {
    rows: []RowSig,
    /// Every span the walker walks: the scripts in row order (mode 0), and the accurate spans.
    spans: []walk.Span,
    /// Inputs counted as P2WPKH (one sigop each).
    w20: u32,
};

/// All-zero rows, for witnesses built without the undo data (the fields' own tests).
pub fn blank(a: std.mem.Allocator, n: usize) ![]RowSig {
    const out = try a.alloc(RowSig, n);
    @memset(out, .{});
    return out;
}

/// The `serTxOut` of each record of the in-circuit undo stream (`coin.records`).
pub fn sersOf(a: std.mem.Allocator, undo: []const u8, recs: anytype) ![][]const u8 {
    const out = try a.alloc([]const u8, recs.len);
    for (recs, out) |rc, *o| o.* = undo[rc.start + 9 ..][0..rc.tl];
    return out;
}

/// `sers[j]`: the `serTxOut` of the `j`-th non-coinbase input's undo record.
pub fn analyse(a: std.mem.Allocator, raw: []const u8, rows: []const fields.Row, sers: []const []const u8) !Out {
    const out = try a.alloc(RowSig, rows.len);
    @memset(out, .{});
    var spans = std.ArrayList(walk.Span).empty;
    var n32s = std.ArrayList(bool).empty;
    var txi: u32 = 0;
    var j: usize = 0;
    var wc: usize = 0;
    var cur_ws = false;
    var w20: u32 = 0;
    for (rows, 0..) |r, i| {
        const ss: u32 = r.start + r.off + r.pref;
        switch (r.kind) {
            fields.K_TXH => {
                n32s.clearRetainingCapacity();
                wc = 0;
            },
            fields.K_IN, fields.K_OUT => {
                var so: walk.SpanOut = .{ .po = false, .rs = 0, .rl = 0 };
                if (r.val != 0) {
                    so = walk.spanOut(raw, ss, r.val);
                    out[i].spo = so.po;
                    out[i].srs = so.rs;
                    out[i].srl = so.rl;
                    try spans.append(a, .{ .start = ss, .len = r.val });
                }
                if (r.kind == fields.K_IN) {
                    var n32 = false;
                    if (txi != 0) {
                        if (j >= sers.len) return error.UndoTruncated;
                        const cls = classOf(sers[j]);
                        j += 1;
                        out[i].cls = cls;
                        const ar0 = r.val != 0 and cls.p2sh and so.po;
                        if (ar0 and so.rl != 0) try spans.append(a, .{ .start = so.rs, .len = so.rl, .mode = 2 });
                        const rwa = ar0 and (so.rl == 22 or so.rl == 34) and raw[so.rs] == 0 and raw[so.rs + 1] == so.rl - 2;
                        if (cls.w20 or (rwa and so.rl == 22)) w20 += 1;
                        n32 = cls.w32 or (rwa and so.rl == 34);
                    }
                    try n32s.append(a, n32);
                }
            },
            fields.K_WCNT => {
                cur_ws = wc < n32s.items.len and n32s.items[wc];
                wc += 1;
                out[i].ws = cur_ws;
            },
            fields.K_WITEM => {
                out[i].ws = cur_ws;
                const last = i + 1 >= rows.len or rows[i + 1].kind != fields.K_WITEM;
                if (cur_ws and last and r.val != 0) try spans.append(a, .{ .start = ss, .len = r.val, .mode = 1 });
            },
            fields.K_LOCK => txi += 1,
            else => {},
        }
    }
    if (j != sers.len) return error.UndoTruncated;
    return .{ .rows = out, .spans = try spans.toOwnedSlice(a), .w20 = w20 };
}

test "the class from a serTxOut agrees with Core's script tests" {
    var buf: [64]u8 = undefined;
    var prng = std.Random.DefaultPrng.init(3);
    const rnd = prng.random();
    const pats = [_][]const u8{ &.{ 0xa9, 0x14 }, &.{ 0x00, 0x14 }, &.{ 0x00, 0x20 }, &.{ 0x51, 0x20 }, &.{ 0x76, 0xa9 } };
    for (0..20000) |_| {
        const len = rnd.uintLessThan(usize, 44);
        @memset(buf[0..8], 0);
        buf[8] = @intCast(len);
        rnd.bytes(buf[9 .. 9 + len]);
        if (len >= 2 and rnd.boolean()) @memcpy(buf[9..11], pats[rnd.uintLessThan(usize, pats.len)]);
        if (len == 23 and rnd.boolean()) buf[9 + 22] = 0x87;
        const script = buf[9 .. 9 + len];
        const c = classOf(buf[0 .. 9 + len]);
        try std.testing.expectEqual(rules.isP2SH(script), c.p2sh);
        const prog = rules.witnessProgram(script);
        try std.testing.expectEqual(prog != null and prog.?.version == 0 and prog.?.prog.len == 20, c.w20);
        try std.testing.expectEqual(prog != null and prog.?.version == 0 and prog.?.prog.len == 32, c.w32);
    }
}
