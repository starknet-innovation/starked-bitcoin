//! Hash messages (M3a.3 `BLK-SHA`): the witness for the `block_msg` component (Lean:
//! `Block/Msg.lean`). One row per padded-message byte: the header (id 0), then per transaction `i`
//! its txid (id 1 + 2i) and wtxid (id 2 + 2i) messages, each starting at a row ≡ 0 (mod 64).

const std = @import("std");
const par = @import("../par.zig");
const M31 = @import("stwo_core").fields.m31.M31;
const fields = @import("fields.zig");

pub const json = @embedFile("air:block_msg");
pub const N_MAIN = 38;
const D = 0;
const P80 = 1;
const ZR = 2;
const LN = 3;
const NIL = 4;
const FIRSTM = 5;
const PC0 = 6;
const PC1 = 7;
const PC2 = 8;
const MT = 9;
const HDR = 10;
const WTX = 11;
const SEG = 12;
const TI = 13;
const TA = 14;
const TW = 15;
const TL = 16;
const MID = 17;
const IDX = 18;
const POS = 19;
const BYTE = 20;
const BIT0 = 21;
const EZ = 29;
const Z = 30;
const INV = 31;
const CONT = 32;
const SW = 33;
const ENDD = 34;
const DLC = 35;
pub const WM = 36;
const MM = 37;

/// A transaction's ranges, as the fields component yields them.
pub const TxRange = struct { i: u32, a: u32, seg: bool, w: u32, l: u32 };

/// The transactions' ranges, from the token rows.
pub fn txRanges(a: std.mem.Allocator, rows: []const fields.Row) ![]TxRange {
    var out = std.ArrayList(TxRange).empty;
    var cur: TxRange = undefined;
    for (rows, 0..) |r, idx| {
        switch (r.kind) {
            fields.K_TXH => {
                cur = .{ .i = @intCast(out.items.len), .a = r.start, .seg = r.seg, .w = 0, .l = 0 };
            },
            fields.K_NOUT, fields.K_OUT => {
                // The row after the last output starts the witness section (or is the locktime).
                const next = rows[idx + 1];
                if (next.kind != fields.K_OUT) cur.w = next.start;
            },
            fields.K_LOCK => {
                cur.l = r.start;
                try out.append(a, cur);
            },
            else => {},
        }
    }
    return out.toOwnedSlice(a);
}

/// A message: its id, kind, tuple, and data bytes' positions.
pub const Message = struct {
    id: u32,
    hdr: bool,
    wtx: bool,
    tx: TxRange,
    positions: []const u32,
    split: bool,
};

pub fn messages(a: std.mem.Allocator, txs: []const TxRange) ![]Message {
    var out = std.ArrayList(Message).empty;
    const hdr_pos = try a.alloc(u32, 80);
    for (hdr_pos, 0..) |*p, j| p.* = @intCast(j);
    try out.append(a, .{ .id = 0, .hdr = true, .wtx = false, .tx = .{ .i = 0, .a = 0, .seg = false, .w = 0, .l = 76 }, .positions = hdr_pos, .split = false });
    for (txs) |t| {
        var txid = std.ArrayList(u32).empty;
        if (t.seg) {
            for (t.a..t.a + 4) |p| try txid.append(a, @intCast(p));
            for (t.a + 6..t.w) |p| try txid.append(a, @intCast(p));
            for (t.l..t.l + 4) |p| try txid.append(a, @intCast(p));
        } else for (t.a..t.l + 4) |p| try txid.append(a, @intCast(p));
        try out.append(a, .{ .id = 1 + 2 * t.i, .hdr = false, .wtx = false, .tx = t, .positions = try txid.toOwnedSlice(a), .split = t.seg });
        const wtx = try a.alloc(u32, t.l + 4 - t.a);
        for (wtx, 0..) |*p, j| p.* = t.a + @as(u32, @intCast(j));
        try out.append(a, .{ .id = 2 + 2 * t.i, .hdr = false, .wtx = true, .tx = t, .positions = wtx, .split = false });
    }
    return out.toOwnedSlice(a);
}

/// Sets the word and length multiplicities: every word of every message is read once by the SHA
/// component, and every message's padded length once.
pub fn setUses(cols: [][]M31) void {
    const n = cols[0].len;
    for (0..n) |r| {
        if (cols[NIL][r].eql(M31.one())) continue;
        if (r % 4 == 3) cols[WM][r] = M31.one();
        if (r % 64 == 63 and cols[LN][r].eql(M31.one())) cols[MM][r] = M31.one();
    }
}

/// Rows needed: each message padded to whole 64-byte blocks, plus one padding row.
pub fn rowsNeeded(msgs: []const Message) usize {
    var n: usize = 0;
    for (msgs) |m| n += (m.positions.len + 9 + 63) / 64 * 64;
    return n + 1;
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

/// Main columns in `2^log_size` rows; `reads` collects the byte positions read.
pub fn generate(a: std.mem.Allocator, log_size: u32, raw: []const u8, msgs: []const Message, reads: *std.ArrayList(u32)) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (rowsNeeded(msgs) > n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    const one = M31.one();
    var r: usize = 0;
    for (msgs) |m| {
        const dl = m.positions.len;
        const padded = (dl + 9 + 63) / 64 * 64;
        const t = m.tx;
        for (0..padded) |j| {
            const row = r + j;
            cols[HDR][row] = f(@intFromBool(m.hdr));
            cols[WTX][row] = f(@intFromBool(m.wtx));
            cols[SEG][row] = f(@intFromBool(t.seg));
            cols[TI][row] = f(t.i);
            cols[TA][row] = f(t.a);
            cols[TW][row] = f(t.w);
            cols[TL][row] = f(t.l);
            cols[MT][row] = f(@intFromBool(m.split));
            cols[MID][row] = f(m.id);
            cols[IDX][row] = f(j);
            if (j == 0) cols[FIRSTM][row] = one;
            var byte: u8 = 0;
            if (j < dl) {
                cols[D][row] = one;
                const p = m.positions[j];
                cols[POS][row] = f(p);
                byte = raw[p];
                try reads.append(a, p);
                const piece: usize = if (!m.split) 0 else if (j < 4) 0 else if (j < dl - 4) 1 else 2;
                cols[PC0 + piece][row] = one;
            } else if (j == dl) {
                cols[P80][row] = one;
                byte = 0x80;
            } else if (j < padded - 8) {
                cols[ZR][row] = one;
            } else {
                cols[LN][row] = one;
                const bits: u64 = 8 * @as(u64, dl);
                byte = @truncate(bits >> @intCast(8 * (padded - 1 - j)));
            }
            cols[BYTE][row] = f(byte);
            for (0..8) |b| cols[BIT0 + b][row] = f((byte >> @intCast(b)) & 1);
        }
        r += padded;
    }
    // Padding rows: copy the last message's values; indices keep counting.
    for (r..n) |row| {
        cols[NIL][row] = one;
        for ([_]usize{ HDR, WTX, SEG, TI, TA, TW, TL, MT, MID }) |c| cols[c][row] = cols[c][row - 1];
        cols[IDX][row] = cols[IDX][row - 1].add(one);
    }
    // Derived columns: row by row on all cores, then the running `DLC` in one pass.
    par.forRanges(n, 1, Derived{ .cols = cols }, Derived.rows);
    for (0..n) |row| {
        cols[DLC][row] = if (cols[P80][row].eql(one)) cols[IDX][row] else if (row > 0) cols[DLC][row - 1] else M31.zero();
    }
    return cols;
}

const Derived = struct {
    cols: [][]M31,

    fn rows(self: Derived, lo: usize, hi: usize) void {
        const cols = self.cols;
        const one = M31.one();
        for (lo..hi) |row| {
            const mt = cols[MT][row];
            const pos = cols[POS][row];
            const tl3 = cols[TL][row].add(f(3));
            const ez = mt.mul(cols[PC0][row].mul(cols[IDX][row].sub(f(3)))
                .add(cols[PC1][row].mul(pos.sub(cols[TW][row]).add(one)))
                .add(cols[PC2][row].mul(pos.sub(tl3))))
                .add(one.sub(mt).mul(pos.sub(tl3)));
            cols[EZ][row] = ez;
            cols[Z][row] = if (ez.isZero()) one else M31.zero();
            cols[INV][row] = ez.inv() catch M31.zero();
            const z = cols[Z][row];
            cols[CONT][row] = cols[D][row].mul(one.sub(z));
            cols[SW][row] = z.mul(mt).mul(cols[PC0][row].add(cols[PC1][row]));
            cols[ENDD][row] = cols[D][row].mul(z).sub(cols[SW][row]);
        }
    }
};

test "block msg: header, txid and wtxid messages of the samples satisfy the message AIR" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const msg_air = (try ir.Air.parseJson(a, json)).value;
    const samples = [_][]const u8{
        @embedFile("testdata:block_0"), @embedFile("testdata:block_170"), @embedFile("testdata:block_91812"),
    };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const txs = try txRanges(a, rows);
        const msgs = try messages(a, txs);
        const need = @max(rowsNeeded(msgs), raw.len + 1, rows.len + 1);
        const log_size: u32 = std.math.log2_int_ceil(usize, need);
        var reads = std.ArrayList(u32).empty;
        const mm = try generate(a, log_size, raw, msgs, &reads);
        const pubs = [_]M31{ f(raw.len), f(rows[0].val) };
        const tr = interp.RowTrace{ .log_size = log_size, .pubs = &pubs, .preprocessed = @ptrCast(try msg_air.genPreprocessed(a, log_size)), .main = @ptrCast(mm) };
        if (try interp.firstViolation(a, msg_air, tr)) |v| {
            std.debug.print("block of {d} bytes: msg row {d} violates constraint {d}\n", .{ raw.len, v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
    }
}

/// The Merkle root of the txid messages' SHA256d (native; a check that the ranges are the txids').
fn merkleOfTxids(a: std.mem.Allocator, raw: []const u8, msgs: []const Message) ![32]u8 {
    const Sha = std.crypto.hash.sha2.Sha256;
    var level = std.ArrayList([32]u8).empty;
    for (msgs) |m| if (!m.hdr and !m.wtx) {
        const data = try a.alloc(u8, m.positions.len);
        for (data, m.positions) |*d, p| d.* = raw[p];
        var h: [32]u8 = undefined;
        Sha.hash(data, &h, .{});
        Sha.hash(&h, &h, .{});
        try level.append(a, h);
    };
    while (level.items.len > 1) {
        if (level.items.len % 2 == 1) try level.append(a, level.items[level.items.len - 1]);
        var next = std.ArrayList([32]u8).empty;
        var i: usize = 0;
        while (i < level.items.len) : (i += 2) {
            var buf: [64]u8 = undefined;
            @memcpy(buf[0..32], &level.items[i]);
            @memcpy(buf[32..64], &level.items[i + 1]);
            var h: [32]u8 = undefined;
            Sha.hash(&buf, &h, .{});
            Sha.hash(&h, &h, .{});
            try next.append(a, h);
        }
        level = next;
    }
    return level.items[0];
}

test "block msg: segwit samples (split txid messages) satisfy the message AIR (run with ReleaseFast)" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const msg_air = (try ir.Air.parseJson(a, json)).value;
    const samples = [_][]const u8{ @embedFile("testdata:block_481824"), @embedFile("testdata:block_709632") };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const txs = try txRanges(a, rows);
        const msgs = try messages(a, txs);
        var nsplit: usize = 0;
        for (msgs) |m| nsplit += @intFromBool(m.split);
        const log_size: u32 = std.math.log2_int_ceil(usize, rowsNeeded(msgs));
        var reads = std.ArrayList(u32).empty;
        const mm = try generate(a, log_size, raw, msgs, &reads);
        const tr = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(try msg_air.genPreprocessed(a, log_size)), .main = @ptrCast(mm) };
        std.debug.print("block of {d} bytes: {d} messages ({d} split), {d} rows, log {d}\n", .{ raw.len, msgs.len, nsplit, rowsNeeded(msgs), log_size });
        try std.testing.expectEqualSlices(u8, raw[36..68], &try merkleOfTxids(a, raw, msgs));
        if (try interp.firstViolation(a, msg_air, tr)) |v| {
            std.debug.print("  row {d} violates constraint {d}\n", .{ v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
    }
}
