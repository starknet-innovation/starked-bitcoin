//! Block fields (M3a.2 `BLK-FIELDS`): the witness for the `block_fields` component (Lean:
//! `Block/Fields.lean`). The block is tokenized into one row per token (header + tx count,
//! tx head, input, output count, output, witness stack count, witness item, locktime), then
//! padding; each row reads its CompactSize (and a segwit head its marker and flag) from the
//! byte table.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;

pub const json = @embedFile("air:block_fields");

pub const K_BLK = 0;
pub const K_TXH = 1;
pub const K_IN = 2;
pub const K_NOUT = 3;
pub const K_OUT = 4;
pub const K_WCNT = 5;
pub const K_WITEM = 6;
pub const K_LOCK = 7;
pub const K_PAD = 8;
const START = 9;
const LEN = 10;
const VAL = 11;
const SEG = 12;
const OFF = 13;
const CP1 = 14;
const CP3 = 15;
const CP5 = 16;
const CB0 = 17;
const RA0 = 22;
const RB0 = 47;
const RS0 = 72;
const TXL = 97;
const INL = 98;
const NIN = 99;
const OUTL = 100;
const WINL = 101;
const ITEML = 102;
const HASW = 103;
const Z1 = 104;
const INV1 = 105;
const Z2 = 106;
const INV2 = 107;
const EOC = 108;
const ESC = 109;
const E1C = 110;
const E2C = 111;
const C4B0 = 112;
const C4B1 = 113;
const TXA = 114;
const WST = 115;
const TXI = 116;
const TXM = 117;
pub const N_MAIN = 118;
const MAX_SIZE: u64 = 0x02000000;

/// One token row.
pub const Row = struct {
    kind: u8,
    start: u32,
    len: u32,
    val: u32 = 0,
    seg: bool = false,
    off: u32 = 0,
    pref: u8 = 0,
};

const Reader = struct {
    raw: []const u8,
    pos: usize = 0,

    fn compact(self: *Reader) !struct { val: u32, pref: u8 } {
        if (self.pos >= self.raw.len) return error.Truncated;
        const b = self.raw[self.pos];
        const r: struct { val: u64, pref: u8 } = switch (b) {
            0...252 => .{ .val = b, .pref = 1 },
            253 => .{ .val = std.mem.readInt(u16, self.raw[self.pos + 1 ..][0..2], .little), .pref = 3 },
            254 => .{ .val = std.mem.readInt(u32, self.raw[self.pos + 1 ..][0..4], .little), .pref = 5 },
            255 => return error.CompactTooLarge,
        };
        if ((r.pref == 3 and r.val < 253) or (r.pref == 5 and r.val < 0x10000)) return error.NonCanonical;
        if (r.val > MAX_SIZE) return error.CompactTooLarge;
        self.pos += r.pref;
        return .{ .val = @intCast(r.val), .pref = r.pref };
    }

    fn skip(self: *Reader, n: usize) !void {
        if (self.pos + n > self.raw.len) return error.Truncated;
        self.pos += n;
    }
};

/// Tokenizes a block (Core's serialization grammar).
pub fn tokenize(a: std.mem.Allocator, raw: []const u8) ![]Row {
    var rows = std.ArrayList(Row).empty;
    var rd = Reader{ .raw = raw };
    try rd.skip(80);
    const ntx = try rd.compact();
    if (ntx.val == 0) return error.EmptyBlock;
    try rows.append(a, .{ .kind = K_BLK, .start = 0, .len = @intCast(rd.pos), .val = ntx.val, .off = 80, .pref = ntx.pref });
    for (0..ntx.val) |_| {
        const s = rd.pos;
        try rd.skip(4);
        const seg = rd.pos + 1 < raw.len and raw[rd.pos] == 0 and raw[rd.pos + 1] == 1;
        if (seg) try rd.skip(2);
        const off: u32 = @intCast(rd.pos - s);
        const nin = try rd.compact();
        if (nin.val == 0) return error.NoInputs;
        try rows.append(a, .{ .kind = K_TXH, .start = @intCast(s), .len = @intCast(rd.pos - s), .val = nin.val, .seg = seg, .off = off, .pref = nin.pref });
        for (0..nin.val) |_| {
            const si = rd.pos;
            try rd.skip(36);
            const sl = try rd.compact();
            try rd.skip(sl.val + 4);
            try rows.append(a, .{ .kind = K_IN, .start = @intCast(si), .len = @intCast(rd.pos - si), .val = sl.val, .seg = seg, .off = 36, .pref = sl.pref });
        }
        const so = rd.pos;
        const nout = try rd.compact();
        try rows.append(a, .{ .kind = K_NOUT, .start = @intCast(so), .len = @intCast(rd.pos - so), .val = nout.val, .seg = seg, .pref = nout.pref });
        for (0..nout.val) |_| {
            const s2 = rd.pos;
            try rd.skip(8);
            const sl = try rd.compact();
            try rd.skip(sl.val);
            try rows.append(a, .{ .kind = K_OUT, .start = @intCast(s2), .len = @intCast(rd.pos - s2), .val = sl.val, .seg = seg, .off = 8, .pref = sl.pref });
        }
        if (seg) {
            var nonempty = false;
            for (0..nin.val) |_| {
                const sw = rd.pos;
                const c = try rd.compact();
                if (c.val != 0) nonempty = true;
                try rows.append(a, .{ .kind = K_WCNT, .start = @intCast(sw), .len = @intCast(rd.pos - sw), .val = c.val, .seg = seg, .pref = c.pref });
                for (0..c.val) |_| {
                    const sit = rd.pos;
                    const il = try rd.compact();
                    try rd.skip(il.val);
                    try rows.append(a, .{ .kind = K_WITEM, .start = @intCast(sit), .len = @intCast(rd.pos - sit), .val = il.val, .seg = seg, .pref = il.pref });
                }
            }
            if (!nonempty) return error.SuperfluousWitness;
        }
        const sl = rd.pos;
        try rd.skip(4);
        try rows.append(a, .{ .kind = K_LOCK, .start = @intCast(sl), .len = 4, .seg = seg });
    }
    if (rd.pos != raw.len) return error.TrailingBytes;
    return rows.toOwnedSlice(a);
}

/// Sets each transaction tuple's multiplicity (at its locktime row) to `uses`.
pub fn setTxUses(cols: [][]M31, rows: []const Row, uses: u32) void {
    for (rows, 0..) |r, i| if (r.kind == K_LOCK) {
        cols[TXM][i] = M31.fromCanonical(uses);
    };
}

/// The positions the fields component reads (for the byte table's multiplicities).
pub fn reads(a: std.mem.Allocator, rows: []const Row) ![]u32 {
    var out = std.ArrayList(u32).empty;
    for (rows) |r| {
        for (0..r.pref) |j| try out.append(a, r.start + r.off + @as(u32, @intCast(j)));
        if (r.kind == K_TXH and r.seg) {
            try out.append(a, r.start + 4);
            try out.append(a, r.start + 5);
        }
    }
    return out.toOwnedSlice(a);
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

fn invOrZero(x: M31) M31 {
    return x.inv() catch M31.zero();
}

/// Main columns in `2^log_size` rows (at least one padding row).
pub fn generate(a: std.mem.Allocator, log_size: u32, raw: []const u8, rows: []const Row) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (rows.len >= n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    const one = M31.one();
    for (0..n) |i| {
        const r: Row = if (i < rows.len) rows[i] else .{ .kind = K_PAD, .start = @intCast(raw.len), .len = 0, .seg = if (rows.len > 0) rows[rows.len - 1].seg else false };
        cols[r.kind][i] = one;
        cols[START][i] = f(r.start);
        cols[LEN][i] = f(r.len);
        cols[VAL][i] = f(r.val);
        cols[SEG][i] = f(@intFromBool(r.seg));
        cols[OFF][i] = f(r.off);
        switch (r.pref) {
            1 => cols[CP1][i] = one,
            3 => cols[CP3][i] = one,
            5 => cols[CP5][i] = one,
            else => {},
        }
        for (0..r.pref) |j| cols[CB0 + j][i] = f(raw[r.start + r.off + j]);
        if (r.pref == 5) {
            const top = raw[r.start + r.off + 4];
            cols[C4B0][i] = f(top & 1);
            cols[C4B1][i] = f((top >> 1) & 1);
        }
        const ra: u32 = switch (r.pref) {
            1 => 252 - r.val,
            3 => r.val - 253,
            5 => r.val - 65536,
            else => 0,
        };
        const rb: u32 = if (r.pref == 5) @intCast(MAX_SIZE - r.val) else 0;
        for (0..25) |j| {
            cols[RA0 + j][i] = f((ra >> @intCast(j)) & 1);
            cols[RB0 + j][i] = f((rb >> @intCast(j)) & 1);
            cols[RS0 + j][i] = f((r.start >> @intCast(j)) & 1);
        }
    }
    // Counters, then the decisions, in two passes: wrapped constraints tie row 0 to the last row,
    // and every counter there is determined by the last transaction.
    for (0..2) |_| {
        for (0..n) |i| {
            const p = if (i == 0) n - 1 else i - 1;
            const kind = for (0..9) |kk| {
                if (cols[kk][i].eql(one)) break kk;
            } else unreachable;
            if (kind == K_BLK) cols[TXL][i] = cols[VAL][i].sub(one) else if (i > 0) cols[TXL][i] = cols[TXL][p].sub(cols[K_LOCK][p]);
            if (kind == K_TXH) {
                cols[INL][i] = cols[VAL][i];
                cols[NIN][i] = cols[VAL][i];
                cols[HASW][i] = M31.zero();
            } else {
                if (i > 0) cols[INL][i] = cols[INL][p].sub(cols[K_IN][p]);
                if (i > 0) cols[NIN][i] = cols[NIN][p];
                cols[HASW][i] = cols[HASW][p].add(cols[K_WCNT][p].mul(one.sub(cols[Z1][p])));
            }
            if (kind == K_NOUT) cols[OUTL][i] = cols[VAL][i] else if (i > 0) cols[OUTL][i] = cols[OUTL][p].sub(cols[K_OUT][p]);
            if (cols[EOC][p].eql(one)) cols[WINL][i] = cols[NIN][i] else cols[WINL][i] = cols[WINL][p].sub(cols[ESC][p]);
            if (kind == K_WCNT) cols[ITEML][i] = cols[VAL][i] else if (i > 0) cols[ITEML][i] = cols[ITEML][p].sub(cols[K_WITEM][p]);
            // Per-transaction values: start, witness-section start, index.
            if (kind == K_TXH) cols[TXA][i] = cols[START][i] else if (i > 0) cols[TXA][i] = cols[TXA][p];
            if (cols[EOC][p].eql(one)) cols[WST][i] = cols[START][i] else if (i > 0) cols[WST][i] = cols[WST][p];
            if (kind == K_BLK) cols[TXI][i] = M31.zero() else if (i > 0) cols[TXI][i] = cols[TXI][p].add(cols[K_LOCK][p]);
            // Decisions.
            const e1 = switch (kind) {
                K_BLK, K_TXH, K_NOUT, K_WCNT => cols[VAL][i],
                K_IN => cols[INL][i].sub(one),
                K_OUT => cols[OUTL][i].sub(one),
                K_WITEM => cols[ITEML][i].sub(one),
                K_LOCK => cols[TXL][i],
                else => M31.zero(),
            };
            cols[E1C][i] = e1;
            cols[Z1][i] = if (e1.isZero()) one else M31.zero();
            cols[INV1][i] = invOrZero(e1);
            const e2 = switch (kind) {
                K_WCNT, K_WITEM => cols[WINL][i].sub(one),
                K_LOCK => cols[HASW][i],
                else => M31.zero(),
            };
            cols[E2C][i] = e2;
            cols[Z2][i] = if (e2.isZero()) one else M31.zero();
            cols[INV2][i] = invOrZero(e2);
            cols[EOC][i] = (cols[K_NOUT][i].add(cols[K_OUT][i])).mul(cols[Z1][i]);
            cols[ESC][i] = (cols[K_WCNT][i].add(cols[K_WITEM][i])).mul(cols[Z1][i]);
        }
    }
    return cols;
}

test "block fields: the sample blocks tokenize and satisfy the fields AIR; small blocks prove with the byte table" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    const bytes = @import("bytes.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const fields_air = (try ir.Air.parseJson(a, json)).value;
    const bytes_air = (try ir.Air.parseJson(a, bytes.json)).value;
    const samples = [_][]const u8{
        @embedFile("testdata:block_0"),     @embedFile("testdata:block_170"),   @embedFile("testdata:block_91722"),
        @embedFile("testdata:block_91812"), @embedFile("testdata:block_91842"), @embedFile("testdata:block_91880"),
    };
    for (samples) |raw| {
        const rows = try tokenize(a, raw);
        const log_size: u32 = @max(std.math.log2_int_ceil(usize, raw.len + 1), std.math.log2_int_ceil(usize, rows.len + 1));
        const fm = try generate(a, log_size, raw, rows);
        const pubs = [_]M31{f(raw.len)};
        const tr = interp.RowTrace{ .log_size = log_size, .pubs = &pubs, .preprocessed = @ptrCast(try fields_air.genPreprocessed(a, log_size)), .main = @ptrCast(fm) };
        if (try interp.firstViolation(a, fields_air, tr)) |v| {
            std.debug.print("block of {d} bytes: row {d} violates constraint {d}\n", .{ raw.len, v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        // Prove (bytes, fields) together: the reads balance against the byte table.
        const bm = try bytes.generate(a, log_size, raw, try reads(a, rows));
        const parts = [_]system.Part{
            .{ .air = &bytes_air, .log_size = log_size, .pubs = &pubs },
            .{ .air = &fields_air, .log_size = log_size, .pubs = &pubs },
        };
        const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
        const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(fm) };
        try system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains));
    }
}

test "block fields: tampered rows or bytes are rejected" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    const bytes = @import("bytes.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const fields_air = (try ir.Air.parseJson(a, json)).value;
    const bytes_air = (try ir.Air.parseJson(a, bytes.json)).value;
    const raw = @embedFile("testdata:block_170");
    const rows = try tokenize(a, raw);
    const log_size: u32 = 9;
    const pubs = [_]M31{f(raw.len)};
    const pre = try fields_air.genPreprocessed(a, log_size);
    // A script length off by one: the rows no longer tile the block.
    {
        const bad = try a.dupe(Row, rows);
        for (bad) |*r| if (r.kind == K_OUT) {
            r.val += 1;
            break;
        };
        const fm = try generate(a, log_size, raw, bad);
        const tr = interp.RowTrace{ .log_size = log_size, .pubs = &pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(fm) };
        try std.testing.expect(try interp.firstViolation(a, fields_air, tr) != null);
    }
    // The block's byte under a CompactSize differs from what the fields read: unbalanced.
    {
        const fm = try generate(a, log_size, raw, rows);
        const tampered = try a.dupe(u8, raw);
        tampered[rows[1].start + rows[1].off] ^= 1;
        const bm = try bytes.generate(a, log_size, tampered, try reads(a, rows));
        const parts = [_]system.Part{
            .{ .air = &bytes_air, .log_size = log_size, .pubs = &pubs },
            .{ .air = &fields_air, .log_size = log_size, .pubs = &pubs },
        };
        const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
        const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(fm) };
        try std.testing.expectError(error.LookupsUnbalanced, system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains)));
    }
}

test "block fields: large and segwit samples satisfy the fields AIR (run with ReleaseFast)" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const fields_air = (try ir.Air.parseJson(a, json)).value;
    const samples = [_][]const u8{
        @embedFile("testdata:block_400000"), @embedFile("testdata:block_481824"), @embedFile("testdata:block_709632"),
        @embedFile("testdata:block_970347"), @embedFile("testdata:block_774628"),
    };
    for (samples) |raw| {
        const rows = try tokenize(a, raw);
        var nseg: usize = 0;
        for (rows) |r| if (r.kind == K_TXH and r.seg) {
            nseg += 1;
        };
        const log_size: u32 = std.math.log2_int_ceil(usize, rows.len + 1);
        const fm = try generate(a, log_size, raw, rows);
        const pubs = [_]M31{f(raw.len)};
        const tr = interp.RowTrace{ .log_size = log_size, .pubs = &pubs, .preprocessed = @ptrCast(try fields_air.genPreprocessed(a, log_size)), .main = @ptrCast(fm) };
        std.debug.print("block of {d} bytes: {d} rows ({d} segwit txs), log {d}\n", .{ raw.len, rows.len, nseg, log_size });
        if (try interp.firstViolation(a, fields_air, tr)) |v| {
            std.debug.print("  row {d} (kind {d}) violates constraint {d}\n", .{ v.row, rows[@min(v.row, rows.len - 1)].kind, v.constraint });
            return error.TestUnexpectedResult;
        }
    }
}
