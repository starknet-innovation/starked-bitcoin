//! Block bytes (M3a.1 `BLK-BYTES`): the witness for the `block_bytes` component
//! (Lean: `Block/Bytes.lean`). One byte per row; rows `r < len` are active and yield
//! `byte(r, raw[r])` with multiplicity "number of reads of position r".

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;

pub const json = @embedFile("air:block_bytes");
pub const reader_json = @embedFile("air:block_reader");
pub const REL_BYTE: u32 = 3;
pub const N_MAIN = 12;
const POS = 0;
const BYTE = 1;
const BIT0 = 2;
const ACTIVE = 10;
const MULT = 11;

/// Main columns for `raw` in `2^log_size` rows; `reads` lists the positions other components
/// read (with repetition).
pub fn generate(a: std.mem.Allocator, log_size: u32, raw: []const u8, reads: []const u32) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (raw.len == 0 or raw.len > n) return error.BlockDoesNotFit;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    for (0..n) |r| {
        cols[POS][r] = M31.fromCanonical(@intCast(r));
        if (r >= raw.len) continue;
        cols[BYTE][r] = M31.fromCanonical(raw[r]);
        for (0..8) |i| cols[BIT0 + i][r] = M31.fromCanonical((raw[r] >> @intCast(i)) & 1);
        cols[ACTIVE][r] = M31.one();
    }
    for (try multiplicities(a, raw.len, reads), 0..) |m, r| cols[MULT][r] = M31.fromCanonical(m);
    return cols;
}

/// The reads per block position (the `MULT` column on the active rows; the device witness
/// generates the other columns from the block itself, src/gpu/cuda/witness.zig `bytes`).
pub fn multiplicities(a: std.mem.Allocator, len: usize, reads: []const u32) ![]u32 {
    const out = try a.alloc(u32, len);
    @memset(out, 0);
    for (reads) |p| {
        if (p >= len) return error.ReadOutOfRange;
        out[p] += 1;
    }
    for (out) |m| if (m >= @import("stwo_core").fields.m31.Modulus) return error.ReadOutOfRange;
    return out;
}

/// The test reader's columns: `(pos, byte, use)` per read, padded with unused rows.
pub fn readerColumns(a: std.mem.Allocator, log_size: u32, reads: []const [2]u32) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (reads.len > n) return error.TooManyReads;
    const cols = try a.alloc([]M31, 3);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    for (reads, 0..) |rd, r| {
        cols[0][r] = M31.fromCanonical(rd[0]);
        cols[1][r] = M31.fromCanonical(rd[1]);
        cols[2][r] = M31.one();
    }
    return cols;
}

test "block bytes: a reader of the genesis header proves; wrong bytes, reads past the end and a wrong length fail" {
    const ir = @import("../air/ir.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    const interp = @import("../air/interp.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const bytes_air = (try ir.Air.parseJson(a, json)).value;
    const reader_air = (try ir.Air.parseJson(a, reader_json)).value;
    const raw = @embedFile("testdata:block_0");
    try std.testing.expectEqual(@as(usize, 285), raw.len);
    const log_size: u32 = 9;
    const len_pub = [_]M31{M31.fromCanonical(raw.len)};
    const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const parts = [_]system.Part{
        .{ .air = &bytes_air, .log_size = log_size, .pubs = &len_pub },
        .{ .air = &reader_air, .log_size = log_size },
    };

    // Honest: the reader reads the 80 header bytes.
    var reads: [80][2]u32 = undefined;
    var positions: [80]u32 = undefined;
    for (&reads, &positions, 0..) |*rd, *p, i| {
        rd.* = .{ @intCast(i), raw[i] };
        p.* = @intCast(i);
    }
    const bm = try generate(a, log_size, raw, &positions);
    const tr = interp.RowTrace{ .log_size = log_size, .pubs = &len_pub, .preprocessed = @ptrCast(try bytes_air.genPreprocessed(a, log_size)), .main = @ptrCast(bm) };
    try std.testing.expect(try interp.firstViolation(a, bytes_air, tr) == null);
    {
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(try readerColumns(a, log_size, &reads)) };
        try system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains));
    }
    // A wrong byte at position 5.
    {
        var bad = reads;
        bad[5][1] ^= 1;
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(try readerColumns(a, log_size, &bad)) };
        try std.testing.expectError(error.LookupsUnbalanced, system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains)));
    }
    // A read past the end (position 300 ≥ 285), even with the table's multiplicity set there.
    {
        var bad = reads;
        bad[0] = .{ 300, 0 };
        const bm2 = try generate(a, log_size, raw, positions[1..]);
        bm2[MULT][300] = M31.one();
        const mains = [_][]const []const M31{ @ptrCast(bm2), @ptrCast(try readerColumns(a, log_size, &bad)) };
        try std.testing.expectError(error.LookupsUnbalanced, system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains)));
    }
    // A wrong public length violates the length constraints.
    {
        const short = [_]M31{M31.fromCanonical(raw.len - 1)};
        const tr2 = interp.RowTrace{ .log_size = log_size, .pubs = &short, .preprocessed = tr.preprocessed, .main = @ptrCast(bm) };
        try std.testing.expect(try interp.firstViolation(a, bytes_air, tr2) != null);
    }
}
