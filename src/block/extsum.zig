//! LogUp running sum against an external challenge (M3b, D-040): the witness for `extsum_test`
//! (Lean: `Block/ExtSum.lean`, `extsum_sound`). Per row a tuple `t` (3 M31), a multiplicity
//! `m ∈ {−1, 0, 1}`, the fraction `f = m / (z − Σₖ αₖ tₖ)` (QM31) and the running sum; the last row's
//! sum is public. The coin-event component reuses the layout.

const std = @import("std");
const core = @import("stwo_core");
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

pub const json = @embedFile("air:extsum_test");
pub const W = 3;
pub const N_MAIN = 12;
pub const N_PUB = 20;

pub const Row = struct { t: [W]M31, m: i2 };

fn q4(x: QM31) [4]M31 {
    return x.toM31Array();
}

pub fn phi(alpha: [W]QM31, t: [W]M31) QM31 {
    var s = QM31.zero();
    for (alpha, t) |a, v| s = s.add(a.mulM31(v));
    return s;
}

pub const Witness = struct { cols: [][]M31, pubs: [N_PUB]M31, sum: QM31 };

pub fn generate(a: std.mem.Allocator, log_size: u32, z: QM31, alpha: [W]QM31, rows: []const Row) !Witness {
    const n = @as(usize, 1) << @intCast(log_size);
    if (rows.len > n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    var acc = QM31.zero();
    for (0..n) |r| {
        const row: Row = if (r < rows.len) rows[r] else .{ .t = .{ M31.zero(), M31.zero(), M31.zero() }, .m = 0 };
        for (0..W) |k| cols[k][r] = row.t[k];
        const m = switch (row.m) {
            0 => M31.zero(),
            1 => M31.one(),
            -1 => M31.zero().sub(M31.one()),
            else => return error.BadMultiplicity,
        };
        cols[3][r] = m;
        const f = if (row.m == 0) QM31.zero() else (try z.sub(phi(alpha, row.t)).inv()).mulM31(m);
        acc = acc.add(f);
        for (q4(f), 0..) |x, j| cols[4 + j][r] = x;
        for (q4(acc), 0..) |x, j| cols[8 + j][r] = x;
    }
    var pubs: [N_PUB]M31 = undefined;
    @memcpy(pubs[0..4], &q4(z));
    for (alpha, 0..) |al, k| @memcpy(pubs[4 + 4 * k ..][0..4], &q4(al));
    @memcpy(pubs[16..20], &q4(acc));
    return .{ .cols = cols, .pubs = pubs, .sum = acc };
}

test "extsum: a running sum against a public challenge proves and verifies; a wrong sum is rejected" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, json)).value;
    const z = QM31.fromU32Unchecked(123456789, 987654321, 55555, 7);
    const alpha = [W]QM31{ QM31.one(), QM31.fromU32Unchecked(11, 22, 33, 44), QM31.fromU32Unchecked(5, 6, 7, 8) };
    // Creations (+1) and spends (−1) of the same tuples cancel; one tuple is left over.
    var rows: [40]Row = undefined;
    for (0..20) |i| {
        const t = [W]M31{ M31.fromCanonical(@intCast(1000 + i)), M31.fromCanonical(@intCast(i)), M31.fromCanonical(7) };
        rows[2 * i] = .{ .t = t, .m = 1 };
        rows[2 * i + 1] = .{ .t = t, .m = if (i == 19) 0 else -1 };
    }
    const log_size: u32 = 6;
    const w = try generate(a, log_size, z, alpha, &rows);
    // The sum is the one leftover fraction.
    const left = try z.sub(phi(alpha, rows[38].t)).inv();
    try std.testing.expect(w.sum.eql(left));
    const pre = try air.genPreprocessed(a, log_size);
    try std.testing.expect(try interp.firstViolation(a, air, .{ .log_size = log_size, .pubs = &w.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(w.cols) }) == null);
    // A wrong public sum violates the last row.
    var bad = w.pubs;
    bad[16] = bad[16].add(M31.one());
    const v = (try interp.firstViolation(a, air, .{ .log_size = log_size, .pubs = &bad, .preprocessed = @ptrCast(pre), .main = @ptrCast(w.cols) })) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, (1 << log_size) - 1), v.row);
    // Prove and verify (test strength).
    const parts = [_]system.Part{.{ .air = &air, .log_size = log_size, .pubs = &w.pubs }};
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const mains = [_][]const []const M31{@ptrCast(w.cols)};
    const proof = try system.prove(E, a, cfg, &parts, &mains);
    try system.verifyExt(a, cfg, &parts, &.{}, proof);
    const parts_bad = [_]system.Part{.{ .air = &air, .log_size = log_size, .pubs = &bad }};
    const proof2 = try system.prove(E, a, cfg, &parts, &mains);
    try std.testing.expect(std.meta.isError(system.verifyExt(a, cfg, &parts_bad, &.{}, proof2)));
}
