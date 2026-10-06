//! Spike AIR: a chain of 32-bit additions, x[i+1] = x[i] + y[i] mod 2^32.
//!
//! It exercises the same building blocks as the SHA-256 AIR: bit-decomposed
//! u32 words, 16-bit limb additions with boolean carries, a next-row (+1)
//! reference, and a preprocessed selector that stops the last row from
//! wrapping onto row 0.
//!
//! Main columns: x_bits[32], y_bits[32], z_bits[32], c_lo, c_hi (98 total).
//! Preprocessed: not_last.

const std = @import("std");
const ir = @import("../ir.zig");
const M31 = @import("stwo_core").fields.m31.M31;

pub const X: u32 = 0;
pub const Y: u32 = 32;
pub const Z: u32 = 64;
pub const C_LO: u32 = 96;
pub const C_HI: u32 = 97;
pub const N_MAIN: u32 = 98;
pub const NOT_LAST: u32 = 0;
pub const N_PRE: u32 = 1;

/// Σ_{i<16} 2^i · bit[base + half*16 + i] at the given row offset.
fn limb(b: *ir.Builder, base: u32, half: u32, offset: i32) !ir.ExprId {
    var acc = try b.constant(0);
    for (0..16) |i| {
        const bit = try b.main(base + half * 16 + @as(u32, @intCast(i)), offset);
        acc = try b.add(acc, try b.scale(@as(u32, 1) << @intCast(i), bit));
    }
    return acc;
}

pub fn build(allocator: std.mem.Allocator, with_selector: bool) !ir.Air {
    var b = ir.Builder.init(allocator);
    defer b.deinit();
    for (0..96) |i| try b.assertBool(try b.main(@intCast(i), 0));
    try b.assertBool(try b.main(C_LO, 0));
    try b.assertBool(try b.main(C_HI, 0));

    const two16: u32 = 1 << 16;
    // lo(x) + lo(y) − lo(z) − 2^16·c_lo = 0
    const lo = try b.sub(
        try b.sub(try b.add(try limb(&b, X, 0, 0), try limb(&b, Y, 0, 0)), try limb(&b, Z, 0, 0)),
        try b.scale(two16, try b.main(C_LO, 0)),
    );
    try b.assertZero(lo);
    // hi(x) + hi(y) + c_lo − hi(z) − 2^16·c_hi = 0   (c_hi discarded: mod 2^32)
    const hi = try b.sub(
        try b.sub(
            try b.add(try b.add(try limb(&b, X, 1, 0), try limb(&b, Y, 1, 0)), try b.main(C_LO, 0)),
            try limb(&b, Z, 1, 0),
        ),
        try b.scale(two16, try b.main(C_HI, 0)),
    );
    try b.assertZero(hi);

    // Chaining: x@+1 = z, gated by not_last (limbs are injective on boolean bits).
    for (0..2) |half| {
        const diff = try b.sub(try limb(&b, X, @intCast(half), 1), try limb(&b, Z, @intCast(half), 0));
        try b.assertZero(if (with_selector) try b.mul(try b.pre(NOT_LAST, 0), diff) else diff);
    }
    return b.finish(if (with_selector) "add32_chain" else "add32_chain_wrapping", &.{.not_last}, N_MAIN);
}

pub const Witness = struct {
    main: [][]M31,

    pub fn deinit(self: Witness, allocator: std.mem.Allocator) void {
        for (self.main) |c| allocator.free(c);
        allocator.free(self.main);
    }
};

pub fn witness(allocator: std.mem.Allocator, log_size: u32, x0: u32, ys: []const u32) !Witness {
    const n = @as(usize, 1) << @intCast(log_size);
    std.debug.assert(ys.len == n);
    const main = try allocator.alloc([]M31, N_MAIN);
    for (main) |*c| c.* = try allocator.alloc(M31, n);
    var x = x0;
    for (0..n) |row| {
        const y = ys[row];
        const z = x +% y;
        for (0..32) |i| {
            main[X + i][row] = M31.fromCanonical((x >> @intCast(i)) & 1);
            main[Y + i][row] = M31.fromCanonical((y >> @intCast(i)) & 1);
            main[Z + i][row] = M31.fromCanonical((z >> @intCast(i)) & 1);
        }
        const lo_sum = (x & 0xffff) + (y & 0xffff);
        const c_lo = lo_sum >> 16;
        const c_hi = ((x >> 16) + (y >> 16) + c_lo) >> 16;
        main[C_LO][row] = M31.fromCanonical(c_lo);
        main[C_HI][row] = M31.fromCanonical(c_hi);
        x = z;
    }
    return .{ .main = main };
}

// ---------------------------------------------------------------- tests

const interp = @import("../interp.zig");
const prove_mod = @import("../prove.zig");
const pcs_core = @import("stwo_core").pcs;
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;

fn randomYs(allocator: std.mem.Allocator, n: usize, seed: u64) ![]u32 {
    var prng = std.Random.DefaultPrng.init(seed);
    const ys = try allocator.alloc(u32, n);
    for (ys) |*y| y.* = prng.random().int(u32);
    return ys;
}

fn testConfig() !pcs_core.PcsConfig {
    return .{ .pow_bits = 0, .fri_config = try @import("stwo_core").fri.FriConfig.init(0, 1, 3) };
}

test "witness satisfies the AIR; tampering and wrap-around are caught" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size = 5;
    const air = try build(a, true);
    try std.testing.expectEqual(@as(u32, 2), try air.maxConstraintDegree(a));
    const w = try witness(a, log_size, 0xffff_fff0, try randomYs(a, 32, 1));
    const t = interp.RowTrace{
        .log_size = log_size,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)),
        .main = @ptrCast(w.main),
    };
    try std.testing.expectEqual(null, try interp.firstViolation(a, air, t));

    // Flip one bit of z at row 7: breaks the addition (and chaining).
    w.main[Z + 3][7] = M31.one().sub(w.main[Z + 3][7]);
    try std.testing.expect(try interp.firstViolation(a, air, t) != null);
    w.main[Z + 3][7] = M31.one().sub(w.main[Z + 3][7]);

    // Without the selector the last row must equal x[0]; generally false.
    const wrapping = try build(a, false);
    const v = (try interp.firstViolation(a, wrapping, t)).?;
    try std.testing.expectEqual(@as(usize, 31), v.row);
}

test "IR JSON round-trips with a stable digest" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = try build(a, true);
    var out: std.Io.Writer.Allocating = .init(a);
    try air.writeJson(&out.writer);
    const parsed = try ir.Air.parseJson(a, out.written());
    try std.testing.expectEqualSlices(u8, &(try air.digest(a)), &(try parsed.value.digest(a)));
}

test "prove and verify on CPU; verification rejects a bad witness and a different AIR" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size = 6;
    const n = @as(usize, 1) << log_size;
    const air = try build(a, true);
    const statement = prove_mod.AirStatement{
        .log_size = log_size,
        .digest = try air.digest(a),
        .air = &air,
        .allocator = a,
    };
    const Engine = prove_mod.Engine(CpuBackend);
    const config = try testConfig();

    {
        const w = try witness(a, log_size, 12345, try randomYs(a, n, 2));
        const proof = try prove_mod.prove(Engine, a, config, try prove_mod.prepare(a, statement, @ptrCast(w.main)));
        try prove_mod.verify(a, config, air, log_size, &.{}, proof);
    }
    {
        // The honest prover refuses a witness that violates the AIR (its
        // composition quotient does not vanish), which also checks that our
        // domain-side constraint evaluation detects violations.
        const w = try witness(a, log_size, 12345, try randomYs(a, n, 3));
        w.main[Z + 20][9] = M31.one().sub(w.main[Z + 20][9]);
        try std.testing.expectError(
            error.ConstraintsNotSatisfied,
            prove_mod.prove(Engine, a, config, try prove_mod.prepare(a, statement, @ptrCast(w.main))),
        );
    }
    {
        // An honest proof for one AIR must not verify against another AIR.
        const w = try witness(a, log_size, 7, try randomYs(a, n, 4));
        const proof = try prove_mod.prove(Engine, a, config, try prove_mod.prepare(a, statement, @ptrCast(w.main)));
        const other = try build(a, false);
        try std.testing.expectError(error.OodsNotMatching, prove_mod.verify(a, config, other, log_size, &.{}, proof));
    }
}

test "a prover that commits forged preprocessed columns is rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size = 5;
    const n = @as(usize, 1) << log_size;
    const air = try build(a, true);
    const statement = prove_mod.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };

    // Break the chain at row 10, then hide it by committing not_last ≡ 0,
    // which switches the chaining constraints off everywhere.
    const w = try witness(a, log_size, 1, try randomYs(a, n, 5));
    for (0..32) |i| w.main[X + i][10] = M31.one().sub(w.main[X + i][10]);
    for (0..n) |row| {
        var x: u32 = 0;
        var y: u32 = 0;
        for (0..32) |i| {
            x |= w.main[X + i][row].toU32() << @intCast(i);
            y |= w.main[Y + i][row].toU32() << @intCast(i);
        }
        const z = x +% y;
        for (0..32) |i| w.main[Z + i][row] = M31.fromCanonical((z >> @intCast(i)) & 1);
        const c_lo = ((x & 0xffff) + (y & 0xffff)) >> 16;
        w.main[C_LO][row] = M31.fromCanonical(c_lo);
        w.main[C_HI][row] = M31.fromCanonical(((x >> 16) + (y >> 16) + c_lo) >> 16);
    }
    const zero_selector = try a.alloc(M31, n);
    @memset(zero_selector, M31.zero());
    const forged = prove_mod.Prepared{
        .request = statement,
        .trace = try @import("stwo_prover_engine").transaction.PreparedTrace.initOwned(
            a,
            try prove_mod.toStorage(a, log_size, &.{zero_selector}),
            try prove_mod.toStorage(a, log_size, @ptrCast(w.main)),
        ),
    };
    const Engine = prove_mod.Engine(CpuBackend);
    const config = try testConfig();
    const proof = try prove_mod.prove(Engine, a, config, forged);
    try std.testing.expectError(error.PreprocessedRootMismatch, prove_mod.verify(a, config, air, log_size, &.{}, proof));
}

/// The AIR as exported from Lean (`lean/StarkedAir/Gadgets/Add32Chain.lean`),
/// where its soundness theorem is proven.
pub const lean_json = @embedFile("air:add32_chain");

test "Lean-exported AIR: Zig witness satisfies it, proves on CPU, and verifies" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const parsed = try ir.Air.parseJson(a, lean_json);
    const air = parsed.value;
    try std.testing.expectEqualStrings("add32_chain", air.name);
    try std.testing.expectEqual(@as(u32, N_MAIN), air.n_main);
    // Same constraint count and degree as the Zig-built prototype; Lean's
    // exporter shares common subexpressions, so the DAG is smaller.
    const zig_air = try build(a, true);
    try std.testing.expectEqual(zig_air.constraints.len, air.constraints.len);
    try std.testing.expect(air.exprs.len < zig_air.exprs.len);

    const log_size = 6;
    const n = @as(usize, 1) << log_size;
    const w = try witness(a, log_size, 0xdead_beef, try randomYs(a, n, 6));
    const t = interp.RowTrace{
        .log_size = log_size,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)),
        .main = @ptrCast(w.main),
    };
    try std.testing.expectEqual(null, try interp.firstViolation(a, air, t));

    const statement = prove_mod.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };
    const config = try testConfig();
    const proof = try prove_mod.prove(prove_mod.Engine(CpuBackend), a, config, try prove_mod.prepare(a, statement, @ptrCast(w.main)));
    try prove_mod.verify(a, config, air, log_size, &.{}, proof);
}
