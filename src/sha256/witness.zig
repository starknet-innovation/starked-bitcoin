//! Witness generation for the SHA-256 compression AIR
//! (lean/StarkedAir/Gadgets/Sha256.lean, exported to airs/sha256_compress.json).
//!
//! Layout per 72-row period: rows 0–3 init, 4–67 rounds, 68–71 finalize. See the
//! Lean file for the column map. Derived columns (Σ/σ/Ch/Maj limbs) are
//! unconditional in the AIR, so they are computed for *every* row from the
//! cyclic neighbours. Carries are filled where their addition constraint is
//! active and are 0 elsewhere.

const std = @import("std");
const spec = @import("spec.zig");
const M31 = @import("stwo_core").fields.m31.M31;

pub const PERIOD: usize = 72;
pub const A: usize = 0;
pub const E: usize = 32;
pub const W: usize = 64;
pub const S0: usize = 96;
pub const S1: usize = 98;
pub const CH: usize = 100;
pub const MJ: usize = 102;
pub const SS0: usize = 104;
pub const SS1: usize = 106;
pub const CA_LO: usize = 108;
pub const CA_HI: usize = 111;
pub const CE_LO: usize = 114;
pub const CE_HI: usize = 117;
pub const CW_LO: usize = 120;
pub const CW_HI: usize = 122;
pub const N_MAIN: usize = 124;

pub const Compression = struct { input: spec.State, block: spec.Block };

pub const Witness = struct {
    main: [][]M31,
    /// Output state of each full compression, in order.
    outputs: []spec.State,

    pub fn deinit(self: Witness, allocator: std.mem.Allocator) void {
        for (self.main) |c| allocator.free(c);
        allocator.free(self.main);
        allocator.free(self.outputs);
    }
};

/// Number of complete compressions that fit in 2^log_size rows.
pub fn capacity(log_size: u32) usize {
    return (@as(usize, 1) << @intCast(log_size)) / PERIOD;
}

fn lo(x: u32) u32 {
    return x & 0xffff;
}
fn hi(x: u32) u32 {
    return x >> 16;
}

pub fn generate(allocator: std.mem.Allocator, log_size: u32, compressions: []const Compression) !Witness {
    const n = @as(usize, 1) << @intCast(log_size);
    if (compressions.len > capacity(log_size)) return error.TooManyCompressions;

    // Word-level trace of a, e, w per row.
    const a = try allocator.alloc(u32, n);
    defer allocator.free(a);
    const e = try allocator.alloc(u32, n);
    defer allocator.free(e);
    const w = try allocator.alloc(u32, n);
    defer allocator.free(w);
    @memset(w, 0);
    const outputs = try allocator.alloc(spec.State, compressions.len);
    errdefer allocator.free(outputs);

    const n_blocks = (n + PERIOD - 1) / PERIOD;
    const dummy = Compression{ .input = [_]u32{0} ** 8, .block = [_]u32{0} ** 16 };
    for (0..n_blocks) |b| {
        const c = if (b < compressions.len) compressions[b] else dummy;
        const trace = spec.compressTraced(c.input, c.block);
        if (b < compressions.len) outputs[b] = trace.output;
        const base = b * PERIOD;
        for (0..PERIOD) |p| {
            const r = base + p;
            if (r >= n) break;
            if (p < 4) {
                a[r] = c.input[3 - p];
                e[r] = c.input[7 - p];
            } else if (p < 68) {
                const t = trace.rounds[p - 4];
                a[r] = t.a;
                e[r] = t.e;
                w[r] = t.w;
            } else {
                a[r] = a[r - 4] +% a[r - 68];
                e[r] = e[r - 4] +% e[r - 68];
            }
        }
    }

    const main = try allocator.alloc([]M31, N_MAIN);
    for (main) |*col| {
        col.* = try allocator.alloc(M31, n);
        @memset(col.*, M31.zero());
    }
    const at = struct {
        fn f(words: []const u32, r: usize, back: usize) u32 {
            return words[(r + words.len - back) % words.len];
        }
    }.f;
    for (0..n) |r| {
        const p = r % PERIOD;
        for (0..32) |i| {
            const s: u5 = @intCast(i);
            main[A + i][r] = M31.fromCanonical((a[r] >> s) & 1);
            main[E + i][r] = M31.fromCanonical((e[r] >> s) & 1);
            main[W + i][r] = M31.fromCanonical((w[r] >> s) & 1);
        }
        const s0v = spec.bigSigma0(at(a, r, 1));
        const s1v = spec.bigSigma1(at(e, r, 1));
        const chv = spec.ch(at(e, r, 1), at(e, r, 2), at(e, r, 3));
        const mjv = spec.maj(at(a, r, 1), at(a, r, 2), at(a, r, 3));
        const ss0 = spec.smallSigma0(at(w, r, 15));
        const ss1 = spec.smallSigma1(at(w, r, 2));
        inline for (.{ .{ S0, s0v }, .{ S1, s1v }, .{ CH, chv }, .{ MJ, mjv }, .{ SS0, ss0 }, .{ SS1, ss1 } }) |pair| {
            main[pair[0]][r] = M31.fromCanonical(lo(pair[1]));
            main[pair[0] + 1][r] = M31.fromCanonical(hi(pair[1]));
        }

        var ca = [2]u32{ 0, 0 };
        var ce = [2]u32{ 0, 0 };
        var cw = [2]u32{ 0, 0 };
        if (p >= 4 and p < 68) {
            const k = spec.K[p - 4];
            const h4 = at(e, r, 4);
            const d4 = at(a, r, 4);
            const t1_lo = lo(h4) + lo(s1v) + lo(chv) + lo(k) + lo(w[r]);
            const t1_hi = hi(h4) + hi(s1v) + hi(chv) + hi(k) + hi(w[r]);
            ca[0] = (t1_lo + lo(s0v) + lo(mjv)) >> 16;
            ca[1] = (t1_hi + hi(s0v) + hi(mjv) + ca[0]) >> 16;
            ce[0] = (lo(d4) + t1_lo) >> 16;
            ce[1] = (hi(d4) + t1_hi + ce[0]) >> 16;
            if (p >= 20) {
                const w7 = at(w, r, 7);
                const w16 = at(w, r, 16);
                cw[0] = (lo(ss1) + lo(w7) + lo(ss0) + lo(w16)) >> 16;
                cw[1] = (hi(ss1) + hi(w7) + hi(ss0) + hi(w16) + cw[0]) >> 16;
            }
        } else if (p >= 68) {
            ca[0] = (lo(at(a, r, 4)) + lo(at(a, r, 68))) >> 16;
            ca[1] = (hi(at(a, r, 4)) + hi(at(a, r, 68)) + ca[0]) >> 16;
            ce[0] = (lo(at(e, r, 4)) + lo(at(e, r, 68))) >> 16;
            ce[1] = (hi(at(e, r, 4)) + hi(at(e, r, 68)) + ce[0]) >> 16;
        }
        inline for (.{ .{ CA_LO, 0, 3, &ca }, .{ CA_HI, 1, 3, &ca }, .{ CE_LO, 0, 3, &ce }, .{ CE_HI, 1, 3, &ce }, .{ CW_LO, 0, 2, &cw }, .{ CW_HI, 1, 2, &cw } }) |cfg| {
            const v = cfg[3][cfg[1]];
            for (0..cfg[2]) |j| main[cfg[0] + j][r] = M31.fromCanonical((v >> @intCast(j)) & 1);
        }
    }
    return .{ .main = main, .outputs = outputs };
}

/// Reads the output state of compression `index` back from its finalize rows.
pub fn readOutput(main: []const []const M31, index: usize) spec.State {
    var out: spec.State = undefined;
    for (0..4) |j| {
        const r = index * PERIOD + 68 + j;
        var aw: u32 = 0;
        var ew: u32 = 0;
        for (0..32) |i| {
            aw |= main[A + i][r].toU32() << @intCast(i);
            ew |= main[E + i][r].toU32() << @intCast(i);
        }
        out[3 - j] = aw;
        out[7 - j] = ew;
    }
    return out;
}

// ---------------------------------------------------------------- tests

const ir = @import("../air/ir.zig");
const interp = @import("../air/interp.zig");
const prove_mod = @import("../air/prove.zig");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;

pub const lean_json = @embedFile("air:sha256_compress");

/// The three compressions of SHA256d over the genesis header.
fn genesisCompressions() [3]Compression {
    const blocks = spec.HeaderBlocks.fromHeader(&spec.genesis_header);
    const mid = spec.compress(spec.IV, blocks.first);
    const inner = spec.compress(mid, blocks.second);
    return .{
        .{ .input = spec.IV, .block = blocks.first },
        .{ .input = mid, .block = blocks.second },
        .{ .input = spec.IV, .block = spec.digestBlock(inner) },
    };
}

test "SHA-256 AIR (from Lean): genesis SHA256d witness satisfies it; finalize rows hold the digests" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    try std.testing.expectEqual(@as(u32, N_MAIN), air.n_main);

    const log_size = 8; // 256 rows: 3 compressions + a partial dummy block
    const cs = genesisCompressions();
    const wit = try generate(a, log_size, &cs);
    const t = interp.RowTrace{
        .log_size = log_size,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)),
        .main = @ptrCast(wit.main),
    };
    if (try interp.firstViolation(a, air, t)) |v| {
        std.debug.print("violation at row {d} constraint {d}\n", .{ v.row, v.constraint });
        return error.WitnessViolatesAir;
    }
    for (0..3) |i| try std.testing.expectEqual(wit.outputs[i], readOutput(@ptrCast(wit.main), i));
    var hash = spec.stateToBytes(readOutput(@ptrCast(wit.main), 2));
    std.mem.reverse(u8, &hash);
    var expected: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&expected, "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
    try std.testing.expectEqualSlices(u8, &expected, &hash);
}

test "SHA-256 AIR: tampering with a round, the schedule, or the output is caught" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const log_size = 8;
    const cs = genesisCompressions();
    const pre = try air.genPreprocessed(a, log_size);
    // Rows: a round's a-bit, a scheduled w-bit (t = 20), a finalize row's e-bit.
    for ([_][2]usize{ .{ A + 5, 40 }, .{ W + 9, 24 }, .{ E + 30, 70 } }) |cell| {
        const wit = try generate(a, log_size, &cs);
        wit.main[cell[0]][cell[1]] = M31.one().sub(wit.main[cell[0]][cell[1]]);
        const t = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        try std.testing.expect(try interp.firstViolation(a, air, t) != null);
    }
}

test "SHA-256 AIR: prove and verify on CPU" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const log_size = 8;
    const cs = genesisCompressions();
    const wit = try generate(a, log_size, &cs);
    const statement = prove_mod.AirStatement{ .log_size = log_size, .digest = try air.digest(a), .air = &air, .allocator = a };
    const config = @import("stwo_core").pcs.PcsConfig{
        .pow_bits = 0,
        .fri_config = try @import("stwo_core").fri.FriConfig.init(0, 1, 3),
    };
    const proof = try prove_mod.prove(prove_mod.Engine(CpuBackend), a, config, try prove_mod.prepare(a, statement, @ptrCast(wit.main)));
    try prove_mod.verify(a, config, air, log_size, &.{}, proof);
}
