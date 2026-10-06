//! Witness generation for the header-chain AIR
//! (lean/StarkedAir/Gadgets/HeaderChain.lean, exported to airs/header_chain.json).
//!
//! One header per 256 rows: compressions at rows 0, 72 and 144 (SHA256d over 80 bytes),
//! rows 216..255 idle. Public inputs: the first header's prev-hash words and the last
//! header's hash words, each word as (lo, hi) 16-bit limbs.

const std = @import("std");
const spec = @import("../sha256/spec.zig");
const sha = @import("../sha256/witness.zig");
const M31 = @import("stwo_core").fields.m31.M31;

pub const PERIOD: usize = 256;
pub const N_PUB: usize = 32;

pub const lean_json = @embedFile("air:header_chain");

pub const Header = [80]u8;

/// Role of row `r` in the header-chain AIR.
pub fn role(r: usize) sha.Role {
    const q = r % PERIOD;
    return if (q < 216) sha.shaRole(q % sha.PERIOD) else .idle;
}

pub const Witness = struct {
    main: [][]M31,
    pubs: [N_PUB]M31,
    /// SHA256d of each header, as big-endian state words.
    hashes: []spec.State,

    pub fn deinit(self: Witness, allocator: std.mem.Allocator) void {
        for (self.main) |c| allocator.free(c);
        allocator.free(self.main);
        allocator.free(self.hashes);
    }
};

fn wordsPubs(out: []M31, words: [8]u32) void {
    for (words, 0..) |word, k| {
        out[2 * k] = M31.fromCanonical(word & 0xffff);
        out[2 * k + 1] = M31.fromCanonical(word >> 16);
    }
}

/// Builds the trace for exactly `2^log_size / 256` headers.
pub fn generate(allocator: std.mem.Allocator, log_size: u32, headers: []const Header) !Witness {
    const n = @as(usize, 1) << @intCast(log_size);
    if (n % PERIOD != 0 or headers.len != n / PERIOD) return error.HeaderCountMismatch;
    const words = try sha.Words.init(allocator, n);
    defer words.deinit(allocator);
    const hashes = try allocator.alloc(spec.State, headers.len);
    errdefer allocator.free(hashes);

    for (headers, 0..) |*header, i| {
        const base = i * PERIOD;
        const blocks = spec.HeaderBlocks.fromHeader(header);
        const mid = words.place(base, .{ .input = spec.IV, .block = blocks.first });
        const inner = words.place(base + 72, .{ .input = mid, .block = blocks.second });
        hashes[i] = words.place(base + 144, .{ .input = spec.IV, .block = spec.digestBlock(inner) });
    }

    var pubs: [N_PUB]M31 = undefined;
    const first = spec.blockFromBytes(headers[0][0..64]);
    wordsPubs(pubs[0..16], first[1..9].*);
    wordsPubs(pubs[16..32], hashes[headers.len - 1]);
    return .{ .main = try sha.columns(allocator, words, &role), .pubs = pubs, .hashes = hashes };
}

// ---------------------------------------------------------------- tests

const ir = @import("../air/ir.zig");
const interp = @import("../air/interp.zig");
const prove_mod = @import("../air/prove.zig");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;

pub fn loadHeaders(allocator: std.mem.Allocator, hex_lines: []const u8) ![]Header {
    var list: std.ArrayList(Header) = .empty;
    var it = std.mem.tokenizeAny(u8, hex_lines, "\n\r ");
    while (it.next()) |line| {
        var h: Header = undefined;
        _ = try std.fmt.hexToBytes(&h, line);
        try list.append(allocator, h);
    }
    return list.toOwnedSlice(allocator);
}

fn displayHash(state: spec.State) [32]u8 {
    var bytes = spec.stateToBytes(state);
    std.mem.reverse(u8, &bytes);
    return bytes;
}

test "header chain AIR (from Lean): mainnet blocks 0..15 satisfy it; tip hash matches" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const headers = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    try std.testing.expectEqual(@as(usize, 16), headers.len);
    const log_size = 12;
    const wit = try generate(a, log_size, headers);

    var expected: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&expected, std.mem.trim(u8, @embedFile("testdata:mainnet_hash_15"), "\n"));
    try std.testing.expectEqualSlices(u8, &expected, &displayHash(wit.hashes[15]));
    for (0..16) |i| try std.testing.expectEqual(wit.hashes[i], sha.readOutputAt(@ptrCast(wit.main), i * PERIOD + 144));

    const t = interp.RowTrace{
        .log_size = log_size,
        .pubs = &wit.pubs,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)),
        .main = @ptrCast(wit.main),
    };
    if (try interp.firstViolation(a, air, t)) |v| {
        std.debug.print("violation at row {d} constraint {d}\n", .{ v.row, v.constraint });
        return error.WitnessViolatesAir;
    }
}

test "header chain AIR: a broken link, a wrong padding word, or a wrong public input is caught" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const pre = try air.genPreprocessed(a, 12);
    const headers = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));

    // 1. Header 7 claims a different previous block (and is otherwise hashed honestly).
    {
        const bad = try a.dupe(Header, headers);
        bad[7][10] ^= 1;
        const wit = try generate(a, 12, bad);
        const t = interp.RowTrace{ .log_size = 12, .pubs = &wit.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        const v = (try interp.firstViolation(a, air, t)).?;
        try std.testing.expectEqual(@as(usize, 7 * PERIOD + 6), v.row);
    }
    // 2. A padding word of compression 1 is altered in the trace.
    {
        const wit = try generate(a, 12, headers);
        const r = 3 * PERIOD + 85; // compression 1, word 9 (must be zero)
        wit.main[sha.W + 4][r] = M31.one();
        const t = interp.RowTrace{ .log_size = 12, .pubs = &wit.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        try std.testing.expect(try interp.firstViolation(a, air, t) != null);
    }
    // 3. The claimed tip hash differs from the chain's.
    {
        var wit = try generate(a, 12, headers);
        wit.pubs[20] = wit.pubs[20].add(M31.one());
        const t = interp.RowTrace{ .log_size = 12, .pubs = &wit.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        try std.testing.expect(try interp.firstViolation(a, air, t) != null);
    }
}

test "header chain AIR: prove and verify blocks 0..15 on CPU" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const headers = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const wit = try generate(a, 12, headers);
    const statement = prove_mod.AirStatement{ .log_size = 12, .digest = try air.digest(a), .pubs = &wit.pubs, .air = &air, .allocator = a };
    const config = @import("stwo_core").pcs.PcsConfig{
        .pow_bits = 0,
        .fri_config = try @import("stwo_core").fri.FriConfig.init(0, 1, 3),
    };
    const proof = try prove_mod.prove(prove_mod.Engine(CpuBackend), a, config, try prove_mod.prepare(a, statement, @ptrCast(wit.main)));
    // Verifying against a different claimed tip must fail; cloning the proof via the wire format.
    var other = wit.pubs;
    other[16] = other[16].add(M31.one());
    const wire = @import("stwo_proof_wire");
    const bytes = try wire.encodeProofBytes(a, proof);
    try std.testing.expect(std.meta.isError(prove_mod.verify(a, config, air, 12, &other, try wire.decodeProofBytes(a, bytes))));
    try prove_mod.verify(a, config, air, 12, &wit.pubs, proof);
}
