//! Reference SHA-256 (FIPS 180-4) with per-round intermediates.
//!
//! This is the executable spec that the SHA-256 AIR's witness generator reads
//! from and that differential tests compare against. It is deliberately plain:
//! no SIMD and no shortcuts, so it can be checked line by line against
//! FIPS 180-4 §4.1.2, §5.3.3 and §6.2.2.

const std = @import("std");

pub const State = [8]u32;
pub const Block = [16]u32;

/// FIPS 180-4 §5.3.3.
pub const IV: State = .{
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
    0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
};

/// FIPS 180-4 §4.2.2.
pub const K: [64]u32 = .{
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
};

// FIPS 180-4 §4.1.2.
pub fn ch(x: u32, y: u32, z: u32) u32 {
    return (x & y) ^ (~x & z);
}
pub fn maj(x: u32, y: u32, z: u32) u32 {
    return (x & y) ^ (x & z) ^ (y & z);
}
pub fn bigSigma0(x: u32) u32 {
    return std.math.rotr(u32, x, 2) ^ std.math.rotr(u32, x, 13) ^ std.math.rotr(u32, x, 22);
}
pub fn bigSigma1(x: u32) u32 {
    return std.math.rotr(u32, x, 6) ^ std.math.rotr(u32, x, 11) ^ std.math.rotr(u32, x, 25);
}
pub fn smallSigma0(x: u32) u32 {
    return std.math.rotr(u32, x, 7) ^ std.math.rotr(u32, x, 18) ^ (x >> 3);
}
pub fn smallSigma1(x: u32) u32 {
    return std.math.rotr(u32, x, 17) ^ std.math.rotr(u32, x, 19) ^ (x >> 10);
}

/// Everything round `t` computes, with each modular addition expressed as an
/// exact (wide) integer sum. This lets the AIR derive the carries.
pub const Round = struct {
    /// Message schedule word W[t] (§6.2.2 step 1).
    w: u32,
    /// For t >= 16: σ1(W[t-2]) and σ0(W[t-15]); zero otherwise.
    small_sigma1: u32,
    small_sigma0: u32,
    big_sigma1: u32,
    big_sigma0: u32,
    ch: u32,
    maj: u32,
    /// New working variables a and e after the round. The other six are
    /// shifted copies of earlier a/e values.
    a: u32,
    e: u32,
    /// Exact integer sums before reduction mod 2^32:
    /// a' = T1 + T2 and e' = d + T1, where
    /// T1 = h + Σ1(e) + Ch(e,f,g) + K[t] + W[t] and T2 = Σ0(a) + Maj(a,b,c).
    a_sum: u64,
    e_sum: u64,
    /// For t >= 16: σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16], unreduced.
    w_sum: u64,
};

pub const Trace = struct {
    rounds: [64]Round,
    /// Hash value after this block (§6.2.2 step 4).
    output: State,
};

/// Process one 512-bit block, recording every round.
pub fn compressTraced(input: State, block: Block) Trace {
    var trace: Trace = undefined;
    var w: [64]u32 = undefined;
    var v = input; // a b c d e f g h
    for (0..64) |t| {
        var r: Round = std.mem.zeroes(Round);
        if (t < 16) {
            w[t] = block[t];
        } else {
            r.small_sigma1 = smallSigma1(w[t - 2]);
            r.small_sigma0 = smallSigma0(w[t - 15]);
            r.w_sum = @as(u64, r.small_sigma1) + w[t - 7] + r.small_sigma0 + w[t - 16];
            w[t] = @truncate(r.w_sum);
        }
        r.w = w[t];
        r.big_sigma1 = bigSigma1(v[4]);
        r.ch = ch(v[4], v[5], v[6]);
        r.big_sigma0 = bigSigma0(v[0]);
        r.maj = maj(v[0], v[1], v[2]);
        const t1: u64 = @as(u64, v[7]) + r.big_sigma1 + r.ch + K[t] + r.w;
        const t2: u64 = @as(u64, r.big_sigma0) + r.maj;
        r.a_sum = t1 + t2;
        r.e_sum = @as(u64, v[3]) + t1;
        r.a = @truncate(r.a_sum);
        r.e = @truncate(r.e_sum);
        // Build the new state in a temporary: assigning the literal straight to
        // `v` would alias, overwriting v[0] before it is read as the new b.
        const next: State = .{ r.a, v[0], v[1], v[2], r.e, v[4], v[5], v[6] };
        v = next;
        trace.rounds[t] = r;
    }
    for (&trace.output, input, v) |*out, h, x| out.* = h +% x;
    return trace;
}

pub fn compress(input: State, block: Block) State {
    return compressTraced(input, block).output;
}

/// Big-endian word decoding (§5.2.1 / §3.1).
pub fn blockFromBytes(bytes: *const [64]u8) Block {
    var block: Block = undefined;
    for (&block, 0..) |*word, i| word.* = std.mem.readInt(u32, bytes[4 * i ..][0..4], .big);
    return block;
}

pub fn stateToBytes(state: State) [32]u8 {
    var out: [32]u8 = undefined;
    for (state, 0..) |word, i| std.mem.writeInt(u32, out[4 * i ..][0..4], word, .big);
    return out;
}

/// The three compressions of Bitcoin's SHA256d over an 80-byte header.
/// Padding is per FIPS 180-4 §5.1.1.
pub const HeaderBlocks = struct {
    /// Header bytes 0..64.
    first: Block,
    /// Header bytes 64..80, then 0x80, zeros, and bit length 640.
    second: Block,

    pub fn fromHeader(header: *const [80]u8) HeaderBlocks {
        var tail = [_]u8{0} ** 64;
        @memcpy(tail[0..16], header[64..80]);
        tail[16] = 0x80;
        std.mem.writeInt(u64, tail[56..64], 80 * 8, .big);
        return .{ .first = blockFromBytes(header[0..64]), .second = blockFromBytes(&tail) };
    }
};

/// The block for SHA-256 of a 32-byte digest (the second hash of SHA256d).
pub fn digestBlock(digest: State) Block {
    var block = [_]u32{0} ** 16;
    @memcpy(block[0..8], &digest);
    block[8] = 0x8000_0000;
    block[15] = 256;
    return block;
}

/// SHA256d(header) as the 8 big-endian state words of the final compression.
/// Bitcoin displays block hashes byte-reversed.
pub fn headerHash(header: *const [80]u8) State {
    const blocks = HeaderBlocks.fromHeader(header);
    const inner = compress(compress(IV, blocks.first), blocks.second);
    return compress(IV, digestBlock(inner));
}

// ---------------------------------------------------------------- tests

const Sha256 = std.crypto.hash.sha2.Sha256;

fn hexToBytes(comptime hex: []const u8) [hex.len / 2]u8 {
    var out: [hex.len / 2]u8 = undefined;
    _ = std.fmt.hexToBytes(&out, hex) catch unreachable;
    return out;
}

/// Bitcoin mainnet genesis block header.
pub const genesis_header = hexToBytes(
    "0100000000000000000000000000000000000000000000000000000000000000" ++
        "000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa" ++
        "4b1e5e4a29ab5f49ffff001d1dac2b7c",
);

test "FIPS 180-4 'abc' vector (one block)" {
    var block_bytes = [_]u8{0} ** 64;
    @memcpy(block_bytes[0..3], "abc");
    block_bytes[3] = 0x80;
    block_bytes[63] = 24;
    const out = stateToBytes(compress(IV, blockFromBytes(&block_bytes)));
    try std.testing.expectEqualSlices(u8, &hexToBytes(
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    ), &out);
}

test "per-round sums reduce to the recorded words" {
    const trace = compressTraced(IV, blockFromBytes(genesis_header[0..64]));
    for (trace.rounds, 0..) |r, t| {
        try std.testing.expectEqual(r.a, @as(u32, @truncate(r.a_sum)));
        try std.testing.expectEqual(r.e, @as(u32, @truncate(r.e_sum)));
        if (t >= 16) try std.testing.expectEqual(r.w, @as(u32, @truncate(r.w_sum)));
        // Bounds the AIR's carry ranges rely on: a' has 7 summands, e' has 6, W has 4.
        try std.testing.expect(r.a_sum < 7 << 32);
        try std.testing.expect(r.e_sum < 6 << 32);
        try std.testing.expect(r.w_sum < 4 << 32);
    }
}

test "genesis block hash" {
    var hash = stateToBytes(headerHash(&genesis_header));
    std.mem.reverse(u8, &hash);
    try std.testing.expectEqualSlices(u8, &hexToBytes(
        "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f",
    ), &hash);
}

test "matches std SHA256d on random headers" {
    var prng = std.Random.DefaultPrng.init(0x5747_4b45);
    for (0..256) |_| {
        var header: [80]u8 = undefined;
        prng.random().bytes(&header);
        var once: [32]u8 = undefined;
        var twice: [32]u8 = undefined;
        Sha256.hash(&header, &once, .{});
        Sha256.hash(&once, &twice, .{});
        try std.testing.expectEqualSlices(u8, &twice, &stateToBytes(headerHash(&header)));
    }
}
