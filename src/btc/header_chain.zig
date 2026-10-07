//! Witness generation for the header-chain AIR
//! (lean/StarkedAir/Gadgets/HeaderChain.lean, exported to airs/header_chain.json).
//!
//! One header per 256 rows: compressions at rows 0, 72 and 144 (SHA256d over 80 bytes),
//! proof-of-work scratch in rows 216..217, chain state 218..219, retarget 220..228, median time
//! past 229..240, chainwork 241..253, rows 254..255 idle. Layout and public inputs: docs/airs/header-chain.md.

const std = @import("std");
const spec = @import("../sha256/spec.zig");
const sha = @import("../sha256/witness.zig");
const M31 = @import("stwo_core").fields.m31.M31;

pub const PERIOD: usize = 256;
pub const N_PUB: usize = 108;
const retarget = @import("retarget.zig");
const work_mod = @import("work.zig");

pub const lean_json = @embedFile("air:header_chain");

pub const Header = [80]u8;

/// Role of row `r` in the header-chain AIR.
pub fn role(r: usize) sha.Role {
    const q = r % PERIOD;
    return if (q < 216) sha.shaRole(q % sha.PERIOD) else .idle;
}

/// Proof-of-work scratch words for rows 216 (a, e, w) and 217 (a), per
/// `HeaderChain.powCs`. Fails if the header does not meet its own target, or uses an
/// encoding outside the AIR's range (nSize ∉ [3, 29]).
pub const PowScratch = struct { a216: u32, e216: u32, w216: u32, a217: u32 };

pub fn powScratch(header: *const Header, hash: spec.State) !PowScratch {
    const word18 = std.mem.readInt(u32, header[72..76], .big);
    const n_size = word18 & 0xff;
    if (n_size < 3 or n_size > 29) return error.UnsupportedTargetEncoding;
    if ((word18 >> 15) & 1 == 1) return error.NegativeTarget;
    const s: usize = n_size - 3;
    const mant: u32 = (word18 >> 24) | (((word18 >> 16) & 0xff) << 8) | (((word18 >> 8) & 0x7f) << 16);
    if (mant == 0) return error.ZeroTarget;
    if (s == 26 and mant > 0xffff) return error.AbovePowLimit;
    var bytes: [32]u32 = undefined;
    for (0..32) |i| bytes[i] = (hash[i / 4] >> @intCast(8 * (3 - i % 4))) & 0xff;
    for (s + 3..32) |i| if (bytes[i] != 0) return error.InsufficientWork;
    const mid = bytes[s] + 256 * bytes[s + 1] + 65536 * bytes[s + 2];
    var low: u32 = 0;
    for (0..s) |i| low += bytes[i];
    const lt: u32 = @intFromBool(mid < mant);
    if (lt == 0 and (mid != mant or low != 0)) return error.InsufficientWork;
    return .{
        .a216 = @as(u32, 1) << @intCast(s),
        .e216 = mant - mid - lt,
        .w216 = lt | ((mant - 1) << 1),
        .a217 = low,
    };
}

/// State before the segment's first header (see docs/design/consensus-rules.md).
pub const ChainStart = struct {
    /// Height of the segment's first header (< 2^30).
    height: u32,
    /// Previous header's nBits and period-start time, as raw header words 18 and 17.
    prev_nbits_word: u32 = 0,
    prev_pst_word: u32 = 0,
    /// Median-time-past window of the first header: the raw time words of its 11
    /// predecessors, newest first (`window[0]` is the predecessor's time). Near genesis it is
    /// padded with `SENTINEL`; use `windowFrom`.
    window: [11]u32,
    /// Chainwork before the segment (0 before genesis).
    work: u256 = 0,
};

const TMAX: u32 = 0xffffffff;
/// Window of the genesis header (decision D-018, docs/airs/header-chain.md § v4): at height
/// `h ≤ 10` the visible tail has exactly `5 − h/2` zeros (6 at genesis), so "≥ 6 of 11 below"
/// matches Core's median over the `h` real predecessors.
pub const SENTINEL = [11]u32{ TMAX, 0, TMAX, 0, TMAX, 0, TMAX, 0, TMAX, 0, 0 };

/// Window for a first header whose real predecessors' raw time words are `prev`, newest
/// first (all 11 when the height is at least 11; fewer near genesis).
pub fn windowFrom(prev: []const u32) [11]u32 {
    var w: [11]u32 = undefined;
    for (0..11) |k| w[k] = if (k < prev.len) prev[k] else SENTINEL[k - prev.len];
    return w;
}

/// Start state for a segment beginning at genesis (height 0 is a period boundary, so the
/// predecessor values are unused).
pub const genesis_start = ChainStart{ .height = 0, .window = SENTINEL };

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

fn headerWordAt(header: *const Header, t: usize) u32 {
    return std.mem.readInt(u32, header[4 * t ..][0..4], .big);
}

/// Builds the trace for exactly `2^log_size / 256` headers.
pub fn generate(allocator: std.mem.Allocator, log_size: u32, headers: []const Header) !Witness {
    return generateFrom(allocator, log_size, headers, genesis_start);
}

pub fn generateFrom(allocator: std.mem.Allocator, log_size: u32, headers: []const Header, start: ChainStart) !Witness {
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
        const pow = try powScratch(header, hashes[i]);
        words.a[base + 216] = pow.a216;
        words.e[base + 216] = pow.e216;
        words.w[base + 216] = pow.w216;
        words.a[base + 217] = pow.a217;
    }

    // Chain state (rows 218, 219).
    var prev_nbits = start.prev_nbits_word;
    var pst = start.prev_pst_word;
    var height_carries = try allocator.alloc(u32, headers.len);
    defer allocator.free(height_carries);
    for (headers, 0..) |*header, i| {
        const base = i * PERIOD;
        const height = start.height + @as(u32, @intCast(i));
        if (height >= 1 << 30) return error.HeightOutOfRange;
        const rem = height % 2016;
        const flag = rem == 0;
        const nbits = headerWordAt(header, 18);
        if (!flag and nbits != prev_nbits) return error.DifficultyChangedMidPeriod;
        if (flag) pst = headerWordAt(header, 17);
        const g: u32 = @intFromBool(i > 0 and !flag);
        const g2: u32 = @intFromBool(i == 0 and !flag);
        words.a[base + 218] = height;
        words.e[base + 218] = pst;
        words.w[base + 218] = @as(u32, @intFromBool(flag)) | (rem << 1) |
            ((if (flag) 0 else rem - 1) << 12) | (g << 23) | (g2 << 24);
        words.a[base + 219] = height / 2016;
        words.e[base + 219] = 2015 - rem;
        height_carries[i] = @intFromBool(i > 0 and (height - 1) & 0xffff == 0xffff);
        prev_nbits = nbits;
    }

    // Retarget (rows 220..228): copies of the predecessor's nBits / time / pst, then the
    // GetNextWorkRequired witness at period boundaries.
    var v32s = try allocator.alloc(u32, headers.len);
    defer allocator.free(v32s);
    var mid_carries = try allocator.alloc(u32, headers.len);
    defer allocator.free(mid_carries);
    for (headers, 0..) |*header, i| {
        const base = i * PERIOD;
        const prev_nb = if (i == 0) start.prev_nbits_word else headerWordAt(&headers[i - 1], 18);
        const prev_time = if (i == 0) start.window[0] else headerWordAt(&headers[i - 1], 17);
        const prev_pst = if (i == 0) start.prev_pst_word else words.e[base - PERIOD + 218];
        words.a[base + 220] = prev_nb;
        words.e[base + 220] = prev_time;
        words.w[base + 220] = prev_pst;
        const height = start.height + @as(u32, @intCast(i));
        const rs = try retarget.scratch(height, prev_nb, prev_time, prev_pst, headerWordAt(header, 18));
        for (0..8) |k| {
            words.a[base + 221 + k] = rs.a[k];
            words.e[base + 221 + k] = rs.e[k];
            words.w[base + 221 + k] = rs.w[k];
        }
        v32s[i] = rs.v32;
        mid_carries[i] = rs.mid_carry;
    }

    // Median time past (rows 229..240): slot k holds T_(k+1), the difference d and own time.
    var bits = try allocator.alloc([11][2]u32, headers.len);
    defer allocator.free(bits);
    var win = start.window;
    for (headers, 0..) |*header, i| {
        const base = i * PERIOD;
        if (i > 0) {
            std.mem.copyBackwards(u32, win[1..], win[0..10]);
            win[0] = headerWordAt(&headers[i - 1], 17);
        }
        const t = headerWordAt(header, 17);
        const tn = retarget.le(t);
        var count: u32 = 0;
        for (win, 0..) |tw, k| {
            const tp = retarget.le(tw);
            const b = tp < tn;
            const d: u32 = if (b) tn - tp - 1 else tp - tn;
            const c: u32 = if (b) ((tp & 0xffff) + 1 + (d & 0xffff)) >> 16 else ((tn & 0xffff) + (d & 0xffff)) >> 16;
            words.a[base + 229 + k] = tw;
            words.e[base + 229 + k] = d;
            words.w[base + 229 + k] = t;
            bits[i][k] = .{ @intFromBool(b), c };
            count += @intFromBool(b);
        }
        if (count < 6) return error.TimeTooOld;
        words.a[base + 240] = count - 6;
    }

    // Chainwork (rows 241..253).
    var work = start.work;
    for (headers, 0..) |*header, i| {
        const base = i * PERIOD;
        const ws = try work_mod.scratch(headerWordAt(header, 18), work);
        for (0..13) |k| {
            words.a[base + 241 + k] = ws.a[k];
            words.e[base + 241 + k] = ws.e[k];
            words.w[base + 241 + k] = ws.w[k];
        }
        work = ws.work;
    }

    var pubs: [N_PUB]M31 = undefined;
    const first = spec.blockFromBytes(headers[0][0..64]);
    wordsPubs(pubs[0..16], first[1..9].*);
    wordsPubs(pubs[16..32], hashes[headers.len - 1]);
    const last = headers.len - 1;
    const limbs = [_]u32{
        start.height,         start.prev_nbits_word,                 start.prev_pst_word,
        start.height + @as(u32, @intCast(last)), headerWordAt(&headers[last], 18), words.e[last * PERIOD + 218],
        start.window[0], headerWordAt(&headers[last], 17),
    } ++ start.window[1..11].* ++ win[0..10].*;
    for (limbs, 0..) |v, k| {
        pubs[32 + 2 * k] = M31.fromCanonical(v & 0xffff);
        pubs[33 + 2 * k] = M31.fromCanonical(v >> 16);
    }
    for (0..10) |l| {
        pubs[88 + l] = M31.fromCanonical(@intCast((start.work >> @intCast(16 * l)) & 0xffff));
        pubs[98 + l] = M31.fromCanonical(@intCast((work >> @intCast(16 * l)) & 0xffff));
    }
    const main = try sha.columns(allocator, words, &role);
    for (height_carries, 0..) |c, i| main[sha.CA_LO][i * PERIOD + 218] = M31.fromCanonical(c);
    for (v32s, mid_carries, 0..) |v, c, i| {
        main[sha.CA_LO][i * PERIOD + 222] = M31.fromCanonical(v);
        main[sha.CE_LO][i * PERIOD + 222] = M31.fromCanonical(c);
    }
    for (bits, 0..) |slots, i| for (slots, 0..) |bc, k| {
        main[sha.CA_LO][i * PERIOD + 229 + k] = M31.fromCanonical(bc[0]);
        main[sha.CA_LO + 1][i * PERIOD + 229 + k] = M31.fromCanonical(bc[1]);
    };
    return .{ .main = main, .pubs = pubs, .hashes = hashes };
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

test "header chain AIR: proof-of-work is enforced" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const pre = try air.genPreprocessed(a, 12);
    const headers = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));

    // A header claiming a harder target (nBits 0x1800ffff) than its hash meets cannot be
    // laid out at all.
    {
        const bad = try a.dupe(Header, headers);
        std.mem.writeInt(u32, bad[9][72..76], 0x1800ffff, .little);
        try std.testing.expectError(error.InsufficientWork, generate(a, 12, bad));
    }
    // Tampering with the scratch witness of a valid chain is caught: flipping `lt`, moving
    // the one-hot exponent, or changing a bit of D.
    for ([_][2]usize{ .{ sha.W + 0, 3 * PERIOD + 216 }, .{ sha.A + 25, 5 * PERIOD + 216 }, .{ sha.E + 3, 8 * PERIOD + 216 } }) |cell| {
        const wit = try generate(a, 12, headers);
        wit.main[cell[0]][cell[1]] = M31.one().sub(wit.main[cell[0]][cell[1]]);
        const t = interp.RowTrace{ .log_size = 12, .pubs = &wit.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        try std.testing.expect(try interp.firstViolation(a, air, t) != null);
    }
}

test "header chain AIR: a broken link, a wrong padding word, or a wrong public input is caught" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const pre = try air.genPreprocessed(a, 12);
    const headers = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));

    // 1. Header 7 claims a different previous block. Its hash then no longer meets the
    //    target either, so the witness is built from the honest header and only the trace's
    //    prev-hash word is altered.
    {
        const wit = try generate(a, 12, headers);
        wit.main[sha.W + 9][7 * PERIOD + 6] = M31.one().sub(wit.main[sha.W + 9][7 * PERIOD + 6]);
        const t = interp.RowTrace{ .log_size = 12, .pubs = &wit.pubs, .preprocessed = @ptrCast(pre), .main = @ptrCast(wit.main) };
        try std.testing.expect(try interp.firstViolation(a, air, t) != null);
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

/// Window from 11 consecutive headers (oldest first in the file).
fn windowOf(a: std.mem.Allocator, hex: []const u8) ![11]u32 {
    const hs = try loadHeaders(a, hex);
    if (hs.len != 11) return error.HeaderCountMismatch;
    var w: [11]u32 = undefined;
    for (0..11) |k| w[k] = headerWordAt(&hs[10 - k], 17);
    return w;
}

fn checkSatisfied(a: std.mem.Allocator, air: ir.Air, log_size: u32, wit: Witness) !?usize {
    const t = interp.RowTrace{
        .log_size = log_size,
        .pubs = &wit.pubs,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)),
        .main = @ptrCast(wit.main),
    };
    return if (try interp.firstViolation(a, air, t)) |v| v.row else null;
}

test "chain state: a segment from height 1 and one across the first period boundary (2016)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const early = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const genesis = &early[0];

    // Heights 1..16: the predecessor is genesis (a boundary, so pst = genesis time).
    const start1 = ChainStart{ .work = 0x100010001, .height = 1, .prev_nbits_word = headerWordAt(genesis, 18), .prev_pst_word = headerWordAt(genesis, 17), .window = windowFrom(&.{headerWordAt(genesis, 17)}) };
    const w1 = try generateFrom(a, 12, early[1..17], start1);
    try std.testing.expectEqual(null, try checkSatisfied(a, air, 12, w1));

    // Heights 1984..2047 cross the boundary at 2016 (pst resets to block 2016's time).
    const around = try loadHeaders(a, @embedFile("testdata:mainnet_headers_1984_2048"));
    const start2 = ChainStart{ .work = 1984 * 0x100010001, .height = 1984, .prev_nbits_word = headerWordAt(&early[1023], 18), .prev_pst_word = headerWordAt(genesis, 17), .window = try windowOf(a, @embedFile("testdata:mainnet_headers_1973_1984")) };
    const w2 = try generateFrom(a, 14, around, start2);
    try std.testing.expectEqual(null, try checkSatisfied(a, air, 14, w2));
    // pst of the last header (height 2047) is block 2016's time.
    try std.testing.expectEqual(headerWordAt(&around[2016 - 1984], 17), (w2.pubs[42].toU32()) | (w2.pubs[43].toU32() << 16));

    // A wrong first height, a flipped boundary flag, or a mid-period difficulty change fail.
    {
        var bad = w1;
        bad.pubs[32] = bad.pubs[32].add(M31.one());
        try std.testing.expect(try checkSatisfied(a, air, 12, bad) != null);
    }
    {
        const w = try generateFrom(a, 14, around, start2);
        const r = (2016 - 1984) * PERIOD + 218;
        w.main[sha.W][r] = M31.one().sub(w.main[sha.W][r]);
        try std.testing.expect(try checkSatisfied(a, air, 14, w) != null);
    }
    {
        var start_bad = start1;
        start_bad.prev_nbits_word = 0x1c00ffff;
        try std.testing.expectError(error.DifficultyChangedMidPeriod, generateFrom(a, 12, early[1..17], start_bad));
    }
}

test "retarget: the first real difficulty change (height 32256) is enforced" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const hs = try loadHeaders(a, @embedFile("testdata:mainnet_headers_32192_32320"));
    const p30240 = (try loadHeaders(a, @embedFile("testdata:mainnet_header_30240")))[0];
    // Heights 32192..32319; the period started at 30240 with nBits 0x1d00ffff.
    const start = ChainStart{ .work = 32192 * 0x100010001, .height = 32192, .prev_nbits_word = headerWordAt(&hs[0], 18), .prev_pst_word = headerWordAt(&p30240, 17), .window = try windowOf(a, @embedFile("testdata:mainnet_headers_32181_32192")) };
    const wit = try generateFrom(a, 15, hs, start);
    try std.testing.expectEqual(null, try checkSatisfied(a, air, 15, wit));
    try std.testing.expectEqual(@as(u32, 0x1d00d86a), retarget.le(headerWordAt(&hs[64], 18)));

    // Tampering with the boundary header's retarget witness is caught: the remainder, the
    // exponent-difference flag, or the clamp-branch flag.
    const r = 64 * PERIOD;
    for ([_][2]usize{ .{ sha.A + 3, r + 225 }, .{ sha.W + 6, r + 221 }, .{ sha.W + 3, r + 221 } }) |cell| {
        const w = try generateFrom(a, 15, hs, start);
        w.main[cell[0]][cell[1]] = M31.one().sub(w.main[cell[0]][cell[1]]);
        try std.testing.expect(try checkSatisfied(a, air, 15, w) != null);
    }
    // Claiming a mid-period difficulty for the first header's predecessor is refused.
    var bad_start = start;
    bad_start.prev_pst_word = headerWordAt(&hs[0], 17);
    try std.testing.expectError(error.RetargetMismatch, generateFrom(a, 15, hs, bad_start));
}

test "median time past: enforced, tamper-evident, and chained through public inputs" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    const around = try loadHeaders(a, @embedFile("testdata:mainnet_headers_1984_2048"));
    const early = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const start = ChainStart{ .work = 1984 * 0x100010001, .height = 1984, .prev_nbits_word = headerWordAt(&early[1023], 18), .prev_pst_word = headerWordAt(&early[0], 17), .window = try windowOf(a, @embedFile("testdata:mainnet_headers_1973_1984")) };
    const wit = try generateFrom(a, 14, around, start);

    // Outputs: the last header's window T_1..T_10 = times of heights 2046 down to 2037.
    for (0..10) |k| {
        const v = wit.pubs[68 + 2 * k].toU32() | (wit.pubs[69 + 2 * k].toU32() << 16);
        try std.testing.expectEqual(headerWordAt(&around[around.len - 2 - k], 17), v);
    }
    // A predecessor window entirely in the future of the first header is refused.
    var future = start;
    future.window = [_]u32{TMAX} ** 11;
    try std.testing.expectError(error.TimeTooOld, generateFrom(a, 14, around, future));
    // Tampering is caught: a comparison bit, a difference bit, a window word, the count slack.
    const r = 5 * PERIOD;
    for ([_][2]usize{ .{ sha.CA_LO, r + 233 }, .{ sha.E + 7, r + 231 }, .{ sha.A + 12, r + 236 }, .{ sha.A + 1, r + 240 } }) |cell| {
        const w = try generateFrom(a, 14, around, start);
        w.main[cell[0]][cell[1]] = M31.one().sub(w.main[cell[0]][cell[1]]);
        try std.testing.expect(try checkSatisfied(a, air, 14, w) != null);
    }
    // A wrong pre-segment window public input is caught.
    {
        var bad = wit;
        bad.pubs[50] = bad.pubs[50].add(M31.one());
        try std.testing.expect(try checkSatisfied(a, air, 14, bad) != null);
    }
}

/// Bitcoin Core `GetMedianTimePast` rule, as a plain reference: sort the (≤ 11) numeric
/// predecessor times and require `t` above the element at index `k / 2`.
fn mtpOkRef(t: u32, prev: []const u32) bool {
    if (prev.len == 0) return true;
    var buf: [11]u32 = undefined;
    const k = @min(prev.len, 11);
    @memcpy(buf[0..k], prev[0..k]);
    std.mem.sort(u32, buf[0..k], {}, std.sort.asc(u32));
    return t > buf[k / 2];
}

test "median time past: the counting rule with the sentinel window matches Core's median" {
    var prng = std.Random.DefaultPrng.init(2024);
    const rnd = prng.random();
    for (0..100_000) |_| {
        const h = rnd.uintLessThan(usize, 14);
        var prev: [11]u32 = undefined;
        const k = @min(h, 11);
        for (0..k) |i| prev[i] = if (rnd.boolean()) rnd.uintLessThan(u32, 40) else rnd.int(u32);
        const t: u32 = switch (rnd.uintLessThan(u8, 4)) {
            0 => rnd.uintLessThan(u32, 40),
            1 => TMAX,
            else => rnd.int(u32),
        };
        // Raw words = byte-swapped numeric values (the window holds raw header words).
        var raw: [11]u32 = undefined;
        for (0..k) |i| raw[i] = @byteSwap(prev[i]);
        const win = windowFrom(raw[0..k]);
        var count: usize = 0;
        for (win) |w| count += @intFromBool(retarget.le(w) < t);
        const ours = count >= 6;
        const core = mtpOkRef(t, prev[0..k]);
        if (ours) try std.testing.expect(core); // soundness
        if (core and t > 0) try std.testing.expect(ours); // completeness (t = 0 never occurs)
    }
}

fn pubWork(pubs: []const M31, first: usize) u256 {
    var w: u256 = 0;
    for (0..10) |l| w |= @as(u256, pubs[first + l].toU32()) << @intCast(16 * l);
    return w;
}

test "chainwork: exact Core values, chained through public inputs, tamper-evident" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, lean_json)).value;
    // Genesis segment: chainwork after height 15 = 16 · 0x100010001 (Core's value).
    const g = try loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const w0 = try generate(a, 12, g);
    try std.testing.expectEqual(@as(u256, 0), pubWork(&w0.pubs, 88));
    try std.testing.expectEqual(@as(u256, 0x1000100010), pubWork(&w0.pubs, 98));
    // Across the first difficulty change: chainwork after 32319 (reference computed in Python).
    const hs = try loadHeaders(a, @embedFile("testdata:mainnet_headers_32192_32320"));
    const p30240 = (try loadHeaders(a, @embedFile("testdata:mainnet_header_30240")))[0];
    const start = ChainStart{ .work = 32192 * 0x100010001, .height = 32192, .prev_nbits_word = headerWordAt(&hs[0], 18), .prev_pst_word = headerWordAt(&p30240, 17), .window = try windowOf(a, @embedFile("testdata:mainnet_headers_32181_32192")) };
    const wit = try generateFrom(a, 15, hs, start);
    try std.testing.expectEqual(@as(u256, 0x7e4c32ec7280), pubWork(&wit.pubs, 98));
    try std.testing.expectEqual(null, try checkSatisfied(a, air, 15, wit));
    // Tampering is caught: a q bit, an R bit, a remainder bit, a chainwork bit, a carry, the input work.
    const r = 70 * PERIOD; // a header after the difficulty change
    for ([_][2]usize{ .{ sha.A + 3, r + 241 }, .{ sha.E + 9, r + 242 }, .{ sha.W + 1, r + 244 }, .{ sha.E + 0, r + 248 }, .{ sha.A + 0, r + 252 } }) |cell| {
        const w = try generateFrom(a, 15, hs, start);
        w.main[cell[0]][cell[1]] = M31.one().sub(w.main[cell[0]][cell[1]]);
        try std.testing.expect(try checkSatisfied(a, air, 15, w) != null);
    }
    {
        var bad = wit;
        bad.pubs[90] = bad.pubs[90].add(M31.one());
        try std.testing.expect(try checkSatisfied(a, air, 15, bad) != null);
    }
}
