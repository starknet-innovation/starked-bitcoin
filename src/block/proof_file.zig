//! Block proof files (BLOCK-DATA): one block's STARK and its public inputs, and the checks a verifier
//! makes against the header chain (docs/design/block-data.md § BLOCK-DATA).
//!
//! `.sbblock` layout (little-endian): magic `SBBLOCK\0`, version u32, log size u32, the 41 public inputs
//! (u32 each, canonical M31), the claimed LogUp sums (count u32, then 4 u32 per QM31), the STARK proof
//! (length u32, then stwo's postcard encoding), the provenance (length u32, bytes), then the header
//! window (D-039, self-contained files): the chain length `n` the paths are for (u32), the count (u32),
//! and per header its height (u32), its 80 bytes, and its MMR inclusion path (steps u32; per step 8 u32
//! sibling words and a side byte). The window is the block's header and up to 11 before it.
//!
//! The FRI configuration is pinned by the verifier, never taken from the file. The header window can be
//! rebuilt for a longer chain without re-proving.

const std = @import("std");
const core = @import("stwo_core");
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const postcard = @import("stwo_postcard");
const ir = @import("../air/ir.zig");
const system = @import("../air/system.zig");
const rec = @import("../air/prove_rec.zig");
const bs = @import("system.zig");
const checks = @import("checks.zig");

pub const MAGIC = "SBBLOCK\x00";
pub const VERSION: u32 = 2;

/// Production strength, as the chain proof's: 70 queries at blowup 2, 26 bits of proof of work.
pub fn productionFri() FriConfigV2 {
    return FriConfigV2.init(26, 0, 1, 70, 1) catch unreachable;
}

/// Test strength (3 queries, 10 bits): fast, not secure.
pub fn testFri() FriConfigV2 {
    return FriConfigV2.init(10, 0, 1, 3, 1) catch unreachable;
}

const HT = @import("../btc/header_tree.zig");

/// A header with its inclusion path in the chain's MMR.
pub const Bound = struct { height: u32, header: [80]u8, steps: []const HT.Step };

pub const File = struct {
    log_size: u32,
    pubs: [bs.N_PUB]M31,
    proof: system.Proof,
    provenance: []const u8,
    /// The chain length the paths are for.
    chain_len: u32 = 0,
    /// The block's header and up to 11 before it, oldest first.
    window: []const Bound = &.{},
};

/// The header window for height `h` against the MMR over `hashes` (the chain's block hashes).
pub fn bindWindow(a: std.mem.Allocator, headers: []const [80]u8, hashes: []const HT.Words, h: u32) ![]Bound {
    if (h >= hashes.len or headers.len < hashes.len) return error.HeightBeyondChain;
    const lo: u32 = if (h >= 11) h - 11 else 0;
    const out = try a.alloc(Bound, h - lo + 1);
    for (out, lo..) |*b, i| b.* = .{ .height = @intCast(i), .header = headers[i], .steps = try HT.inclusionProof(a, hashes, i) };
    return out;
}

/// Checks the window against a verified chain (length `n`, MMR root `t`): consecutive heights ending
/// at the block's, starting at `max(0, h − 11)`, each header's hash included at its height.
pub fn checkWindow(a: std.mem.Allocator, f: *const File, n: usize, t: HT.Words) ![]const [80]u8 {
    if (f.chain_len != n) return error.WindowForOtherChainLength;
    const h = f.pubs[2].toU32();
    if (h >= n) return error.HeightBeyondChain;
    const lo: u32 = if (h >= 11) h - 11 else 0;
    if (f.window.len != h - lo + 1) return error.BadWindow;
    const hs = try a.alloc([80]u8, f.window.len);
    for (f.window, 0..) |b, i| {
        if (b.height != lo + i) return error.BadWindow;
        if (!try HT.verifyAt(a, HT.blockHash(&b.header), b.steps, b.height, n, t)) return error.HeaderNotInChain;
        hs[i] = b.header;
    }
    return hs;
}

pub fn partsOf(airs: *const [bs.N_COMP]ir.Air, log_size: u32, pubs: *const [bs.N_PUB]M31) [bs.N_COMP]system.Part {
    var out: [bs.N_COMP]system.Part = undefined;
    for (&out, 0..) |*p, i| p.* = .{ .air = &airs[i], .log_size = log_size, .pubs = pubs[0..bs.n_pubs[i]] };
    return out;
}

pub fn prove(a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, b: *const bs.Built, fri: FriConfigV2) !system.Proof {
    const ps = bs.parts(airs, b);
    const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    return system.prove(E, a, cfg, &ps, &mains);
}

/// Verifies the STARK under the pinned `fri`: the proof's own configuration must match it.
pub fn verifyStark(a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, f: *const File, fri: FriConfigV2) !void {
    if (f.log_size < 8 or f.log_size > 24) return error.LogSizeOutOfRange;
    const c = f.proof.stark.commitment_scheme_proof.config;
    if (c.pow_bits != fri.pow_bits or c.fri_config.log_blowup_factor != fri.log_blowup_factor or
        c.fri_config.n_queries != fri.n_queries or c.fri_config.log_last_layer_degree_bound != fri.log_last_layer_degree_bound)
        return error.ConfigMismatch;
    const ps = partsOf(airs, f.log_size, &f.pubs);
    try system.verifyExt(a, rec.Config.fromFriAndTraceSize(fri, f.log_size), &ps, &.{}, f.proof);
}

pub fn encode(a: std.mem.Allocator, f: *const File) ![]u8 {
    var out = std.ArrayList(u8).empty;
    const w = out.writer(a);
    try w.writeAll(MAGIC);
    try w.writeInt(u32, VERSION, .little);
    try w.writeInt(u32, f.log_size, .little);
    for (f.pubs) |p| try w.writeInt(u32, p.toU32(), .little);
    try w.writeInt(u32, @intCast(f.proof.claimed_sums.len), .little);
    for (f.proof.claimed_sums) |s| for (s.toM31Array()) |x| try w.writeInt(u32, x.toU32(), .little);
    var pb = std.ArrayList(u8).empty;
    try postcard.serializeProof(rec.Hasher, pb.writer(a), f.proof.stark);
    try w.writeInt(u32, @intCast(pb.items.len), .little);
    try w.writeAll(pb.items);
    try w.writeInt(u32, @intCast(f.provenance.len), .little);
    try w.writeAll(f.provenance);
    try w.writeInt(u32, f.chain_len, .little);
    try w.writeInt(u32, @intCast(f.window.len), .little);
    for (f.window) |b| {
        try w.writeInt(u32, b.height, .little);
        try w.writeAll(&b.header);
        try w.writeInt(u32, @intCast(b.steps.len), .little);
        for (b.steps) |st| {
            for (st.sibling) |x| try w.writeInt(u32, x, .little);
            try w.writeByte(@intFromBool(st.left));
        }
    }
    return out.toOwnedSlice(a);
}

fn m31(x: u32) !M31 {
    if (x >= 0x7fffffff) return error.NonCanonical;
    return M31.fromCanonical(x);
}

pub fn decode(a: std.mem.Allocator, bytes: []const u8) !File {
    var fbs = std.io.fixedBufferStream(bytes);
    const r = fbs.reader();
    var magic: [8]u8 = undefined;
    try r.readNoEof(&magic);
    if (!std.mem.eql(u8, &magic, MAGIC)) return error.BadMagic;
    if (try r.readInt(u32, .little) != VERSION) return error.BadVersion;
    var f: File = undefined;
    f.log_size = try r.readInt(u32, .little);
    for (&f.pubs) |*p| p.* = try m31(try r.readInt(u32, .little));
    const n_sums = try r.readInt(u32, .little);
    if (n_sums > bs.N_COMP) return error.TooManySums;
    const sums = try a.alloc(QM31, n_sums);
    for (sums) |*s| {
        var v: [4]M31 = undefined;
        for (&v) |*x| x.* = try m31(try r.readInt(u32, .little));
        s.* = QM31.fromM31Array(v);
    }
    const plen = try r.readInt(u32, .little);
    const start = fbs.pos;
    if (plen > bytes.len - start) return error.Truncated;
    var pfbs = std.io.fixedBufferStream(bytes[start .. start + plen]);
    const stark = try postcard.deserializeProof(rec.Hasher, a, pfbs.reader());
    if (pfbs.pos != plen) return error.TrailingProofBytes;
    fbs.pos = start + plen;
    const vlen = try r.readInt(u32, .little);
    if (vlen > bytes.len - fbs.pos) return error.Truncated;
    f.provenance = bytes[fbs.pos .. fbs.pos + vlen];
    fbs.pos += vlen;
    f.chain_len = try r.readInt(u32, .little);
    const nw = try r.readInt(u32, .little);
    if (nw > 12) return error.BadWindow;
    const win = try a.alloc(Bound, nw);
    for (win) |*b| {
        b.height = try r.readInt(u32, .little);
        try r.readNoEof(&b.header);
        const ns = try r.readInt(u32, .little);
        if (ns > 64) return error.BadWindow;
        const steps = try a.alloc(HT.Step, ns);
        for (steps) |*st| {
            for (&st.sibling) |*x| x.* = try r.readInt(u32, .little);
            const side = try r.readByte();
            if (side > 1) return error.BadWindow;
            st.left = side == 1;
        }
        b.steps = steps;
    }
    f.window = win;
    if (fbs.pos != bytes.len) return error.TrailingBytes;
    f.proof = .{ .stark = stark, .claimed_sums = sums };
    return f;
}

/// Median time past of the 11 headers below `height` (Core's `GetMedianTimePast` of the previous
/// block); `headers[i]` is the 80-byte header at height `i`.
/// The 11 predecessors' headers (oldest first), when the block is at or above the CSV height (D-043
/// part 3: the block proof derives the previous MTP from them).
pub fn ancestors(headers: []const [80]u8, height: usize) ?*const [11][80]u8 {
    if (height < checks.CSV_HEIGHT) return null;
    return headers[height - 11 ..][0..11];
}

pub fn prevMtp(headers: []const [80]u8, height: usize) u32 {
    const lo = if (height >= 11) height - 11 else 0;
    return mtpOf(headers[lo..height]);
}

/// The median of up to 11 headers' times (0 for none).
pub fn mtpOf(prev: []const [80]u8) u32 {
    if (prev.len == 0) return 0;
    var t: [11]u32 = undefined;
    for (prev, 0..) |h, i| t[i] = std.mem.readInt(u32, h[68..72], .little);
    std.mem.sort(u32, t[0..prev.len], {}, std.sort.asc(u32));
    return t[prev.len / 2];
}

/// What a verified block proof states once its public inputs match the headers.
pub const Statement = struct {
    height: u32,
    block_len: u32,
    ntx: u32,
    undo_len: u32,
    /// `blake2s(undo)` (D-038 as amended), in byte order.
    commitment: [32]u8,
};

/// Checks the public inputs against a window of headers bound to a verified chain (`checkWindow`): the
/// block's header (the window's last) gives the block hash (inputs 25–40), the ones before it the
/// previous median time past; with the height, the context inputs 2–7.
pub fn checkPubs(pubs: *const [bs.N_PUB]M31, window: []const [80]u8) !Statement {
    const height = pubs[2].toU32();
    if (window.len == 0 or window.len != @min(height, 11) + 1) return error.BadWindow;
    const want_hash = bs.hashLimbs(&window[window.len - 1]);
    for (0..16) |j| if (!pubs[bs.PUB_HASH + j].eql(want_hash[j])) return error.BlockHashMismatch;
    const ctx = checks.Ctx{ .height = height, .prev_mtp = mtpOf(window[0 .. window.len - 1]) };
    const want = checks.pubs(&.{}, 0, ctx);
    for (2..8) |i| if (!pubs[i].eql(want[i])) return error.ContextMismatch;
    var c: [32]u8 = undefined;
    for (0..8) |w| {
        const word = pubs[9 + 2 * w].toU32() | (pubs[10 + 2 * w].toU32() << 16);
        std.mem.writeInt(u32, c[4 * w ..][0..4], word, .little);
    }
    return .{ .height = height, .block_len = pubs[0].toU32(), .ntx = pubs[1].toU32(), .undo_len = pubs[8].toU32(), .commitment = c };
}

test "block proof file: round trip, verify, and the header checks (block 170, test strength)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const s = checks.samples_small[1];
    try std.testing.expectEqual(@as(u32, 170), s.ctx.height);
    const b = try bs.buildU(a, s.raw, s.undo, s.ctx);
    const proof = try prove(a, &airs, &b, testFri());
    const bytes = try encode(a, &.{ .log_size = b.log_size, .pubs = b.pubs, .proof = proof, .provenance = "test" });
    const f = try decode(a, bytes);
    try verifyStark(a, &airs, &f, testFri());
    try std.testing.expectError(error.ConfigMismatch, verifyStark(a, &airs, &f, productionFri()));
    // A tampered public input fails the STARK.
    var g = try decode(a, bytes);
    g.pubs[bs.PUB_HASH] = g.pubs[bs.PUB_HASH].add(M31.one());
    try std.testing.expect(std.meta.isError(verifyStark(a, &airs, &g, testFri())));
    // The header checks, with block 170's 11 predecessors (testdata) and its header.
    var hs = try a.alloc([80]u8, 12);
    @memcpy(hs[0..11], checks.ancOf("170"));
    hs[11] = s.raw[0..80].*;
    const st = try checkPubs(&f.pubs, hs);
    try std.testing.expectEqual(@as(u32, 170), st.height);
    var hs2 = try a.dupe([80]u8, hs);
    hs2[11][0] ^= 1;
    try std.testing.expectError(error.BlockHashMismatch, checkPubs(&f.pubs, hs2));
    try std.testing.expectError(error.BadWindow, checkPubs(&f.pubs, hs[1..]));
    // A tampered activation bit, and (below the CSV height) a nonzero MTP limb, mismatch the context.
    var p4 = f.pubs;
    p4[4] = M31.one().sub(p4[4]);
    try std.testing.expectError(error.ContextMismatch, checkPubs(&p4, hs));
    var p3 = f.pubs;
    p3[3] = p3[3].add(M31.one());
    try std.testing.expectError(error.ContextMismatch, checkPubs(&p3, hs));
    var c: [32]u8 = undefined;
    for (0..8) |w| std.mem.writeInt(u32, c[4 * w ..][0..4], b.commitment_words[w], .little);
    var want: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(try bs.undoStreamOf(a, s.raw, s.undo, null, s.ctx.height), &want, .{});
    try std.testing.expectEqualSlices(u8, &want, &c);
}

test "prevMtp: median of the previous 11 header times" {
    var hs: [13][80]u8 = undefined;
    for (&hs, 0..) |*h, i| {
        @memset(h, 0);
        // Times out of order: 100, 50, 102, 52, ...
        std.mem.writeInt(u32, h[68..72], @intCast(if (i % 2 == 0) 100 + i else 50 + i), .little);
    }
    try std.testing.expectEqual(@as(u32, 0), prevMtp(&hs, 0));
    try std.testing.expectEqual(@as(u32, 100), prevMtp(&hs, 1));
    // heights 1..11 below 12: times 51,102,53,104,55,106,57,108,59,110,61 -> sorted median 61
    try std.testing.expectEqual(@as(u32, 61), prevMtp(&hs, 12));
}

test "block 170 with its undo stream from the node: the commitment is blake2s of the in-circuit stream" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const s = checks.samples_small[1];
    const undo = @embedFile("testdata:undo_170");
    const b = try bs.buildU(a, s.raw, undo, s.ctx);
    try std.testing.expect(try bs.firstViolation(a, &airs, &b) == null);
    try std.testing.expect(try bs.unbalanced(a, &airs, &b) == null);
    var c: [32]u8 = undefined;
    for (0..8) |w| std.mem.writeInt(u32, c[4 * w ..][0..4], b.commitment_words[w], .little);
    // Computed independently (Python hashlib.blake2s over the fetched stream with the record's 3-byte
    // creating-transaction index, 0, and its 2-byte serTxOut length, 76, after its code).
    var want: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&want, "d36ebac0076bd797bb6a9cb46a43319f48603a5c065c34e12c6df84a5c152480");
    try std.testing.expectEqualSlices(u8, &want, &c);
    try std.testing.expectEqual(@as(u32, 86), b.pubs[8].toU32());
}

test "block proof file: a self-contained window binds block 170 to a 1024-header MMR (test strength)" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const H = @import("../btc/header_chain.zig");
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const hashes = try a.alloc(HT.Words, headers.len);
    for (hashes, headers) |*h, *hd| h.* = HT.blockHash(hd);
    const t = try HT.mmrRoot(a, hashes);
    const airs = try bs.parseAirs(a);
    const s = checks.samples_small[1];
    try std.testing.expectEqual(s.ctx.prev_mtp, prevMtp(headers, 170));
    const b = try bs.buildU(a, s.raw, @embedFile("testdata:undo_170"), s.ctx);
    const proof = try prove(a, &airs, &b, testFri());
    const win = try bindWindow(a, headers, hashes, 170);
    const bytes = try encode(a, &.{ .log_size = b.log_size, .pubs = b.pubs, .proof = proof, .provenance = "test", .chain_len = @intCast(headers.len), .window = win });
    const f = try decode(a, bytes);
    try verifyStark(a, &airs, &f, testFri());
    const hs = try checkWindow(a, &f, headers.len, t);
    const st = try checkPubs(&f.pubs, hs);
    try std.testing.expectEqual(@as(u32, 170), st.height);
    try std.testing.expectEqual(@as(u32, 2), st.ntx);
    // Rejected: another chain length, a wrong root, a tampered window header.
    try std.testing.expectError(error.WindowForOtherChainLength, checkWindow(a, &f, headers.len - 1, t));
    var t2 = t;
    t2[0] ^= 1;
    try std.testing.expectError(error.HeaderNotInChain, checkWindow(a, &f, headers.len, t2));
    var g = try decode(a, bytes);
    const w2 = try a.dupe(Bound, g.window);
    w2[3].header[70] ^= 1;
    g.window = w2;
    try std.testing.expectError(error.HeaderNotInChain, checkWindow(a, &g, headers.len, t));
}
