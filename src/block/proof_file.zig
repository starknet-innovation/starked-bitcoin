//! Block proof files (BLOCK-DATA): one block's STARK and its public inputs, and the checks a verifier
//! makes against the header chain (docs/design/block-data.md § BLOCK-DATA).
//!
//! `.sbblock` layout (little-endian): magic `SBBLOCK\0`, version u32, log size u32, the 41 public inputs
//! (u32 each, canonical M31), the claimed LogUp sums (count u32, then 4 u32 per QM31), the STARK proof
//! (length u32, then stwo's postcard encoding), the provenance (length u32, bytes).
//!
//! The FRI configuration is pinned by the verifier, never taken from the file.

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
pub const VERSION: u32 = 1;

/// Production strength, as the chain proof's: 70 queries at blowup 2, 26 bits of proof of work.
pub fn productionFri() FriConfigV2 {
    return FriConfigV2.init(26, 0, 1, 70, 1) catch unreachable;
}

/// Test strength (3 queries, 10 bits): fast, not secure.
pub fn testFri() FriConfigV2 {
    return FriConfigV2.init(10, 0, 1, 3, 1) catch unreachable;
}

pub const File = struct {
    log_size: u32,
    pubs: [bs.N_PUB]M31,
    proof: system.Proof,
    provenance: []const u8,
};

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
    if (fbs.pos != bytes.len) return error.TrailingBytes;
    f.proof = .{ .stark = stark, .claimed_sums = sums };
    return f;
}

/// Median time past of the 11 headers below `height` (Core's `GetMedianTimePast` of the previous
/// block); `headers[i]` is the 80-byte header at height `i`.
pub fn prevMtp(headers: []const [80]u8, height: usize) u32 {
    if (height == 0) return 0;
    const lo = if (height >= 11) height - 11 else 0;
    var t: [11]u32 = undefined;
    const n = height - lo;
    for (0..n) |i| t[i] = std.mem.readInt(u32, headers[lo + i][68..72], .little);
    std.mem.sort(u32, t[0..n], {}, std.sort.asc(u32));
    return t[n / 2];
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

/// Checks the public inputs against the header at their height: the block hash (25–40), the height's
/// context (MTP limbs and soft-fork flags, inputs 3–7). `headers` must already be bound to a verified
/// chain (its hashes fold to the chain proof's MMR root).
pub fn checkPubs(pubs: *const [bs.N_PUB]M31, headers: []const [80]u8) !Statement {
    const height = pubs[2].toU32();
    if (height >= headers.len) return error.HeightBeyondChain;
    const want_hash = bs.hashLimbs(&headers[height]);
    for (0..16) |j| if (!pubs[bs.PUB_HASH + j].eql(want_hash[j])) return error.BlockHashMismatch;
    const ctx = checks.Ctx{ .height = height, .prev_mtp = prevMtp(headers, height) };
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
    const b = try bs.build(a, s.raw, s.ctx);
    const proof = try prove(a, &airs, &b, testFri());
    const bytes = try encode(a, &.{ .log_size = b.log_size, .pubs = b.pubs, .proof = proof, .provenance = "test" });
    const f = try decode(a, bytes);
    try verifyStark(a, &airs, &f, testFri());
    try std.testing.expectError(error.ConfigMismatch, verifyStark(a, &airs, &f, productionFri()));
    // A tampered public input fails the STARK.
    var g = try decode(a, bytes);
    g.pubs[bs.PUB_HASH] = g.pubs[bs.PUB_HASH].add(M31.one());
    try std.testing.expect(std.meta.isError(verifyStark(a, &airs, &g, testFri())));
    // The header checks: block 170's header and a context from the 11 headers below it are not in the
    // repo, so check the hash binding with a one-header "chain" placed at height 170.
    var hs = try a.alloc([80]u8, 171);
    @memset(hs, [_]u8{0} ** 80);
    hs[170] = s.raw[0..80].*;
    try std.testing.expectError(error.ContextMismatch, checkPubs(&f.pubs, hs));
    var hs2 = try a.dupe([80]u8, hs);
    hs2[170][0] ^= 1;
    try std.testing.expectError(error.BlockHashMismatch, checkPubs(&f.pubs, hs2));
    // The commitment bytes are D-038's.
    const st = checkPubs(&f.pubs, hs) catch |e| switch (e) {
        error.ContextMismatch => null,
        else => return e,
    };
    try std.testing.expect(st == null);
    var c: [32]u8 = undefined;
    for (0..8) |w| std.mem.writeInt(u32, c[4 * w ..][0..4], b.commitment_words[w], .little);
    var want: [32]u8 = undefined;
    std.crypto.hash.blake2.Blake2s256.hash(&[_]u8{1}, &want, .{});
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

test "block 170 with its undo stream from the node: the commitment is blake2s(undo)" {
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
    // Computed independently (Python hashlib.blake2s).
    var want: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&want, "000f60585ef4c4ec168547418dd7282ea2e2b3896937443cbc6f1cfef87e7a03");
    try std.testing.expectEqualSlices(u8, &want, &c);
    try std.testing.expectEqual(@as(u32, 81), b.pubs[8].toU32());
}
