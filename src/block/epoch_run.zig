//! An epoch's block proofs from local files (M3b, D-040): what `chainproof prove-epoch` (CPU) and
//! `cuda-epoch` (the resident CUDA prover, src/gpu/cuda/epoch.zig) share. Both read
//! `<dir>/blocks/<h>.bin`, `<dir>/undo/<h>.undo` and `.ctx` (scripts/fetch_undo.py --ctx) for the
//! heights `from..to`, derive the epoch's challenge from the blocks' hashes and commitments and the
//! final coin set, build each block's witness under it, and write `<dir>/proofs/<h>.sbblock` and the
//! coin set `<dir>/set-<to>.bin`. The proof files are the same bytes whichever prover made them
//! (the CUDA proof is byte-identical to the CPU's).

const std = @import("std");
const bs = @import("system.zig");
const checks = @import("checks.zig");
const coin = @import("coin.zig");
const EP = @import("epoch.zig");
const PF = @import("proof_file.zig");
const S = @import("../recursion/store.zig");
const HT = @import("../btc/header_tree.zig");
const system = @import("../air/system.zig");

/// The provenance both provers write (so their files are byte-identical).
pub const provenance = "prove-epoch";

/// An epoch's start: genesis, or block `height` from the coin set after `height − 1` (`prev_set`).
pub const From = struct {
    height: u32 = 0,
    prev_set: ?[]const u8 = null,
};

pub const Init = struct { set: []const EP.Coin, hash: ?[32]u8, digest: ?[32]u8 };

/// The initial set of an epoch from a previous set: decoded, strictly sorted, created before `from`.
pub fn loadInit(a: std.mem.Allocator, from: From) !Init {
    const path = from.prev_set orelse {
        if (from.height != 0) return error.PrevSetRequired;
        return .{ .set = &.{}, .hash = null, .digest = null };
    };
    if (from.height == 0) return error.GenesisHasNoPrevSet;
    const set = try EP.decodeSet(a, try S.readFile(a, path));
    if (!EP.sortedStrict(set)) return error.SetNotSorted;
    if (!EP.createdBefore(set, from.height)) return error.PrevSetTooNew;
    return .{ .set = set, .hash = EP.hashSerialized(set), .digest = try EP.setDigest(a, set) };
}

pub fn pathOf(a: std.mem.Allocator, dir: []const u8, sub: []const u8, h: u32, ext: []const u8) ![]u8 {
    return std.fmt.allocPrint(a, "{s}/{s}/{d}.{s}", .{ dir, sub, h, ext });
}

/// The epoch's blocks, the final coin set and the challenge.
pub const Epoch = struct {
    dir: []const u8,
    from: u32,
    to: u32,
    /// The chain proof's header count, and the headers 0..n−1 (and their hashes: the MMR leaves).
    n: u32,
    all: []const [80]u8,
    /// The MMR over the headers' hashes, folded once (every block's window paths).
    paths: HT.Paths,
    raws: []const []const u8,
    undos: []const []const u8,
    ctxs: []const []const u32,
    set: []const EP.Coin,
    ch: coin.Challenge,

    pub fn count(self: *const Epoch) usize {
        return self.raws.len;
    }

    /// Block `i`'s context (height, previous MTP, ancestors).
    pub fn ctxOf(self: *const Epoch, i: usize) checks.Ctx {
        const hh: u32 = self.from + @as(u32, @intCast(i));
        return .{ .height = hh, .prev_mtp = PF.prevMtp(self.all, hh), .anc = PF.ancestors(self.all, hh) };
    }

    /// Block `i`'s witness under the epoch's challenge. `size`: the profile choice (prove-epoch's
    /// default `auto`); `skip_device_columns`: the lean build a device witness completes.
    pub fn build(self: *const Epoch, a: std.mem.Allocator, i: usize, size: Size, skip_device_columns: bool) !bs.Built {
        return bs.buildFull(a, self.raws[i], self.undos[i], self.ctxOf(i), .{
            .chal = self.ch,
            .ctx = self.ctxs[i],
            .profile = if (size == .tiered) .tiered else .uniform,
            .auto = size == .auto,
            .skip_device_columns = skip_device_columns,
        });
    }

    /// Block `i`'s proof file: the proof, its public inputs and its header window.
    pub fn encode(self: *const Epoch, a: std.mem.Allocator, i: usize, b: *const bs.Built, proof: system.Proof) ![]u8 {
        const hh: u32 = self.from + @as(u32, @intCast(i));
        const window = try PF.bindWindowPaths(a, self.all, &self.paths, hh);
        return PF.encode(a, &.{ .log_size = b.log_size, .profile = b.profile, .pubs = b.pubs, .proof = proof, .provenance = provenance, .chain_len = self.n, .window = window });
    }

    pub fn writeProof(self: *const Epoch, a: std.mem.Allocator, i: usize, bytes: []const u8) !void {
        try S.writeFileAtomic(try pathOf(a, self.dir, "proofs", self.from + @as(u32, @intCast(i)), "sbblock"), bytes);
    }

    pub fn writeSet(self: *const Epoch, a: std.mem.Allocator) !void {
        try S.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ self.dir, self.to }), try EP.encodeSet(a, self.set));
    }
};

pub const Size = enum { auto, uniform, tiered };

/// Reads the epoch `from..to` from `dir` against the chain's headers (`all`, at least `n`).
pub fn load(a: std.mem.Allocator, all: []const [80]u8, n: u32, dir: []const u8, from: From, to: u32) !Epoch {
    if (to >= n or all.len < n) return error.HeightBeyondChain;
    if (from.height > to) return error.EmptyEpoch;
    const init = try loadInit(a, from);
    const nb = to - from.height + 1;
    const raws = try a.alloc([]const u8, nb);
    const undos = try a.alloc([]const u8, nb);
    const ctxs = try a.alloc([]const u32, nb);
    const hashes = try a.alloc([32]u8, nb);
    const commits = try a.alloc([32]u8, nb);
    for (0..nb) |i| {
        const hh: u32 = from.height + @as(u32, @intCast(i));
        raws[i] = try S.readFile(a, try pathOf(a, dir, "blocks", hh, "bin"));
        if (raws[i].len < 80 or !std.mem.eql(u8, raws[i][0..80], &all[hh])) return error.HeaderMismatch;
        undos[i] = try S.readFile(a, try pathOf(a, dir, "undo", hh, "undo"));
        const cb = try S.readFile(a, try pathOf(a, dir, "undo", hh, "ctx"));
        const cx = try a.alloc(u32, cb.len / 4);
        for (cx, 0..) |*x, j| x.* = std.mem.readInt(u32, cb[4 * j ..][0..4], .little);
        ctxs[i] = cx;
        var h1: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(raws[i][0..80], &h1, .{});
        std.crypto.hash.sha2.Sha256.hash(&h1, &hashes[i], .{});
        // The commitment is of the in-circuit stream, which holds the creating transactions' indices.
        std.crypto.hash.blake2.Blake2s256.hash(try bs.undoStreamOf(a, raws[i], undos[i], cx, hh), &commits[i], .{});
    }
    // The final set is computed first: the seed binds it.
    const set = try EP.coinSetFrom(a, init.set, from.height, raws);
    const ch = EP.challenge(EP.seedFrom(from.height, to, init.digest, try EP.setDigest(a, set), hashes, commits));
    const tree = try a.alloc(HT.Words, n);
    for (tree, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    const paths = try HT.Paths.init(a, tree);
    return .{ .dir = dir, .from = from.height, .to = to, .n = n, .all = all, .paths = paths, .raws = raws, .undos = undos, .ctxs = ctxs, .set = set, .ch = ch };
}
