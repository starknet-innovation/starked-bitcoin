//! An epoch's block proofs from local files (M3b, D-040): what `chainproof prove-epoch` (CPU) and
//! `cuda-epoch` (the resident CUDA prover, src/gpu/cuda/epoch.zig) share. Both read
//! `<dir>/blocks/<h>.bin`, `<dir>/undo/<h>.undo` and `.ctx` (scripts/fetch_undo.py --ctx) for the
//! heights `from..to`, derive the epoch's challenge from the blocks' hashes and commitments and the
//! final coin set, build each block's witness under it, and write `<dir>/proofs/<h>.sbblock` and the
//! coin set `<dir>/set-<to>.bin`. The proof files are the same bytes whichever prover made them
//! (the CUDA proof is byte-identical to the CPU's).
//!
//! Host memory does not grow with the epoch: `load` reads each block once (its hash and commitment, and
//! its coin events applied to `replay.Set`, which streams the previous set in and the final set out), and
//! `build` reads block `i`'s files again when it is proved. The peak is the coin table, ~25 GB at today's
//! ~165 M coins, freed before proving.

const std = @import("std");
const bs = @import("system.zig");
const checks = @import("checks.zig");
const coin = @import("coin.zig");
const EP = @import("epoch.zig");
const PF = @import("proof_file.zig");
const S = @import("../recursion/store.zig");
const HT = @import("../btc/header_tree.zig");
const system = @import("../air/system.zig");
const R = @import("replay.zig");
const SF = @import("set_file.zig");

/// The provenance both provers write (so their files are byte-identical).
pub const provenance = "prove-epoch";

/// An epoch's start: genesis, or block `height` from the coin set after `height − 1` (`prev_set`).
pub const From = struct {
    height: u32 = 0,
    prev_set: ?[]const u8 = null,
};

/// An epoch's initial set: none at genesis, else the previous set file's facts (streamed and checked:
/// strictly sorted, every coin created before `from`).
pub const Init = struct { info: ?SF.Info = null };

pub fn loadInit(gpa: std.mem.Allocator, from: From) !Init {
    const path = from.prev_set orelse {
        if (from.height != 0) return error.PrevSetRequired;
        return .{};
    };
    if (from.height == 0) return error.GenesisHasNoPrevSet;
    return .{ .info = try SF.scan(gpa, path, from.height) };
}

pub fn pathOf(a: std.mem.Allocator, dir: []const u8, sub: []const u8, h: u32, ext: []const u8) ![]u8 {
    return std.fmt.allocPrint(a, "{s}/{s}/{d}.{s}", .{ dir, sub, h, ext });
}

/// The epoch's blocks, the final coin set and the challenge.
pub const Epoch = struct {
    dir: []const u8,
    from: u32,
    to: u32,
    /// Block `i`'s height: `from + i` in an epoch; listed in a standalone run (`loadHeights`).
    heights: []const u32,
    /// A standalone run: the testing challenge, no coin set; the proofs are not bound to an epoch
    /// (`chainproof verify-epoch` rejects them). For measurements over chosen blocks.
    standalone: bool = false,
    /// The chain proof's header count, and the headers 0..n−1 (and their hashes: the MMR leaves).
    n: u32,
    all: []const [80]u8,
    /// The MMR over the headers' hashes, folded once (every block's window paths).
    paths: HT.Paths,
    /// The final set, written to `<dir>/set-<to>.bin` by `load` (none in a standalone run).
    fin: ?SF.Info = null,
    ch: coin.Challenge,

    pub fn count(self: *const Epoch) usize {
        return self.heights.len;
    }

    /// Block `i`'s context (height, previous MTP, ancestors).
    pub fn ctxOf(self: *const Epoch, i: usize) checks.Ctx {
        const hh = self.heights[i];
        return .{ .height = hh, .prev_mtp = PF.prevMtp(self.all, hh), .anc = PF.ancestors(self.all, hh) };
    }

    /// Block `i`'s witness under the epoch's challenge. `size`: the profile choice (prove-epoch's
    /// default `auto`); `skip_device_columns`: the lean build a device witness completes.
    pub fn build(self: *const Epoch, a: std.mem.Allocator, i: usize, size: Size, skip_device_columns: bool) !bs.Built {
        const f = try readBlock(a, self.all, self.dir, self.heights[i]);
        return bs.buildFull(a, f.raw, f.undo, self.ctxOf(i), .{
            .chal = self.ch,
            .ctx = f.ctx,
            .profile = if (size == .tiered) .tiered else .uniform,
            .auto = size == .auto,
            .skip_device_columns = skip_device_columns,
        });
    }

    /// Block `i`'s proof file: the proof, its public inputs and its header window.
    pub fn encode(self: *const Epoch, a: std.mem.Allocator, i: usize, b: *const bs.Built, proof: system.Proof) ![]u8 {
        const hh = self.heights[i];
        const window = try PF.bindWindowPaths(a, self.all, &self.paths, hh);
        return PF.encode(a, &.{ .log_size = b.log_size, .profile = b.profile, .pubs = b.pubs, .proof = proof, .provenance = provenance, .chain_len = self.n, .window = window });
    }

    pub fn writeProof(self: *const Epoch, a: std.mem.Allocator, i: usize, bytes: []const u8) !void {
        try S.writeFileAtomic(try pathOf(a, self.dir, "proofs", self.heights[i], "sbblock"), bytes);
    }
};

pub const Size = enum { auto, uniform, tiered };

/// Block `hh`'s files: the raw block (checked against the header), its fetched undo stream and the
/// creating transactions' indices.
fn readBlock(a: std.mem.Allocator, all: []const [80]u8, dir: []const u8, hh: u32) !struct { raw: []const u8, undo: []const u8, ctx: []const u32 } {
    const raw = try S.readFile(a, try pathOf(a, dir, "blocks", hh, "bin"));
    if (raw.len < 80 or !std.mem.eql(u8, raw[0..80], &all[hh])) return error.HeaderMismatch;
    const undo = try S.readFile(a, try pathOf(a, dir, "undo", hh, "undo"));
    const cb = try S.readFile(a, try pathOf(a, dir, "undo", hh, "ctx"));
    const cx = try a.alloc(u32, cb.len / 4);
    for (cx, 0..) |*x, j| x.* = std.mem.readInt(u32, cb[4 * j ..][0..4], .little);
    return .{ .raw = raw, .undo = undo, .ctx = cx };
}

/// Reads the epoch `from..to` from `dir` against the chain's headers (`all`, at least `n`), and writes
/// its final set to `<dir>/set-<to>.bin`.
pub fn load(a: std.mem.Allocator, all: []const [80]u8, n: u32, dir: []const u8, from: From, to: u32) !Epoch {
    if (to >= n or all.len < n) return error.HeightBeyondChain;
    if (from.height > to) return error.EmptyEpoch;
    const gpa = std.heap.page_allocator;
    var set = try R.Set.init(gpa, 0);
    defer set.deinit();
    var prev: ?[32]u8 = null;
    if (from.prev_set) |path| {
        if (from.height == 0) return error.GenesisHasNoPrevSet;
        prev = (try set.loadFile(path, from.height)).digest;
    } else if (from.height != 0) return error.PrevSetRequired;
    const nb = to - from.height + 1;
    const heights = try a.alloc(u32, nb);
    const hashes = try a.alloc([32]u8, nb);
    const commits = try a.alloc([32]u8, nb);
    var tmp = std.heap.ArenaAllocator.init(gpa);
    defer tmp.deinit();
    for (0..nb) |i| {
        _ = tmp.reset(.retain_capacity);
        const ta = tmp.allocator();
        const hh: u32 = from.height + @as(u32, @intCast(i));
        heights[i] = hh;
        const f = try readBlock(ta, all, dir, hh);
        var h1: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(f.raw[0..80], &h1, .{});
        std.crypto.hash.sha2.Sha256.hash(&h1, &hashes[i], .{});
        // The commitment is of the in-circuit stream, which holds the creating transactions' indices.
        std.crypto.hash.blake2.Blake2s256.hash(try bs.undoStreamOf(ta, f.raw, f.undo, f.ctx, hh), &commits[i], .{});
        _ = try set.apply(ta, f.raw, &all[hh], hh, false);
        try set.maybeCompact();
    }
    // The final set is computed first: the seed binds it.
    std.fs.cwd().makePath(dir) catch {};
    const fin = try set.writeFile(try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to }));
    const ch = EP.challenge(EP.seedFrom(from.height, to, prev, fin.digest, hashes, commits));
    return .{ .dir = dir, .from = from.height, .to = to, .heights = heights, .n = n, .all = all, .paths = try pathsOf(a, all, n), .fin = fin, .ch = ch };
}

/// A standalone run over the listed heights (any order): each block under the testing challenge.
pub fn loadHeights(a: std.mem.Allocator, all: []const [80]u8, n: u32, dir: []const u8, heights: []const u32) !Epoch {
    if (heights.len == 0) return error.EmptyEpoch;
    for (heights) |hh| if (hh >= n or all.len < n) return error.HeightBeyondChain;
    return .{ .dir = dir, .from = heights[0], .to = heights[heights.len - 1], .heights = heights, .standalone = true, .n = n, .all = all, .paths = try pathsOf(a, all, n), .ch = coin.Challenge.testing() };
}

fn pathsOf(a: std.mem.Allocator, all: []const [80]u8, n: u32) !HT.Paths {
    const tree = try a.alloc(HT.Words, n);
    for (tree, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    return HT.Paths.init(a, tree);
}
