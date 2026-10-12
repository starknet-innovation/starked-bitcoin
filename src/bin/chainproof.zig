//! `chainproof`: the header-chain proof as a file (PROOF-STORE, D-036; docs/design/proof-store.md).
//!
//!   chainproof setup <n_queries> <pow_bits> <max_log> <headers.bin> <out.vk>
//!       The frozen node shape and the VK (leaf identities for segment log sizes 9..max_log).
//! `<vk>` is a VK file, or `mainnet` for the pinned production VK built into the binary.
//!
//!   chainproof prove <vk> <headers.bin> <to> <out.sbchain> [--from <in.sbchain>] [--segments K] [--max-log L]
//!       Proves headers [0, to) (or extends a verified <in.sbchain> to `to`). Checkpoints after
//!       every segment to <out.sbchain>.ckpt and resumes from it. Writes the file, then reloads and
//!       verifies it. `--segments K` stops after K segments (rerun to continue): a driver loop of
//!       one-segment processes bounds memory on long runs (tools/prove_loop.sh).
//!   chainproof verify <vk> <file.sbchain> [--min-work <hex>]
//!       Standalone verification with the VK pinned. The chainwork must reach a trusted minimum (it
//!       is the only defence against a cheap low-difficulty chain): by default Bitcoin Core's
//!       mainnet `nMinimumChainWork`; `--min-work 0` disables the check (e.g. for a short test chain).
//!   chainproof info <file.sbchain>
//!       What a file holds (plan, peaks, provenance), without verifying it.
//!   chainproof inclusion <vk> <file.sbchain> <headers.bin> <height>
//!       Prints and checks the MMR inclusion path of a block hash in the (verified) file's `T`.
//!
//!   chainproof prove-block <block.bin> <undo.bin | -> <headers.bin> <height> <file.sbchain> <out.sbblock> [--test-strength]
//!       Proves one block (BLOCK-DATA): its checks, its block hash and its commitment
//!       `blake2s(undo)` (D-038) as public inputs. `undo.bin` is the
//!       undo stream (`0x01` and the spent-output records, scripts/fetch_undo.py); `-` uses the empty
//!       stream (no spent outputs: only right for a coinbase-only block). The block's header must be
//!       `headers.bin`'s at `height`, whose 11 predecessors give the median time past. The file is
//!       self-contained (D-039): it carries those headers with MMR inclusion paths for the chain
//!       `file.sbchain` proves (its length only is read; it is not verified here).
//!   chainproof verify-block <vk> <file.sbchain> <file.sbblock> [--min-work <hex> | --min-work 0] [--test-strength]
//!       Verifies the chain proof, the block file's headers against its MMR root, the block proof
//!       under the pinned FRI configuration, and its height, context and block hash against those
//!       headers. Needs no header file. Prints the proven statement.
//!   chainproof prove-epoch <headers.bin> <dir> <to> <file.sbchain> [--test-strength] [--tiered]
//!       M3b (D-040): proves blocks 0..to from <dir>/blocks/<h>.bin, <dir>/undo/<h>.undo and .ctx
//!       (scripts/fetch_undo.py --ctx) under the epoch's challenge (derived from the blocks' hashes and
//!       commitments), writing <dir>/proofs/<h>.sbblock and the coin set <dir>/set-<to>.bin.
//!   chainproof verify-epoch <vk> <file.sbchain> <dir> <to> [--min-work <hex> | --min-work 0] [--test-strength]
//!       Verifies every block proof against the chain, recomputes the challenge from their hashes and
//!       commitments, and checks that their partial sums minus the coin set's fractions are zero, the
//!       set strictly sorted: the coin set after block `to`. Prints Core's hash_serialized and total.
//!   chainproof prove-epoch-tree <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
//!       BLOCK-REC: the epoch's block proofs (<dir>/proofs) as a forest of recursion trees, one per
//!       aligned subtree; writes the block VK <dir>/blockvk.bin (setup) and <dir>/forest-<to>.bin.
//!   chainproof verify-epoch-tree <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0]
//!       Verifies the chain proof, the forest against the block VK (identities, keys, proofs, ranges,
//!       the challenge from the seed over the roots, the block hashes against the chain's T) and the
//!       balance against <dir>/set-<to>.bin. Each block proof binds its previous MTP (D-043 part 3).
//!   chainproof rebind-block <in.sbblock> <headers.bin> <file.sbchain> <out.sbblock>
//!       Rebuilds a block file's header window for another (longer) chain proof, without re-proving.
//!
//! `headers.bin`: raw 80-byte headers from height 0. CPU only. `--test-strength`: 3 queries, 10
//! PoW bits (fast, not secure); without it block proofs use the chain proof's 70 queries, 26 bits.

const std = @import("std");
const sb = @import("starked_bitcoin");
const build_options = @import("build_options");
const FriConfigV2 = @import("stwo_core").pcs.config_v2.FriConfigV2;

const S = sb.recursion.store;
const L = sb.recursion.leaf;
const HT = sb.header_tree;
const H = sb.header_chain;

fn usage() noreturn {
    std.debug.print(
        \\usage:
        \\  chainproof setup <n_queries> <pow_bits> <max_log> <headers.bin> <out.vk>
        \\  chainproof prove <vk> <headers.bin> <to> <out.sbchain> [--from <in.sbchain>] [--segments K] [--max-log L]
        \\  chainproof verify <vk> <file.sbchain> [--min-work <hex> | --min-work 0]
        \\  chainproof inclusion <vk> <file.sbchain> <headers.bin> <height>
        \\  chainproof info <file.sbchain>
        \\  chainproof prove-block <block.bin> <undo.bin | -> <headers.bin> <height> <file.sbchain> <out.sbblock> [--test-strength]
        \\  chainproof verify-block <vk> <file.sbchain> <file.sbblock> [--min-work <hex> | --min-work 0] [--test-strength]
        \\  chainproof rebind-block <in.sbblock> <headers.bin> <file.sbchain> <out.sbblock>
        \\  chainproof prove-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
        \\  chainproof verify-epoch <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--test-strength]
        \\
    , .{});
    std.process.exit(2);
}

pub fn main() !void {
    // Debug builds check for leaks; release builds use libc malloc, which returns freed memory
    // (DebugAllocator's growth made a full-chain run swap, 2026-10-10).
    var gpa_state: std.heap.DebugAllocator(.{}) = .init;
    defer if (@import("builtin").mode == .Debug) {
        _ = gpa_state.deinit();
    };
    const gpa = if (@import("builtin").mode == .Debug) gpa_state.allocator() else std.heap.c_allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const args = try std.process.argsAlloc(a);
    if (args.len < 2) usage();
    const cmd = args[1];
    if (std.mem.eql(u8, cmd, "setup") and args.len == 7) return setup(gpa, a, try parseU32(args[2]), try parseU32(args[3]), try parseU32(args[4]), args[5], args[6]);
    if (std.mem.eql(u8, cmd, "prove") and args.len >= 6) {
        var from: ?[]const u8 = null;
        var max_segments: ?usize = null;
        var max_log: ?u32 = null;
        var i: usize = 6;
        while (i + 1 < args.len) : (i += 2) {
            if (std.mem.eql(u8, args[i], "--from")) from = args[i + 1]
            else if (std.mem.eql(u8, args[i], "--segments")) max_segments = try std.fmt.parseInt(usize, args[i + 1], 10)
            else if (std.mem.eql(u8, args[i], "--max-log")) max_log = try std.fmt.parseInt(u32, args[i + 1], 10)
            else usage();
        }
        if (i != args.len) usage();
        return prove(gpa, a, args[2], args[3], try std.fmt.parseInt(usize, args[4], 10), args[5], from, max_segments, max_log);
    }
    if (std.mem.eql(u8, cmd, "verify") and (args.len == 4 or (args.len == 6 and std.mem.eql(u8, args[4], "--min-work"))))
        return verify(gpa, a, args[2], args[3], if (args.len == 6) try std.fmt.parseInt(u256, args[5], 16) else core_min_work);
    if (std.mem.eql(u8, cmd, "info") and args.len == 3) return info(gpa, a, args[2]);
    if (std.mem.eql(u8, cmd, "prove-block") and (args.len == 8 or (args.len == 9 and std.mem.eql(u8, args[8], "--test-strength"))))
        return proveBlock(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), args[6], args[7], args.len == 9);
    if (std.mem.eql(u8, cmd, "verify-block") and args.len >= 5) {
        var min_work: u256 = core_min_work;
        var weak = false;
        var i: usize = 5;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--test-strength")) {
                weak = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--min-work") and i + 1 < args.len) {
                min_work = try std.fmt.parseInt(u256, args[i + 1], 16);
                i += 2;
            } else usage();
        }
        return verifyBlock(gpa, a, args[2], args[3], args[4], min_work, weak);
    }
    if (std.mem.eql(u8, cmd, "prove-epoch") and args.len >= 6) {
        var weak = false;
        var from: EpochFrom = .{};
        var i: usize = 6;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--test-strength")) {
                weak = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--tiered")) {
                from.tiered = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--from") and i + 2 < args.len) {
                from.height = try std.fmt.parseInt(u32, args[i + 1], 10);
                from.prev_set = args[i + 2];
                i += 3;
            } else usage();
        }
        return proveEpoch(gpa, a, args[2], args[3], try std.fmt.parseInt(u32, args[4], 10), args[5], weak, from);
    }
    if (std.mem.eql(u8, cmd, "verify-epoch") and args.len >= 6) {
        var min_work: u256 = core_min_work;
        var weak = false;
        var from: EpochFrom = .{};
        var i: usize = 6;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--test-strength")) {
                weak = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--min-work") and i + 1 < args.len) {
                min_work = try std.fmt.parseInt(u256, args[i + 1], 16);
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--from") and i + 2 < args.len) {
                from = .{ .height = try std.fmt.parseInt(u32, args[i + 1], 10), .prev_set = args[i + 2] };
                i += 3;
            } else usage();
        }
        return verifyEpoch(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, weak, from);
    }
    if ((std.mem.eql(u8, cmd, "prove-epoch-tree") or std.mem.eql(u8, cmd, "verify-epoch-tree")) and args.len >= 6) {
        var min_work: u256 = core_min_work;
        var from: EpochFrom = .{};
        var i: usize = 6;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--min-work") and i + 1 < args.len) {
                min_work = try std.fmt.parseInt(u256, args[i + 1], 16);
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--test-strength")) {
                from.weak = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--from") and i + 2 < args.len) {
                from.height = try std.fmt.parseInt(u32, args[i + 1], 10);
                from.prev_set = args[i + 2];
                i += 3;
            } else usage();
        }
        if (std.mem.eql(u8, cmd, "prove-epoch-tree"))
            return proveEpochTree(gpa, a, args[2], args[3], try std.fmt.parseInt(u32, args[4], 10), args[5], from);
        return verifyEpochTree(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, from);
    }
    if (std.mem.eql(u8, cmd, "rebind-block") and args.len == 6) return rebindBlock(gpa, a, args[2], args[3], args[4], args[5]);
    if (std.mem.eql(u8, cmd, "inclusion") and args.len == 6) return inclusion(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(usize, args[5], 10));
    usage();
}

fn parseU32(s: []const u8) !u32 {
    return std.fmt.parseInt(u32, s, 10);
}

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

fn loadHeaderFile(a: std.mem.Allocator, path: []const u8) ![]const H.Header {
    const raw = try S.readFile(a, path);
    if (raw.len % 80 != 0) return error.BadHeaderFile;
    const out = try a.alloc(H.Header, raw.len / 80);
    @memcpy(std.mem.sliceAsBytes(out), raw);
    return out;
}

fn printWords(label: []const u8, w: [8]u32) void {
    std.debug.print("{s}", .{label});
    for (w) |x| std.debug.print("{x:0>8}", .{x});
    std.debug.print("\n", .{});
}

/// Block hash in display order (big-endian hex, as explorers show it).
fn printHash(label: []const u8, w: [8]u32) void {
    var bytes: [32]u8 = undefined;
    for (w, 0..) |x, i| std.mem.writeInt(u32, bytes[4 * i ..][0..4], x, .big);
    std.mem.reverse(u8, &bytes);
    std.debug.print("{s}{x}\n", .{ label, bytes });
}

fn setup(gpa: std.mem.Allocator, a: std.mem.Allocator, n_queries: u32, pow_bits: u32, max_log: u32, headers_path: []const u8, out: []const u8) !void {
    const all = try loadHeaderFile(a, headers_path);
    const fri = try FriConfigV2.init(pow_bits, 0, 1, n_queries, 1);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();
    var su = try S.setup(gpa, a, tables, fri, max_log, all);
    defer su.shape.deinit(gpa);
    try S.writeFileAtomic(out, try su.vk.encode(a));
    std.debug.print("setup: queries {d}, pow {d}, segment logs 9..{d}; {d:.1}s\n", .{ n_queries, pow_bits, max_log, secs(timer.read()) });
    printWords("  vk digest  ", try su.vk.digest(a));
    printWords("  node root  ", su.vk.node.root);
    printWords("  node hash  ", su.vk.node.hash);
    std.debug.print("  wrote {s}\n", .{out});
}

/// Bitcoin Core's mainnet `nMinimumChainWork` (kernel/chainparams.cpp at c067aa716f8c, 2026-10-09;
/// the work at about height 966143): the default minimum `verify` requires, as Core refuses to sync
/// a lower-work chain. Checked by `tools/specfuzz/check_constants.py`.
const core_min_work: u256 = 0x145ec036acc5ba740052af1a0;

/// The pinned production VK (`vk/mainnet-q70-p26-l20.vk`): 70 queries, 26 PoW bits, segment log
/// sizes 9..20. `mainnet` as the VK argument selects it.
const mainnet_vk = @embedFile("vk:mainnet");

fn loadVk(a: std.mem.Allocator, path: []const u8) !S.Vk {
    const vk = try S.Vk.decode(a, if (std.mem.eql(u8, path, "mainnet")) mainnet_vk else try S.readFile(a, path));
    var d: [8]u32 = try vk.digest(a);
    std.debug.print("VK {s}: digest ", .{path});
    for (&d) |w| std.debug.print("{x:0>8}", .{w});
    std.debug.print(" (queries {d}, pow {d}, segment logs 9..{d})\n", .{ vk.fri.n_queries, vk.fri.pow_bits, vk.max_log });
    return vk;
}

fn fileExists(path: []const u8) bool {
    std.fs.cwd().access(path, .{}) catch return false;
    return true;
}

fn prove(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, headers_path: []const u8, to_req: usize, out: []const u8, from: ?[]const u8, max_segments: ?usize, max_log_req: ?u32) !void {
    const vk = try loadVk(a, vk_path);
    const all = try loadHeaderFile(a, headers_path);
    const to = @min(to_req, all.len);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();
    var shape = try S.shapeFromVk(gpa, a, tables, &vk);
    defer shape.deinit(gpa);
    std.debug.print("shape from VK checked: {d:.1}s\n", .{secs(timer.lap())});

    var pr = try S.Prover.init(gpa, a, tables, &shape, &vk);
    defer pr.deinit();
    pr.verbose = true;
    const ckpt = try std.fmt.allocPrint(a, "{s}.ckpt", .{out});
    // Start from the checkpoint if any, else from the input file if any. Stored peaks are
    // verified before anything is built on them.
    const start: ?[]const u8 = if (fileExists(ckpt)) ckpt else from;
    if (start) |path| {
        var c = try S.Chain.decode(gpa, a, try S.readFile(a, path));
        defer c.deinit();
        if (c.root_kind == .none) try S.checkPeaks(gpa, a, tables, &vk, &c) else _ = try S.verifyChain(gpa, a, tables, &vk, &c);
        try pr.continueFrom(&c, all);
        std.debug.print("continuing from {s}: {d} headers, {d} peaks verified ({d:.1}s)\n", .{ path, pr.next, pr.stack.items.len, secs(timer.lap()) });
    }
    if (pr.next > to) return error.AlreadyBeyondTarget;

    // Smaller segments lower the peak memory of a leaf (a 2^20-row leaf peaks near 34 GB); any
    // log size up to the VK's is valid, and the plan stays aligned.
    const max_log = max_log_req orelse vk.max_log;
    if (max_log < HT.MIN_SEG_LOG or max_log > vk.max_log) return error.BadMaxLog;
    const plan = try HT.planSegments(a, pr.next, to, max_log);
    std.debug.print("proving {d} segments, headers {d}..{d}\n", .{ plan.len, pr.next, if (plan.len > 0) plan[plan.len - 1][0] + HT.segHeaders(@intCast(plan[plan.len - 1][1])) - 1 else pr.next });
    for (plan, 0..) |s, i| {
        if (max_segments) |m| if (i == m) {
            // Bounded run: the checkpoint holds the progress; rerun the same command to continue.
            std.debug.print("STOPPED after {d} segments at {d} headers ({d} to go); checkpoint {s}\n", .{ m, pr.next, plan.len - m, ckpt });
            return;
        };
        try pr.pushSegment(all, @intCast(s[1]));
        try pr.checkpoint(all, ckpt);
        if (i % 8 == 7 or i + 1 == plan.len) std.debug.print("  {d}/{d} segments, elapsed {d:.0}s\n", .{ i + 1, plan.len, secs(timer.read()) });
    }
    const t_segments = timer.lap();

    var root = try pr.bag();
    defer if (root) |*r| r.proof.deinit();
    const t_bag = timer.lap();
    const n = pr.next;
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(std.mem.sliceAsBytes(all[0..n]), &digest, .{});
    const provenance = try std.fmt.allocPrint(a, "repo={s} stwo-zig={s} headers=0..{d} headers_sha256={x} created_unix={d} segments_s={d:.0} bag_s={d:.0}", .{ build_options.repo_commit, build_options.stwo_commit, n - 1, digest, std.time.timestamp(), secs(t_segments), secs(t_bag) });
    const c = try pr.chain(root, all, provenance);
    // Write first, then verify the file as read back from disk.
    try S.writeFileAtomic(out, try c.encode(a));
    std.debug.print("wrote {s} ({d} headers, {d} peaks)\n", .{ out, n, c.peaks.len });
    try verify(gpa, a, vk_path, out, if (n > 966143) core_min_work else 0);
    std.fs.cwd().deleteFile(ckpt) catch {};
}

fn verify(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, path: []const u8, min_work: ?u256) !void {
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();
    const bytes = try S.readFile(a, path);
    var c = try S.Chain.decode(gpa, a, bytes);
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    std.debug.print("VERIFIED {s} ({d} bytes) in {d:.2}s\n", .{ path, bytes.len, secs(timer.read()) });
    std.debug.print("  headers 0..{d} from Bitcoin's genesis block; {d} segments, {d} peaks\n", .{ s.headers - 1, c.logs.len, c.peaks.len });
    std.debug.print("  tip height {d}\n", .{s.tip_height});
    printHash("  tip hash   ", s.tip);
    std.debug.print("  chainwork  0x{x}\n", .{s.work});
    printWords("  MMR root T ", s.t);
    std.debug.print("  provenance {s}\n", .{c.provenance});
    if (min_work) |w| if (w != 0) {
        if (s.work < w) {
            std.debug.print("REJECTED: chainwork below the required minimum 0x{x}\n", .{w});
            return error.InsufficientWork;
        }
        std.debug.print("  chainwork >= required minimum 0x{x}{s}\n", .{ w, if (w == core_min_work) " (Bitcoin Core's nMinimumChainWork)" else "" });
    } else std.debug.print("  NOTE: compare the chainwork with a trusted minimum (--min-work); a valid proof alone does not show this is the real chain\n", .{});
}

fn inclusion(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, path: []const u8, headers_path: []const u8, height: usize) !void {
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    const all = try loadHeaderFile(a, headers_path);
    if (all.len < s.headers or height >= s.headers) return error.OutOfRange;
    const hashes = try a.alloc(HT.Words, s.headers);
    for (hashes, all[0..s.headers]) |*h, *hd| h.* = HT.blockHash(hd);
    const steps = try HT.inclusionProof(a, hashes, height);
    if (!try HT.verifyAt(a, hashes[height], steps, height, s.headers, s.t)) return error.InclusionFailed;
    printHash("block hash ", hashes[height]);
    std.debug.print("included at height {d} in T (verified file); path of {d} steps (sibling, side):\n", .{ height, steps.len });
    for (steps) |st| {
        printWords("  ", st.sibling);
        std.debug.print("    {s}\n", .{if (st.left) "left" else "right"});
    }
}

const PF = sb.block.proof_file;
const BS = sb.block.system;

fn blockFri(weak: bool) FriConfigV2 {
    return if (weak) PF.testFri() else PF.productionFri();
}

fn proveBlock(gpa: std.mem.Allocator, a: std.mem.Allocator, block_path: []const u8, undo_path: []const u8, headers_path: []const u8, height: u32, chain_path: []const u8, out: []const u8, weak: bool) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    const raw = try S.readFile(a, block_path);
    const undo: []const u8 = if (std.mem.eql(u8, undo_path, "-")) &.{1} else try S.readFile(a, undo_path);
    if (undo.len == 0 or undo[0] != 1) return error.BadUndoStream;
    const all = try loadHeaderFile(a, headers_path);
    if (height >= n or all.len < n) return error.HeightBeyondChain;
    if (raw.len < 80 or !std.mem.eql(u8, raw[0..80], &all[height])) return error.HeaderMismatch;
    const ctx = sb.block.checks.Ctx{ .height = height, .prev_mtp = PF.prevMtp(all, height), .anc = PF.ancestors(all, height) };
    var timer = try std.time.Timer.start();
    const airs = try BS.parseAirs(a);
    const b = try BS.buildU(a, raw, undo, ctx);
    if (b.ntx > 1 and undo.len == 1) {
        std.debug.print("REJECTED: the block spends outputs; pass its undo stream (scripts/fetch_undo.py), not `-`\n", .{});
        return error.UndoRequired;
    }
    if (try BS.firstViolation(a, &airs, &b)) |v| {
        std.debug.print("REJECTED: {s} row {d} violates constraint {d} (the block or its undo data is invalid)\n", .{ BS.names[v.comp], v.row, v.constraint });
        return error.Unsatisfied;
    }
    if (try BS.unbalanced(a, &airs, &b)) |rel| {
        std.debug.print("REJECTED: relation {d} unbalanced\n", .{rel});
        return error.Unbalanced;
    }
    std.debug.print("block {d}: {d} bytes, {d} txs, undo {d} bytes, trace 2^{d} rows; witness in {d:.1}s\n", .{ height, raw.len, b.ntx, undo.len, b.log_size, secs(timer.lap()) });
    const fri = blockFri(weak);
    const proof = try PF.prove(a, &airs, &b, fri);
    std.debug.print("proved in {d:.1}s ({s})\n", .{ secs(timer.lap()), if (weak) "TEST STRENGTH, not secure" else "70 queries, 26 PoW bits" });
    const prov = try std.fmt.allocPrint(a, "starked-bitcoin {s}, stwo-zig {s}", .{ build_options.repo_commit, build_options.stwo_commit });
    const hashes = try a.alloc(HT.Words, n);
    for (hashes, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    const window = try PF.bindWindow(a, all, hashes, height);
    const bytes = try PF.encode(a, &.{ .log_size = b.log_size, .profile = b.profile, .pubs = b.pubs, .proof = proof, .provenance = prov, .chain_len = @intCast(n), .window = window });
    try S.writeFileAtomic(out, bytes);
    const f = try PF.decode(a, try S.readFile(a, out));
    try PF.verifyStark(a, &airs, &f, fri);
    std.debug.print("wrote {s} ({d} bytes), reloaded and verified in {d:.1}s\n", .{ out, bytes.len, secs(timer.lap()) });
}

const EP = sb.block.epoch;

fn pathOf(a: std.mem.Allocator, dir: []const u8, sub: []const u8, h: u32, ext: []const u8) ![]u8 {
    return std.fmt.allocPrint(a, "{s}/{s}/{d}.{s}", .{ dir, sub, h, ext });
}

/// An epoch's start: genesis, or block `height` from the coin set after `height − 1` (`prev_set`).
const EpochFrom = struct {
    height: u32 = 0,
    prev_set: ?[]const u8 = null,
    /// prove-epoch `--tiered`: the tiered size profile where a block fits it (D-045).
    tiered: bool = false,
    /// prove-epoch-tree `--test-strength`: the block proofs were made at test strength.
    weak: bool = false,
};

/// The initial set of an epoch from a previous set: decoded, strictly sorted, created before `from`.
fn loadInit(a: std.mem.Allocator, from: EpochFrom) !struct { set: []const EP.Coin, hash: ?[32]u8, digest: ?[32]u8 } {
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

fn proveEpoch(gpa: std.mem.Allocator, a: std.mem.Allocator, headers_path: []const u8, dir: []const u8, to: u32, chain_path: []const u8, weak: bool, from: EpochFrom) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    const all = try loadHeaderFile(a, headers_path);
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
        if (!std.mem.eql(u8, raws[i][0..80], &all[hh])) return error.HeaderMismatch;
        undos[i] = try S.readFile(a, try pathOf(a, dir, "undo", hh, "undo"));
        const cb = try S.readFile(a, try pathOf(a, dir, "undo", hh, "ctx"));
        const cx = try a.alloc(u32, cb.len / 4);
        for (cx, 0..) |*x, j| x.* = std.mem.readInt(u32, cb[4 * j ..][0..4], .little);
        ctxs[i] = cx;
        var h1: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(raws[i][0..80], &h1, .{});
        std.crypto.hash.sha2.Sha256.hash(&h1, &hashes[i], .{});
        // The commitment is of the in-circuit stream, which holds the creating transactions' indices.
        std.crypto.hash.blake2.Blake2s256.hash(try BS.undoStreamOf(a, raws[i], undos[i], cx, hh), &commits[i], .{});
    }
    // The final set is computed first: the seed binds it.
    const set = try EP.coinSetFrom(a, init.set, from.height, raws);
    const ch = EP.challenge(EP.seedFrom(from.height, to, init.digest, try EP.setDigest(a, set), hashes, commits));
    const tree = try a.alloc(HT.Words, n);
    for (tree, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    const airs = try BS.parseAirs(a);
    const fri = blockFri(weak);
    const pdir = try std.fmt.allocPrint(a, "{s}/proofs", .{dir});
    std.fs.cwd().makePath(pdir) catch {};
    var timer = try std.time.Timer.start();
    for (0..nb) |i| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const ba = arena.allocator();
        const hh: u32 = from.height + @as(u32, @intCast(i));
        const ctx = sb.block.checks.Ctx{ .height = hh, .prev_mtp = PF.prevMtp(all, hh), .anc = PF.ancestors(all, hh) };
        const b = try BS.buildFull(ba, raws[i], undos[i], ctx, .{ .chal = ch, .ctx = ctxs[i], .profile = if (from.tiered) .tiered else .uniform });
        const proof = try PF.prove(ba, &airs, &b, fri);
        const window = try PF.bindWindow(ba, all, tree, hh);
        const bytes = try PF.encode(ba, &.{ .log_size = b.log_size, .profile = b.profile, .pubs = b.pubs, .proof = proof, .provenance = "prove-epoch", .chain_len = @intCast(n), .window = window });
        try S.writeFileAtomic(try pathOf(ba, dir, "proofs", hh, "sbblock"), bytes);
        if (hh % 50 == 0 or hh == to) std.debug.print("block {d}: proved ({d:.0}s so far)\n", .{ hh, secs(timer.read()) });
    }
    try S.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to }), try EP.encodeSet(a, set));
    std.debug.print("epoch {d}..{d}: {d} block proofs, coin set of {d} coins written\n", .{ from.height, to, nb, set.len });
}

fn verifyEpoch(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, dir: []const u8, to: u32, min_work: u256, weak: bool, from: EpochFrom) !void {
    var timer = try std.time.Timer.start();
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) return error.InsufficientWork;
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    if (from.height > to) return error.EmptyEpoch;
    const init = try loadInit(a, from);
    const airs = try BS.parseAirs(a);
    const nb = to - from.height + 1;
    const files = try a.alloc(PF.File, nb);
    const hashes = try a.alloc([32]u8, nb);
    const commits = try a.alloc([32]u8, nb);
    var nin: u64 = 0;
    for (0..nb) |i| {
        const hh: u32 = from.height + @as(u32, @intCast(i));
        const f = try PF.decode(a, try S.readFile(a, try pathOf(a, dir, "proofs", hh, "sbblock")));
        const window = try PF.checkWindow(a, &f, s.headers, s.t);
        try PF.verifyStark(a, &airs, &f, blockFri(weak));
        const st = try PF.checkPubs(&f.pubs, window);
        if (st.height != hh) return error.WrongHeight;
        var h1: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(&window[window.len - 1], &h1, .{});
        std.crypto.hash.sha2.Sha256.hash(&h1, &hashes[i], .{});
        commits[i] = st.commitment;
        nin += f.pubs[sb.block.coin.PUB_NIN].toU32();
        files[i] = f;
    }
    const set = try EP.decodeSet(a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to })));
    if (!EP.sortedStrict(set)) return error.SetNotSorted;
    const ch = EP.challenge(EP.seedFrom(from.height, to, init.digest, try EP.setDigest(a, set), hashes, commits));
    var sum = @import("stwo_core").fields.qm31.QM31.zero();
    for (files, 0..) |f, i| {
        try EP.checkPubs(&f.pubs, ch, from.height + @as(u32, @intCast(i)));
        sum = sum.add(EP.partialSum(&f.pubs));
    }
    std.debug.print("{d} block proofs verified, challenge recomputed from their hashes and commitments ({d:.1}s)\n", .{ nb, secs(timer.lap()) });
    // Events below p: initial + created + spent + final (the creations are at most the outputs).
    if (nin + set.len + init.set.len >= 1 << 30) return error.EpochTooLarge;
    // The initial set counts as created (Spec/UtxoEpochFrom.lean).
    sum = sum.add(try EP.finalSum(ch, init.set));
    const fin = try EP.finalSum(ch, set);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    if (init.hash) |h| std.debug.print("  from the set after block {d}: {d} coins, hash_serialized {x}\n", .{ from.height - 1, init.set.len, h });
    std.debug.print("VERIFIED epoch {d}..{d}: the coin set after block {d} is {d} coins ({d} inputs spent in the epoch)\n", .{ from.height, to, to, set.len, nin });
    std.debug.print("  total amount     {d} sat\n", .{EP.totalAmount(set)});
    std.debug.print("  hash_serialized  {x}  (Core's HASH_SERIALIZED of this set)\n", .{EP.hashSerialized(set)});
}

const BF = sb.recursion.block_forest;

fn proveEpochTree(gpa: std.mem.Allocator, a: std.mem.Allocator, headers_path: []const u8, dir: []const u8, to: u32, chain_path: []const u8, from: EpochFrom) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    const all = try loadHeaderFile(a, headers_path);
    if (to >= n or all.len < n) return error.HeightBeyondChain;
    if (from.height > to) return error.EmptyEpoch;
    const nb = to - from.height + 1;
    const files = try a.alloc(PF.File, nb);
    for (files, 0..) |*f, i| f.* = try PF.decode(a, try S.readFile(a, try pathOf(a, dir, "proofs", from.height + @as(u32, @intCast(i)), "sbblock")));
    const airs = try BS.parseAirs(a);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var timer = try std.time.Timer.start();
    const bfri = blockFri(from.weak);
    var su = try BF.setup(gpa, a, tables, &airs, files, bfri);
    defer su.shape.deinit(gpa);
    try S.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/blockvk.bin", .{dir}), try su.vk.encode(a));
    std.debug.print("setup: shape and block VK in {d:.1}s\n", .{secs(timer.lap())});
    const leaves = try a.alloc(HT.Words, n);
    for (leaves, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    const forest = try BF.proveForest(gpa, a, tables, &su.shape, &airs, files, from.height, bfri, leaves);
    defer for (forest.roots) |*r| r.proved.proof.deinit();
    const out = try std.fmt.allocPrint(a, "{s}/forest-{d}.bin", .{ dir, to });
    try S.writeFileAtomic(out, try forest.encode(a));
    std.debug.print("epoch {d}..{d}: {d} blocks in {d} recursion trees, written to {s} ({d:.0}s)\n", .{ from.height, to, nb, forest.roots.len, out, secs(timer.read()) });
}

fn verifyEpochTree(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, dir: []const u8, to: u32, min_work: u256, from: EpochFrom) !void {
    var timer = try std.time.Timer.start();
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) return error.InsufficientWork;
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    const bvk = try BF.Vk.decode(try S.readFile(a, try std.fmt.allocPrint(a, "{s}/blockvk.bin", .{dir})));
    var forest = try BF.Forest.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/forest-{d}.bin", .{ dir, to })));
    defer for (forest.roots) |*r| r.proved.proof.deinit();
    if (forest.from != from.height or forest.to != to) return error.WrongEpoch;
    const init = try loadInit(a, from);
    const set = try EP.decodeSet(a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to })));
    if (!EP.sortedStrict(set)) return error.SetNotSorted;
    const v = try BF.verifyForest(gpa, a, tables, &bvk, &forest, s.headers, s.t, init.digest, try EP.setDigest(a, set));
    std.debug.print("{d} recursion trees verified: blocks {d}..{d}, the challenge from the seed over their roots, the block hashes the chain's ({d:.1}s)\n", .{ forest.roots.len, from.height, to, secs(timer.lap()) });
    if (v.nin + set.len + init.set.len >= 1 << 30) return error.EpochTooLarge;
    var sum = v.sum.add(try EP.finalSum(v.challenge, init.set));
    const fin = try EP.finalSum(v.challenge, set);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    std.debug.print("VERIFIED epoch {d}..{d} (recursion): the coin set after block {d} is {d} coins ({d} inputs spent)\n", .{ from.height, to, to, set.len, v.nin });
    std.debug.print("  total amount     {d} sat\n", .{EP.totalAmount(set)});
    std.debug.print("  hash_serialized  {x}\n", .{EP.hashSerialized(set)});
}

fn rebindBlock(gpa: std.mem.Allocator, a: std.mem.Allocator, in_path: []const u8, headers_path: []const u8, chain_path: []const u8, out: []const u8) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    var f = try PF.decode(a, try S.readFile(a, in_path));
    const all = try loadHeaderFile(a, headers_path);
    if (all.len < n) return error.HeadersShorterThanChain;
    const hashes = try a.alloc(HT.Words, n);
    for (hashes, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    const height = f.pubs[2].toU32();
    // The block's header must stay the same: the proof's public block hash fixes it.
    const want = BS.hashLimbs(&all[height]);
    for (0..16) |j| if (!f.pubs[BS.PUB_HASH + j].eql(want[j])) return error.BlockHashMismatch;
    f.window = try PF.bindWindow(a, all, hashes, height);
    f.chain_len = @intCast(n);
    try S.writeFileAtomic(out, try PF.encode(a, &f));
    std.debug.print("rebound {s} to a chain of {d} headers: {s}\n", .{ in_path, n, out });
}

fn verifyBlock(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, block_path: []const u8, min_work: u256, weak: bool) !void {
    var timer = try std.time.Timer.start();
    // 1. The chain proof.
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) {
        std.debug.print("REJECTED: chainwork 0x{x} below the required minimum 0x{x}\n", .{ s.work, min_work });
        return error.InsufficientWork;
    }
    std.debug.print("chain proof verified: headers 0..{d}, chainwork 0x{x}{s} ({d:.1}s)\n", .{ s.headers - 1, s.work, if (min_work == 0) " (minimum-work check DISABLED)" else "", secs(timer.lap()) });
    // 2. The block file: its headers against the chain's MMR root, its STARK, its public inputs.
    const airs = try BS.parseAirs(a);
    const f = try PF.decode(a, try S.readFile(a, block_path));
    const window = try PF.checkWindow(a, &f, s.headers, s.t);
    try PF.verifyStark(a, &airs, &f, blockFri(weak));
    const st = try PF.checkPubs(&f.pubs, window);
    std.debug.print("VERIFIED block proof {s} ({s}) in {d:.1}s\n", .{ block_path, if (weak) "TEST STRENGTH, not secure" else "70 queries, 26 PoW bits", secs(timer.lap()) });
    printHash("  block hash  ", HT.blockHash(&window[window.len - 1]));
    std.debug.print("  height      {d} (header and {d} predecessors included in the chain's MMR root)\n  block       {d} bytes, {d} transactions\n", .{ st.height, window.len - 1, st.block_len, st.ntx });
    std.debug.print("  valid under Core's CheckBlock (without proof of work, which the chain proof covers) and\n  ContextualCheckBlock, given no repeated prevout (M3b)\n", .{});
    std.debug.print("  undo        {d} bytes (committed, not checked: M3b)\n  commitment  {x}  (blake2s(undo))\n", .{ st.undo_len, st.commitment });
    std.debug.print("  provenance  {s}\n", .{f.provenance});
}

fn info(gpa: std.mem.Allocator, a: std.mem.Allocator, path: []const u8) !void {
    const bytes = try S.readFile(a, path);
    var c = try S.Chain.decode(gpa, a, bytes);
    defer c.deinit();
    std.debug.print("{s}: {d} bytes, NOT verified (use `verify`)\n", .{ path, bytes.len });
    printWords("  VK digest   ", c.vk_digest);
    std.debug.print("  FRI         queries {d}, pow {d}; segment logs up to {d}\n", .{ c.fri.n_queries, c.fri.pow_bits, c.max_log });
    std.debug.print("  headers     0..{d} in {d} segments; {d} peaks; root {s}\n", .{ c.headers() - 1, c.logs.len, c.peaks.len, @tagName(c.root_kind) });
    var counts = [_]usize{0} ** 21;
    for (c.logs) |l| counts[l] += 1;
    std.debug.print("  segment logs", .{});
    for (counts, 0..) |n, l| if (n > 0) std.debug.print(" {d}x{d}", .{ n, l });
    std.debug.print("\n  peaks (headers each):", .{});
    for (c.peaks) |p| std.debug.print(" {d}", .{sb.recursion.node.headerCount(p.pubs)});
    std.debug.print("\n  provenance  {s}\n", .{c.provenance});
}
