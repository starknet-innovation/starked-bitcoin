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
//!   chainproof prove-epoch <headers.bin> <dir> <to> <file.sbchain> [--test-strength] [--uniform | --tiered]
//!       M3b (D-040): proves blocks 0..to from <dir>/blocks/<h>.bin, <dir>/undo/<h>.undo and .ctx
//!       (scripts/fetch_undo.py --ctx) under the epoch's challenge (derived from the blocks' hashes and
//!       commitments), writing <dir>/proofs/<h>.sbblock and the coin set <dir>/set-<to>.bin.
//!   chainproof verify-epoch <vk> <file.sbchain> <dir> <to> [--min-work <hex> | --min-work 0] [--test-strength] [--jobs <n>]
//!       Verifies every block proof against the chain, recomputes the challenge from their hashes and
//!       commitments, and checks that their partial sums minus the coin set's fractions are zero, the
//!       set strictly sorted: the coin set after block `to`. Prints Core's hash_serialized and total.
//!   chainproof prove-epoch-tree <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
//!       BLOCK-REC: the epoch's block proofs (<dir>/proofs) as a forest of recursion trees, one per
//!       aligned subtree; writes the block VK <dir>/blockvk.bin (setup) and <dir>/forest-<to>.bin.
//!   chainproof verify-epoch-tree <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--unpinned]
//!       Verifies the chain proof, the forest against the block VK (identities, keys, proofs, ranges,
//!       the challenge from the seed over the roots, the block hashes against the chain's T) and the
//!       balance against <dir>/set-<to>.bin. Each block proof binds its previous MTP (D-043 part 3).
//!   chainproof prove-epoch-wide <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
//!       BLOCK-REC with wide nodes and per-level shapes (src/recursion/block_tree.zig): writes the tree VK
//!       <dir>/treevk.bin, each proof to <dir>/tree/<k>-<x>.sbproof (a stopped run resumes from them)
//!       and the forest <dir>/forestk-<to>.bin.
//!   chainproof verify-epoch-wide <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--unpinned]
//!       As verify-epoch-tree, for prove-epoch-wide's forest.
//!   chainproof prove-epoch-root <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--set-digests <prev|-> <fin>]
//!       The epoch root over prove-epoch-wide's forest (src/recursion/epoch_root.zig): one proof for the
//!       epoch; writes <dir>/rootvk.bin and <dir>/epochroot-<to>.bin (CPU: small epochs).
//!   chainproof verify-epoch-root <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--unpinned]
//!       Verifies the chain proof, the epoch root proof and the balance against <dir>/set-<to>.bin.
//!   chainproof rebind-block <in.sbblock> <headers.bin> <file.sbchain> <out.sbblock>
//!       Rebuilds a block file's header window for another (longer) chain proof, without re-proving.
//!   chainproof rebind-forest <vk> <in forestk-<to>.bin> <headers.bin> <file.sbchain> <out>
//!       The same for a forest's root paths (an epoch proved under an older chain file).
//!   chainproof setup-vks <out-dir> [--max-m M] [--test-strength] <dir>:<to>[:<from>:<prev-set.bin>]...
//!       Remakes the epoch layers' VKs (tree, root, join) from the forests and one block proof per
//!       size key, proving nothing, and says which equal the pinned ones (vk/epoch/).
//!
//! The epoch verifiers (verify-epoch-tree, -wide, -root, verify-chain) accept only the pinned VKs in
//! vk/epoch/, built into this binary: a VK read from the prover's files could name any circuit.
//! `--unpinned` accepts any VK, for tests (small epochs, test strength); the output says so.
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
        \\  chainproof rebind-forest <vk> <in forestk-<to>.bin> <headers.bin> <file.sbchain> <out>
        \\  chainproof set-pass-model <set.bin> [--per N]
        \\  chainproof setup-vks <out-dir> [--max-m M] [--test-strength] <dir>:<to>[:<from>:<prev-set.bin>]...
        \\  chainproof prove-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
        \\  chainproof prove-chain <vk> <file.sbchain> <out-dir> [--max-m M] <dir>:<to>[:<from>:<prev-set.bin>][#<prev-hex|->,<fin-hex>]...
        \\  chainproof verify-chain <vk> <file.sbchain> <out-dir> [--min-work <hex> | --min-work 0] [--unpinned] <dir>:<to>[:<from>:<prev-set.bin>]...
        \\  chainproof verify-epoch <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--test-strength] [--jobs <n>]
        \\  chainproof prove-epoch-wide|prove-epoch-tree <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength]
        \\  chainproof prove-epoch-root <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--set-digests <prev|-> <fin>]
        \\  chainproof verify-epoch-wide|verify-epoch-tree|verify-epoch-root <vk> <file.sbchain> <dir> <to> [--from <a> <prev-set.bin>] [--min-work <hex> | --min-work 0] [--unpinned]
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
                from.size = .tiered;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--uniform")) {
                from.size = .uniform;
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
                from = .{ .height = try std.fmt.parseInt(u32, args[i + 1], 10), .prev_set = args[i + 2], .jobs = from.jobs };
                i += 3;
            } else if (std.mem.eql(u8, args[i], "--jobs") and i + 1 < args.len) {
                from.jobs = try std.fmt.parseInt(u32, args[i + 1], 10);
                if (from.jobs == 0) usage();
                i += 2;
            } else usage();
        }
        return verifyEpoch(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, weak, from);
    }
    if ((std.mem.eql(u8, cmd, "prove-epoch-tree") or std.mem.eql(u8, cmd, "verify-epoch-tree") or
        std.mem.eql(u8, cmd, "prove-epoch-wide") or std.mem.eql(u8, cmd, "verify-epoch-wide") or
        std.mem.eql(u8, cmd, "prove-epoch-root") or std.mem.eql(u8, cmd, "verify-epoch-root")) and args.len >= 6)
    {
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
            } else if (std.mem.eql(u8, args[i], "--unpinned") and std.mem.startsWith(u8, cmd, "verify-")) {
                from.unpinned = true;
                i += 1;
            } else if (std.mem.eql(u8, args[i], "--from") and i + 2 < args.len) {
                from.height = try std.fmt.parseInt(u32, args[i + 1], 10);
                from.prev_set = args[i + 2];
                i += 3;
            } else if (std.mem.eql(u8, args[i], "--set-digests") and i + 2 < args.len) {
                from.digests = .{ .prev = if (std.mem.eql(u8, args[i + 1], "-")) null else try parseDigest(args[i + 1]), .fin = try parseDigest(args[i + 2]) };
                i += 3;
            } else usage();
        }
        if (std.mem.eql(u8, cmd, "prove-epoch-tree"))
            return proveEpochTree(gpa, a, args[2], args[3], try std.fmt.parseInt(u32, args[4], 10), args[5], from);
        if (std.mem.eql(u8, cmd, "prove-epoch-wide"))
            return proveEpochWide(gpa, a, args[2], args[3], try std.fmt.parseInt(u32, args[4], 10), args[5], from);
        if (std.mem.eql(u8, cmd, "prove-epoch-root"))
            return proveEpochRoot(gpa, a, args[2], args[3], try std.fmt.parseInt(u32, args[4], 10), args[5], from);
        if (std.mem.eql(u8, cmd, "verify-epoch-root"))
            return verifyEpochRoot(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, from);
        if (std.mem.eql(u8, cmd, "verify-epoch-wide"))
            return verifyEpochWide(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, from);
        return verifyEpochTree(gpa, a, args[2], args[3], args[4], try std.fmt.parseInt(u32, args[5], 10), min_work, from);
    }
    if (std.mem.eql(u8, cmd, "prove-chain") and args.len >= 7) {
        var max_m: ?usize = null;
        var specs: std.ArrayList(ChainSpec) = .empty;
        var i: usize = 5;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--max-m") and i + 1 < args.len) {
                max_m = try std.fmt.parseInt(usize, args[i + 1], 10);
                i += 2;
            } else {
                try specs.append(a, parseChainSpec(args[i]) catch usage());
                i += 1;
            }
        }
        return proveChain(gpa, a, args[2], args[3], args[4], max_m, specs.items);
    }
    if (std.mem.eql(u8, cmd, "verify-chain") and args.len >= 7) {
        var min_work: u256 = core_min_work;
        var unpinned = false;
        var specs: std.ArrayList(ChainSpec) = .empty;
        var i: usize = 5;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--min-work") and i + 1 < args.len) {
                min_work = try std.fmt.parseInt(u256, args[i + 1], 16);
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--unpinned")) {
                unpinned = true;
                i += 1;
            } else {
                try specs.append(a, parseChainSpec(args[i]) catch usage());
                i += 1;
            }
        }
        if (specs.items.len < 2) usage();
        return verifyChainCmd(gpa, a, args[2], args[3], args[4], min_work, unpinned, specs.items);
    }
    if (std.mem.eql(u8, cmd, "set-pass-model") and (args.len == 3 or (args.len == 5 and std.mem.eql(u8, args[3], "--per"))))
        return setPassModel(gpa, args[2], if (args.len == 5) try std.fmt.parseInt(u32, args[4], 10) else 23000);
    if (std.mem.eql(u8, cmd, "setup-vks") and args.len >= 4) {
        var max_m: ?usize = null;
        var weak = false;
        var specs: std.ArrayList(ChainSpec) = .empty;
        var i: usize = 3;
        while (i < args.len) {
            if (std.mem.eql(u8, args[i], "--max-m") and i + 1 < args.len) {
                max_m = try std.fmt.parseInt(usize, args[i + 1], 10);
                i += 2;
            } else if (std.mem.eql(u8, args[i], "--test-strength")) {
                weak = true;
                i += 1;
            } else {
                try specs.append(a, parseChainSpec(args[i]) catch usage());
                i += 1;
            }
        }
        if (specs.items.len == 0) usage();
        return setupVks(gpa, a, args[2], max_m, weak, specs.items);
    }
    if (std.mem.eql(u8, cmd, "join-demo") and args.len == 8)
        return joinDemo(gpa, a, args[2], try std.fmt.parseInt(u32, args[3], 10), args[4], try std.fmt.parseInt(u32, args[5], 10), try std.fmt.parseInt(u32, args[6], 10), args[7]);
    if (std.mem.eql(u8, cmd, "rebind-block") and args.len == 6) return rebindBlock(gpa, a, args[2], args[3], args[4], args[5]);
    if (std.mem.eql(u8, cmd, "rebind-forest") and args.len == 7) return rebindForest(gpa, a, args[2], args[3], args[4], args[5], args[6]);
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

/// The epoch layers' pinned production VKs (`vk/epoch/`), by kind. A VK names the circuits a proof
/// must be from; one read from the prover's files could name a circuit that checks nothing, so the
/// epoch verifiers accept only these (or any, with `--unpinned`, for tests). Each is remade from
/// public inputs (the forest, one block proof per size key, the circuit programs in this binary) by
/// `chainproof setup-vks`, byte for byte.
const PinnedVk = struct { name: []const u8, bytes: []const u8 };
const VkKind = enum { block, tree, root, join };
const pinned_vks = struct {
    const block = [_]PinnedVk{};
    const tree = [_]PinnedVk{
        .{ .name = "vk/epoch/tree-935001-945000.vk", .bytes = @embedFile("vk:epoch/tree-935001-945000") },
        .{ .name = "vk/epoch/tree-945001-972500.vk", .bytes = @embedFile("vk:epoch/tree-945001-972500") },
    };
    // Both mainnet epochs' standalone roots (16 children, a previous set, one node shape).
    const root = [_]PinnedVk{
        .{ .name = "vk/epoch/root-16-prev.vk", .bytes = @embedFile("vk:epoch/root-16-prev") },
    };
    const join = [_]PinnedVk{
        .{ .name = "vk/epoch/join-935001-972500.vk", .bytes = @embedFile("vk:epoch/join-935001-972500") },
    };
};

fn pinnedOf(kind: VkKind) []const PinnedVk {
    return switch (kind) {
        .block => &pinned_vks.block,
        .tree => &pinned_vks.tree,
        .root => &pinned_vks.root,
        .join => &pinned_vks.join,
    };
}

/// The pinned VK equal to `bytes`, if any.
fn pinnedName(kind: VkKind, bytes: []const u8) ?[]const u8 {
    for (pinnedOf(kind)) |p| if (std.mem.eql(u8, p.bytes, bytes)) return p.name;
    return null;
}

/// Reads the `kind` VK at `path` and accepts it only when it is a pinned one (`unpinned`: any, said so).
fn readPinnedVk(a: std.mem.Allocator, kind: VkKind, path: []const u8, unpinned: bool) ![]const u8 {
    const bytes = try S.readFile(a, path);
    if (pinnedName(kind, bytes)) |name| {
        std.debug.print("{s} VK {s}: pinned ({s})\n", .{ @tagName(kind), path, name });
        return bytes;
    }
    if (unpinned) {
        std.debug.print("{s} VK {s}: NOT PINNED, accepted by --unpinned (tests only: it does not fix the circuits)\n", .{ @tagName(kind), path });
        return bytes;
    }
    std.debug.print("REJECTED: {s} VK {s} is not a pinned production VK (vk/epoch/; --unpinned for tests)\n", .{ @tagName(kind), path });
    return error.VkNotPinned;
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
    const b = try BS.buildFull(a, raw, undo, ctx, .{ .auto = true });
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

const ER = sb.block.epoch_run;
const SizeChoice = ER.Size;

/// An epoch's start: genesis, or block `height` from the coin set after `height − 1` (`prev_set`).
const EpochFrom = struct {
    height: u32 = 0,
    prev_set: ?[]const u8 = null,
    /// prove-epoch size profile: by size (default: tiered from 2^12, uniform below), or forced with
    /// `--uniform` / `--tiered` (D-045).
    size: SizeChoice = .auto,
    /// prove-epoch-tree `--test-strength`: the block proofs were made at test strength.
    weak: bool = false,
    /// verify-epoch-tree/-wide/-root `--unpinned`: accept VKs that are not pinned (tests).
    unpinned: bool = false,
    /// verify-epoch `--jobs`: threads verifying block proofs (default: the CPU count).
    jobs: ?u32 = null,
    /// prove-epoch-root `--set-digests <prev> <fin>`: the sets' digests (hex; `-` for no previous set)
    /// instead of scanning the set files (a pod without them).
    digests: ?struct { prev: ?[32]u8, fin: [32]u8 } = null,
};

fn parseDigest(hex: []const u8) ![32]u8 {
    var d: [32]u8 = undefined;
    if (hex.len != 64) return error.BadDigest;
    _ = try std.fmt.hexToBytes(&d, hex);
    return d;
}

fn proveEpoch(gpa: std.mem.Allocator, a: std.mem.Allocator, headers_path: []const u8, dir: []const u8, to: u32, chain_path: []const u8, weak: bool, from: EpochFrom) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    const all = try loadHeaderFile(a, headers_path);
    const ep = try ER.load(a, all, @intCast(n), dir, .{ .height = from.height, .prev_set = from.prev_set }, to);
    const airs = try BS.parseAirs(a);
    const fri = blockFri(weak);
    const pdir = try std.fmt.allocPrint(a, "{s}/proofs", .{dir});
    std.fs.cwd().makePath(pdir) catch {};
    var timer = try std.time.Timer.start();
    for (0..ep.count()) |i| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const ba = arena.allocator();
        const hh: u32 = from.height + @as(u32, @intCast(i));
        const b = try ep.build(ba, i, from.size, false);
        const proof = try PF.prove(ba, &airs, &b, fri);
        try ep.writeProof(ba, i, try ep.encode(ba, i, &b, proof));
        if (hh % 50 == 0 or hh == to) std.debug.print("block {d}: proved ({d:.0}s so far)\n", .{ hh, secs(timer.read()) });
    }
    std.debug.print("epoch {d}..{d}: {d} block proofs, coin set of {d} coins written\n", .{ from.height, to, ep.count(), ep.fin.?.count });
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
    const init = try ER.loadInit(gpa, .{ .height = from.height, .prev_set = from.prev_set });
    const airs = try BS.parseAirs(a);
    const nb = to - from.height + 1;
    var roots = PF.PreRoots{ .airs = &airs, .fri = blockFri(weak) };
    // Only each proof's public inputs are kept: a proof file is decoded and verified in its own arena,
    // on `jobs` threads (the proofs are independent; the epoch's checks below use them in order).
    var w = VerifyWork{
        .gpa = gpa,
        .dir = dir,
        .from = from.height,
        .headers = s.headers,
        .t = s.t,
        .airs = &airs,
        .roots = &roots,
        .pubs = try a.alloc([BS.N_PUB]M31, nb),
        .hashes = try a.alloc([32]u8, nb),
        .commits = try a.alloc([32]u8, nb),
    };
    const jobs = @min(from.jobs orelse @as(u32, @intCast(std.Thread.getCpuCount() catch 1)), nb);
    const threads = try a.alloc(std.Thread, jobs - 1);
    for (threads) |*th| th.* = try std.Thread.spawn(.{}, VerifyWork.run, .{&w});
    w.run();
    for (threads) |th| th.join();
    if (w.err) |e| {
        std.debug.print("REJECTED: block {d}: {s}\n", .{ w.err_height, @errorName(e) });
        return e;
    }
    const pubs = w.pubs;
    const hashes = w.hashes;
    const commits = w.commits;
    var nin: u64 = 0;
    for (pubs) |*p| nin += p[sb.block.coin.PUB_NIN].toU32();
    const set_path = try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to });
    const fin_info = try SF.scan(gpa, set_path, null);
    const ch = EP.challenge(EP.seedFrom(from.height, to, if (init.info) |x| x.digest else null, fin_info.digest, hashes, commits));
    var sum = @import("stwo_core").fields.qm31.QM31.zero();
    for (pubs, 0..) |p, i| {
        try EP.checkPubs(&p, ch, from.height + @as(u32, @intCast(i)));
        sum = sum.add(EP.partialSum(&p));
    }
    std.debug.print("{d} block proofs verified on {d} threads, challenge recomputed from their hashes and commitments ({d:.1}s)\n", .{ nb, jobs, secs(timer.lap()) });
    const init_count: u64 = if (init.info) |x| x.count else 0;
    // Events below p: initial + created + spent + final (the creations are at most the outputs).
    if (nin + fin_info.count + init_count >= 1 << 30) return error.EpochTooLarge;
    // The initial set counts as created (Spec/UtxoEpochFrom.lean).
    if (init.info) |x| sum = sum.add(try sumSet(gpa, from.prev_set.?, ch, x.digest));
    const fin = try sumSet(gpa, set_path, ch, fin_info.digest);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    if (init.info) |x| std.debug.print("  from the set after block {d}: {d} coins, hash_serialized {x}\n", .{ from.height - 1, x.count, x.hash });
    std.debug.print("VERIFIED epoch {d}..{d}: the coin set after block {d} is {d} coins ({d} inputs spent in the epoch)\n", .{ from.height, to, to, fin_info.count, nin });
    std.debug.print("  total amount     {d} sat\n", .{fin_info.amount});
    std.debug.print("  hash_serialized  {x}  (Core's HASH_SERIALIZED of this set)\n", .{fin_info.hash});
}

const SF = sb.block.set_file;
const M31 = @import("stwo_core").fields.m31.M31;

/// verify-epoch's block proofs, shared by its threads: each takes the next index, checks that proof
/// (window, STARK, statement) in its own arena and fills that index's slots. The first failure (the
/// lowest height among those seen) stops the others from taking more.
const VerifyWork = struct {
    gpa: std.mem.Allocator,
    dir: []const u8,
    from: u32,
    headers: usize,
    t: HT.Words,
    airs: *const [BS.N_COMP]sb.air.ir.Air,
    roots: *PF.PreRoots,
    pubs: [][BS.N_PUB]M31,
    hashes: [][32]u8,
    commits: [][32]u8,
    next: std.atomic.Value(usize) = .init(0),
    failed: std.atomic.Value(bool) = .init(false),
    mutex: std.Thread.Mutex = .{},
    err: ?anyerror = null,
    err_height: u32 = 0,

    fn run(w: *VerifyWork) void {
        while (!w.failed.load(.acquire)) {
            const i = w.next.fetchAdd(1, .monotonic);
            if (i >= w.pubs.len) return;
            const hh = w.from + @as(u32, @intCast(i));
            w.one(i, hh) catch |e| {
                w.mutex.lock();
                defer w.mutex.unlock();
                if (w.err == null or hh < w.err_height) {
                    w.err = e;
                    w.err_height = hh;
                }
                w.failed.store(true, .release);
            };
        }
    }

    fn one(w: *VerifyWork, i: usize, hh: u32) !void {
        var arena = std.heap.ArenaAllocator.init(w.gpa);
        defer arena.deinit();
        const pa = arena.allocator();
        const f = try PF.decode(pa, try S.readFile(pa, try pathOf(pa, w.dir, "proofs", hh, "sbblock")));
        const window = try PF.checkWindow(pa, &f, w.headers, w.t);
        try PF.verifyStarkRoots(pa, w.gpa, w.roots, &f);
        const st = try PF.checkPubs(&f.pubs, window);
        if (st.height != hh) return error.WrongHeight;
        var h1: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(&window[window.len - 1], &h1, .{});
        std.crypto.hash.sha2.Sha256.hash(&h1, &w.hashes[i], .{});
        w.commits[i] = st.commitment;
        w.pubs[i] = f.pubs;
    }
};

/// A set file's fractions under `ch` (a second, streamed pass); its digest must be the one the challenge
/// was derived from (the file did not change between the passes).
fn sumSet(gpa: std.mem.Allocator, path: []const u8, ch: sb.block.coin.Challenge, digest: [32]u8) !@import("stwo_core").fields.qm31.QM31 {
    const r = try SF.sum(gpa, path, ch);
    if (!std.mem.eql(u8, &r.digest, &digest)) return error.SetChanged;
    return r.sum;
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
    const bvk = try BF.Vk.decode(try readPinnedVk(a, .block, try std.fmt.allocPrint(a, "{s}/blockvk.bin", .{dir}), from.unpinned));
    var forest = try BF.Forest.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/forest-{d}.bin", .{ dir, to })));
    defer for (forest.roots) |*r| r.proved.proof.deinit();
    if (forest.from != from.height or forest.to != to) return error.WrongEpoch;
    const init = try ER.loadInit(gpa, .{ .height = from.height, .prev_set = from.prev_set });
    const set_path = try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to });
    const fin_info = try SF.scan(gpa, set_path, null);
    const v = try BF.verifyForest(gpa, a, tables, &bvk, &forest, s.headers, s.t, if (init.info) |x| x.digest else null, fin_info.digest);
    std.debug.print("{d} recursion trees verified: blocks {d}..{d}, the challenge from the seed over their roots, the block hashes the chain's ({d:.1}s)\n", .{ forest.roots.len, from.height, to, secs(timer.lap()) });
    const init_count: u64 = if (init.info) |x| x.count else 0;
    if (v.nin + fin_info.count + init_count >= 1 << 30) return error.EpochTooLarge;
    var sum = v.sum;
    if (init.info) |x| sum = sum.add(try sumSet(gpa, from.prev_set.?, v.challenge, x.digest));
    const fin = try sumSet(gpa, set_path, v.challenge, fin_info.digest);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    std.debug.print("VERIFIED epoch {d}..{d} (recursion): the coin set after block {d} is {d} coins ({d} inputs spent)\n", .{ from.height, to, to, fin_info.count, v.nin });
    std.debug.print("  total amount     {d} sat\n", .{fin_info.amount});
    std.debug.print("  hash_serialized  {x}\n", .{fin_info.hash});
}

const BT = sb.recursion.block_tree;
const br_mod = sb.recursion.block_rec;

fn proveEpochWide(gpa: std.mem.Allocator, a: std.mem.Allocator, headers_path: []const u8, dir: []const u8, to: u32, chain_path: []const u8, from: EpochFrom) !void {
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    const n = c.headers();
    c.deinit();
    const all = try loadHeaderFile(a, headers_path);
    if (to >= n or all.len < n) return error.HeightBeyondChain;
    if (from.height > to) return error.EmptyEpoch;
    const nb = to - from.height + 1;
    var timer = try std.time.Timer.start();
    const keys = try BT.epochKeys(a, .{ .dir = dir }, from.height, nb);
    const airs = try BS.parseAirs(a);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    const bfri = blockFri(from.weak);
    var roots = PF.PreRoots{ .airs = &airs, .fri = bfri };
    var shapes = try BT.Shapes.init(gpa, &tables.table, try BT.leafStart(gpa, a, &airs, keys.firsts, bfri, &roots), BT.circuitFri());
    defer shapes.deinit(gpa);
    const tvk = try BT.loadOrSetupVk(gpa, a, tables, &airs, keys.firsts, bfri, &roots, &shapes, .{ .dir = dir });
    std.debug.print("setup: {d} block sizes, leaves at 2^{d}, nodes at 2^{d}; tree VK in {d:.1}s\n", .{ keys.firsts.len, tvk.leaf_log, tvk.node_log, secs(timer.lap()) });
    const leaves = try a.alloc(HT.Words, n);
    for (leaves, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
    var prover: BT.CpuProver = .{ .gpa = gpa, .tables = tables, .shapes = &shapes, .airs = &airs, .bfri = bfri, .roots = &roots };
    const forest = try BT.proveForest(&prover, gpa, a, .{ .dir = dir }, from.height, keys.logs, leaves);
    defer for (forest.roots) |*r| r.proved.proof.deinit();
    const out = try std.fmt.allocPrint(a, "{s}/forestk-{d}.bin", .{ dir, to });
    try S.writeFileAtomic(out, try forest.encode(a));
    std.debug.print("epoch {d}..{d}: {d} blocks in {d} recursion trees (wide nodes), written to {s} ({d:.0}s)\n", .{ from.height, to, nb, forest.roots.len, out, secs(timer.read()) });
}

const ERoot = sb.recursion.epoch_root;

/// The epoch root over `prove-epoch-wide`'s forest: one-block roots lifted (a one-child node), the root
/// circuit checked against the native digest, then proved and verified on the CPU (Mac-sized epochs; a
/// GPU driver for real ones). Needs both sets' digests: `<dir>/set-<to>.bin` and `--from`'s set.
/// An epoch's root inputs: its shapes, forest, and the forest's roots as node-shaped children (one-block
/// roots lifted), with the epoch's set digests. Owned by `a` (pointers stay valid); `deinit` frees the
/// shapes and the proofs.
const RootInputs = struct {
    shapes: BT.Shapes,
    forest: BT.Forest,
    lifted: []br_mod.Proved,
    n_lifted: usize,
    children: []*const br_mod.Proved,
    ep: ERoot.Epoch,
    logs: []const u8,

    fn deinit(self: *RootInputs, gpa: std.mem.Allocator) void {
        for (self.lifted[0..self.n_lifted]) |*p| p.proof.deinit();
        for (self.forest.roots) |*r| r.proved.proof.deinit();
        self.shapes.deinit(gpa);
    }
};

fn rootInputs(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const L.Tables, dir: []const u8, to: u32, from: EpochFrom) !*RootInputs {
    var timer = try std.time.Timer.start();
    // The size keys as the forest records them, and one block proof per key.
    const forest = try BT.Forest.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/forestk-{d}.bin", .{ dir, to })));
    if (forest.from != from.height or forest.to != to or forest.logs.len != to - from.height + 1) return error.WrongEpoch;
    const keys = .{ .logs = forest.logs, .firsts = try BT.firstsOf(a, .{ .dir = dir }, from.height, forest.logs) };
    const airs = try a.create([BS.N_COMP]sb.air.ir.Air);
    airs.* = try BS.parseAirs(a);
    const bfri = blockFri(from.weak);
    const roots = try a.create(PF.PreRoots);
    roots.* = .{ .airs = airs, .fri = bfri };
    const ri = try a.create(RootInputs);
    ri.shapes = try BT.Shapes.init(gpa, &tables.table, try BT.leafStart(gpa, a, airs, keys.firsts, bfri, roots), BT.circuitFri());
    errdefer ri.shapes.deinit(gpa);
    ri.logs = keys.logs;
    ri.forest = forest;
    ri.ep = if (from.digests) |d| blk: {
        if ((d.prev != null) != (from.height != 0)) return error.PrevSetRequired;
        break :blk .{ .from = from.height, .to = to, .prev = d.prev, .fin = d.fin };
    } else blk: {
        const init = try ER.loadInit(gpa, .{ .height = from.height, .prev_set = from.prev_set });
        const fin_info = try SF.scan(gpa, try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to }), null);
        break :blk .{ .from = from.height, .to = to, .prev = if (init.info) |x| x.digest else null, .fin = fin_info.digest };
    };
    std.debug.print("epoch {d}..{d}: {d} forest roots; set digests {s} ({d:.1}s)\n", .{ from.height, to, ri.forest.roots.len, if (from.digests != null) "given" else "scanned", secs(timer.lap()) });
    // One-block roots are leaf-shaped: lift them to the node shape (the slice never moves).
    ri.lifted = try a.alloc(br_mod.Proved, ri.forest.roots.len);
    ri.n_lifted = 0;
    ri.children = try a.alloc(*const br_mod.Proved, ri.forest.roots.len);
    for (ri.forest.roots, ri.children) |*r, *c| {
        if (r.k == 0) {
            const view = ri.shapes.nodeView(.over_leaves);
            ri.lifted[ri.n_lifted] = try sb.recursion.block_node_k.prove(gpa, a, tables, 0, &view, &.{&r.proved});
            c.* = &ri.lifted[ri.n_lifted];
            ri.n_lifted += 1;
            std.debug.print("  root at {d} (one block) lifted ({d:.1}s)\n", .{ r.x, secs(timer.lap()) });
        } else c.* = &r.proved;
    }
    return ri;
}

const EJ = sb.recursion.epoch_join;

/// `join-demo <dir1> <to1> <dir2> <from2> <to2> <prev-set-2>` (Mac test): epoch 0..to1 (from genesis)
/// and epoch from2..to2 (from the set after from2 − 1) as roots at one shape, and the base join over
/// them: satisfied, output digest = the native join's, proved and verified.
fn joinDemo(gpa: std.mem.Allocator, a: std.mem.Allocator, dir1: []const u8, to1: u32, dir2: []const u8, from2: u32, to2: u32, prev2: []const u8) !void {
    var timer = try std.time.Timer.start();
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    const r1 = try rootInputs(gpa, a, tables, dir1, to1, .{});
    defer r1.deinit(gpa);
    const r2 = try rootInputs(gpa, a, tables, dir2, to2, .{ .height = from2, .prev_set = prev2 });
    defer r2.deinit(gpa);
    if (!std.meta.eql(r1.shapes.node.target, r2.shapes.node.target)) return error.NodeShapesDiffer;
    const fri = BT.circuitFri();
    const nsh = &r1.shapes.node.shared;
    // The chain's root shape: both roots' natural sizes, elementwise.
    const target = (try ERoot.naturalSize(gpa, &tables.table, r1.children.len, false, nsh)).elementwiseMax(try ERoot.naturalSize(gpa, &tables.table, r2.children.len, true, nsh));
    var p1 = try ERoot.proveRootAt(gpa, a, tables, nsh, fri, r1.children, r1.ep, true, target);
    defer if (p1.proof) |*p| p.deinit();
    var p2 = try ERoot.proveRootAt(gpa, a, tables, nsh, fri, r2.children, r2.ep, true, target);
    defer if (p2.proof) |*p| p.deinit();
    std.debug.print("both roots proved at one shape ({d:.1}s)\n", .{secs(timer.lap())});
    var rshared = try EJ.sharedFor(gpa, target, fri);
    defer rshared.deinit(gpa);
    const left = try EJ.childOf(a, &p1.proof.?, &rshared, .{ .root = .{ .key = p1.key, .ep = r1.ep, .rest = p1.rest } });
    const right = try EJ.childOf(a, &p2.proof.?, &rshared, .{ .root = .{ .key = p2.key, .ep = r2.ep, .rest = p2.rest } });
    var j = try EJ.proveJoin(gpa, a, tables, .base_genesis, left, p1.proof.?.circuit_hash, right, p2.proof.?.circuit_hash, fri, null, true);
    defer if (j.proof) |*p| p.deinit();
    std.debug.print("base join over epochs 0..{d} and {d}..{d}: {d} vars, satisfied, output digest = the native one; proved and verified ({d:.1}s), {d} bytes\n", .{ to1, from2, to2, j.n_vars, secs(timer.lap()), j.proof.?.bytes.len });
    std.debug.print("  range {d}..{d}, start set genesis, end set {any}\n", .{ j.open.a, j.open.b, j.open.end });
}

/// One epoch of a chain on the command line: `<dir>:<to>` (from genesis) or
/// `<dir>:<to>:<from>:<prev-set.bin>`, optionally followed by `#<prev-hex|->,<fin-hex>` (the sets'
/// digests, for a prover without the set files).
const ChainSpec = struct { dir: []const u8, to: u32, from: EpochFrom };

fn parseChainSpec(s: []const u8) !ChainSpec {
    var body = s;
    var digests: ?[]const u8 = null;
    if (std.mem.indexOfScalar(u8, s, '#')) |h| {
        body = s[0..h];
        digests = s[h + 1 ..];
    }
    var it = std.mem.splitScalar(u8, body, ':');
    const dir = it.next() orelse return error.BadSpec;
    const to = try parseU32(it.next() orelse return error.BadSpec);
    var from: EpochFrom = .{};
    if (it.next()) |f| {
        from.height = try parseU32(f);
        from.prev_set = it.next() orelse return error.BadSpec;
    }
    if (it.next() != null) return error.BadSpec;
    if (digests) |d| {
        var dit = std.mem.splitScalar(u8, d, ',');
        const p = dit.next() orelse return error.BadSpec;
        const f = dit.next() orelse return error.BadSpec;
        from.digests = .{ .prev = if (std.mem.eql(u8, p, "-")) null else try parseDigest(p), .fin = try parseDigest(f) };
    }
    return .{ .dir = dir, .to = to, .from = from };
}

/// The public part of an epoch's root over `ri`'s children: the children (aligned subtrees, block-hash
/// roots, paths), the summed partial sum and input count, the challenge.
fn rootHead(a: std.mem.Allocator, ri: *const RootInputs) !ERoot.Head {
    const n = ri.children.len;
    const kids = try a.alloc(ERoot.Child, n);
    for (kids, ri.forest.roots) |*k, fr| {
        k.* = .{ .x = fr.x, .k = fr.k, .hash_root = undefined, .path = fr.path };
        @memcpy(&k.hash_root, fr.proved.sum[19..35]);
    }
    const hs = try a.alloc([8]u32, n);
    const ks = try a.alloc([8]u32, n);
    const ss = try a.alloc(br_mod.Summary, n);
    for (ri.children, hs, ks, ss) |c, *h, *k, *x| {
        h.* = c.proof.circuit_hash;
        k.* = c.key;
        x.* = c.sum;
    }
    const want = ERoot.expected(hs, ks, ss, ri.ep);
    var head: ERoot.Head = .{ .from = ri.ep.from, .to = ri.ep.to, .logs = ri.logs, .children = kids, .s = want.s, .nin = want.nin, .challenge = undefined };
    @memcpy(&head.challenge, ri.children[0].sum[7..19]);
    return head;
}

/// The two heads encode to the same bytes.
fn sameHead(a: std.mem.Allocator, x: *const ERoot.Head, y: *const ERoot.Head) !bool {
    var ex: S.Enc = .{ .a = a };
    var ey: S.Enc = .{ .a = a };
    try x.encode(&ex);
    try y.encode(&ey);
    return std.mem.eql(u8, ex.buf.items, ey.buf.items);
}

/// `prove-chain <vk> <file.sbchain> <out-dir> [--max-m M] <epoch>...` (epochs as `ChainSpec`, in chain
/// order, each with `prove-epoch-wide`'s forest and tree VK in its dir): the chain's shapes (the root
/// shape for up to `M` children, default the most any epoch has) and VK (`<out>/joinvk.bin`), each
/// epoch's root at the root shape (`<out>/root-<to>.bin`, reused when present), then the joins, one
/// epoch at a time: `<out>/chain-<to>.bin` after each, itself a chain proof up to that epoch.
fn proveChain(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, out: []const u8, max_m_opt: ?usize, specs: []const ChainSpec) !void {
    var timer = try std.time.Timer.start();
    if (specs.len < 2) return error.NeedTwoEpochs;
    try std.fs.cwd().makePath(out);
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    const n = specs.len;
    const ris = try a.alloc(*RootInputs, n);
    var n_ri: usize = 0;
    defer for (ris[0..n_ri]) |ri| ri.deinit(gpa);
    const tvks = try a.alloc(BT.Vk, n);
    var max_m: usize = 0;
    for (specs, ris, tvks) |sp, *ri, *tvk| {
        ri.* = try rootInputs(gpa, a, tables, sp.dir, sp.to, sp.from);
        n_ri += 1;
        tvk.* = try BT.Vk.decode(try S.readFile(a, try std.fmt.allocPrint(a, "{s}/treevk.bin", .{sp.dir})));
        max_m = @max(max_m, ri.*.children.len);
    }
    if (max_m_opt) |m| {
        if (m < max_m) return error.MaxMTooSmall;
        max_m = m;
    }
    const fri = BT.circuitFri();
    // The node configurations, each once.
    var shareds: std.ArrayList(*const @TypeOf(ris[0].shapes.node.shared)) = .empty;
    var tags: std.ArrayList([8]u32) = .empty;
    for (ris, tvks) |ri, *tvk| {
        const tag = EJ.nodeTag(tvk);
        if (for (tags.items) |t| {
            if (std.mem.eql(u32, &t, &tag)) break true;
        } else false) continue;
        try tags.append(a, tag);
        try shareds.append(a, &ri.shapes.node.shared);
    }
    const rtarget = try EJ.rootTarget(gpa, &tables.table, max_m, shareds.items);
    var js = try EJ.Shapes.init(gpa, &tables.table, rtarget, fri);
    defer js.deinit(gpa);
    const setups = try a.alloc(EJ.EpochSetup, n);
    for (setups, ris, tvks) |*st, ri, *tvk| st.* = .{ .tshapes = &ri.shapes, .tvk = tvk, .m = ri.children.len, .prev = ri.ep.prev != null };
    const jvk = try EJ.setupVk(gpa, a, tables, &js, setups);
    try S.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/joinvk.bin", .{out}), try jvk.encode(a));
    std.debug.print("chain shapes: roots (up to {d} children) at 2^{d}, joins at 2^{d}; {d} node shape(s); join VK {s}/joinvk.bin ({d:.1}s)\n", .{ max_m, jvk.root_log, jvk.join_log, tags.items.len, out, secs(timer.lap()) });
    // The epoch roots at the root shape.
    const files = try a.alloc(ERoot.File, n);
    var n_files: usize = 0;
    defer for (files[0..n_files]) |*f| f.proof.deinit();
    const opens = try a.alloc(EJ.RootOpen, n);
    for (ris, tvks, files, opens, 0..) |ri, *tvk, *f, *o, i| {
        const entry = try jvk.rootFor(ri.children.len, ri.ep.prev != null, EJ.nodeTag(tvk));
        const path = try std.fmt.allocPrint(a, "{s}/root-{d}.bin", .{ out, ri.ep.to });
        const head = try rootHead(a, ri);
        // A root file already there (this run's, or the epoch's own root when it is at the chain's
        // root shape) is reused when its public part is this run's (the paths in this chain file's
        // header tree included); any other is proved again.
        const reused = if (S.readFile(a, path)) |bytes| blk: {
            var g = ERoot.File.decode(gpa, a, bytes) catch break :blk false;
            if (std.mem.eql(u32, &g.proof.request.preprocessed_root, &entry.id.root) and std.mem.eql(u32, &g.proof.circuit_hash, &entry.id.hash) and try sameHead(a, &g.head, &head)) {
                f.* = g;
                break :blk true;
            }
            g.proof.deinit();
            std.debug.print("  epoch {d}: {s} is not at the chain's root shape or not over these inputs (paths: this chain file's): proving again\n", .{ i, path });
            break :blk false;
        } else |_| false;
        if (reused) {
            n_files += 1;
            std.debug.print("  epoch {d}: root {s} (reused)\n", .{ i, path });
        } else {
            const r = try ERoot.proveRootAt(gpa, a, tables, &ri.shapes.node.shared, fri, ri.children, ri.ep, true, js.root.target);
            f.* = .{ .head = head, .proof = r.proof.? };
            n_files += 1;
            try S.writeFileAtomic(path, try f.encode(a));
            std.debug.print("  epoch {d}: {d}..{d}, {d} children, root proved at the root shape, {s} ({d:.1}s)\n", .{ i, ri.ep.from, ri.ep.to, ri.children.len, path, secs(timer.lap()) });
        }
        const op = try ERoot.openHead(a, tvk, entry.lift.hash, &f.head, ri.ep, s.headers, s.t);
        o.* = .{ .key = op.key, .ep = ri.ep, .rest = op.rest };
    }
    // The joins, one epoch at a time.
    const heads = try a.alloc(ERoot.Head, n);
    for (heads, files) |*h, f| h.* = f.head;
    var left = try EJ.childOf(a, &files[0].proof, &js.root.shared, .{ .root = opens[0] });
    var lh = files[0].proof.circuit_hash;
    var prev_join: ?L.CircuitProof = null;
    defer if (prev_join) |*p| p.deinit();
    for (1..n) |i| {
        const v = EJ.variantAt(i, ris[0].ep);
        left.shared = js.leftShared(v);
        const right = try EJ.childOf(a, &files[i].proof, &js.root.shared, .{ .root = opens[i] });
        const j = try EJ.proveJoin(gpa, a, tables, v, left, lh, right, files[i].proof.circuit_hash, fri, js.join.target, true);
        const cf: EJ.ChainFile = .{ .heads = heads[0 .. i + 1], .proof = j.proof.? };
        const path = try std.fmt.allocPrint(a, "{s}/chain-{d}.bin", .{ out, ris[i].ep.to });
        const bytes = try cf.encode(a);
        try S.writeFileAtomic(path, bytes);
        std.debug.print("  join {d} ({s}): blocks {d}..{d} in one proof, {s}, {d} bytes ({d:.1}s)\n", .{ i, @tagName(v), j.open.a, j.open.b, path, bytes.len, secs(timer.lap()) });
        if (prev_join) |*p| p.deinit();
        prev_join = j.proof.?;
        left = try EJ.childOf(a, &prev_join.?, &js.join.shared, .{ .join = j.open });
        lh = prev_join.?.circuit_hash;
    }
}

/// `setup-vks <out-dir> [--max-m M] [--test-strength] <dir>:<to>[:<from>:<prev-set>]...`: the epoch
/// layers' VKs remade from public inputs alone: each epoch's forest (its size keys) and one block
/// proof per key from `<dir>/proofs` (as prove-chain reads them), and the circuit programs in this
/// binary. No proof is made. Writes `<out>/tree-<to>.vk` and `<out>/root-<to>.vk` per epoch and, for
/// two or more epochs, `<out>/join.vk` (the chain's shapes as prove-chain sets them), and says which
/// equal a pinned VK (vk/epoch/): this is how a pinned VK is checked to be the honest circuits'.
fn setupVks(gpa: std.mem.Allocator, a: std.mem.Allocator, out: []const u8, max_m_opt: ?usize, weak: bool, specs: []const ChainSpec) !void {
    var timer = try std.time.Timer.start();
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    try std.fs.cwd().makePath(out);
    const airs = try a.create([BS.N_COMP]sb.air.ir.Air);
    airs.* = try BS.parseAirs(a);
    const bfri = blockFri(weak);
    const roots = try a.create(PF.PreRoots);
    roots.* = .{ .airs = airs, .fri = bfri };
    const n = specs.len;
    const shapes = try a.alloc(BT.Shapes, n);
    var n_shapes: usize = 0;
    defer for (shapes[0..n_shapes]) |*sh| sh.deinit(gpa);
    const tvks = try a.alloc(BT.Vk, n);
    const setups = try a.alloc(EJ.EpochSetup, n);
    var max_m: usize = 0;
    var all_pinned = true;
    for (specs, shapes, tvks, setups) |sp, *sh, *tvk, *st| {
        const forest = try BT.Forest.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/forestk-{d}.bin", .{ sp.dir, sp.to })));
        defer for (forest.roots) |*r| r.proved.proof.deinit();
        if (forest.from != sp.from.height or forest.to != sp.to) return error.WrongEpoch;
        const firsts = try BT.firstsOf(a, .{ .dir = sp.dir }, sp.from.height, forest.logs);
        const su = try BT.setup(gpa, a, tables, airs, firsts, bfri, roots);
        sh.* = su.shapes;
        n_shapes += 1;
        tvk.* = su.vk;
        const m = forest.roots.len;
        const prev = sp.from.height != 0;
        st.* = .{ .tshapes = sh, .tvk = tvk, .m = m, .prev = prev };
        max_m = @max(max_m, m);
        all_pinned = try writeVk(a, .tree, try std.fmt.allocPrint(a, "{s}/tree-{d}.vk", .{ out, sp.to }), try tvk.encode(a)) and all_pinned;
        const rvk = try ERoot.setupVk(gpa, tables, sh, m, prev);
        all_pinned = try writeVk(a, .root, try std.fmt.allocPrint(a, "{s}/root-{d}.vk", .{ out, sp.to }), try rvk.encode(a)) and all_pinned;
        std.debug.print("  epoch {d}..{d}: {d} size keys, {d} children ({d:.1}s)\n", .{ sp.from.height, sp.to, firsts.len, m, secs(timer.lap()) });
    }
    if (n >= 2) {
        if (max_m_opt) |m| {
            if (m < max_m) return error.MaxMTooSmall;
            max_m = m;
        }
        // As prove-chain: the node configurations, each once; the root and join shapes; the VK.
        var shareds: std.ArrayList(*const @TypeOf(shapes[0].node.shared)) = .empty;
        var tags: std.ArrayList([8]u32) = .empty;
        for (shapes, tvks) |*sh, *tvk| {
            const tag = EJ.nodeTag(tvk);
            if (for (tags.items) |t| {
                if (std.mem.eql(u32, &t, &tag)) break true;
            } else false) continue;
            try tags.append(a, tag);
            try shareds.append(a, &sh.node.shared);
        }
        var js = try EJ.Shapes.init(gpa, &tables.table, try EJ.rootTarget(gpa, &tables.table, max_m, shareds.items), BT.circuitFri());
        defer js.deinit(gpa);
        const jvk = try EJ.setupVk(gpa, a, tables, &js, setups);
        all_pinned = try writeVk(a, .join, try std.fmt.allocPrint(a, "{s}/join.vk", .{out}), try jvk.encode(a)) and all_pinned;
        std.debug.print("  chain: roots (up to {d} children) at 2^{d}, joins at 2^{d} ({d:.1}s)\n", .{ max_m, jvk.root_log, jvk.join_log, secs(timer.lap()) });
    }
    std.debug.print("{s}\n", .{if (all_pinned) "every VK remade equals a pinned one" else "some VKs remade are not pinned (see above)"});
}

/// Writes a remade VK and says whether it is a pinned one.
fn writeVk(a: std.mem.Allocator, kind: VkKind, path: []const u8, bytes: []const u8) !bool {
    _ = a;
    try S.writeFileAtomic(path, bytes);
    if (pinnedName(kind, bytes)) |name| {
        std.debug.print("{s} VK {s}: equals the pinned {s}\n", .{ @tagName(kind), path, name });
        return true;
    }
    std.debug.print("{s} VK {s}: not pinned\n", .{ @tagName(kind), path });
    return false;
}

/// `set-pass-model <set.bin> [--per N]`: the coin-set pass's native model (`block.set_pass`) over a set
/// file in segments of N records (default 23,000): its facts, which must equal `scan`'s, and its sizing.
fn setPassModel(gpa: std.mem.Allocator, path: []const u8, per: u32) !void {
    var timer = try std.time.Timer.start();
    const SP = sb.block.set_pass;
    const chs = [_]sb.block.coin.Challenge{sb.block.epoch.challenge(@splat(7))};
    const f = try SP.runFile(gpa, path, &chs, per);
    std.debug.print("{s}: {d} coins, amount {d} sat, highest coin at {d}\n", .{ path, f.count, f.amount, f.max_height });
    std.debug.print("  hash_serialized {x}\n  digest          {x}\n", .{ f.hash, f.digest });
    std.debug.print("  file {d} bytes ({d} Blake2s blocks), TxOutSer {d} bytes ({d} SHA-256 blocks); {d} segments of {d} records ({d:.1}s)\n", .{ f.file_bytes, f.b2_blocks, f.sha_bytes, f.sha_blocks, (f.count + per - 1) / per, per, secs(timer.lap()) });
}

/// `verify-chain <vk> <file.sbchain> <out-dir> <epoch>...`: the chain proof `<out>/chain-<to>.bin` (to:
/// the last epoch's) under `<out>/joinvk.bin`, each epoch's tree VK from its dir, and each epoch's
/// balance against its sets (the previous set given, the final `<dir>/set-<to>.bin`).
fn verifyChainCmd(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, out: []const u8, min_work: u256, unpinned: bool, specs: []const ChainSpec) !void {
    var timer = try std.time.Timer.start();
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) return error.InsufficientWork;
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    const jvk = try EJ.Vk.decode(a, try readPinnedVk(a, .join, try std.fmt.allocPrint(a, "{s}/joinvk.bin", .{out}), unpinned));
    var file = try EJ.ChainFile.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/chain-{d}.bin", .{ out, specs[specs.len - 1].to })));
    defer file.proof.deinit();
    const ins = try a.alloc(EJ.EpochIn, specs.len);
    const tvks = try a.alloc(BT.Vk, specs.len);
    const inits = try a.alloc(@TypeOf(try ER.loadInit(gpa, .{})), specs.len);
    const fins = try a.alloc(@TypeOf(try SF.scan(gpa, "", null)), specs.len);
    for (specs, ins, tvks, inits, fins) |sp, *in, *tvk, *init, *fin| {
        tvk.* = try BT.Vk.decode(try readPinnedVk(a, .tree, try std.fmt.allocPrint(a, "{s}/treevk.bin", .{sp.dir}), unpinned));
        init.* = try ER.loadInit(gpa, .{ .height = sp.from.height, .prev_set = sp.from.prev_set });
        fin.* = try SF.scan(gpa, try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ sp.dir, sp.to }), null);
        in.* = .{ .tvk = tvk, .ep = .{ .from = sp.from.height, .to = sp.to, .prev = if (init.info) |x| x.digest else null, .fin = fin.digest } };
    }
    const vs = try EJ.verifyChain(gpa, a, tables, &jvk, &file, ins, s.headers, s.t);
    std.debug.print("chain of epochs verified: ONE proof for blocks {d}..{d} ({d} epochs joined), the block hashes the chain's ({d:.1}s)\n", .{ specs[0].from.height, specs[specs.len - 1].to, specs.len, secs(timer.lap()) });
    for (specs, vs, inits, fins) |sp, v, init, fin| {
        const init_count: u64 = if (init.info) |x| x.count else 0;
        if (v.nin + fin.count + init_count >= 1 << 30) return error.EpochTooLarge;
        var sum = v.sum;
        if (init.info) |x| sum = sum.add(try sumSet(gpa, sp.from.prev_set.?, v.challenge, x.digest));
        const set_path = try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ sp.dir, sp.to });
        if (!sum.eql(try sumSet(gpa, set_path, v.challenge, fin.digest))) {
            std.debug.print("REJECTED: epoch {d}..{d}: the blocks' coin events do not end at its coin set\n", .{ sp.from.height, sp.to });
            return error.EpochUnbalanced;
        }
        std.debug.print("  epoch {d}..{d} balanced: {d} coins after block {d} ({d} inputs spent)\n", .{ sp.from.height, sp.to, fin.count, sp.to, v.nin });
    }
    const last = fins[fins.len - 1];
    std.debug.print("VERIFIED blocks {d}..{d} as one chain proof: the coin set after block {d} is {d} coins\n", .{ specs[0].from.height, specs[specs.len - 1].to, specs[specs.len - 1].to, last.count });
    std.debug.print("  total amount     {d} sat\n", .{last.amount});
    std.debug.print("  hash_serialized  {x}  (Core's HASH_SERIALIZED of this set)\n", .{last.hash});
}

fn proveEpochRoot(gpa: std.mem.Allocator, a: std.mem.Allocator, headers_path: []const u8, dir: []const u8, to: u32, chain_path: []const u8, from: EpochFrom) !void {
    _ = headers_path;
    _ = chain_path;
    var timer = try std.time.Timer.start();
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    const ri = try rootInputs(gpa, a, tables, dir, to, from);
    defer ri.deinit(gpa);
    const shapes = &ri.shapes;
    const forest = &ri.forest;
    const keys = .{ .logs = ri.logs };
    const ep = ri.ep;
    const children = ri.children;
    const ch = try ERoot.challengeOf(blk: {
        const sums = try a.alloc(br_mod.Summary, children.len);
        for (sums, children) |*s, c| s.* = c.sum;
        break :blk sums;
    }, ep);
    std.debug.print("  native challenge from the seed over the roots: gamma {any}\n", .{ch.gamma});
    var r = try ERoot.proveRoot(gpa, a, tables, &shapes.node.shared, BT.circuitFri(), children, ep, true);
    defer if (r.proof) |*p| p.deinit();
    std.debug.print("epoch root: {d} children, {d} vars, satisfied, output digest = the native one; proved and verified ({d:.1}s), {d} bytes\n", .{ children.len, r.n_vars, secs(timer.lap()), r.proof.?.bytes.len });
    const rvk = try ERoot.setupVk(gpa, tables, shapes, children.len, ep.prev != null);
    try S.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/rootvk.bin", .{dir}), try rvk.encode(a));
    const kids = try a.alloc(ERoot.Child, children.len);
    for (kids, forest.roots) |*k, fr| {
        k.* = .{ .x = fr.x, .k = fr.k, .hash_root = undefined, .path = fr.path };
        @memcpy(&k.hash_root, fr.proved.sum[19..35]);
    }
    var file: ERoot.File = .{ .head = .{ .from = from.height, .to = to, .logs = keys.logs, .children = kids, .s = undefined, .nin = children[0].sum[6], .challenge = undefined }, .proof = r.proof.? };
    const want = blk: {
        const hs = try a.alloc([8]u32, children.len);
        const ks = try a.alloc([8]u32, children.len);
        const ss = try a.alloc(br_mod.Summary, children.len);
        for (children, hs, ks, ss) |c, *h, *k, *x| {
            h.* = c.proof.circuit_hash;
            k.* = c.key;
            x.* = c.sum;
        }
        break :blk ERoot.expected(hs, ks, ss, ep);
    };
    file.head.s = want.s;
    file.head.nin = want.nin;
    @memcpy(&file.head.challenge, children[0].sum[7..19]);
    const out = try std.fmt.allocPrint(a, "{s}/epochroot-{d}.bin", .{ dir, to });
    try S.writeFileAtomic(out, try file.encode(a));
    std.debug.print("root VK {s}/rootvk.bin (root at 2^{d}); epoch root proof written to {s}\n", .{ dir, rvk.root_log, out });
}

fn verifyEpochRoot(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, dir: []const u8, to: u32, min_work: u256, from: EpochFrom) !void {
    var timer = try std.time.Timer.start();
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) return error.InsufficientWork;
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    const tvk = try BT.Vk.decode(try readPinnedVk(a, .tree, try std.fmt.allocPrint(a, "{s}/treevk.bin", .{dir}), from.unpinned));
    const rvk = try ERoot.RootVk.decode(try readPinnedVk(a, .root, try std.fmt.allocPrint(a, "{s}/rootvk.bin", .{dir}), from.unpinned));
    var file = try ERoot.File.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/epochroot-{d}.bin", .{ dir, to })));
    defer file.proof.deinit();
    const init = try ER.loadInit(gpa, .{ .height = from.height, .prev_set = from.prev_set });
    const set_path = try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to });
    const fin_info = try SF.scan(gpa, set_path, null);
    const ep: ERoot.Epoch = .{ .from = from.height, .to = to, .prev = if (init.info) |x| x.digest else null, .fin = fin_info.digest };
    const v = try ERoot.verify(gpa, a, tables, &tvk, &rvk, &file, ep, s.headers, s.t);
    std.debug.print("epoch root verified: ONE proof for blocks {d}..{d} ({d} subtrees), the seed and the challenge in-circuit, the block hashes the chain's ({d:.1}s)\n", .{ from.height, to, file.head.children.len, secs(timer.lap()) });
    const init_count: u64 = if (init.info) |x| x.count else 0;
    if (v.nin + fin_info.count + init_count >= 1 << 30) return error.EpochTooLarge;
    var sum = v.sum;
    if (init.info) |x| sum = sum.add(try sumSet(gpa, from.prev_set.?, v.challenge, x.digest));
    const fin = try sumSet(gpa, set_path, v.challenge, fin_info.digest);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    if (init.info) |x| std.debug.print("  from the set after block {d}: {d} coins, hash_serialized {x}\n", .{ from.height - 1, x.count, x.hash });
    std.debug.print("VERIFIED epoch {d}..{d} (one root proof): the coin set after block {d} is {d} coins ({d} inputs spent)\n", .{ from.height, to, to, fin_info.count, v.nin });
    std.debug.print("  total amount     {d} sat\n", .{fin_info.amount});
    std.debug.print("  hash_serialized  {x}  (Core's HASH_SERIALIZED of this set)\n", .{fin_info.hash});
}

fn verifyEpochWide(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, chain_path: []const u8, dir: []const u8, to: u32, min_work: u256, from: EpochFrom) !void {
    var timer = try std.time.Timer.start();
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    if (min_work != 0 and s.work < min_work) return error.InsufficientWork;
    std.debug.print("chain proof verified: headers 0..{d} ({d:.1}s)\n", .{ s.headers - 1, secs(timer.lap()) });
    const tvk = try BT.Vk.decode(try readPinnedVk(a, .tree, try std.fmt.allocPrint(a, "{s}/treevk.bin", .{dir}), from.unpinned));
    var forest = try BT.Forest.decode(gpa, a, try S.readFile(a, try std.fmt.allocPrint(a, "{s}/forestk-{d}.bin", .{ dir, to })));
    defer for (forest.roots) |*r| r.proved.proof.deinit();
    if (forest.from != from.height or forest.to != to) return error.WrongEpoch;
    const init = try ER.loadInit(gpa, .{ .height = from.height, .prev_set = from.prev_set });
    const set_path = try std.fmt.allocPrint(a, "{s}/set-{d}.bin", .{ dir, to });
    const fin_info = try SF.scan(gpa, set_path, null);
    const v = try BT.verifyForest(gpa, a, tables, &tvk, &forest, s.headers, s.t, if (init.info) |x| x.digest else null, fin_info.digest);
    std.debug.print("{d} recursion trees (wide nodes) verified: blocks {d}..{d}, the challenge from the seed over their roots, the block hashes the chain's ({d:.1}s)\n", .{ forest.roots.len, from.height, to, secs(timer.lap()) });
    const init_count: u64 = if (init.info) |x| x.count else 0;
    if (v.nin + fin_info.count + init_count >= 1 << 30) return error.EpochTooLarge;
    var sum = v.sum;
    if (init.info) |x| sum = sum.add(try sumSet(gpa, from.prev_set.?, v.challenge, x.digest));
    const fin = try sumSet(gpa, set_path, v.challenge, fin_info.digest);
    if (!sum.eql(fin)) {
        std.debug.print("REJECTED: the blocks' coin events do not end at this coin set\n", .{});
        return error.EpochUnbalanced;
    }
    if (init.info) |x| std.debug.print("  from the set after block {d}: {d} coins, hash_serialized {x}\n", .{ from.height - 1, x.count, x.hash });
    std.debug.print("VERIFIED epoch {d}..{d} (recursion, wide nodes): the coin set after block {d} is {d} coins ({d} inputs spent)\n", .{ from.height, to, to, fin_info.count, v.nin });
    std.debug.print("  total amount     {d} sat\n", .{fin_info.amount});
    std.debug.print("  hash_serialized  {x}  (Core's HASH_SERIALIZED of this set)\n", .{fin_info.hash});
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

/// `rebind-forest <vk> <in forestk-*.bin> <headers.bin> <file.sbchain> <out>`: the forest's root paths
/// recomputed in a longer chain's header tree. The paths are native data (the epoch root checks them
/// against the chain's root, its circuits never see them), so an epoch proved against an older chain
/// file joins under a newer one after this, with no proof redone. Each subtree's block-hash root is
/// checked against the new chain proof's root.
fn rebindForest(gpa: std.mem.Allocator, a: std.mem.Allocator, vk_path: []const u8, in_path: []const u8, headers_path: []const u8, chain_path: []const u8, out: []const u8) !void {
    const vk = try loadVk(a, vk_path);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try S.readFile(a, chain_path));
    defer c.deinit();
    const s = try S.verifyChain(gpa, a, tables, &vk, &c);
    const all = try loadHeaderFile(a, headers_path);
    if (all.len < s.headers) return error.HeadersShorterThanChain;
    const hashes = try a.alloc(HT.Words, s.headers);
    for (hashes, all[0..s.headers]) |*h, *hd| h.* = HT.blockHash(hd);
    var paths = try HT.Paths.init(a, hashes);
    defer paths.deinit(a);
    var f = try BT.Forest.decode(gpa, a, try S.readFile(a, in_path));
    if (f.to >= s.headers) return error.BeyondChain;
    const roots = try a.dupe(BT.Root, f.roots);
    for (roots) |*r| {
        const full = try paths.proof(a, r.x);
        if (full.len < r.k) return error.BadPath;
        var w: HT.Words = undefined;
        for (&w, 0..) |*q, i| q.* = r.proved.sum[19 + 2 * i].toU32() | (r.proved.sum[19 + 2 * i + 1].toU32() << 16);
        if (!HT.verifyInclusion(w, full[r.k..], s.t)) return error.HashesNotTheChain;
        r.path = full[r.k..];
    }
    f.roots = roots;
    try S.writeFileAtomic(out, try f.encode(a));
    std.debug.print("rebound {s} ({d} roots, blocks {d}..{d}) to a chain of {d} headers: {s}\n", .{ in_path, roots.len, f.from, f.to, s.headers, out });
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
