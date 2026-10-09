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
//!   chainproof inclusion <file.sbchain> <headers.bin> <height>
//!       Prints and checks the MMR inclusion path of a block hash in the (verified) file's `T`.
//!
//! `headers.bin`: raw 80-byte headers from height 0. CPU only.

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
