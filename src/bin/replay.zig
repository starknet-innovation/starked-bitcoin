//! `replay`: full-chain data preparation (src/block/replay.zig). Applies raw blocks in height order to
//! an in-memory coin set, each checked against the pinned header at its height, and writes what the
//! provers read (`epoch_run`): per block in a window, `blocks/<h>.bin`, `undo/<h>.undo` and
//! `undo/<h>.ctx` (the bytes `scripts/fetch_undo.py --blocks --ctx` writes), and the coin set after
//! chosen blocks, `set-<h>.bin` (`chainproof prove-epoch`'s format; an epoch's `--from h+1` set, and a
//! checkpoint to resume from).
//!
//!   replay <headers.bin> <out> [--from <h> <set-(h-1).bin>] [--to <h>] [--blocks <dir>]
//!          [--window <a> <b>] [--set-at <h>]... [--set-every <n>] [--capacity <coins>]
//!
//! Blocks come from `<dir>/<h>.bin` (`--blocks`, needs `--to`) or from stdin as records
//! (LE32 height, LE32 n, n raw bytes; scripts/stream_blocks.py), consecutive from `--from` (default 0)
//! until `--to` or the end of the stream. `--set-every n` writes the set after every block h with
//! n | h + 1. Progress goes to stderr every 10 s; one line per written set (count, amount, Core's
//! `hash_serialized`, the digest of the file).

const std = @import("std");
const sb = @import("starked_bitcoin");
const R = sb.block.replay;

fn usage() noreturn {
    std.debug.print("usage: replay <headers.bin> <out> [--from <h> <set.bin>] [--to <h>] [--blocks <dir>] [--window <a> <b>] [--set-at <h>]... [--set-every <n>] [--capacity <coins>]\n", .{});
    std.process.exit(2);
}

fn parse(s: []const u8) u32 {
    return std.fmt.parseInt(u32, s, 10) catch usage();
}

fn hex(b: [32]u8) [64]u8 {
    return std.fmt.bytesToHex(b, .lower);
}

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len < 3) usage();
    var from: u32 = 0;
    var from_set: ?[]const u8 = null;
    var to: ?u32 = null;
    var blocks_dir: ?[]const u8 = null;
    var window: ?[2]u32 = null;
    var set_at = std.ArrayList(u32).empty;
    defer set_at.deinit(gpa);
    var set_every: u32 = 0;
    var capacity: u32 = 0;
    var i: usize = 3;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        const more = args.len - i - 1;
        if (std.mem.eql(u8, x, "--from") and more >= 2) {
            from = parse(args[i + 1]);
            from_set = args[i + 2];
            i += 2;
        } else if (std.mem.eql(u8, x, "--to") and more >= 1) {
            to = parse(args[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, x, "--blocks") and more >= 1) {
            blocks_dir = args[i + 1];
            i += 1;
        } else if (std.mem.eql(u8, x, "--window") and more >= 2) {
            window = .{ parse(args[i + 1]), parse(args[i + 2]) };
            i += 2;
        } else if (std.mem.eql(u8, x, "--set-at") and more >= 1) {
            try set_at.append(gpa, parse(args[i + 1]));
            i += 1;
        } else if (std.mem.eql(u8, x, "--set-every") and more >= 1) {
            set_every = parse(args[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, x, "--capacity") and more >= 1) {
            capacity = parse(args[i + 1]);
            i += 1;
        } else usage();
    }
    if (blocks_dir != null and to == null) usage();
    if ((from == 0) != (from_set == null)) {
        std.debug.print("replay: --from h needs the set after h-1 (and genesis has none)\n", .{});
        std.process.exit(2);
    }
    const out = args[2];
    try std.fs.cwd().makePath(out);
    if (window != null) {
        try std.fs.cwd().makePath(try std.fmt.allocPrint(gpa, "{s}/blocks", .{out}));
        try std.fs.cwd().makePath(try std.fmt.allocPrint(gpa, "{s}/undo", .{out}));
    }
    const headers = try std.fs.cwd().readFileAlloc(gpa, args[1], 1 << 30);
    defer gpa.free(headers);
    if (headers.len % 80 != 0) return error.BadHeaderFile;
    const n_headers: u32 = @intCast(headers.len / 80);

    var set = try R.Set.init(gpa, capacity);
    defer set.deinit();
    var timer = try std.time.Timer.start();
    if (from_set) |path| {
        const info = try set.loadFile(path, from);
        std.debug.print("loaded {s}: {d} coins, {d} sat, hash_serialized {s}, digest {s} ({d:.1} s)\n", .{ path, info.count, info.amount, hex(info.hash), hex(info.digest), secs(timer.lap()) });
    }

    var in_buf: [1 << 20]u8 = undefined;
    var stdin = std.fs.File.stdin().reader(&in_buf);
    const r = &stdin.interface;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var h = from;
    var bytes: u64 = 0;
    var last_report: u64 = 0;
    var path_buf: [std.fs.max_path_bytes]u8 = undefined;
    while (to == null or h <= to.?) : (h += 1) {
        _ = arena.reset(.retain_capacity);
        const a = arena.allocator();
        const raw = if (blocks_dir) |d|
            try std.fs.cwd().readFileAlloc(a, try std.fmt.bufPrint(&path_buf, "{s}/{d}.bin", .{ d, h }), 1 << 26)
        else blk: {
            const got = r.takeInt(u32, .little) catch |e| switch (e) {
                error.EndOfStream => break,
                else => return e,
            };
            if (got != h) {
                std.debug.print("replay: stream has height {d}, expected {d}\n", .{ got, h });
                return error.OutOfOrder;
            }
            const n = try r.takeInt(u32, .little);
            if (n > 1 << 26) return error.BlockTooLarge;
            const b = try a.alloc(u8, n);
            try r.readSliceAll(b);
            break :blk b;
        };
        if (h >= n_headers) return error.BeyondHeaders;
        const want = if (window) |w| h >= w[0] and h <= w[1] else false;
        const u = set.apply(a, raw, headers[80 * h ..][0..80], h, want) catch |e| {
            std.debug.print("replay: block {d}: {s}\n", .{ h, @errorName(e) });
            return e;
        };
        bytes += raw.len;
        if (u) |x| {
            try std.fs.cwd().writeFile(.{ .sub_path = try std.fmt.bufPrint(&path_buf, "{s}/blocks/{d}.bin", .{ out, h }), .data = raw });
            try std.fs.cwd().writeFile(.{ .sub_path = try std.fmt.bufPrint(&path_buf, "{s}/undo/{d}.undo", .{ out, h }), .data = x.undo });
            try std.fs.cwd().writeFile(.{ .sub_path = try std.fmt.bufPrint(&path_buf, "{s}/undo/{d}.ctx", .{ out, h }), .data = x.ctx });
        }
        try set.maybeCompact();
        const at = std.mem.indexOfScalar(u32, set_at.items, h) != null or (set_every > 0 and (h + 1) % set_every == 0);
        if (at) {
            const path = try std.fmt.bufPrint(&path_buf, "{s}/set-{d}.bin", .{ out, h });
            var t = try std.time.Timer.start();
            const info = try set.writeFile(path);
            std.debug.print("set after {d}: {d} coins, {d} sat, hash_serialized {s}, digest {s} ({s}, {d:.1} s)\n", .{ h, info.count, info.amount, hex(info.hash), hex(info.digest), path, secs(t.read()) });
        }
        const now = timer.read();
        if (now - last_report > 10 * std.time.ns_per_s) {
            last_report = now;
            const s = secs(now);
            std.debug.print("{d}: {d} coins, heap {d} MB ({d} MB live), {d:.0} s, {d:.1} MB/s\n", .{ h, set.count(), set.heap.items.len >> 20, set.live >> 20, s, @as(f64, @floatFromInt(bytes)) / 1e6 / s });
        }
    }
    std.debug.print("replay {d}..{d}: {d} blocks, {d:.1} MB, {d} coins; {d:.1} s\n", .{ from, h -% 1, h - from, @as(f64, @floatFromInt(bytes)) / 1e6, set.count(), secs(timer.read()) });
}

fn secs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e9;
}
