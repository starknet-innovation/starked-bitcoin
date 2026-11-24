//! `survey`: the chain survey (docs/design/chain-survey.md). Reads blocks with their undo streams on
//! stdin and prints, per block, the trace size the prover would choose (`system.sizesAuto`, D-046) from
//! `system.shape`'s needs, without building any witness column.
//!
//!   survey < records > sizes.csv
//!
//! A record: LE32 height, LE32 n, n raw block bytes, LE32 m, m bytes of the fetched undo stream
//! (`0x01` and per non-coinbase input LE32 code, LE64 value, CompactSize length, script; as
//! scripts/fetch_undo.py builds it). Output, one line per record (flushed):
//!   height,L,profile,block_bytes,undo_bytes,ntx,uniform_L,binding,misfit,covered,arena_gib
//! `binding`: the component whose need sets L (`floor` when the 2^8 or tiered 2^12 minimum does);
//! `misfit`: on a fallback to uniform, the first component that missed its tier (else empty);
//! `covered`: Lean's SizeOk holds; `arena_gib`: the CUDA prover's planned device arena (device LogUp)
//! at (L, profile), from `src/gpu/cuda/arena_test.zig` (STARKED_ARENA_TABLE=1). A block that fails to
//! parse prints `height,error,<name>`.

const std = @import("std");
const sb = @import("starked_bitcoin");
const sys = sb.block.system;

/// Planned arena bytes, `prover.Prepared.init(...).memory.bytes()` with device LogUp, production
/// config (`prove_rec.config(L)`), computed on the host by `zig build cuda-test -Dcuda=true
/// -Dtest-filter="chain survey"` with STARKED_ARENA_TABLE=1 (2026-11-23, branch `connect-rules`, after D-060 and D-061). Index L − 8.
const arena_uniform = [_]u64{ 9192336, 15844736, 30016496, 58357104, 114952160, 228051568, 454155392, 906263584, 1810376000, 3618492416, 7234612304, 14466734640, 28930857376, 57858976416, 115715083568, 231427162448, 462851180288 };
/// Index L − 12.
const arena_tiered = [_]u64{ 41882896, 69473184, 127742576, 244181840, 476956384, 942397104, 1873165584, 3734585056, 7457302096, 14902609744, 29793094112, 59573927424, 119135454128 };
/// Index L − 12 (TIERS-2).
const arena_tight = [_]u64{ 32860288, 50639392, 86891088, 159295088, 305073376, 597930512, 1183879984, 2356013888, 4700159648, 9388324768, 18764524096, 37516787296, 75021173776 };

pub fn arenaBytes(L: u32, profile: sys.Profile) ?u64 {
    return switch (profile) {
        .uniform => if (L >= 8 and L - 8 < arena_uniform.len) arena_uniform[L - 8] else null,
        .tiered => if (L >= 12 and L - 12 < arena_tiered.len) arena_tiered[L - 12] else null,
        .tight => if (L >= 12 and L - 12 < arena_tight.len) arena_tight[L - 12] else null,
    };
}

const Bip68 = struct { inputs: u32 = 0, hl: u32 = 0, tl: u32 = 0, tl_heights: u32 = 0 };

fn cs(raw: []const u8, p: *usize) !u64 {
    if (p.* >= raw.len) return error.Truncated;
    const b = raw[p.*];
    p.* += 1;
    const n: usize = switch (b) {
        0xfd => 2,
        0xfe => 4,
        0xff => 8,
        else => return b,
    };
    if (p.* + n > raw.len) return error.Truncated;
    var v: u64 = 0;
    for (0..n) |i| v |= @as(u64, raw[p.* + i]) << @intCast(8 * i);
    p.* += n;
    return v;
}

/// BIP68 counts of a raw block and its fetched undo stream (`0x01`, per non-coinbase input LE32 code,
/// LE64 value, CompactSize length, script; the code is `2·height + coinbase`).
fn bip68Counts(a: std.mem.Allocator, raw: []const u8, undo: []const u8) !Bip68 {
    var out: Bip68 = .{};
    var heights = std.AutoHashMap(u32, void).init(a);
    var p: usize = 80;
    var u: usize = 1;
    const ntx = try cs(raw, &p);
    for (0..ntx) |t| {
        if (p + 4 > raw.len) return error.Truncated;
        const version = std.mem.readInt(u32, raw[p..][0..4], .little);
        p += 4;
        var segwit = false;
        if (p + 2 <= raw.len and raw[p] == 0 and raw[p + 1] != 0) {
            segwit = true;
            p += 2;
        }
        const nin = try cs(raw, &p);
        for (0..nin) |_| {
            p += 36;
            const sl = try cs(raw, &p);
            p += sl;
            if (p + 4 > raw.len) return error.Truncated;
            const seq = std.mem.readInt(u32, raw[p..][0..4], .little);
            p += 4;
            if (t == 0) continue;
            if (u + 12 > undo.len) return error.UndoTruncated;
            const code = std.mem.readInt(u32, undo[u..][0..4], .little);
            u += 12;
            const ul = try cs(undo, &u);
            u += ul;
            out.inputs += 1;
            if (version < 2 or seq & 0x80000000 != 0 or seq & 0xffff == 0) continue;
            if (seq & 0x00400000 != 0) {
                out.tl += 1;
                try heights.put(code >> 1, {});
            } else out.hl += 1;
        }
        const nout = try cs(raw, &p);
        for (0..nout) |_| {
            p += 8;
            const sl = try cs(raw, &p);
            p += sl;
        }
        if (segwit) for (0..nin) |_| {
            const items = try cs(raw, &p);
            for (0..items) |_| {
                const il = try cs(raw, &p);
                p += il;
            }
        };
        p += 4;
    }
    if (p != raw.len or u != undo.len) return error.LengthMismatch;
    out.tl_heights = heights.count();
    return out;
}

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    var in_buf: [1 << 16]u8 = undefined;
    var out_buf: [4096]u8 = undefined;
    var stdin = std.fs.File.stdin().reader(&in_buf);
    var stdout = std.fs.File.stdout().writer(&out_buf);
    const r = &stdin.interface;
    const w = &stdout.interface;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const needs_mode = std.posix.getenv("STARKED_SURVEY_NEEDS") != null;
    const bip68_mode = std.posix.getenv("STARKED_SURVEY_BIP68") != null;
    const rules_mode = std.posix.getenv("STARKED_SURVEY_RULES") != null;
    const sigops_mode = std.posix.getenv("STARKED_SURVEY_SIGOPS") != null;
    while (true) {
        _ = arena.reset(.retain_capacity);
        const a = arena.allocator();
        const height = r.takeInt(u32, .little) catch |e| switch (e) {
            error.EndOfStream => break,
            else => return e,
        };
        const n = try r.takeInt(u32, .little);
        const raw = try a.alloc(u8, n);
        try r.readSliceAll(raw);
        const m = try r.takeInt(u32, .little);
        const undo = try a.alloc(u8, m);
        try r.readSliceAll(undo);
        const sh = sys.shape(a, raw, undo, null, null, height, false) catch |e| {
            try w.print("{d},error,{s}\n", .{ height, @errorName(e) });
            try w.flush();
            continue;
        };
        // STARKED_SURVEY_SIGOPS=1: what the accurate sigop count would add to `block_walk` (CONNECT-RULES
        // step 3). Prints `height,walk_need,redeem_n,redeem_bytes,wscript_n,wscript_bytes,p2sh,witness`.
        if (sigops_mode) {
            const c = sb.block.connect_rules.blockRules(a, raw, undo, height, true) catch |e| {
                try w.print("{d},error,{s}\n", .{ height, @errorName(e) });
                try w.flush();
                continue;
            };
            try w.print("{d},{d},{d},{d},{d},{d},{d},{d}\n", .{ height, sh.needs[sys.C.walk], c.redeem_n, c.redeem_bytes, c.wscript_n, c.wscript_bytes, c.sigops.p2sh, c.sigops.witness });
            try w.flush();
            continue;
        }
        // STARKED_SURVEY_RULES=1: the native check of CONNECT-RULES (`block/connect_rules.zig`). Prints
        // `height,sigop_cost,legacy,p2sh,witness,inputs,height_locks,height_failed,time_locks`, then one
        // line `tl,height,coin_height,lock` per time-based lock, which needs median times past to check.
        if (rules_mode) {
            const c = sb.block.connect_rules.blockRules(a, raw, undo, height, true) catch |e| {
                try w.print("{d},error,{s}\n", .{ height, @errorName(e) });
                try w.flush();
                continue;
            };
            try w.print("{d},{d},{d},{d},{d},{d},{d},{d},{d}\n", .{ height, sb.block.connect_rules.cost(c.sigops), c.sigops.legacy, c.sigops.p2sh, c.sigops.witness, c.inputs, c.height_locks, c.height_failed, c.time_locks.len });
            for (c.time_locks) |l| try w.print("tl,{d},{d},{d}\n", .{ height, l.coin_height, l.lock });
            try w.flush();
            continue;
        }
        // STARKED_SURVEY_BIP68=1: print `height,inputs,height_locks,time_locks,time_lock_coin_heights`
        // (non-coinbase inputs; BIP68 locks with a nonzero value in transactions of version >= 2;
        // distinct creation heights among the time-locked inputs' coins), for CONNECT-RULES.
        if (bip68_mode) {
            const c = bip68Counts(a, raw, undo) catch |e| {
                try w.print("{d},error,{s}\n", .{ height, @errorName(e) });
                try w.flush();
                continue;
            };
            try w.print("{d},{d},{d},{d},{d}\n", .{ height, c.inputs, c.hl, c.tl, c.tl_heights });
            try w.flush();
            continue;
        }
        // STARKED_SURVEY_NEEDS=1: print `height,<need of each component, in `sys.names` order>` instead
        // (the rows each component needs, before any rounding), for the cost split per component.
        if (needs_mode) {
            try w.print("{d}", .{height});
            for (sh.needs) |x| try w.print(",{d}", .{x});
            try w.writeAll("\n");
            try w.flush();
            continue;
        }
        const rep = sys.sizeReport(sh.needs);
        try w.print("{d},{d},{s},{d},{d},{d},{d},{s},{s},{d},", .{
            height,                                                     rep.sized.L,
            @tagName(rep.sized.profile),                                raw.len,
            undo.len,                                                   sh.ntx,
            rep.uniform_L,                                              if (rep.binding) |i| sys.names[i] else "floor",
            if (rep.misfit) |i| sys.names[i] else "",                   @intFromBool(rep.covered),
        });
        if (arenaBytes(rep.sized.L, rep.sized.profile)) |b|
            try w.print("{d:.2}\n", .{@as(f64, @floatFromInt(b)) / (1 << 30)})
        else
            try w.writeAll("\n");
        try w.flush();
        // Keep the arena from holding a large block's peak forever.
        if (arena.queryCapacity() > 256 << 20) {
            arena.deinit();
            arena = std.heap.ArenaAllocator.init(gpa);
        }
    }
}
