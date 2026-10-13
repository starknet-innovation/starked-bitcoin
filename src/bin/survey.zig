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
/// -Dtest-filter="chain survey"` with STARKED_ARENA_TABLE=1 at d9a2aba. Index L − 8.
const arena_uniform = [_]u64{ 8529232, 14633024, 27447056, 53293200, 104899328, 208020864, 414168992, 826365760, 1650655328, 3299126048, 6595954544, 13189494096, 26376451264, 52750239168, 105497684048, 210992438384, 421981807136 };
/// Index L − 12.
const arena_tiered = [_]u64{ 40078384, 66538160, 122020240, 232884832, 454510064, 897652176, 1783823392, 3556048384, 7100376432, 14188906096, 28365834496, 56719555872, 113426858704 };

pub fn arenaBytes(L: u32, profile: sys.Profile) ?u64 {
    return switch (profile) {
        .uniform => if (L >= 8 and L - 8 < arena_uniform.len) arena_uniform[L - 8] else null,
        .tiered => if (L >= 12 and L - 12 < arena_tiered.len) arena_tiered[L - 12] else null,
    };
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
        const sh = sys.shape(a, raw, undo, null, height, false) catch |e| {
            try w.print("{d},error,{s}\n", .{ height, @errorName(e) });
            try w.flush();
            continue;
        };
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
