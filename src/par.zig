//! Row-range parallelism for witness and trace builders: `forRanges` splits `0..n` into chunks
//! (multiples of `quantum`, so chunks can start on a period boundary) and runs `body(ctx, lo, hi)`
//! on all cores. Each chunk must write only its own rows.

const std = @import("std");

pub fn forRanges(n: usize, quantum: usize, ctx: anytype, comptime body: fn (@TypeOf(ctx), usize, usize) void) void {
    const max_threads = 64;
    const cpus = @min(std.Thread.getCpuCount() catch 1, max_threads);
    // At least 16 Ki rows per chunk; four chunks per core for balance.
    const want = @max(@as(usize, 1), @min(cpus * 4, n / (16 * 1024)));
    var chunk = (n + want - 1) / want;
    chunk = (chunk + quantum - 1) / quantum * quantum;
    if (chunk == 0 or chunk >= n or cpus == 1) {
        body(ctx, 0, n);
        return;
    }
    const Shared = struct {
        next: std.atomic.Value(usize) = .init(0),
        n: usize,
        chunk: usize,
        ctx: @TypeOf(ctx),
        fn run(s: *@This()) void {
            while (true) {
                const lo = s.next.fetchAdd(s.chunk, .monotonic);
                if (lo >= s.n) return;
                body(s.ctx, lo, @min(lo + s.chunk, s.n));
            }
        }
    };
    var shared = Shared{ .n = n, .chunk = chunk, .ctx = ctx };
    var threads: [max_threads]?std.Thread = @splat(null);
    for (threads[0 .. cpus - 1]) |*t| t.* = std.Thread.spawn(.{}, Shared.run, .{&shared}) catch null;
    Shared.run(&shared);
    for (threads[0 .. cpus - 1]) |t| if (t) |th| th.join();
}

test "forRanges covers every index once, chunks aligned to the quantum" {
    const n = 1_000_003;
    const seen = try std.testing.allocator.alloc(u8, n);
    defer std.testing.allocator.free(seen);
    @memset(seen, 0);
    const Ctx = struct {
        seen: []u8,
        fn f(c: @This(), lo: usize, hi: usize) void {
            std.debug.assert(lo % 72 == 0);
            for (c.seen[lo..hi]) |*s| s.* += 1;
        }
    };
    forRanges(n, 72, Ctx{ .seen = seen }, Ctx.f);
    for (seen) |s| try std.testing.expectEqual(@as(u8, 1), s);
}
