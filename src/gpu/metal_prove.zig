//! GPU plan step 2: whole block-system proofs on `MetalCommitBackend` with the Metal device
//! composition stage, byte-identical to the CPU proof (`zig build metal-prove`).
//!
//! Env: `METAL_PROVE_SAMPLES=n` (first n of `checks.samples_small`, default all),
//! `METAL_PROVE_PROFILE=test` (3 queries, PoW 10) instead of the production profile.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const metal_backend = @import("stwo_metal_backend");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const MetalComposition = @import("metal_composition.zig").MetalComposition;
const system = sb.air.system;
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;

fn peakRssMiB() u64 {
    const usage = std.posix.getrusage(std.posix.rusage.SELF);
    return @as(u64, @intCast(usage.maxrss)) >> 20; // bytes on macOS
}

fn ms(ns: u64) u64 {
    return ns / std.time.ns_per_ms;
}

test "metal: block-system proofs on the Metal backend are byte-identical to CPU and verify" {
    const gpa = std.heap.page_allocator;
    try metal_backend.MetalCommitBackend.initializeRuntime(gpa, .source_jit);
    var air_arena = std.heap.ArenaAllocator.init(gpa);
    defer air_arena.deinit();
    const airs = try bs.parseAirs(air_arena.allocator());
    var mc = MetalComposition.init(gpa);
    defer mc.deinit();
    const test_profile = std.process.hasEnvVarConstant("METAL_PROVE_PROFILE");
    const n_samples = if (std.process.getEnvVarOwned(gpa, "METAL_PROVE_SAMPLES")) |v| try std.fmt.parseInt(usize, v, 10) else |_| sb.block.checks.samples_small.len;
    const Cpu = rec.Engine(CpuBackend);
    const Metal = rec.Engine(metal_backend.MetalCommitBackend);
    for (sb.block.checks.samples_small[0..@min(n_samples, sb.block.checks.samples_small.len)]) |s| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const a = arena.allocator();
        var timer = try std.time.Timer.start();
        const b = try bs.buildU(a, s.raw, s.undo, s.ctx);
        const t_wit = timer.lap();
        const ps = bs.parts(&airs, &b);
        const fri = if (test_profile) try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1) else try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
        const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
        var mains: [bs.N_COMP][]const []const M31 = undefined;
        for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);

        timer.reset();
        const want = try system.proofBytes(a, try system.prove(Cpu, a, cfg, &ps, &mains));
        const t_cpu = timer.lap();
        const host_comp = try system.proofBytes(a, try system.prove(Metal, a, cfg, &ps, &mains));
        const t_metal_host = timer.lap();
        var counts: sb.air.stwzeva.DeviceCounts = .{};
        const compiles_before = mc.stats.compiles;
        mc.stats.gpu_ms = 0;
        mc.stats.copy_ns = 0;
        const proof = try system.proveOpts(Metal, a, cfg, &ps, &mains, .{ .composition = .stwzeva, .device = mc.device(&ps), .counts = &counts });
        const t_metal = timer.lap();
        const got = try system.proofBytes(a, proof);
        try std.testing.expectEqualSlices(u8, want, host_comp);
        try std.testing.expectEqualSlices(u8, want, got);
        try std.testing.expectEqual(@as(usize, bs.N_COMP), counts.device_components);
        try std.testing.expectEqual(@as(usize, 0), counts.device_fallbacks);
        try system.verifyExt(a, cfg, &ps, &.{}, proof);
        const t_verify = timer.lap();
        std.debug.print(
            "height {d} (log {d}, {s}): byte-identical, verified. witness {d} ms | CPU {d} ms | Metal+host composition {d} ms | Metal+device composition {d} ms (GPU composition {d:.0} ms, copies {d} ms, {d} new kernels) | verify {d} ms | peak RSS {d} MiB\n",
            .{ s.ctx.height, b.log_size, if (test_profile) "test profile" else "production profile", ms(t_wit), ms(t_cpu), ms(t_metal_host), ms(t_metal), mc.stats.gpu_ms, ms(mc.stats.copy_ns), mc.stats.compiles - compiles_before, ms(t_verify), peakRssMiB() },
        );
    }
    std.debug.print("kernel compiles: {d} in {d} ms total\n", .{ mc.stats.compiles, ms(mc.stats.compile_ns) });
}
