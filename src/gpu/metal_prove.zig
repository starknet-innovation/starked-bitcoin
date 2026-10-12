//! GPU plan step 2: whole block-system proofs on `MetalCommitBackend` with the Metal device
//! composition stage, byte-identical to the CPU proof (`zig build metal-prove`).
//!
//! Env:
//! - `METAL_PROVE_SAMPLES=n`: the first n of `checks.samples_small` (default all);
//! - `METAL_PROVE_PROFILE=test`: 3 queries, PoW 10, instead of the production profile;
//! - `METAL_PROVE_MIN_LOG=k`: pad every sample to at least 2^k rows (benchmarks);
//! - `METAL_PROVE_ONLY=cpu|metal|host`: one prover only, printing the proof's SHA-256 (separate
//!   processes give separate peak RSS); `host` is the Metal backend with host composition.

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

const Mode = enum { cpu, host, metal };

const Run = struct { bytes: []u8, ns: u64, counts: sb.air.stwzeva.DeviceCounts = .{} };

fn proveOne(mode: Mode, out: std.mem.Allocator, mc: *MetalComposition, cfg: rec.Config, ps: []const system.Part, mains: []const []const []const M31, verify: bool) !Run {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var timer = try std.time.Timer.start();
    var counts: sb.air.stwzeva.DeviceCounts = .{};
    const proof = switch (mode) {
        .cpu => try system.prove(rec.Engine(CpuBackend), a, cfg, ps, mains),
        .host => try system.prove(rec.Engine(metal_backend.MetalCommitBackend), a, cfg, ps, mains),
        .metal => try system.proveOpts(rec.Engine(metal_backend.MetalCommitBackend), a, cfg, ps, mains, .{ .composition = .stwzeva, .device = mc.device(ps), .counts = &counts }),
    };
    const ns = timer.read();
    const bytes = try out.dupe(u8, try system.proofBytes(a, proof));
    if (verify) try system.verifyExt(a, cfg, ps, &.{}, proof);
    return .{ .bytes = bytes, .ns = ns, .counts = counts };
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
    const min_log = if (std.process.getEnvVarOwned(gpa, "METAL_PROVE_MIN_LOG")) |v| try std.fmt.parseInt(u32, v, 10) else |_| 0;
    const only: ?Mode = if (std.process.getEnvVarOwned(gpa, "METAL_PROVE_ONLY")) |v| std.meta.stringToEnum(Mode, v) orelse return error.BadMode else |_| null;
    for (sb.block.checks.samples_small[0..@min(n_samples, sb.block.checks.samples_small.len)]) |s| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const a = arena.allocator();
        var timer = try std.time.Timer.start();
        const b = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log });
        const t_wit = timer.lap();
        const ps = bs.parts(&airs, &b);
        const fri = if (test_profile) try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1) else try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
        const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
        var mains: [bs.N_COMP][]const []const M31 = undefined;
        for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
        const profile = if (test_profile) "test profile" else "production profile";
        if (only) |mode| {
            const compiles = mc.stats.compiles;
            const r = try proveOne(mode, a, &mc, cfg, &ps, &mains, false);
            var digest: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(r.bytes, &digest, .{});
            std.debug.print("height {d} (log {d}, {s}) {s}: {d} ms, proof sha256 {s}, {d} B, device components {d}, new kernels {d}, peak RSS {d} MiB\n", .{
                s.ctx.height, b.log_size, profile, @tagName(mode), ms(r.ns), std.fmt.bytesToHex(digest, .lower)[0..16], r.bytes.len, r.counts.device_components, mc.stats.compiles - compiles, peakRssMiB(),
            });
            continue;
        }
        mc.stats.gpu_ms = 0;
        mc.stats.copy_ns = 0;
        const cpu = try proveOne(.cpu, a, &mc, cfg, &ps, &mains, false);
        const host = try proveOne(.host, a, &mc, cfg, &ps, &mains, false);
        const compiles = mc.stats.compiles;
        const dev = try proveOne(.metal, a, &mc, cfg, &ps, &mains, true);
        try std.testing.expectEqualSlices(u8, cpu.bytes, host.bytes);
        try std.testing.expectEqualSlices(u8, cpu.bytes, dev.bytes);
        try std.testing.expectEqual(@as(usize, bs.N_COMP), dev.counts.device_components);
        try std.testing.expectEqual(@as(usize, 0), dev.counts.device_fallbacks);
        std.debug.print(
            "height {d} (log {d}, {s}): byte-identical, verified. witness {d} ms | CPU {d} ms | Metal+host composition {d} ms | Metal+device composition {d} ms (GPU composition {d:.0} ms, copies {d} ms, {d} new kernels) | peak RSS {d} MiB\n",
            .{ s.ctx.height, b.log_size, profile, ms(t_wit), ms(cpu.ns), ms(host.ns), ms(dev.ns), mc.stats.gpu_ms, ms(mc.stats.copy_ns), mc.stats.compiles - compiles, peakRssMiB() },
        );
    }
    std.debug.print("kernel compiles: {d} in {d} ms total\n", .{ mc.stats.compiles, ms(mc.stats.compile_ns) });
}
