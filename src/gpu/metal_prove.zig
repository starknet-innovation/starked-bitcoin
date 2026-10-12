//! GPU plan step 2: whole block-system proofs on `MetalCommitBackend` with the Metal device
//! composition stage, byte-identical to the CPU proof (`zig build metal-prove`).
//!
//! Env:
//! - `METAL_PROVE_SAMPLES=n`: the first n of `checks.samples_small` (default all);
//! - `METAL_PROVE_PROFILE=test`: 3 queries, PoW 10, instead of the production profile;
//! - `METAL_PROVE_MIN_LOG=k`: pad every sample to at least 2^k rows (benchmarks);
//! - `METAL_PROVE_ONLY=cpu|metal|host`: one prover only, printing the proof's SHA-256 (separate
//!   processes give separate peak RSS); `host` is the Metal backend with host composition;
//! - `METAL_PROVE_DISCARD=1` (with `ONLY`): `discard_mains`, the witness is released mid-proof;
//! - `METAL_PROVE_STORAGE=default|evaluations_only|compact`: the commitment storage policy;
//! - `METAL_PROVE_COMPOSITION=interpreter|stwzeva|stwzeva_native`: the CPU prover's composition;
//! - `METAL_PROVE_TIERED=1`: the tiered size profile (D-045);
//! - `METAL_PROVE_VERIFY=1` (with `ONLY`): verify the proof after proving;
//! - `METAL_PROVE_LARGE=height`: one sample of `checks.samples_large` (e.g. 400000, a 2^22 block).

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

// ---- memory sampler: process footprint, Metal device allocations, system memory in use.
extern fn MTLCreateSystemDefaultDevice() ?*anyopaque;
extern fn sel_registerName(name: [*:0]const u8) *anyopaque;
extern fn objc_msgSend() void;
extern fn host_statistics64(host: u32, flavor: i32, info: *[38]u32, count: *u32) i32;
extern fn mach_host_self() u32;

fn deviceAllocated(device: *anyopaque) u64 {
    const f: *const fn (*anyopaque, *anyopaque) callconv(.c) u64 = @ptrCast(&objc_msgSend);
    return f(device, sel_registerName("currentAllocatedSize"));
}

/// Pages active + wired + compressor-occupied, in bytes (system-wide; includes other processes).
fn systemUsed() u64 {
    var info: [38]u32 = undefined;
    var count: u32 = 38;
    if (host_statistics64(mach_host_self(), 4, &info, &count) != 0) return 0; // HOST_VM_INFO64
    const page: u64 = 16384;
    // vm_statistics64: free, active, inactive, wire (u32 each), then 64-bit counters...; compressor_page_count at u32 index 32.
    return (@as(u64, info[1]) + info[3] + info[32]) * page;
}

const Sampler = struct {
    device: ?*anyopaque,
    stop: std.atomic.Value(bool) = .init(false),
    peak_footprint: u64 = 0,
    peak_device: u64 = 0,
    peak_sum: u64 = 0,
    peak_system: u64 = 0,
    base_system: u64 = 0,

    fn run(self: *Sampler) void {
        while (!self.stop.load(.monotonic)) {
            self.sampleOnce();
            std.Thread.sleep(5 * std.time.ns_per_ms);
        }
    }
    fn sampleOnce(self: *Sampler) void {
        const usage = @import("stwo_prover_engine").measurement.process_usage.sample() catch return;
        const fp = usage.current_physical_footprint_bytes orelse 0;
        const dev = if (self.device) |d| deviceAllocated(d) else 0;
        const sys = systemUsed();
        self.peak_footprint = @max(self.peak_footprint, fp);
        self.peak_device = @max(self.peak_device, dev);
        self.peak_sum = @max(self.peak_sum, fp + dev);
        self.peak_system = @max(self.peak_system, sys);
    }
};

const Run = struct { bytes: []u8, ns: u64, counts: sb.air.stwzeva.DeviceCounts = .{} };

fn proveOne(mode: Mode, out: std.mem.Allocator, mc: *MetalComposition, cfg: rec.Config, ps: []const system.Part, mains: []const []const []const M31, verify: bool, discard: bool) !Run {
    const storage: system.Storage = if (std.process.getEnvVarOwned(std.heap.page_allocator, "METAL_PROVE_STORAGE")) |v| std.meta.stringToEnum(system.Storage, v) orelse .default else |_| .default;
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var timer = try std.time.Timer.start();
    var counts: sb.air.stwzeva.DeviceCounts = .{};
    const proof = switch (mode) {
        .cpu => try system.proveOpts(rec.Engine(CpuBackend), a, cfg, ps, mains, .{ .tile_columns = if (std.process.getEnvVarOwned(std.heap.page_allocator, "METAL_PROVE_TILE_COLUMNS")) |v| try std.fmt.parseInt(usize, v, 10) else |_| 0, .discard_mains = discard, .storage = storage, .composition = if (std.process.getEnvVarOwned(std.heap.page_allocator, "METAL_PROVE_COMPOSITION")) |v| std.meta.stringToEnum(system.Composition, v) orelse .interpreter else |_| .interpreter }),
        .host => try system.proveOpts(rec.Engine(metal_backend.MetalCommitBackend), a, cfg, ps, mains, .{ .discard_mains = discard, .storage = storage }),
        .metal => try system.proveOpts(rec.Engine(metal_backend.MetalCommitBackend), a, cfg, ps, mains, .{ .work_allocator = if (std.process.hasEnvVarConstant("METAL_PROVE_PAGE_ALLOC")) std.heap.page_allocator else null, .composition = .stwzeva, .device = mc.device(ps), .counts = &counts, .discard_mains = discard, .storage = storage }),
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
    const first = if (std.process.getEnvVarOwned(gpa, "METAL_PROVE_FIRST")) |v| try std.fmt.parseInt(usize, v, 10) else |_| 0;
    // `METAL_PROVE_LARGE=height`: that sample of `checks.samples_large` instead of the small ones.
    const large: ?u32 = if (std.process.getEnvVarOwned(gpa, "METAL_PROVE_LARGE")) |v| try std.fmt.parseInt(u32, v, 10) else |_| null;
    const samples = if (large) |h| blk: {
        for (sb.block.checks.samples_large, 0..) |s, i| if (s.ctx.height == h) break :blk sb.block.checks.samples_large[i .. i + 1];
        return error.NoSuchSample;
    } else sb.block.checks.samples_small[first..@min(n_samples, sb.block.checks.samples_small.len)];
    for (samples) |s| {
        var arena = std.heap.ArenaAllocator.init(gpa);
        defer arena.deinit();
        const a = arena.allocator();
        var timer = try std.time.Timer.start();
        const b = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = if (std.process.hasEnvVarConstant("METAL_PROVE_TIERED")) .tiered else .uniform });
        const t_wit = timer.lap();
        std.debug.print("height {d}: size profile {s}, L = {d}, component logs {any}\n", .{ s.ctx.height, @tagName(b.profile), b.log_size, b.logs });
        @import("stwo_prover_engine").measurement.process_usage.reportStage("witness built");
        const ps = bs.parts(&airs, &b);
        const fri = if (test_profile) try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1) else try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
        const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
        var mains: [bs.N_COMP][]const []const M31 = undefined;
        for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
        const profile = if (test_profile) "test profile" else "production profile";
        if (only) |mode| {
            const compiles = mc.stats.compiles;
            var sampler = Sampler{ .device = MTLCreateSystemDefaultDevice(), .base_system = systemUsed() };
            const sampler_thread = try std.Thread.spawn(.{}, Sampler.run, .{&sampler});
            const r = try proveOne(mode, a, &mc, cfg, &ps, &mains, std.process.hasEnvVarConstant("METAL_PROVE_VERIFY"), std.process.hasEnvVarConstant("METAL_PROVE_DISCARD"));
            var digest: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(r.bytes, &digest, .{});
            sampler.stop.store(true, .monotonic);
            sampler_thread.join();
            std.debug.print("height {d} (log {d}, {s}) {s}: {d} ms, proof sha256 {s}, {d} B, device components {d}, new kernels {d}, peak RSS {d} MiB\n", .{
                s.ctx.height, b.log_size, profile, @tagName(mode), ms(r.ns), std.fmt.bytesToHex(digest, .lower)[0..16], r.bytes.len, r.counts.device_components, mc.stats.compiles - compiles, peakRssMiB(),
            });
            std.debug.print("  sampled peaks (5 ms): footprint {d} MB, Metal device allocations {d} MB, footprint+device {d} MB, system in use {d} MB over baseline\n", .{
                sampler.peak_footprint >> 20, sampler.peak_device >> 20, sampler.peak_sum >> 20, (sampler.peak_system -| sampler.base_system) >> 20,
            });
            continue;
        }
        mc.stats.gpu_ms = 0;
        mc.stats.copy_ns = 0;
        const cpu = try proveOne(.cpu, a, &mc, cfg, &ps, &mains, false, false);
        const host = try proveOne(.host, a, &mc, cfg, &ps, &mains, false, false);
        const compiles = mc.stats.compiles;
        const dev = try proveOne(.metal, a, &mc, cfg, &ps, &mains, true, false);
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

test "metal: how a shared resident buffer is accounted (footprint vs device allocations)" {
    try metal_backend.MetalCommitBackend.initializeRuntime(std.heap.page_allocator, .source_jit);
    var lease = try metal_backend.shared_runtime.acquireExisting();
    defer lease.deinit();
    const device = MTLCreateSystemDefaultDevice().?;
    const usage = @import("stwo_prover_engine").measurement.process_usage;
    const fp0 = (try usage.sample()).current_physical_footprint_bytes.?;
    const dev0 = deviceAllocated(device);
    var buffer = try lease.runtime.allocateResidentBuffer(1 << 30);
    defer buffer.deinit();
    const words: [*]u32 = @ptrCast(@alignCast(buffer.contents));
    @memset(words[0 .. (1 << 28)], 7);
    const fp1 = (try usage.sample()).current_physical_footprint_bytes.?;
    const dev1 = deviceAllocated(device);
    std.debug.print("1 GiB shared resident buffer, touched: footprint +{d} MB, device allocations +{d} MB\n", .{ (fp1 -| fp0) >> 20, (dev1 -| dev0) >> 20 });
}
