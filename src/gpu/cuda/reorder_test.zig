//! The natural → storage reorder on the host: the exact AOT source (`reorder.zig`, the file in
//! `gpu/cuda_aot`) built as host C++ with a shim for the CUDA built-ins and run over every
//! (block, thread) of each launch's grid.
//!
//! 1. Kernel = `air/prove.zig toStorage` for many log sizes and mixed-size cohorts packed as the
//!    commitment packs them (each cohort's columns contiguous, cohorts back to back).
//! 2. The whole `.trace_generation` stage (`pipeline.assembleTrace`, through `reorder.Kernel.launch`
//!    and `logup.Bound.gather`) over a host-memory arena bound with the real plans of block 0
//!    (uniform and tiered): ingress uploads `prover.hostTraceTrees` (natural order) into the staging
//!    views; afterwards every tree-0/1 coefficient column must equal the CPU prover's storage-order
//!    column (`system.preprocessedColumns`, `toStorage` of the witness) and the LogUp sources the
//!    storage-order columns the lookups read.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const reorder = @import("reorder.zig");
const pipeline = @import("pipeline.zig");
const prover = @import("prover.zig");
const memory = @import("memory.zig");
const logup = @import("logup.zig");
const catalog_mod = @import("catalog.zig");
const cc = @import("stwo_circuit_cuda_integration");
const common = cuda.runtime.stages.common;
const system = sb.air.system;
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;
const P = core.fields.m31.Modulus;

const shim =
    \\#include <cstdint>
    \\#define __global__
    \\#define __device__ static
    \\#define __forceinline__ inline
    \\#define __launch_bounds__(x)
    \\struct StarkedHostDim3 { unsigned x, y, z; };
    \\static thread_local StarkedHostDim3 blockIdx, blockDim, threadIdx;
    \\static inline unsigned __brev(unsigned v) {
    \\    v = ((v >> 1u) & 0x55555555u) | ((v & 0x55555555u) << 1u);
    \\    v = ((v >> 2u) & 0x33333333u) | ((v & 0x33333333u) << 2u);
    \\    v = ((v >> 4u) & 0x0f0f0f0fu) | ((v & 0x0f0f0f0fu) << 4u);
    \\    v = ((v >> 8u) & 0x00ff00ffu) | ((v & 0x00ff00ffu) << 8u);
    \\    return (v >> 16u) | (v << 16u);
    \\}
    \\
;

/// Runs the kernel over a whole grid (every block, every thread of the block).
const Drive = *const fn (u32, u32, u32, [*]const u32, [*]u32, u32, u32) callconv(.c) void;

const Host = struct {
    lib: std.DynLib,
    drive: Drive,
};

fn build(a: std.mem.Allocator, dir: std.fs.Dir, k: *const reorder.Kernel) !Host {
    const path = try dir.realpathAlloc(a, ".");
    const tu = try std.fmt.allocPrint(a,
        \\{s}{s}
        \\extern "C" void drive(unsigned grid_x, unsigned grid_y, unsigned block_x,
        \\    const unsigned *natural, unsigned *storage, unsigned log_size, unsigned columns) {{
        \\    blockDim = {{block_x, 1u, 1u}};
        \\    for (unsigned by = 0; by < grid_y; ++by)
        \\        for (unsigned bx = 0; bx < grid_x; ++bx)
        \\            for (unsigned t = 0; t < block_x; ++t) {{
        \\                blockIdx = {{bx, by, 0u}};
        \\                threadIdx = {{t, 0u, 0u}};
        \\                {s}(natural, storage, log_size, columns);
        \\            }}
        \\}}
        \\
    , .{ shim, k.source, k.kernel_name });
    try dir.writeFile(.{ .sub_path = "reorder.cpp", .data = tu });
    const so = try std.fs.path.join(a, &.{ path, "reorder.so" });
    const res = try std.process.Child.run(.{ .allocator = a, .argv = &.{ "zig", "c++", "-shared", "-O2", "-std=c++17", "-w", "-o", so, try std.fs.path.join(a, &.{ path, "reorder.cpp" }) }, .max_output_bytes = 1 << 20 });
    if (res.term != .Exited or res.term.Exited != 0) {
        std.debug.print("zig c++ failed:\n{s}\n", .{res.stderr});
        return error.CompileFailed;
    }
    var lib = try std.DynLib.open(so);
    errdefer lib.close();
    return .{ .drive = lib.lookup(Drive, "drive") orelse return error.MissingKernel, .lib = lib };
}

/// A session whose device memory is host memory: `launchKernel` runs the host build of the kernel
/// with the launch's own grid and arguments; copies are memcpy.
const HostSession = struct {
    context: Context,
    drive: Drive,
    kernel: *const reorder.Kernel,
    launches: usize = 0,

    const Context = struct {
        pub fn deviceSlicePointer(_: *Context, comptime F: type, slice: anytype, minimum: usize) ![*]F {
            if (minimum == 0 or slice.len < minimum or slice.address % @alignOf(F) != 0) return error.InvalidDeviceAddress;
            return @ptrFromInt(slice.address);
        }
        pub fn copyDeviceSlice(self: *Context, comptime F: type, dst: anytype, src: anytype) !void {
            if (dst.len == 0 or dst.len != src.len) return error.SizeOverflow;
            const d = try self.deviceSlicePointer(F, dst, dst.len);
            const s = try self.deviceSlicePointer(F, src, src.len);
            @memcpy(d[0..dst.len], s[0..src.len]);
        }
    };

    pub fn launchKernel(self: *HostSession, k: cuda.runtime.kernel.Kernel, arguments: []const ?*anyopaque) !void {
        try k.validate();
        if (k.cache_key != self.kernel.cache_key or !std.mem.eql(u8, k.name, self.kernel.kernel_name) or
            k.abi_schema != reorder.abi_schema or k.stage != .trace_generation or
            arguments.len != reorder.argument_count or k.argument_count != reorder.argument_count or
            k.grid[2] != 1 or k.block[1] != 1 or k.block[2] != 1 or k.grid[1] > reorder.max_columns_per_launch)
            return error.InvalidKernelDescriptor;
        const natural: *const [*]const u32 = @ptrCast(@alignCast(arguments[0].?));
        const storage: *const [*]u32 = @ptrCast(@alignCast(arguments[1].?));
        const log_size: *const u32 = @ptrCast(@alignCast(arguments[2].?));
        const columns: *const u32 = @ptrCast(@alignCast(arguments[3].?));
        self.drive(k.grid[0], k.grid[1], k.block[0], natural.*, storage.*, log_size.*, columns.*);
        self.launches += 1;
    }
};

fn words(a: std.mem.Allocator, n: usize) !common.Words {
    const buf = try a.alignedAlloc(u32, .@"64", n);
    return .{ .address = @intFromPtr(buf.ptr), .len = n, .owner = 1, .generation = 1 };
}
fn hostWords(w: common.Words) []u32 {
    const p: [*]u32 = @ptrFromInt(w.address);
    return p[0..w.len];
}

test "cuda reorder: the AOT kernel (host C++) equals toStorage, mixed-size cohorts" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var k = try reorder.kernel(a);
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try build(a, tmp.dir, &k);
    defer host.lib.close();
    var session = HostSession{ .context = .{}, .drive = host.drive, .kernel = &k };
    var prng = std.Random.DefaultPrng.init(0x5eed);
    const r = prng.random();
    // (log, columns): below, at and above one 256-thread block; odd counts; a tree's worth.
    const cohorts = [_][2]u32{ .{ 0, 2 }, .{ 1, 3 }, .{ 2, 1 }, .{ 4, 5 }, .{ 7, 2 }, .{ 8, 7 }, .{ 9, 3 }, .{ 11, 4 }, .{ 12, 1 }, .{ 16, 2 } };
    var total: usize = 0;
    for (cohorts) |c| total += c[1] << @intCast(c[0]);
    const src = try words(a, total);
    const dst = try words(a, total);
    for (hostWords(src)) |*v| v.* = r.uintLessThan(u32, P);
    @memset(hostWords(dst), 0xdead_beef);
    var offset: usize = 0;
    for (cohorts) |c| {
        const n = @as(usize, c[1]) << @intCast(c[0]);
        try k.launch(&session, try src.sub(offset, n), try dst.sub(offset, n), c[0], c[1]);
        offset += n;
    }
    try std.testing.expectEqual(cohorts.len, session.launches);
    offset = 0;
    for (cohorts) |c| {
        const rows = @as(usize, 1) << @intCast(c[0]);
        const cols = try a.alloc([]const M31, c[1]);
        for (cols, 0..) |*col, j| col.* = @ptrCast(hostWords(src)[offset + j * rows ..][0..rows]);
        const want = try sb.air.prove.toStorage(a, c[0], cols);
        for (want, 0..) |w, j| try std.testing.expectEqualSlices(u32, @ptrCast(w.values), hostWords(dst)[offset + j * rows ..][0..rows]);
        offset += c[1] * rows;
    }
    std.debug.print("cuda reorder: kernel = toStorage for {d} cohorts (logs 0..16, {d} words)\n", .{ cohorts.len, total });
}

/// The arena in host memory (`memory.bind`'s transaction interface).
const HostArena = struct {
    placement: *const cuda.runtime.arena.Plan,
    base: usize,

    pub fn slot(self: *HostArena, id: u32) !common.Words {
        const placed = try self.placement.placement(id);
        return .{ .address = self.base + placed.offset_words * 4, .len = placed.requirement.words, .owner = 1, .generation = 1 };
    }
    pub fn residentArenaWords(self: *HostArena) !common.Words {
        return .{ .address = self.base, .len = self.placement.total_words, .owner = 1, .generation = 1 };
    }
};

fn checkStage(a: std.mem.Allocator, host: *const Host, k: *const reorder.Kernel, cat: *const catalog_mod.Catalog, airs: *const [bs.N_COMP]sb.air.ir.Air, profile: bs.Profile, min_log: u32) !void {
    const s = sb.block.checks.samples_small[0];
    const b = try a.create(bs.Built);
    b.* = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = profile });
    const parts = bs.parts(airs, b);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), b.log_size);
    var prepared = try prover.Prepared.init(a, &parts, cat, cfg, .device_logup);
    defer prepared.deinit();
    // The arena in host memory (pages the stage does not touch are never committed).
    const total = prepared.memory.placement.total_words;
    const backing = try std.heap.page_allocator.alignedAlloc(u32, .@"64", total);
    defer std.heap.page_allocator.free(backing);
    var fake = HostArena{ .placement = &prepared.memory.placement, .base = @intFromPtr(backing.ptr) };
    const plan = prepared.logup.?;
    var views = try memory.bind(a, &fake, .{
        .plans = &prepared.memory,
        .commitments = &prepared.plans.commits,
        .fri = &prepared.plans.fri,
        .terminal = &prepared.terminal_bundle,
        .logup_slab_words = plan.slab_words,
    });
    defer views.deinit();
    const lv = views.logup.?;
    var bound = try logup.Bound.init(a, plan, .{
        .sources = lv.sources,
        .trace = .{ views.coefficient_columns[0], views.coefficient_columns[1] },
        .outputs = views.coefficient_columns[2],
        .denominators = lv.denominators,
        .tables = lv.tables,
        .geometry = lv.geometry,
        .partials = lv.partials,
        .scan = lv.scan,
        .statement = views.statement,
        .lookup = views.transcript.lookup,
        .z = views.relation_z,
        .powers = views.relation_alpha_powers,
        .claims_mixed = views.claims_mixed,
        .claims_component = views.claims_component,
        .error_flag = views.error_flag,
    });
    defer bound.deinit();

    // Ingress: the natural-order host trees into the staging views (as `prover.uploadTree`).
    var trees = try prover.hostTraceTrees(a, .{ .parts = &parts, .mains = &mains, .config = cfg, .catalog = cat });
    defer trees.deinit(a);
    for (views.columns[0..2], trees.trees[0..2]) |dst, src| {
        try std.testing.expectEqual(dst.len, src.len);
        for (dst, src) |d, c| {
            try std.testing.expectEqual(d.len, c.values.len);
            @memcpy(hostWords(d), @as([]const u32, @ptrCast(c.values)));
        }
    }
    for (views.coefficient_columns[0..2]) |cols| for (cols) |c| @memset(hostWords(c), 0xdead_beef);
    @memset(hostWords(lv.sources), 0xdead_beef);

    // `.trace_generation`, exactly as the schedule runs it.
    var session = HostSession{ .context = .{}, .drive = host.drive, .kernel = k };
    var plans: [3]*const cc.resident_commit.Plan = undefined;
    var coefficients: [3]common.Words = undefined;
    for (&plans, &coefficients, 0..) |*pp, *kk, t| {
        pp.* = &prepared.plans.commits[t];
        kk.* = views.commits[t].coefficients;
    }
    try pipeline.assembleTrace(&session, k, plans, coefficients, views.staging, &bound, null);

    // Trees 0–1 = the CPU prover's storage-order columns.
    const want_pre = try system.preprocessedColumns(a, &parts);
    var want_main = std.ArrayList(@import("stwo_prover_engine").pcs.ColumnEvaluation).empty;
    for (parts, mains) |p, m| try want_main.appendSlice(a, try sb.air.prove.toStorage(a, p.log_size, m));
    const want = [2][]const @import("stwo_prover_engine").pcs.ColumnEvaluation{ want_pre, want_main.items };
    var columns: usize = 0;
    for (want, views.coefficient_columns[0..2]) |w, got| {
        try std.testing.expectEqual(w.len, got.len);
        for (w, got) |x, y| try std.testing.expectEqualSlices(u32, @ptrCast(x.values), hostWords(y));
        columns += w.len;
    }
    // LogUp sources = the storage-order columns the lookups read.
    for (plan.instances) |x| for (x.columns, 0..) |c, j| {
        try std.testing.expectEqualSlices(u32, @ptrCast(want[c.tree][c.column].values), hostWords(lv.sources)[x.source_offset + j * x.rows ..][0..x.rows]);
    };
    var cohorts: usize = 0;
    for (plans[0..2]) |p| cohorts += p.cohorts.len;
    try std.testing.expectEqual(cohorts, session.launches);
    std.debug.print("cuda reorder: block 0 {s} (L {d}, logs {any}): .trace_generation over the real plans: {d} columns in {d} launches = CPU storage order; LogUp sources = storage order\n", .{ @tagName(profile), b.log_size, b.logs, columns, session.launches });
}

test "cuda reorder: .trace_generation (reorder + LogUp gather) reproduces the CPU storage-order trees" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try build(a, tmp.dir, &cat.reorder.?);
    defer host.lib.close();
    try checkStage(a, &host, &cat.reorder.?, &cat, airs, .uniform, 0);
    try checkStage(a, &host, &cat.reorder.?, &cat, airs, .tiered, bs.TIERED_MIN_L);
}
