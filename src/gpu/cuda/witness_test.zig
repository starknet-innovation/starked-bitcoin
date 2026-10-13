//! The device witness generators on the host: the exact AOT sources (`witness.zig`, the files in
//! `gpu/cuda_aot`) built as host C++ with a shim for the CUDA built-ins, each launch run over its
//! whole grid with the launch's own argument array (as `cuLaunchKernel` passes it).
//!
//! 1. Kernels = CPU generators: for a block, `witness.Bound.upload` + `generate` over host memory
//!    reproduce `block.system.buildFull`'s `block_sha` (144) and `block_b2s` (312) columns and
//!    `system.preprocessedNatural` (tree 0) exactly. Block 0 uniform and tiered, blocks 170 and
//!    91812 tiered; `STARKED_WITNESS_SAMPLES=2,4,5` adds small samples, `STARKED_WITNESS_LARGE=400000`
//!    a large block (tiered, its own L; SHA and Blake2s only; several GB of RAM).
//! 2. The whole `.trace_generation` stage with a device witness (`pipeline.assembleTrace`: the
//!    generators, the reorder, the LogUp gather) over a host-memory arena bound with the real
//!    plans of block 0 (uniform and tiered), the host witness built without the generated columns
//!    (`skip_device_columns`) and ingress uploading only the rest (`prover.uploadTree`): every
//!    tree-0/1 coefficient column equals the CPU prover's storage-order column, and the LogUp
//!    sources the storage-order columns they read.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const witness = @import("witness.zig");
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
const ColumnEvaluation = @import("stwo_prover_engine").pcs.ColumnEvaluation;

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

/// Runs a kernel over a whole grid with the launch's argument array.
const Drive = *const fn (u32, u32, u32, [*]const ?*anyopaque) callconv(.c) void;

const Host = struct {
    lib: std.DynLib,
    names: []const []const u8,
    drives: []const Drive,

    fn find(self: *const Host, name: []const u8) ?Drive {
        for (self.names, self.drives) |n, d| if (std.mem.eql(u8, n, name)) return d;
        return null;
    }
};

/// The parameter list of each kernel, as the driver casts `args[i]`.
fn parameterTypes(which: ?witness.Which) [5][]const u8 {
    return if (which) |w| switch (w) {
        .sha_words => .{ "const unsigned *", "const unsigned *", "unsigned", "unsigned *", "unsigned" },
        .sha_columns, .b2s => .{ "const unsigned *", "const unsigned *", "unsigned", "const u64 *", "unsigned" },
        .pre => .{ "const unsigned *", "const unsigned *", "unsigned", "unsigned", "unsigned" },
    } else .{ "const unsigned *", "unsigned *", "unsigned", "unsigned", "" };
}

fn build(a: std.mem.Allocator, dir: std.fs.Dir, cat: *const catalog_mod.Catalog) !Host {
    const path = try dir.realpathAlloc(a, ".");
    var argv = std.ArrayList([]const u8).empty;
    const so = try std.fs.path.join(a, &.{ path, "witness.so" });
    try argv.appendSlice(a, &.{ "zig", "c++", "-shared", "-O2", "-std=c++17", "-w", "-o", so });
    var names = std.ArrayList([]const u8).empty;
    const r = &cat.reorder.?;
    const ws = cat.witness.?.all();
    for (0..ws.len + 1) |i| {
        const which: ?witness.Which = if (i < ws.len) ws[i].which else null;
        const name: []const u8 = if (which != null) ws[i].kernel_name else r.kernel_name;
        const source: []const u8 = if (which != null) ws[i].source else r.source;
        const types = parameterTypes(which);
        const n: usize = if (which != null) 5 else 4;
        var call = std.ArrayList(u8).empty;
        for (types[0..n], 0..) |t, k| try call.print(a, "{s}*({s}*)args[{d}]", .{ if (k == 0) "" else ", ", t, k });
        const tu = try std.fmt.allocPrint(a,
            \\{s}{s}
            \\extern "C" void drive_{s}(unsigned grid_x, unsigned grid_y, unsigned block_x, void *const *args) {{
            \\    blockDim = {{block_x, 1u, 1u}};
            \\    for (unsigned by = 0; by < grid_y; ++by)
            \\        for (unsigned bx = 0; bx < grid_x; ++bx)
            \\            for (unsigned t = 0; t < block_x; ++t) {{
            \\                blockIdx = {{bx, by, 0u}};
            \\                threadIdx = {{t, 0u, 0u}};
            \\                {s}({s});
            \\            }}
            \\}}
            \\
        , .{ shim, source, name, name, call.items });
        const file = try std.fmt.allocPrint(a, "k{d}.cpp", .{i});
        try dir.writeFile(.{ .sub_path = file, .data = tu });
        try argv.append(a, try std.fs.path.join(a, &.{ path, file }));
        try names.append(a, name);
    }
    var timer = try std.time.Timer.start();
    const res = try std.process.Child.run(.{ .allocator = a, .argv = argv.items, .max_output_bytes = 1 << 20 });
    if (res.term != .Exited or res.term.Exited != 0) {
        std.debug.print("zig c++ failed:\n{s}\n", .{res.stderr});
        return error.CompileFailed;
    }
    std.debug.print("cuda witness: host C++ build of {d} kernels {d} ms\n", .{ names.items.len, timer.read() / std.time.ns_per_ms });
    var lib = try std.DynLib.open(so);
    errdefer lib.close();
    const drives = try a.alloc(Drive, names.items.len);
    for (names.items, drives) |n, *d| {
        const sym = try std.fmt.allocPrintSentinel(a, "drive_{s}", .{n}, 0);
        d.* = lib.lookup(Drive, sym) orelse return error.MissingKernel;
    }
    return .{ .lib = lib, .names = names.items, .drives = drives };
}

/// A session whose device memory is host memory: `launchKernel` runs the host build of the named
/// kernel with the launch's own grid and arguments; uploads and copies are memcpy.
const HostSession = struct {
    context: Context = .{},
    host: *const Host,
    cat: *const catalog_mod.Catalog,
    launches: usize = 0,
    uploaded: usize = 0,

    const Context = struct {
        uploaded: usize = 0,
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
        pub fn uploadSlice(self: *Context, comptime F: type, dst: anytype, src: []const F) !void {
            if (dst.len != src.len) return error.SizeOverflow;
            const d = try self.deviceSlicePointer(F, dst, dst.len);
            @memcpy(d[0..dst.len], src);
            self.uploaded += src.len * @sizeOf(F);
        }
    };

    pub fn launchKernel(self: *HostSession, k: cuda.runtime.kernel.Kernel, arguments: []const ?*anyopaque) !void {
        try k.validate();
        const r = &self.cat.reorder.?;
        var known = std.mem.eql(u8, k.name, r.kernel_name) and k.cache_key == r.cache_key and k.abi_schema == reorder.abi_schema and arguments.len == reorder.argument_count;
        for (self.cat.witness.?.all()) |g| {
            if (std.mem.eql(u8, k.name, g.kernel_name) and k.cache_key == g.cache_key and k.abi_schema == witness.abi_schema and arguments.len == witness.argument_count) known = true;
        }
        if (!known or k.stage != .trace_generation or k.argument_count != arguments.len or k.grid[2] != 1 or k.block[1] != 1 or k.block[2] != 1 or k.grid[1] > 65_535)
            return error.InvalidKernelDescriptor;
        const drive = self.host.find(k.name) orelse return error.MissingKernel;
        drive(k.grid[0], k.grid[1], k.block[0], arguments.ptr);
        self.launches += 1;
    }
};

fn words(a: std.mem.Allocator, n: usize) !common.Words {
    const buf = try a.alignedAlloc(u32, .@"64", @max(n, 1));
    return .{ .address = @intFromPtr(buf.ptr), .len = n, .owner = 1, .generation = 1 };
}
fn hostWords(w: common.Words) []u32 {
    const p: [*]u32 = @ptrFromInt(w.address);
    return p[0..w.len];
}

fn expectColumns(what: []const u8, want: []const []const M31, got: []const common.Words) !void {
    try std.testing.expectEqual(want.len, got.len);
    for (want, got, 0..) |w, g, c| {
        const gw = hostWords(g);
        if (!std.mem.eql(u32, @ptrCast(w), gw)) {
            for (w, gw, 0..) |x, y, row| if (x.toU32() != y) {
                std.debug.print("cuda witness: {s} column {d} row {d}: CPU {d}, kernel {d}\n", .{ what, c, row, x.toU32(), y });
                break;
            };
            return error.TestExpectedEqual;
        }
    }
}

/// Kernels vs CPU generators for one block.
fn checkSample(host: *const Host, cat: *const catalog_mod.Catalog, airs: *const [bs.N_COMP]sb.air.ir.Air, s: sb.block.checks.Sample, profile: bs.Profile, min_log: u32, pre: bool) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const x = arena.allocator();
    const b = try x.create(bs.Built);
    b.* = try bs.buildFull(x, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = profile });
    const parts = bs.parts(airs, b);
    const inputs = try witness.Inputs.ofBlock(x, b);
    var plan = try witness.Plan.init(x, &parts, &inputs);
    // Device memory: the generated columns (tree 0, the two components) and dummies elsewhere.
    const staging0 = try x.alloc(common.Words, plan.pre_logs.len);
    for (staging0, plan.pre_logs) |*w, log| w.* = if (pre) try words(x, @as(usize, 1) << @intCast(log)) else .{ .address = 0, .len = 0, .owner = 1, .generation = 1 };
    const staging1 = try x.alloc(common.Words, plan.generated_main.len);
    var k: usize = 0;
    for (parts) |p| for (0..p.air.n_main) |_| {
        staging1[k] = if (plan.generated_main[k]) try words(x, @as(usize, 1) << @intCast(p.log_size)) else .{ .address = 0, .len = 0, .owner = 1, .generation = 1 };
        k += 1;
    };
    for (staging0) |w| if (w.len != 0) @memset(hostWords(w), 0xdead_beef);
    for (staging1) |w| if (w.len != 0) @memset(hostWords(w), 0xdead_beef);
    var cohorts = try witness.preCohorts(x, &plan);
    if (!pre) cohorts = &.{};
    const bound = witness.Bound{
        .plan = &plan,
        .kernels = &cat.witness.?,
        .buffers = .{ .inputs = try words(x, plan.layout.words), .scratch = try words(x, plan.scratch_words) },
        .pre_cohorts = cohorts,
    };
    var session = HostSession{ .host = host, .cat = cat };
    if (!pre) {
        // The image needs every tree-0 address; give the descriptors a scratch column.
        const sink = try words(x, 1);
        for (staging0) |*w| w.* = .{ .address = sink.address, .len = 0, .owner = 1, .generation = 1 };
    }
    var timer = try std.time.Timer.start();
    try bound.upload(x, &session, .{ staging0, staging1 });
    try bound.generate(&session);
    const elapsed = timer.read();
    try expectColumns("block_sha", @ptrCast(b.mains[bs.C.sha]), staging1[plan.sha_first..][0..witness.SHA_COLUMNS]);
    try expectColumns("block_b2s", @ptrCast(b.mains[bs.C.b2s]), staging1[plan.b2s_first..][0..witness.B2S_COLUMNS]);
    if (pre) {
        const want = try system.preprocessedNatural(x, &parts);
        const cols = try x.alloc([]const M31, want.len);
        for (cols, want) |*c, w| c.* = w.values;
        try expectColumns("preprocessed", cols, staging0);
    }
    if (pre and s.ctx.height == 0 and profile == .uniform) {
        // Mutations: one message word of compression 1, one Blake2s counter:
        // each must change the generated columns.
        const img = hostWords(bound.buffers.inputs);
        const l = plan.layout;
        inline for (.{ l.comps + 24 + 8 + 5, l.periods + 24 }, .{ "block_sha", "block_b2s" }) |at, what| {
            img[at] ^= 1;
            try bound.generate(&session);
            const first = if (std.mem.eql(u8, what, "block_sha")) plan.sha_first else plan.b2s_first;
            const n = if (std.mem.eql(u8, what, "block_sha")) witness.SHA_COLUMNS else witness.B2S_COLUMNS;
            const want: []const []const M31 = @ptrCast(b.mains[if (std.mem.eql(u8, what, "block_sha")) bs.C.sha else bs.C.b2s]);
            var differs = false;
            for (want, staging1[first..][0..n]) |w, g| differs = differs or !std.mem.eql(u32, @ptrCast(w), hostWords(g));
            try std.testing.expect(differs);
            img[at] ^= 1;
        }
        try bound.generate(&session);
        try expectColumns("block_sha", @ptrCast(b.mains[bs.C.sha]), staging1[plan.sha_first..][0..witness.SHA_COLUMNS]);
        std.debug.print("cuda witness: mutations (a message word, a Blake2s counter) are caught\n", .{});
    }
    std.debug.print("cuda witness: block {d} {s} (L {d}, sha log {d}: {d} compressions; b2s log {d}: {d} blocks): kernels = CPU for block_sha (144), block_b2s (312){s}; {d} launches, {d} KiB uploaded, {d} ms on the host\n", .{
        s.ctx.height,                     @tagName(b.profile), b.log_size, plan.sha_log, inputs.compressions.len, plan.b2s_log, inputs.blocks.len,
        if (pre) " and tree 0" else "", session.launches,    session.context.uploaded / 1024, elapsed / std.time.ns_per_ms,
    });
}

test "cuda witness: the AOT generators (host C++) reproduce block_sha, block_b2s and tree 0" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try build(a, tmp.dir, &cat);
    defer host.lib.close();
    const small = sb.block.checks.samples_small;
    try checkSample(&host, &cat, airs, small[0], .uniform, 0, true);
    try checkSample(&host, &cat, airs, small[0], .tiered, bs.TIERED_MIN_L, true);
    try checkSample(&host, &cat, airs, small[1], .tiered, bs.TIERED_MIN_L, true);
    try checkSample(&host, &cat, airs, small[3], .tiered, bs.TIERED_MIN_L, true);
    if (std.process.getEnvVarOwned(a, "STARKED_WITNESS_SAMPLES")) |list| {
        var it = std.mem.tokenizeScalar(u8, list, ',');
        while (it.next()) |tok| try checkSample(&host, &cat, airs, small[try std.fmt.parseInt(usize, tok, 10)], .tiered, bs.TIERED_MIN_L, true);
    } else |_| {}
    if (std.process.getEnvVarOwned(a, "STARKED_WITNESS_LARGE")) |h| {
        const height = try std.fmt.parseInt(u32, h, 10);
        for (sb.block.checks.samples_large) |s| if (s.ctx.height == height) {
            try checkSample(&host, &cat, airs, s, .tiered, 0, false);
            break;
        } else return error.NoSuchLargeSample;
    } else |_| {}
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

fn checkStage(a: std.mem.Allocator, host: *const Host, cat: *const catalog_mod.Catalog, airs: *const [bs.N_COMP]sb.air.ir.Air, profile: bs.Profile, min_log: u32) !void {
    const s = sb.block.checks.samples_small[0];
    // The lean host witness (what `cuda-prove` builds) and the full one (the CPU reference).
    const lean = try a.create(bs.Built);
    lean.* = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = profile, .skip_device_columns = true });
    const full = try a.create(bs.Built);
    full.* = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = profile });
    try std.testing.expectEqual(@as(usize, 0), lean.mains[bs.C.sha].len);
    try std.testing.expectEqual(@as(usize, 0), lean.mains[bs.C.b2s].len);
    const parts = bs.parts(airs, lean);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, lean.mains) |*m, y| m.* = @ptrCast(y);
    const inputs = try witness.Inputs.ofBlock(a, lean);
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), lean.log_size);
    var prepared = try prover.Prepared.initWitness(a, &parts, cat, cfg, .device_logup, &inputs);
    defer prepared.deinit();
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
    var lbound = try logup.Bound.init(a, plan, .{
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
    defer lbound.deinit();

    // Ingress, as `prover.proofPass`: the host columns, then the witness inputs.
    for (views.staging[0..2]) |st| @memset(hostWords(st.?), 0xdead_beef);
    var session = HostSession{ .host = host, .cat = cat };
    var trees = try prover.hostTraceTreesFor(a, .{ .parts = &parts, .mains = &mains, .config = cfg, .catalog = cat }, prepared.witness);
    defer trees.deinit(a);
    try std.testing.expectEqual(@as(usize, 0), trees.bytes(0));
    for (views.columns[0..2], trees.trees[0..2], 0..) |dst, src, tree| try prover.uploadTree(&session, dst, src, &trees, tree);
    const wv = views.witness.?;
    const wbound = witness.Bound{ .plan = prepared.witness.?, .kernels = &cat.witness.?, .buffers = .{ .inputs = wv.inputs, .scratch = wv.scratch }, .pre_cohorts = prepared.witness_cohorts };
    try wbound.upload(a, &session, .{ views.columns[0], views.columns[1] });
    const uploaded = session.context.uploaded;
    for (views.coefficient_columns[0..2]) |cols| for (cols) |c| @memset(hostWords(c), 0xdead_beef);
    @memset(hostWords(lv.sources), 0xdead_beef);

    // `.trace_generation`, exactly as the schedule runs it.
    var plans: [3]*const cc.resident_commit.Plan = undefined;
    var coefficients: [3]common.Words = undefined;
    for (&plans, &coefficients, 0..) |*pp, *kk, t| {
        pp.* = &prepared.plans.commits[t];
        kk.* = views.commits[t].coefficients;
    }
    try pipeline.assembleTrace(&session, &cat.reorder.?, plans, coefficients, views.staging, &lbound, &wbound);

    // Trees 0–1 = the CPU prover's storage-order columns (from the full host witness).
    const want_pre = try system.preprocessedColumns(a, &parts);
    var want_main = std.ArrayList(ColumnEvaluation).empty;
    for (parts, full.mains) |p, m| try want_main.appendSlice(a, try sb.air.prove.toStorage(a, p.log_size, @ptrCast(m)));
    const want = [2][]const ColumnEvaluation{ want_pre, want_main.items };
    var columns: usize = 0;
    for (want, views.coefficient_columns[0..2]) |w, got| {
        try std.testing.expectEqual(w.len, got.len);
        for (w, got) |x, y| try std.testing.expectEqualSlices(u32, @ptrCast(x.values), hostWords(y));
        columns += w.len;
    }
    for (plan.instances) |x| for (x.columns, 0..) |c, j| {
        try std.testing.expectEqualSlices(u32, @ptrCast(want[c.tree][c.column].values), hostWords(lv.sources)[x.source_offset + j * x.rows ..][0..x.rows]);
    };
    var full_bytes: usize = 0;
    for (want) |w| for (w) |c| {
        full_bytes += c.values.len * 4;
    };
    std.debug.print("cuda witness: block 0 {s} (L {d}): .trace_generation with device witness: {d} columns = CPU storage order, LogUp sources too; {d} launches; ingress {d} KiB (trees 0-1 in full: {d} KiB)\n", .{ @tagName(profile), lean.log_size, columns, session.launches, uploaded / 1024, full_bytes / 1024 });
}

test "cuda witness: .trace_generation (generators + reorder + LogUp gather) reproduces the CPU storage-order trees" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try build(a, tmp.dir, &cat);
    defer host.lib.close();
    try checkStage(a, &host, &cat, airs, .uniform, 0);
    try checkStage(a, &host, &cat, airs, .tiered, bs.TIERED_MIN_L);
}
