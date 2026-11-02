//! Device LogUp on the host: the generated fraction kernels (the exact `gpu/cuda_aot` sources,
//! built as host C++ with a shim for the CUDA built-ins) and a host model of stwo-zig's relation
//! completion (`logup.hostComplete`), fed what the device gets (storage-order columns gathered by
//! the plan, the statement words, `α⁰…α^w`, `z`), must reproduce `system.interactionTrace`: every
//! tree-2 column and every claimed sum. The completion kernels themselves (batch inverse, ragged
//! reductions, block scans) are stwo-zig's and are checked only on a device.
//!
//! Cases: block 0 in the uniform and tiered profiles; `STARKED_LOGUP_SAMPLES=1,2` adds small
//! samples, `STARKED_LOGUP_LARGE=400000` a large one (tiered, its own L; several GB of RAM).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const logup = @import("logup.zig");
const transcript = @import("transcript.zig");
const system = sb.air.system;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
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
    \\static inline unsigned atomicOr(unsigned *p, unsigned v) { const unsigned o = *p; *p = o | v; return o; }
    \\
;

const Drive = *const fn ([*]const u32, [*]const [*]u32, [*]const u32, [*]const u32, [*]const u32, [*]u32, *u32, u32) callconv(.c) void;

pub fn build(a: std.mem.Allocator, dir: std.fs.Dir, kernels: []const ?logup.Kernel) !std.DynLib {
    const path = try dir.realpathAlloc(a, ".");
    var argv = std.ArrayList([]const u8).empty;
    try argv.appendSlice(a, &.{ "zig", "c++", "-shared", "-O1", "-std=c++17", "-w", "-o", try std.fs.path.join(a, &.{ path, "logup.so" }) });
    for (kernels, 0..) |maybe, i| if (maybe) |k| {
        const tu = try std.fmt.allocPrint(a,
            \\{s}{s}
            \\extern "C" void drive_{s}(const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
            \\    const unsigned *powers, const unsigned *z, unsigned *denominators, unsigned *error, unsigned log_size) {{
            \\    blockDim = {{{d}u, 1u, 1u}};
            \\    const unsigned rows = 1u << log_size;
            \\    for (unsigned row = 0; row < rows; ++row) {{
            \\        blockIdx = {{row / {d}u, 0u, 0u}};
            \\        threadIdx = {{row % {d}u, 0u, 0u}};
            \\        {s}(sources, outputs, pubs, powers, z, denominators, error, log_size);
            \\    }}
            \\}}
            \\
        , .{ shim, k.source, k.kernel_name, logup.threads, logup.threads, logup.threads, k.kernel_name });
        const name = try std.fmt.allocPrint(a, "l{d}.cpp", .{i});
        try dir.writeFile(.{ .sub_path = name, .data = tu });
        try argv.append(a, try std.fs.path.join(a, &.{ path, name }));
    };
    if (std.process.getEnvVarOwned(a, "STARKED_LOGUP_KEEP")) |keep| {
        for (argv.items[8..]) |f| try std.fs.copyFileAbsolute(f, try std.fs.path.join(a, &.{ keep, std.fs.path.basename(f) }), .{});
    } else |_| {}
    var timer = try std.time.Timer.start();
    const res = try std.process.Child.run(.{ .allocator = a, .argv = argv.items, .max_output_bytes = 1 << 20 });
    if (res.term != .Exited or res.term.Exited != 0) {
        std.debug.print("zig c++ failed:\n{s}\n", .{res.stderr});
        return error.CompileFailed;
    }
    std.debug.print("cuda logup: host C++ build of {d} fraction kernels {d} ms\n", .{ argv.items.len - 8, timer.read() / std.time.ns_per_ms });
    return std.DynLib.open(try std.fs.path.join(a, &.{ path, "logup.so" }));
}

fn randQ(r: std.Random) QM31 {
    return QM31.fromM31(M31.fromCanonical(r.uintLessThan(u32, P)), M31.fromCanonical(r.uintLessThan(u32, P)), M31.fromCanonical(r.uintLessThan(u32, P)), M31.fromCanonical(r.uintLessThan(u32, P)));
}

fn words(a: std.mem.Allocator, xs: []const QM31) ![]u32 {
    const out = try a.alloc(u32, 4 * xs.len);
    for (xs, 0..) |x, i| for (x.toM31Array(), 0..) |c, k| {
        out[4 * i + k] = c.toU32();
    };
    return out;
}

/// One system: device model vs `system.interactionTrace`.
pub fn check(a: std.mem.Allocator, lib: *std.DynLib, kernels: []const ?logup.Kernel, parts: []const system.Part, mains: []const []const []const M31, seed: u64, what: []const u8) !void {
    var prng = std.Random.DefaultPrng.init(seed);
    const el = core.channel.lookup_transcript.LookupElements{ .z = randQ(prng.random()), .alpha = randQ(prng.random()) };
    var timer = try std.time.Timer.start();
    const want = try system.interactionTrace(a, parts, mains, el);
    const cpu_ms = timer.lap() / std.time.ns_per_ms;

    var plan = try logup.Plan.init(a, parts, kernels);
    defer plan.deinit();
    // What ingress uploads (storage-order trees 0–1, as `prover.hostTraceTrees`), for the columns
    // the lookups read only (the others stay empty), and the statement.
    const ColumnEvaluation = @import("stwo_prover_engine").pcs.ColumnEvaluation;
    var trees: [2][]ColumnEvaluation = undefined;
    trees[0] = try system.preprocessedColumns(a, parts);
    var n_main: usize = 0;
    for (parts) |p| n_main += p.air.n_main;
    trees[1] = try a.alloc(ColumnEvaluation, n_main);
    for (trees[1]) |*c| c.* = .{ .log_size = 0, .values = &.{} };
    for (plan.instances) |x| for (x.columns) |c| if (c.tree == 1) {
        var first: usize = 0;
        for (parts[0..x.component]) |p| first += p.air.n_main;
        const col = mains[x.component][c.column - first];
        const st = try sb.air.prove.toStorage(a, x.log_size, &.{col});
        trees[1][c.column] = st[0];
    };
    var statement = try transcript.Statement.init(a, parts);
    defer statement.deinit(a);
    // α⁰…α^w and z, as `stwo_relation_expand_challenges_on` writes them.
    const powers = try a.alloc(QM31, plan.alpha_powers);
    for (powers, 0..) |*x, i| x.* = if (i == 0) QM31.one() else powers[i - 1].mul(el.alpha);
    const power_words = try words(a, powers);
    const z_words = try words(a, &.{el.z});

    try std.testing.expectEqual(want.sums.len, plan.instances.len);
    var output_columns: usize = 0;
    for (plan.instances, plan.geometry, 0..) |x, g, j| {
        const p = parts[x.component];
        try std.testing.expectEqualSlices(u32, @ptrCast(p.pubs), statement.words[x.pub_offset..][0..x.n_pub]);
        try std.testing.expectEqual(output_columns, x.output_first);
        output_columns += 4 * x.batches;
        const rows: usize = x.rows;
        // Per-component buffers come from the page allocator and are freed (large blocks).
        var local = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer local.deinit();
        const la = local.allocator();
        // The gather of `logup.Bound.gather`.
        const sources = try la.alloc(u32, @max(x.columns.len * rows, 1));
        for (x.columns, 0..) |c, k| {
            const col = trees[c.tree][c.column];
            try std.testing.expectEqual(rows, col.values.len);
            for (col.values, 0..) |v, i| sources[k * rows + i] = v.toU32();
        }
        const outputs = try la.alloc([]M31, 4 * x.batches);
        const pointers = try la.alloc([*]u32, 4 * x.batches);
        for (outputs, pointers) |*o, *ptr| {
            o.* = try la.alloc(M31, rows);
            @memset(o.*, M31.fromCanonical(0x5a5a5a5));
            ptr.* = @ptrCast(o.*.ptr);
        }
        const slab = try la.alloc(QM31, rows * x.batches);
        var err: u32 = 0;
        const sym = try std.fmt.allocPrintSentinel(a, "drive_{s}", .{x.kernel.kernel_name}, 0);
        const drive = lib.lookup(Drive, sym) orelse {
            std.debug.print("cuda logup: missing {s}\n", .{sym});
            return error.MissingKernel;
        };
        const pubs: [*]const u32 = statement.words[x.pub_offset..].ptr;
        drive(sources.ptr, pointers.ptr, pubs, power_words.ptr, z_words.ptr, @ptrCast(slab.ptr), &err, x.log_size);
        try std.testing.expectEqual(@as(u32, 0), err);
        const claim = try logup.hostComplete(g, outputs, slab);
        try std.testing.expect(claim.eql(want.sums[j]));
        for (outputs, 0..) |o, k| {
            const expect = want.columns[x.output_first + k].values;
            if (!std.mem.eql(u32, @ptrCast(expect), @ptrCast(o))) {
                std.debug.print("cuda logup: {s} column {d} differs\n", .{ p.air.name, k });
                return error.LogupColumnMismatch;
            }
        }
    }
    try std.testing.expectEqual(want.columns.len, output_columns);
    std.debug.print("cuda logup: {s}: {d} components, {d} tree-2 columns, {d} claims: generated kernels + completion model = system.interactionTrace (CPU {d} ms, model {d} ms)\n", .{
        what, plan.instances.len, output_columns, want.sums.len, cpu_ms, timer.read() / std.time.ns_per_ms,
    });
}

fn checkSample(a: std.mem.Allocator, lib: *std.DynLib, airs: *const [bs.N_COMP]sb.air.ir.Air, kernels: []const ?logup.Kernel, s: sb.block.checks.Sample, profile: bs.Profile, min_log: u32) !void {
    const b = try a.create(bs.Built);
    b.* = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = min_log, .profile = profile });
    const parts = bs.parts(airs, b);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    const what = try std.fmt.allocPrint(a, "block {d} {s} (L {d}, logs {any})", .{ s.ctx.height, @tagName(profile), b.log_size, b.logs });
    try check(a, lib, kernels, &parts, &mains, s.ctx.height + @intFromEnum(profile), what);
}

test "cuda logup: generated fraction kernels (host C++) and the completion model reproduce system.interactionTrace" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    const kernels = try a.alloc(?logup.Kernel, bs.N_COMP);
    for (airs, kernels) |air, *k| k.* = if (air.lookups.len == 0) null else try logup.kernel(a, air);
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var lib = try build(a, tmp.dir, kernels);
    defer lib.close();

    const small = sb.block.checks.samples_small;
    try checkSample(a, &lib, airs, kernels, small[0], .uniform, 0);
    try checkSample(a, &lib, airs, kernels, small[0], .tiered, bs.TIERED_MIN_L);
    if (std.process.getEnvVarOwned(a, "STARKED_LOGUP_SAMPLES")) |list| {
        var it = std.mem.tokenizeScalar(u8, list, ',');
        while (it.next()) |tok| {
            const i = try std.fmt.parseInt(usize, tok, 10);
            try checkSample(a, &lib, airs, kernels, small[i], .tiered, bs.TIERED_MIN_L);
        }
    } else |_| {}
    if (std.process.getEnvVarOwned(a, "STARKED_LOGUP_LARGE")) |h| {
        const height = try std.fmt.parseInt(u32, h, 10);
        for (sb.block.checks.samples_large) |s| if (s.ctx.height == height) {
            try checkSample(a, &lib, airs, kernels, s, .tiered, 0);
            break;
        } else return error.NoSuchLargeSample;
    } else |_| {}
}

test "cuda logup: kernel identities follow stwo-zig's native-authenticated scheme" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    var n: usize = 0;
    for (airs) |air| {
        if (air.lookups.len == 0) continue;
        const k = try logup.kernel(a, air);
        n += 1;
        // semantic hash = sha256(contract)[:16], kernel name and label are canonical, the file
        // name is `witness_<label>_<cache key>.cu`.
        var d: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(k.semantic_contract, &d, .{});
        try std.testing.expectEqual(std.mem.readInt(u64, d[0..8], .big), k.semantic_hash);
        const label = try k.label(a);
        for (label) |c| try std.testing.expect(std.ascii.isLower(c) or std.ascii.isDigit(c) or c == '_');
        try std.testing.expectEqualStrings(try std.fmt.allocPrint(a, "witness_{s}_{x:0>16}.cu", .{ label, k.cache_key }), try k.fileName(a));
        try std.testing.expect(k.cache_key != 0 and k.semantic_hash != 0);
        try std.testing.expect(std.mem.indexOf(u8, k.source, k.kernel_name) != null);
    }
    try std.testing.expectEqual(@as(usize, 15), n);
}
