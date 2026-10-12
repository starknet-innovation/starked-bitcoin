//! GPU plan step 3, item 1: our lowered STWZEVA programs as CUDA kernels (`zig build cuda-parity`).
//!
//! stwo-zig's CUDA code generator (`integrations/cairo_cuda/eval_codegen.zig`, non-parametric
//! `generate`, the resident `StwoCairoEvalArgs` ABI) turns each AIR's *template* program (public
//! input k as base `param` k, `stwzeva.lowerTemplate`) into a CUDA kernel. No GPU here: the
//! kernels are compiled as host C++ (`zig c++`) with a small shim for the CUDA built-ins
//! (`__global__`, `blockIdx`, `__brev`, `__clz`) and run row by row over the arena layout the
//! Metal parity test uses. The composition they accumulate must equal our interpreter's
//! (`component.Component.evaluateConstraintQuotientsOnDomain`), with the public inputs bound
//! through `args->base_params` as the device will bind them.
//!
//! This checks the generated CUDA source's semantics, not NVIDIA codegen: nvcc/ptxas and the
//! device run come with a GPU (docs/design/gpu.md, step 3).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const codegen = @import("cairo_cuda_eval_codegen");
const prover_component = @import("stwo_prover_engine").air.component_prover;
const DomainAccumulator = @import("stwo_prover_engine").air.accumulation.DomainEvaluationAccumulator;
const generateSecurePowers = @import("stwo_prover_engine").air.accumulation.generateSecurePowers;
const ir = sb.air.ir;
const stwzeva = sb.air.stwzeva;
const component_mod = sb.air.component;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const P = core.fields.m31.Modulus;

/// The CUDA built-ins the generated kernels use, for a host C++ build. Each kernel's translation
/// unit gets its own copies (everything is `static`), and a driver that runs every row.
const shim =
    \\#include <cstdint>
    \\#define __global__
    \\#define __device__ static
    \\#define __forceinline__ inline
    \\#define __launch_bounds__(x)
    \\struct StwoHostDim3 { unsigned x, y, z; };
    \\static thread_local StwoHostDim3 blockIdx, blockDim, threadIdx;
    \\static inline unsigned __brev(unsigned v) {
    \\    v = ((v >> 1u) & 0x55555555u) | ((v & 0x55555555u) << 1u);
    \\    v = ((v >> 2u) & 0x33333333u) | ((v & 0x33333333u) << 2u);
    \\    v = ((v >> 4u) & 0x0f0f0f0fu) | ((v & 0x0f0f0f0fu) << 4u);
    \\    v = ((v >> 8u) & 0x00ff00ffu) | ((v & 0x00ff00ffu) << 8u);
    \\    return (v >> 16u) | (v << 16u);
    \\}
    \\static inline int __clz(unsigned v) { return v == 0u ? 32 : __builtin_clz(v); }
    \\
;

const Case = struct {
    name: []const u8,
    air: ir.Air,
    seed: u64,
    kernel: []const u8 = "",
};

fn randM31(r: std.Random) M31 {
    return M31.fromCanonical(r.uintLessThan(u32, P));
}
fn randQM31(r: std.Random) QM31 {
    return QM31.fromM31(randM31(r), randM31(r), randM31(r), randM31(r));
}

/// Mirrors the generated `StwoCairoEvalArgs`.
const Args = extern struct {
    trace_offsets: u64,
    interaction_offsets: u64,
    base_params: u64,
    ext_params: u64,
    random_coeffs: u64,
    denom_inv: u64,
    coord: [4]u64,
    row_count: u32,
    trace_log_size: u32,
    domain_log_size: u32,
    rc_base: u32,
};
const Drive = *const fn ([*]u32, u64, *const Args) callconv(.c) void;

fn check(lib: *std.DynLib, a: std.mem.Allocator, c: Case, log_size: u32) !void {
    var prng = std.Random.DefaultPrng.init(c.seed);
    const r = prng.random();
    const air = c.air;
    const pubs = try a.alloc(M31, air.n_pub);
    for (pubs) |*p| p.* = randM31(r);
    var reference = try component_mod.Component.init(a, air, log_size, pubs);
    const n_batches = component_mod.nBatches(air);
    reference.n_trees = if (n_batches != 0) 3 else 2;
    if (n_batches != 0) reference.logup = .{ .z = randQM31(r), .alpha = randQM31(r), .claimed_sum = randQM31(r) };
    // The literal program fixes the parameters and denominators the template shares.
    var captured = try stwzeva.lowerComponent(a, air, pubs, .{ .log_size = log_size });
    const pre_logs = try a.alloc(u32, air.n_preprocessed);
    @memset(pre_logs, log_size);
    const wrapped = try stwzeva.Component.init(a, &reference, &captured, pre_logs, log_size);
    const n: usize = captured.n_constraints;
    const eval_log = log_size + 1;
    const rows: usize = @as(usize, 1) << @intCast(eval_log);

    const counts = [3]usize{ air.n_preprocessed, air.n_main, 4 * n_batches };
    var tree_polys: [3][]prover_component.Poly = undefined;
    for (&tree_polys, counts) |*t, k| {
        t.* = try a.alloc(prover_component.Poly, k);
        for (t.*) |*poly| {
            const values = try a.alloc(M31, rows);
            for (values) |*v| v.* = randM31(r);
            poly.* = .{ .log_size = eval_log, .values = values };
        }
    }
    var items: [3][]const prover_component.Poly = .{ tree_polys[0], tree_polys[1], tree_polys[2] };
    const trace = prover_component.Trace{ .polys = .{ .items = items[0..reference.n_trees] } };
    const alpha = randQM31(r);
    var acc = try DomainAccumulator.init(a, alpha, eval_log, n);
    try reference.evaluateConstraintQuotientsOnDomain(&trace, &acc);
    const want = try acc.finalize();

    const n_cols = counts[0] + counts[1] + counts[2];
    const params = try wrapped.prover.runtime.extensionParameters();
    var next: usize = 1;
    const column_base = next;
    next += n_cols * rows;
    const trace_offsets = next;
    next += n_cols;
    const interaction_offsets = next;
    next += 3;
    const base_params = next;
    next += pubs.len;
    const ext_params = next;
    next += 4 * params.len;
    const random_coeffs = next;
    next += 4 * n;
    const denom_inv = next;
    next += captured.denominator_inverses.len;
    var coordinates: [4]u64 = undefined;
    for (&coordinates) |*k| {
        k.* = next;
        next += rows;
    }
    const words = try a.alloc(u32, next);
    @memset(words, 0);
    var global: usize = 0;
    for (tree_polys, 0..) |t, tree| {
        words[interaction_offsets + tree] = @intCast(global);
        for (t) |poly| {
            const at = column_base + global * rows;
            for (poly.values, 0..) |v, i| words[at + i] = v.toU32();
            words[trace_offsets + global] = @intCast(at);
            global += 1;
        }
    }
    for (pubs, 0..) |p, i| words[base_params + i] = p.toU32();
    for (params, 0..) |p, i| for (p.toM31Array(), 0..) |x, k| {
        words[ext_params + 4 * i + k] = x.toU32();
    };
    const powers = try generateSecurePowers(a, alpha, n);
    for (0..n) |i| for (powers[n - 1 - i].toM31Array(), 0..) |x, k| {
        words[random_coeffs + 4 * i + k] = x.toU32();
    };
    for (captured.denominator_inverses, 0..) |d, i| words[denom_inv + i] = d;

    const args = Args{
        .trace_offsets = trace_offsets,
        .interaction_offsets = interaction_offsets,
        .base_params = base_params,
        .ext_params = ext_params,
        .random_coeffs = random_coeffs,
        .denom_inv = denom_inv,
        .coord = coordinates,
        .row_count = @intCast(rows),
        .trace_log_size = log_size,
        .domain_log_size = log_size,
        .rc_base = 0,
    };
    const sym = try std.fmt.allocPrintSentinel(a, "drive_{s}", .{c.kernel}, 0);
    const drive = lib.lookup(Drive, sym) orelse return error.MissingKernel;
    var timer = try std.time.Timer.start();
    drive(words.ptr, words.len, &args);
    const host_ns = timer.read();
    for (want.columns, coordinates) |column, at| {
        for (column, 0..) |v, row| try std.testing.expectEqual(v.toU32(), words[at + row]);
    }
    std.debug.print("cuda {s} (log {d}, {d} constraints, {d} public inputs as base params): CUDA kernel (host C++) = interpreter ({d} ms)\n", .{
        c.name, log_size, n, pubs.len, host_ns / std.time.ns_per_ms,
    });
}

test "cuda: lowered STWZEVA template kernels compute our composition (host C++ build)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size: u32 = if (std.process.getEnvVarOwned(a, "CUDA_PARITY_LOG")) |v| try std.fmt.parseInt(u32, v, 10) else |_| 10;

    var cases = std.ArrayList(Case).empty;
    try cases.append(a, .{ .name = "header_chain", .air = (try ir.Air.parseJson(a, sb.header_chain.lean_json)).value, .seed = 1 });
    for (sb.block.system.names, sb.block.system.jsons, 0..) |name, json, i|
        try cases.append(a, .{ .name = name, .air = (try ir.Air.parseJson(a, json)).value, .seed = 100 + i });

    // Generate every kernel, one translation unit each, and build them into one shared library.
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const dir = try tmp.dir.realpathAlloc(a, ".");
    var argv = std.ArrayList([]const u8).empty;
    try argv.appendSlice(a, &.{ "zig", "c++", "-shared", "-O2", "-std=c++17", "-w", "-o", try std.fs.path.join(a, &.{ dir, "kernels.so" }) });
    var source_bytes: usize = 0;
    for (cases.items, 0..) |*c, i| {
        const template = try stwzeva.lowerTemplate(a, c.air, log_size);
        const body = try codegen.generate(a, template);
        c.kernel = try codegen.kernelName(a, template.header.semantic_hash);
        source_bytes += body.len;
        const tu = try std.fmt.allocPrint(a,
            \\{s}{s}
            \\extern "C" void drive_{s}(unsigned *arena, u64 words, const StwoCairoEvalArgs *args) {{
            \\    blockDim = {{256u, 1u, 1u}};
            \\    for (unsigned row = 0; row < args->row_count; ++row) {{
            \\        blockIdx = {{row / 256u, 0u, 0u}};
            \\        threadIdx = {{row % 256u, 0u, 0u}};
            \\        {s}(arena, words, args);
            \\    }}
            \\}}
            \\
        , .{ shim, body, c.kernel, c.kernel });
        const path = try std.fmt.allocPrint(a, "k{d}.cpp", .{i});
        try tmp.dir.writeFile(.{ .sub_path = path, .data = tu });
        try argv.append(a, try std.fs.path.join(a, &.{ dir, path }));
    }
    var timer = try std.time.Timer.start();
    const res = try std.process.Child.run(.{ .allocator = a, .argv = argv.items, .max_output_bytes = 1 << 20 });
    if (res.term != .Exited or res.term.Exited != 0) {
        std.debug.print("zig c++ failed:\n{s}\n", .{res.stderr});
        return error.CompileFailed;
    }
    std.debug.print("cuda: {d} kernels, {d} KiB of CUDA source, host C++ build {d} ms\n", .{ cases.items.len, source_bytes / 1024, timer.read() / std.time.ns_per_ms });
    var lib = try std.DynLib.open(try std.fs.path.join(a, &.{ dir, "kernels.so" }));
    defer lib.close();
    for (cases.items) |c| try check(&lib, a, c, log_size);
}
