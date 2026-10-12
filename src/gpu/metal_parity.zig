//! GPU plan step 1, item 4: our lowered STWZEVA programs on the Apple GPU (`zig build metal-parity`).
//!
//! stwo-zig's Metal code generator (`integrations/cairo_metal/eval_codegen.zig`, eval-domain ABI)
//! turns a lowered program into an MSL kernel; the Metal runtime compiles it from source
//! (`Runtime.compileEvalLibrary`, no Xcode `metal`/`metallib` needed) and dispatches it over an
//! arena laid out as `tests/metal/composition_binding_test.zig` does. The composition it writes
//! must equal our interpreter's (`component.Component.evaluateConstraintQuotientsOnDomain`).
//! This is the kernel only, not `circuit_metal`'s device stage: that stage admits kernels only
//! from a digest-pinned, Xcode-built metallib (`cairo_metal/composition_stage.zig`).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const metal = @import("stwo_metal_backend").runtime;
const codegen = @import("cairo_metal_eval_codegen");
const prover_component = @import("stwo_prover_engine").air.component_prover;
const DomainAccumulator = @import("stwo_prover_engine").air.accumulation.DomainEvaluationAccumulator;
const generateSecurePowers = @import("stwo_prover_engine").air.accumulation.generateSecurePowers;
const ir = sb.air.ir;
const stwzeva = sb.air.stwzeva;
const component_mod = sb.air.component;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const P = core.fields.m31.Modulus;

fn randM31(r: std.Random) M31 {
    return M31.fromCanonical(r.uintLessThan(u32, P));
}
fn randQM31(r: std.Random) QM31 {
    return QM31.fromM31(randM31(r), randM31(r), randM31(r), randM31(r));
}

fn check(runtime: *metal.Runtime, a: std.mem.Allocator, name: []const u8, air: ir.Air, log_size: u32, seed: u64) !void {
    var prng = std.Random.DefaultPrng.init(seed);
    const r = prng.random();
    const pubs = try a.alloc(M31, air.n_pub);
    for (pubs) |*p| p.* = randM31(r);
    var reference = try component_mod.Component.init(a, air, log_size, pubs);
    const n_batches = component_mod.nBatches(air);
    reference.n_trees = if (n_batches != 0) 3 else 2;
    if (n_batches != 0) reference.logup = .{ .z = randQM31(r), .alpha = randQM31(r), .claimed_sum = randQM31(r) };
    var captured = try stwzeva.lowerComponent(a, air, pubs, .{ .log_size = log_size });
    const pre_logs = try a.alloc(u32, air.n_preprocessed);
    @memset(pre_logs, log_size);
    const wrapped = try stwzeva.Component.init(a, &reference, &captured, pre_logs, log_size);
    const program = captured.parts[0].program;
    const n: usize = captured.n_constraints;
    const eval_log = log_size + 1;
    const rows: usize = @as(usize, 1) << @intCast(eval_log);

    // Random columns on the evaluation domain.
    const counts = [3]usize{ air.n_preprocessed, air.n_main, 4 * n_batches };
    var tree_polys: [3][]prover_component.Poly = undefined;
    for (&tree_polys, counts) |*t, c| {
        t.* = try a.alloc(prover_component.Poly, c);
        for (t.*) |*poly| {
            const values = try a.alloc(M31, rows);
            for (values) |*v| v.* = randM31(r);
            poly.* = .{ .log_size = eval_log, .values = values };
        }
    }
    var items: [3][]const prover_component.Poly = .{ tree_polys[0], tree_polys[1], tree_polys[2] };
    const trace = prover_component.Trace{ .polys = .{ .items = items[0..reference.n_trees] } };
    const alpha = randQM31(r);
    var timer = try std.time.Timer.start();
    var acc = try DomainAccumulator.init(a, alpha, eval_log, n);
    try reference.evaluateConstraintQuotientsOnDomain(&trace, &acc);
    const want = try acc.finalize();
    const cpu_ns = timer.read();

    // Arena: columns, the per-interaction column tables, ext params, coefficients, denominators,
    // four output coordinates.
    const n_cols = counts[0] + counts[1] + counts[2];
    const params = try wrapped.prover.runtime.extensionParameters();
    var next: usize = 1;
    const column_base = next;
    next += n_cols * rows;
    const trace_offsets = next;
    next += n_cols;
    const interaction_offsets = next;
    next += 3;
    const ext_params = next;
    next += 4 * params.len;
    const random_coeffs = next;
    next += 4 * n;
    const denom_inv = next;
    next += captured.denominator_inverses.len;
    var coordinates: [4]u32 = undefined;
    for (&coordinates) |*c| {
        c.* = @intCast(next);
        next += rows;
    }
    var arena = try runtime.allocateResidentBuffer(next * @sizeOf(u32));
    defer arena.deinit();
    const words: [*]u32 = @ptrCast(@alignCast(arena.contents));
    @memset(words[0..next], 0);
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
    for (params, 0..) |p, i| for (p.toM31Array(), 0..) |x, k| {
        words[ext_params + 4 * i + k] = x.toU32();
    };
    const powers = try generateSecurePowers(a, alpha, n);
    for (0..n) |i| for (powers[n - 1 - i].toM31Array(), 0..) |x, k| {
        words[random_coeffs + 4 * i + k] = x.toU32();
    };
    for (captured.denominator_inverses, 0..) |d, i| words[denom_inv + i] = d;

    const source = try codegen.generate(a, program);
    timer.reset();
    var library = try runtime.compileEvalLibrary(source);
    defer library.deinit();
    const compile_ns = timer.read();
    const kernel = try codegen.kernelName(a, program.header.semantic_hash);
    var plan = try runtime.prepareEvalFromLibrary(library, kernel, .{
        .trace_offsets = @intCast(trace_offsets),
        .interaction_offsets = @intCast(interaction_offsets),
        .base_params = 0,
        .ext_params = @intCast(ext_params),
        .random_coeffs = @intCast(random_coeffs),
        .denom_inv = @intCast(denom_inv),
        .coordinates = coordinates,
        .row_count = @intCast(rows),
        .trace_log_size = log_size,
        .domain_log_size = log_size,
        .rc_base = 0,
    });
    defer plan.deinit();
    const gpu_ms = try runtime.evalPrepared(arena, plan);
    for (want.columns, coordinates) |column, at| {
        for (column, 0..) |v, row| try std.testing.expectEqual(v.toU32(), words[at + row]);
    }
    std.debug.print("metal {s} (log {d}, {d} constraints, {d} KiB MSL): GPU composition = interpreter; GPU {d:.2} ms, CPU interpreter {d} ms, MSL compile {d} ms\n", .{
        name, log_size, n, source.len / 1024, gpu_ms, cpu_ns / std.time.ns_per_ms, compile_ns / std.time.ns_per_ms,
    });
}

test "metal: lowered STWZEVA kernels compute our composition on the Apple GPU" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var runtime = try metal.Runtime.initFull();
    defer runtime.deinit();
    const log_size: u32 = if (std.process.getEnvVarOwned(a, "METAL_PARITY_LOG")) |v| try std.fmt.parseInt(u32, v, 10) else |_| 10;
    const header = (try ir.Air.parseJson(a, sb.header_chain.lean_json)).value;
    try check(&runtime, a, "header_chain", header, log_size, 1);
    for (sb.block.system.names, sb.block.system.jsons, 0..) |name, json, i| {
        const air = (try ir.Air.parseJson(a, json)).value;
        try check(&runtime, a, name, air, log_size, 100 + i);
    }
}
