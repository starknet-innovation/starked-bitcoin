//! The coin-set pass's segment system (`block/set_seg.zig`) on the resident CUDA prover, checked on the
//! host (no GPU; docs/design/gpu-cuda.md § Set pass):
//! - a CPU proof of a real segment (set-170, small logs): the resident plans reproduce the verifier's
//!   capture, and our transcript (host channel and the device sink's model) every challenge;
//! - its LogUp fraction kernels (the exact `gpu/cuda_aot` sources, host C++) and the completion model
//!   reproduce `system.interactionTrace`;
//! - the host trees `prover.Input{ .witness = null }` uploads;
//! - the production arena (`chainproof` `default_set_logs`) plans and binds; its size is printed.
//! Skipped when `data/epoch/set-170.bin` is missing (all but the arena).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const catalog_mod = @import("catalog.zig");
const prover = @import("prover.zig");
const memory = @import("memory.zig");
const controller = @import("composition_controller.zig");
const logup = @import("logup.zig");
const parity = @import("cpu_parity_test.zig");
const logup_test = @import("logup_test.zig");
const system = sb.air.system;
const rec = sb.air.prove_rec;
const SS = sb.block.set_seg;
const ST = sb.recursion.set_tree;
const M31 = core.fields.m31.M31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;

/// The set tree test's logs (`set_tree.zig`): every component small, two over 2^10.
const test_logs: ST.Logs = .{ 10, 8, 6, 6, 10, 8, 11, 10, 11, 10, 12, 13 };
/// `chainproof` `default_set_logs` (production, provisional).
pub const production_logs: ST.Logs = .{ 23, 8, 6, 16, 22, 21, 23, 23, 23, 22, 23, 23 };
/// Every component but the fixed tables one size down: fits a 94 GB H100 NVL or an H200.
pub const halved_logs: ST.Logs = .{ 22, 8, 6, 15, 21, 20, 22, 22, 22, 21, 22, 22 };
/// Two sizes down: fits an 80 GB H100.
pub const quartered_logs: ST.Logs = .{ 21, 8, 6, 14, 20, 19, 21, 21, 21, 20, 21, 21 };

fn gib(bytes: usize) f64 {
    return @as(f64, @floatFromInt(bytes)) / (1 << 30);
}

const Segment = struct { b: *SS.Built, parts: [SS.N_COMP]system.Part, mains: [SS.N_COMP][]const []const M31 };

fn segment0(a: std.mem.Allocator, airs: *const [SS.N_COMP]sb.air.ir.Air) !?Segment {
    const file = std.fs.cwd().readFileAlloc(a, "data/epoch/set-170.bin", 1 << 30) catch return null;
    const ends = try SS.cut(a, file, test_logs);
    const b = try a.create(SS.Built);
    b.* = try SS.buildAt(a, sb.block.epoch.challenge(@splat(7)), SS.begin(file[0..4].*), file[4..ends[0]], test_logs);
    var out: Segment = .{ .b = b, .parts = ST.partsOf(airs, b.logs, &b.pubs), .mains = undefined };
    for (&out.mains, b.mains) |*m, x| m.* = @ptrCast(x);
    return out;
}

test "cuda set: plans and transcript reproduce a CPU segment proof (set-170, test logs)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    const seg = (try segment0(a, airs)) orelse return error.SkipZigTest;
    const cfg = rec.Config.fromFriAndTraceSize(try FriConfigV2.init(10, 0, 1, 3, 1), ST.maxLog(seg.b.logs));
    const proof = try system.proveOpts(rec.Engine(CpuBackend), a, cfg, &seg.parts, &seg.mains, .{});
    var capture: core.verifier.ProofCapture(rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &seg.parts, &.{}, &proof, &capture);
    std.debug.print("set segment 0 of set-170: {d} records, logs {any}, CPU proof verified\n", .{ seg.b.recs, seg.b.logs });
    const view: parity.View = .{ .parts = &seg.parts, .cfg = cfg, .proof = &proof, .capture = &capture };
    try parity.checkPlans(a, &cat, view);
    try parity.checkHostTranscript(a, view);
    try parity.checkDeviceSinkModel(a, view);

    // The host trees a `witness = null` proof uploads: tree 0 generated on the host, tree 1 the
    // witness's own columns (borrowed), every column at its component's size.
    const in = prover.Input{ .parts = &seg.parts, .mains = &seg.mains, .config = cfg, .catalog = &cat };
    var host = try prover.hostTraceTrees(a, in);
    defer host.deinit(a);
    var n_pre: usize = 0;
    var n_main: usize = 0;
    for (airs) |air| {
        n_pre += air.n_preprocessed;
        n_main += air.n_main;
    }
    try std.testing.expectEqual(n_pre, host.trees[0].len);
    try std.testing.expectEqual(n_main, host.trees[1].len);
    var k: usize = 0;
    for (seg.parts, seg.mains) |p, m| for (m) |col| {
        try std.testing.expectEqual(col.ptr, host.trees[1][k].values.ptr);
        try std.testing.expectEqual(@as(usize, 1) << @intCast(p.log_size), host.trees[1][k].values.len);
        k += 1;
    };
    std.debug.print("  host trees: {d} preprocessed ({d:.1} MiB) + {d} main ({d:.1} MiB, borrowed) columns\n", .{ n_pre, gib(host.bytes(0)) * 1024, n_main, gib(host.bytes(1)) * 1024 });
}

test "cuda set: generated fraction kernels (host C++) and the completion model reproduce system.interactionTrace (set-170 segment)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    const seg = (try segment0(a, airs)) orelse return error.SkipZigTest;
    const kernels = try a.alloc(?logup.Kernel, SS.N_COMP);
    for (airs, kernels) |air, *k| k.* = if (air.lookups.len == 0) null else try logup.kernel(a, air);
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var lib = try logup_test.build(a, tmp.dir, kernels);
    defer lib.close();
    try logup_test.check(a, &lib, kernels, &seg.parts, &seg.mains, 170, try std.fmt.allocPrint(a, "set-170 segment 0 (logs {any})", .{seg.b.logs}));
}

test "cuda set: the segment arena plans and binds (production default_set_logs, halved, quartered)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    const pubs = try a.alloc(M31, SS.N_PUB);
    @memset(pubs, M31.zero());
    const fri = sb.block.proof_file.productionFri();
    // Production, then every component one and two sizes down (records too, so that the tree
    // component still holds the records' heap tree: `SS.treeLog`). Halving the logs about doubles the
    // segment count; the rows, hence the device time per set, stay about the same.
    for ([_]ST.Logs{ production_logs, halved_logs, quartered_logs }, [_][]const u8{ "production", "halved", "quartered" }) |logs, what| {
        try std.testing.expect(logs[SS.C.mt] >= SS.treeLog(logs[SS.C.rec]));
        const parts = ST.partsOf(airs, logs, pubs[0..SS.N_PUB]);
        const cfg = rec.Config.fromFriAndTraceSize(fri, ST.maxLog(logs));
        var prepared = try prover.Prepared.init(a, &parts, &cat, cfg, .device_logup);
        defer prepared.deinit();
        var fake = memory.FakeArena{ .placement = &prepared.memory.placement };
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
        try bound.prepareCompletion();
        var evaluator = try controller.Bound.init(a, &prepared.plans.composition, views.composition);
        defer evaluator.deinit();
        try prepared.plans.fri.validate(views.fri, views.twiddles_inverse);
        var host_prepared = try prover.Prepared.init(a, &parts, &cat, cfg, .host_logup);
        defer host_prepared.deinit();
        const m = &prepared.memory;
        const traces = m.kindBytes(.commit_coefficients) + m.kindBytes(.commit_evaluations) + m.kindBytes(.commit_hashes);
        var host_bytes: usize = 0;
        for (parts) |p| host_bytes += (p.air.n_main + p.air.n_preprocessed) * (@as(usize, 4) << @intCast(p.log_size));
        std.debug.print("set segment, {s} logs {any}: resident arena {d:.1} GiB with device LogUp ({d:.1} GiB host LogUp; trees {d:.1} GiB, LogUp sources {d:.2} GiB); host trees (planned H2D) {d:.1} GiB\n", .{
            what,               logs,
            gib(try m.bytes()), gib(try host_prepared.memory.bytes()),
            gib(traces),        gib(m.kindBytes(.logup_sources)),
            gib(host_bytes),
        });
    }
}
