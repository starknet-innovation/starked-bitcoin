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
        // The device witness `cuda-set` uses (the gadgets and tree 0 generated): its inputs are sized
        // by the logs, so placeholder inputs plan the same arena as a real segment's.
        var b2s: [3]witness.SetInputs.B2 = undefined;
        for (&b2s, [_]usize{ SS.C.b2c, SS.C.lc, SS.C.mt }) |*g, c| {
            const periods = try a.alloc(sb.blake2s_air.Input, ((@as(usize, 1) << @intCast(logs[c])) + 87) / 88);
            @memset(periods, .{ .h = @splat(0), .m = @splat(0), .t = 0, .f = false });
            g.* = .{ .component = c, .periods = periods };
        }
        const set_inputs = witness.SetInputs{ .b2 = &b2s, .sha = .{ .component = SS.C.shac, .compressions = &.{} } };
        var prepared = try prover.Prepared.initSource(a, &parts, &cat, cfg, .device_logup, .{ .set = &set_inputs });
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
        var host_prepared = try prover.Prepared.initSource(a, &parts, &cat, cfg, .host_logup, .{ .set = &set_inputs });
        defer host_prepared.deinit();
        const m = &prepared.memory;
        const traces = m.kindBytes(.commit_coefficients) + m.kindBytes(.commit_evaluations) + m.kindBytes(.commit_hashes);
        var host_bytes: usize = 0;
        for (parts) |p| host_bytes += (p.air.n_main + p.air.n_preprocessed) * (@as(usize, 4) << @intCast(p.log_size));
        // Planned H2D with the device witness: the host's (non-generated) main columns and the
        // witness inputs; tree 0 is generated.
        const wp = prepared.witness.?;
        var lean_bytes: usize = wp.inputBytes();
        var k: usize = 0;
        for (parts) |p| for (0..p.air.n_main) |_| {
            if (!wp.generated_main[k]) lean_bytes += @as(usize, 4) << @intCast(p.log_size);
            k += 1;
        };
        std.debug.print("set segment, {s} logs {any}: resident arena {d:.1} GiB with device LogUp and witness ({d:.1} GiB host LogUp; trees {d:.1} GiB, LogUp sources {d:.2} GiB); planned H2D {d:.2} GiB with the device witness ({d:.2} MiB of it inputs), {d:.1} GiB with host witnesses\n", .{
            what,               logs,
            gib(try m.bytes()), gib(try host_prepared.memory.bytes()),
            gib(traces),        gib(m.kindBytes(.logup_sources)),
            gib(lean_bytes),    gib(wp.inputBytes()) * 1024,
            gib(host_bytes),
        });
    }
}

// ------------------------------------------------------------------ device witness (set system)

const witness = @import("witness.zig");
const wt = @import("witness_test.zig");
const pipeline = @import("pipeline.zig");
const cc = @import("stwo_circuit_cuda_integration");
const common = @import("stwo_cuda_backend").runtime.stages.common;
const ColumnEvaluation = @import("stwo_prover_engine").pcs.ColumnEvaluation;

/// Segment `k` of `path` at `logs`, built in full (the CPU reference) and lean (`skip_gadgets`).
fn segmentPair(a: std.mem.Allocator, path: []const u8, logs: ST.Logs, k: usize) !?struct { full: *SS.Built, lean: *SS.Built } {
    const file = std.fs.cwd().readFileAlloc(a, path, 1 << 30) catch return null;
    const ch = sb.block.epoch.challenge(@splat(7));
    const ends = try SS.cut(a, file, logs);
    if (k >= ends.len) return error.NoSuchSegment;
    var st = SS.begin(file[0..4].*);
    var at: usize = 4;
    for (ends[0..k]) |end| {
        st = try SS.advance(a, ch, st, file[at..end]);
        at = end;
    }
    const full = try a.create(SS.Built);
    full.* = try SS.buildAt(a, ch, st, file[at..ends[k]], logs);
    const lean = try a.create(SS.Built);
    lean.* = try SS.buildAtOpts(a, ch, st, file[at..ends[k]], logs, .{ .skip_gadgets = true });
    return .{ .full = full, .lean = lean };
}

/// Kernels vs the host witness for one segment: the gadget columns of `set_b2c`, `set_lc`, `set_mt`
/// (300 each), `set_shac` (124) and tree 0.
fn checkGadgets(host: *const wt.Host, cat: *const catalog_mod.Catalog, airs: *const [SS.N_COMP]sb.air.ir.Air, path: []const u8, logs: ST.Logs, k: usize, mutate: bool) !void {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const x = arena.allocator();
    const pair = (try segmentPair(x, path, logs, k)) orelse return error.SkipZigTest;
    const b = pair.full;
    // The lean build: the same non-gadget columns and inputs, no gadget columns.
    for ([_]usize{ SS.C.b2c, SS.C.lc, SS.C.mt }) |c| {
        for (pair.lean.mains[c][0..SS.B2_GADGET_COLUMNS]) |col| try std.testing.expectEqual(@as(usize, 0), col.len);
        for (pair.lean.mains[c][SS.B2_GADGET_COLUMNS..], b.mains[c][SS.B2_GADGET_COLUMNS..]) |l, f| try std.testing.expectEqualSlices(u32, @ptrCast(f), @ptrCast(l));
    }
    for (pair.lean.mains[SS.C.shac][0..SS.SHA_GADGET_COLUMNS]) |col| try std.testing.expectEqual(@as(usize, 0), col.len);
    try std.testing.expectEqualSlices(M31, &b.pubs, &pair.lean.pubs);
    const parts = ST.partsOf(airs, b.logs, &b.pubs);
    var b2s: [3]witness.SetInputs.B2 = undefined;
    const inputs = witness.SetInputs.ofSegment(pair.lean, &b2s);
    var plan = try witness.Plan.initSet(x, &parts, &inputs);
    const staging0 = try x.alloc(common.Words, plan.pre_logs.len);
    for (staging0, plan.pre_logs) |*w, log| w.* = try wt.words(x, @as(usize, 1) << @intCast(log));
    const staging1 = try x.alloc(common.Words, plan.generated_main.len);
    var j: usize = 0;
    for (parts) |p| for (0..p.air.n_main) |_| {
        staging1[j] = if (plan.generated_main[j]) try wt.words(x, @as(usize, 1) << @intCast(p.log_size)) else .{ .address = 0, .len = 0, .owner = 1, .generation = 1 };
        j += 1;
    };
    for (staging0) |w| @memset(wt.hostWords(w), 0xdead_beef);
    for (staging1) |w| if (w.len != 0) @memset(wt.hostWords(w), 0xdead_beef);
    const bound = witness.Bound{
        .plan = &plan,
        .kernels = &cat.witness.?,
        .buffers = .{ .inputs = try wt.words(x, plan.layout.words), .scratch = try wt.words(x, plan.scratch_words) },
        .pre_cohorts = try witness.preCohorts(x, &plan),
    };
    var session = wt.HostSession{ .host = host, .cat = cat };
    var timer = try std.time.Timer.start();
    try bound.upload(x, &session, .{ staging0, staging1 });
    try bound.generate(&session);
    const elapsed = timer.read();
    const sp = plan.set.?;
    const names = [_][]const u8{ "set_b2c", "set_lc", "set_mt" };
    for (sp.b2[0..sp.n_b2], [_]usize{ SS.C.b2c, SS.C.lc, SS.C.mt }, names) |g, c, name| {
        try wt.expectColumns(name, @ptrCast(b.mains[c][0..SS.B2_GADGET_COLUMNS]), staging1[g.first..][0..SS.B2_GADGET_COLUMNS]);
    }
    try wt.expectColumns("set_shac", @ptrCast(b.mains[SS.C.shac][0..SS.SHA_GADGET_COLUMNS]), staging1[sp.sha.?.first..][0..SS.SHA_GADGET_COLUMNS]);
    {
        const want = try system.preprocessedNatural(x, &parts);
        const cols = try x.alloc([]const M31, want.len);
        for (cols, want) |*c, w| c.* = w.values;
        try wt.expectColumns("preprocessed", cols, staging0);
    }
    var generated: usize = 0;
    for (plan.generated_main) |g| generated += @intFromBool(g);
    if (mutate) {
        // A message word of set_b2c's period 1, a counter of set_lc's period 0, a set_mt input word
        // and one word of set_shac's first compression: each must change its component's columns.
        const img = wt.hostWords(bound.buffers.inputs);
        const sha = sp.sha.?;
        inline for (.{ sp.b2[0].periods + 27 + 8 + 3, sp.b2[1].periods + 24, sp.b2[2].periods + 9, sha.comps + 8 + 2 }, .{ 0, 1, 2, 3 }) |at, which| {
            img[at] ^= 1;
            try bound.generate(&session);
            const first = if (which < 3) sp.b2[which].first else sha.first;
            const n = if (which < 3) SS.B2_GADGET_COLUMNS else SS.SHA_GADGET_COLUMNS;
            const comp = switch (which) {
                0 => SS.C.b2c,
                1 => SS.C.lc,
                2 => SS.C.mt,
                else => SS.C.shac,
            };
            const want: []const []const M31 = @ptrCast(b.mains[comp][0..n]);
            var differs = false;
            for (want, staging1[first..][0..n]) |w, g| differs = differs or !std.mem.eql(u32, @ptrCast(w), wt.hostWords(g));
            try std.testing.expect(differs);
            img[at] ^= 1;
        }
        try bound.generate(&session);
        try wt.expectColumns("set_b2c", @ptrCast(b.mains[SS.C.b2c][0..SS.B2_GADGET_COLUMNS]), staging1[sp.b2[0].first..][0..SS.B2_GADGET_COLUMNS]);
        std.debug.print("cuda set witness: mutations (a Blake2s message word, a counter, a tree-node word, a SHA-256 block word) are caught\n", .{});
    }
    std.debug.print("cuda set witness: {s} segment {d} (logs {any}): kernels = host witness for {d} gadget columns (set_b2c, set_lc, set_mt 300 each, set_shac 124) and tree 0 ({d} columns); {d} launches, {d} KiB inputs, {d} ms on the host\n", .{ path, k, b.logs, generated, staging0.len, session.launches, plan.layout.words * 4 / 1024, elapsed / std.time.ns_per_ms });
}

test "cuda set witness: the gadget generators (host C++) reproduce the host witness's gadget columns and tree 0 (set-170, set-1000)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try wt.build(a, tmp.dir, &cat);
    defer host.lib.close();
    // set-170: the first segment (no previous key, Blake2s pending bytes = the count), a middle one
    // and the last one (short); set-1000: the first.
    try checkGadgets(&host, &cat, airs, "data/epoch/set-170.bin", test_logs, 0, true);
    try checkGadgets(&host, &cat, airs, "data/epoch/set-170.bin", test_logs, 12, false);
    try checkGadgets(&host, &cat, airs, "data/epoch/set-170.bin", test_logs, 24, false);
    try checkGadgets(&host, &cat, airs, "data/epoch/set-1000.bin", test_logs, 0, false);
    // Larger logs (the hash components at 2^17 and 2^19), `STARKED_SET_WITNESS_LARGE=1`.
    if (std.process.hasEnvVarConstant("STARKED_SET_WITNESS_LARGE"))
        try checkGadgets(&host, &cat, airs, "data/epoch/set-1000.bin", .{ 17, 8, 6, 12, 17, 16, 17, 17, 17, 16, 17, 19 }, 0, false);
}

test "cuda set witness: .trace_generation (gadgets + tree 0 + reorder + LogUp gather) reproduces the CPU storage-order trees" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    var host = try wt.build(a, tmp.dir, &cat);
    defer host.lib.close();
    const pair = (try segmentPair(a, "data/epoch/set-170.bin", test_logs, 3)) orelse return error.SkipZigTest;
    const lean = pair.lean;
    const parts = ST.partsOf(airs, lean.logs, &lean.pubs);
    var mains: [SS.N_COMP][]const []const M31 = undefined;
    for (&mains, lean.mains) |*m, y| m.* = @ptrCast(y);
    var b2s: [3]witness.SetInputs.B2 = undefined;
    const inputs = witness.SetInputs.ofSegment(lean, &b2s);
    const cfg = rec.Config.fromFriAndTraceSize(try FriConfigV2.init(10, 0, 1, 3, 1), ST.maxLog(lean.logs));
    var prepared = try prover.Prepared.initSource(a, &parts, &cat, cfg, .device_logup, .{ .set = &inputs });
    defer prepared.deinit();
    const total = prepared.memory.placement.total_words;
    const backing = try std.heap.page_allocator.alignedAlloc(u32, .@"64", total);
    defer std.heap.page_allocator.free(backing);
    var fake = wt.HostArena{ .placement = &prepared.memory.placement, .base = @intFromPtr(backing.ptr) };
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
    // Ingress, as `prover.proofPass`: the host columns (lean witness), then the witness inputs.
    for (views.staging[0..2]) |st| @memset(wt.hostWords(st.?), 0xdead_beef);
    var session = wt.HostSession{ .host = &host, .cat = &cat };
    const in = prover.Input{ .parts = &parts, .mains = &mains, .config = cfg, .catalog = &cat, .set_witness = &inputs };
    var trees = try prover.hostTraceTreesFor(a, in, prepared.witness);
    defer trees.deinit(a);
    try std.testing.expectEqual(@as(usize, 0), trees.bytes(0));
    for (views.columns[0..2], trees.trees[0..2], 0..) |dst, src, tree| try prover.uploadTree(&session, dst, src, &trees, tree);
    const wv = views.witness.?;
    const wbound = witness.Bound{ .plan = prepared.witness.?, .kernels = &cat.witness.?, .buffers = .{ .inputs = wv.inputs, .scratch = wv.scratch }, .pre_cohorts = prepared.witness_cohorts };
    try wbound.upload(a, &session, .{ views.columns[0], views.columns[1] });
    const uploaded = session.context.uploaded;
    for (views.coefficient_columns[0..2]) |cols| for (cols) |c| @memset(wt.hostWords(c), 0xdead_beef);
    @memset(wt.hostWords(lv.sources), 0xdead_beef);
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
    for (parts, pair.full.mains) |p, m| try want_main.appendSlice(a, try sb.air.prove.toStorage(a, p.log_size, @ptrCast(m)));
    const want = [2][]const ColumnEvaluation{ want_pre, want_main.items };
    var columns: usize = 0;
    var full_bytes: usize = 0;
    for (want, views.coefficient_columns[0..2]) |w, got| {
        try std.testing.expectEqual(w.len, got.len);
        for (w, got) |xx, y| try std.testing.expectEqualSlices(u32, @ptrCast(xx.values), wt.hostWords(y));
        columns += w.len;
        for (w) |c| full_bytes += c.values.len * 4;
    }
    for (plan.instances) |xx| for (xx.columns, 0..) |c, j| {
        try std.testing.expectEqualSlices(u32, @ptrCast(want[c.tree][c.column].values), wt.hostWords(lv.sources)[xx.source_offset + j * xx.rows ..][0..xx.rows]);
    };
    std.debug.print("cuda set witness: set-170 segment 3 (logs {any}): .trace_generation with device witness: {d} columns = CPU storage order, LogUp sources too; {d} launches; ingress {d} KiB (trees 0-1 in full: {d} KiB)\n", .{ lean.logs, columns, session.launches, uploaded / 1024, full_bytes / 1024 });
}
