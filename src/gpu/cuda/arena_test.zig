//! The resident arena of real block sizes, planned and bound on the host (no GPU).
//!
//! A block's component sizes are a function of (L, profile) only (`block.system.profileLogs`), so
//! a 2^22 block's arena is planned from its sizes. Every stage's views must bind inside one arena
//! (stwo-zig's lifetime-checked placement), and the composition controller, FRI plan, terminal
//! layout and device LogUp (its buffers and stwo-zig's checked completion plan) must accept them.
//! The host-LogUp arena is printed beside it.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const catalog_mod = @import("catalog.zig");
const prover = @import("prover.zig");
const memory = @import("memory.zig");
const controller = @import("composition_controller.zig");
const logup = @import("logup.zig");
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;

fn gib(bytes: usize) f64 {
    return @as(f64, @floatFromInt(bytes)) / (1 << 30);
}

test "cuda resident arena: real block sizes plan and bind (uniform and tiered, L = 20..23)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    const pubs = try a.alloc(M31, bs.N_PUB);
    @memset(pubs, M31.zero());
    for ([_]u32{ 20, 22, 23 }) |L| for ([_]bs.Profile{ .uniform, .tiered }) |profile| {
        const logs = bs.profileLogs(L, profile);
        const parts = bs.partsAt(airs, logs, pubs[0..bs.N_PUB]);
        const cfg = try rec.config(L);
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
        try std.testing.expect(views.staging[2] == null and views.columns[2].len == 0);
        var host_prepared = try prover.Prepared.init(a, &parts, &cat, cfg, .host_logup);
        defer host_prepared.deinit();
        var evaluator = try controller.Bound.init(a, &prepared.plans.composition, views.composition);
        defer evaluator.deinit();
        try prepared.plans.fri.validate(views.fri, views.twiddles_inverse);
        try std.testing.expectEqual(views.proof.decommitment.address, views.proof.bundle.address + prepared.terminal_bundle.section(.decommitment).offset_words * 4);
        const m = &prepared.memory;
        const traces = m.kindBytes(.commit_coefficients) + m.kindBytes(.commit_evaluations) + m.kindBytes(.commit_hashes);
        std.debug.print("L={d} {s}: resident arena {d:.1} GiB with device LogUp ({d:.1} GiB host LogUp; trees {d:.1} GiB, LogUp sources {d:.2} GiB, LDE tile {d:.2} GiB, accumulators {d:.2} GiB, quotient+FRI {d:.2} GiB); {d} slots\n", .{
            L,                                                                  @tagName(profile),
            gib(try m.bytes()),                                                 gib(try host_prepared.memory.bytes()),
            gib(traces),                                                        gib(m.kindBytes(.logup_sources)),
            gib(m.kindBytes(.composition_lde_tile)),                            gib(m.kindBytes(.composition_accumulators)),
            gib(m.kindBytes(.quotient_result) + m.kindBytes(.quotient_partial_coordinates) + m.kindBytes(.fri_coordinates) + m.kindBytes(.fri_hashes)),
            m.slots.len,
        });
    };
}
