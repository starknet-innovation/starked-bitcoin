//! Host checks of the resident plan and transcript against real CPU block proofs.
//!
//! A block-system proof from `system.proveOpts` (CPU) is verified with capture; the capture is
//! the verifier's own view (tree column sizes, OODS mask, transcript challenges, queries). The
//! resident plans for the same parts must reproduce its shape, and our transcript, both on the
//! CPU channel (`HostSink`) and as the device sink's call sequence (`ModelSink` over the host
//! model), must reproduce every challenge it drew, through the queries.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const catalog_mod = @import("catalog.zig");
const plan_mod = @import("plan.zig");
const transcript = @import("transcript.zig");
const system = sb.air.system;
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const cuda = @import("stwo_cuda_backend");
const common = cuda.runtime.stages.common;

const Case = struct {
    profile: bs.Profile,
    min_log: u32,
};

const Proved = struct {
    parts: [bs.N_COMP]system.Part,
    cfg: rec.Config,
    proof: system.Proof,
    capture: core.verifier.ProofCapture(rec.Hasher),
};

fn proveSample(a: std.mem.Allocator, airs: *const [bs.N_COMP]sb.air.ir.Air, c: Case) !Proved {
    const s = sb.block.checks.samples_small[0];
    const b = try a.create(bs.Built);
    b.* = try bs.buildFull(a, s.raw, s.undo, s.ctx, .{ .min_log = c.min_log, .profile = c.profile });
    const parts = bs.parts(airs, b);
    // Test profile (3 queries, PoW 10): the shape and transcript order are those of production.
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), b.log_size);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    const proof = try system.proveOpts(rec.Engine(CpuBackend), a, cfg, &parts, &mains, .{});
    var capture: core.verifier.ProofCapture(rec.Hasher) = undefined;
    const pc = try a.create([bs.N_COMP]system.Part);
    pc.* = parts;
    try system.verifyCaptureBorrowed(a, cfg, pc, &.{}, &proof, &capture);
    std.debug.print("block {d}: profile {s}, logs {any}, CPU proof verified\n", .{ s.ctx.height, @tagName(b.profile), b.logs });
    return .{ .parts = parts, .cfg = cfg, .proof = proof, .capture = capture };
}

/// Claimed sums per component (zero where a component has no lookups), as the composition reads them.
fn perComponentSums(a: std.mem.Allocator, parts: []const system.Part, sums: []const QM31) ![]QM31 {
    const out = try a.alloc(QM31, parts.len);
    var k: usize = 0;
    for (parts, out) |p, *o| {
        if (p.air.lookups.len == 0) {
            o.* = QM31.zero();
            continue;
        }
        o.* = sums[k];
        k += 1;
    }
    if (k != sums.len) return error.ClaimCountMismatch;
    return out;
}

fn checkPlans(a: std.mem.Allocator, cat: *const catalog_mod.Catalog, p: *const Proved) !void {
    var plans = try plan_mod.Plans.init(a, &p.parts, cat, p.cfg);
    defer plans.deinit();
    const geo = &plans.geometry;
    const blowup = p.cfg.fri_config.log_blowup_factor;
    // (1) Tree shapes: the verifier's FRI-extended column sizes, tree by tree, and the roots' count.
    const stark = &p.proof.stark.commitment_scheme_proof;
    try std.testing.expectEqual(@as(usize, 4), stark.commitments.items.len);
    try std.testing.expectEqual(@as(usize, 4), p.capture.column_log_sizes.len);
    for (geo.trees, p.capture.column_log_sizes) |t, logs| {
        try std.testing.expectEqual(logs.len, t.column_logs.len);
        for (t.column_logs, logs) |mine, theirs| try std.testing.expectEqual(theirs, mine + blowup);
    }
    // (2) The OODS mask: per tree and column, the resident sample count is the verifier's.
    var total: usize = 0;
    for (p.capture.sampled_points, plans.proof_layout.sample_counts) |tree, counts| {
        try std.testing.expectEqual(tree.len, counts.len);
        for (tree, counts) |col, n| {
            try std.testing.expectEqual(col.len, @as(usize, n));
            total += col.len;
        }
    }
    try std.testing.expectEqual(total, plans.oods.offsets.len);
    try std.testing.expectEqual(total, p.capture.sampled_values.len);
    // (3) FRI: one first layer plus the inner layers; the last layer's size.
    try std.testing.expectEqual(1 + stark.fri_proof.inner_layers.len, geo.fri_layers.len);
    try std.testing.expectEqual(stark.fri_proof.last_layer_poly.coeffs.len, @as(usize, 1) << @intCast(p.cfg.fri_config.log_last_layer_degree_bound));
    // (4) The composition plan: one placement per component, every constraint once.
    var constraints: u64 = 0;
    for (plans.bundle.components) |c| constraints += c.n_constraints;
    try std.testing.expectEqual(constraints, plans.composition.topology.summary.constraint_count);
    try std.testing.expectEqual(@as(usize, bs.N_COMP), plans.composition.placements.len);
    std.debug.print("  resident plans match the CPU proof: trees {d}/{d}/{d}/{d} columns (lifted to {d}/{d}/{d}/{d}), {d} OODS samples, {d} FRI layers, {d} constraints, {d} composition constants\n", .{
        geo.trees[0].column_logs.len, geo.trees[1].column_logs.len, geo.trees[2].column_logs.len, geo.trees[3].column_logs.len,
        geo.trees[0].lifted_log,      geo.trees[1].lifted_log,      geo.trees[2].lifted_log,      geo.trees[3].lifted_log,
        total,                        geo.fri_layers.len,           constraints,                  plans.composition.constants.len,
    });
}

fn checkHostTranscript(a: std.mem.Allocator, p: *const Proved) !void {
    const stark = &p.proof.stark.commitment_scheme_proof;
    const roots = stark.commitments.items;
    var statement = try transcript.Statement.init(a, &p.parts);
    defer statement.deinit(a);
    var sink = transcript.HostSink{};
    var prefix = transcript.Prefix(transcript.HostSink){ .sink = &sink };
    try prefix.mixConfig(p.cfg);
    try prefix.commitPreprocessed(roots[0]);
    try prefix.mixStatement(statement, statement.words);
    try prefix.commitMain(roots[1]);
    _ = try prefix.drawLookupElements();
    try prefix.mixInteractionClaim(p.proof.claimed_sums);
    try prefix.commitInteraction(roots[2]);
    try prefix.admitComposition();
    // The tail, in stwo's order; each challenge must be the verifier's.
    var ch = &sink.channel;
    try std.testing.expect(ch.drawSecureFelt().eql(p.capture.composition_randomness));
    rec.MerkleChannel.mixRoot(ch, roots[3]);
    try std.testing.expect(ch.drawSecureFelt().eql(p.capture.oods_seed));
    ch.mixFelts(p.capture.sampled_values);
    try std.testing.expect(ch.drawSecureFelt().eql(p.capture.deep_randomness));
    rec.MerkleChannel.mixRoot(ch, stark.fri_proof.first_layer.commitment);
    _ = ch.drawSecureFelt();
    for (stark.fri_proof.inner_layers) |l| {
        rec.MerkleChannel.mixRoot(ch, l.commitment);
        _ = ch.drawSecureFelt();
    }
    ch.mixFelts(stark.fri_proof.last_layer_poly.coeffs);
    try std.testing.expect(ch.verifyPowNonce(p.cfg.fri_config.pow_bits, stark.proof_of_work));
    ch.mixU64(stark.proof_of_work);
    const raw = try core.queries.drawQueries(ch, a, p.cfg.trace_lifting_log_size, p.cfg.fri_config.n_queries);
    try std.testing.expectEqualSlices(usize, p.capture.queries.raw, raw);
}

/// The device sink's whole call sequence on the host model, fed the proof's roots and values as
/// device words: every challenge it writes is the verifier's, the grind finds the proof's nonce
/// and the drawn queries are the proof's.
fn checkDeviceSinkModel(a: std.mem.Allocator, p: *const Proved) !void {
    const stark = &p.proof.stark.commitment_scheme_proof;
    const roots = stark.commitments.items;
    var model = transcript.HostModel{ .allocator = a };
    defer model.deinit();
    var session = transcript.HostModel.Session{ .model = &model, .context = .{ .model = &model } };
    const bindings = transcript.Bindings{
        .state = try model.alloc(u32, 16),
        .boundary_snapshot = try model.alloc(u32, 16),
        .fri_config = try model.alloc(u32, 8),
        .lookup = try model.alloc(cuda.abi.field.SecureField, 2),
        .pow_prefix = try model.alloc(u32, 8),
        .pow_best_nonce = try model.alloc(u64, 1),
        .pow_completed_blocks = try model.alloc(u32, 16),
        .pow_nonce_words = try model.alloc(u32, 2),
    };
    var sink = try transcript.ModelSink.init(&session, bindings, [_]u8{1} ** 32);
    // Ingress: everything the host knows before proving.
    try sink.prime(p.cfg);
    var statement = try transcript.Statement.init(a, &p.parts);
    defer statement.deinit(a);
    const statement_view = try model.alloc(u32, statement.words.len);
    try session.context.uploadSlice(u32, statement_view, statement.words);
    // Device-produced words (roots, sums, sampled values, FRI data), here copied from the proof.
    const root = struct {
        fn put(m: *transcript.HostModel, h: rec.Hasher.Hash) !common.Words {
            const v = try m.alloc(u32, 8);
            @memcpy(std.mem.sliceAsBytes(try m.wordsOf(v)), std.mem.asBytes(&h));
            return v;
        }
        fn felts(m: *transcript.HostModel, xs: []const QM31) !common.SecureFields {
            const v = try m.alloc(cuda.abi.field.SecureField, xs.len);
            const w = try m.wordsOf(v);
            for (xs, 0..) |x, i| for (x.toM31Array(), 0..) |c, k| {
                w[4 * i + k] = c.toU32();
            };
            return v;
        }
        fn read(m: *transcript.HostModel, v: common.SecureFields) !QM31 {
            const w = try m.wordsOf(v);
            return QM31.fromU32Unchecked(w[0], w[1], w[2], w[3]);
        }
    };
    try sink.initialize();
    var prefix = transcript.Prefix(transcript.ModelSink){ .sink = &sink };
    try prefix.mixConfig(p.cfg);
    try prefix.commitPreprocessed(try root.put(&model, roots[0]));
    try prefix.mixStatement(statement, statement_view);
    try prefix.commitMain(try root.put(&model, roots[1]));
    _ = try prefix.drawLookupElements();
    try prefix.mixInteractionClaim(try (try root.felts(&model, p.proof.claimed_sums)).cast(u32));
    try prefix.commitInteraction(try root.put(&model, roots[2]));
    try prefix.admitComposition();
    sink.readyForComposition();
    const challenge = try model.alloc(cuda.abi.field.SecureField, 1);
    try sink.drawCompositionAlpha(challenge);
    try std.testing.expect((try root.read(&model, challenge)).eql(p.capture.composition_randomness));
    try sink.mixCompositionRoot(try root.put(&model, roots[3]));
    try sink.drawOodsParameter(challenge);
    try std.testing.expect((try root.read(&model, challenge)).eql(p.capture.oods_seed));
    try sink.mixSampledValues(try root.felts(&model, p.capture.sampled_values));
    try sink.drawQuotientAlpha(challenge);
    try std.testing.expect((try root.read(&model, challenge)).eql(p.capture.deep_randomness));
    const fri = &stark.fri_proof;
    try sink.setFriLayers(@intCast(1 + fri.inner_layers.len));
    try sink.mixFriRoot(try root.put(&model, fri.first_layer.commitment));
    try sink.drawFriAlpha(challenge);
    for (fri.inner_layers) |l| {
        try sink.mixFriRoot(try root.put(&model, l.commitment));
        try sink.drawFriAlpha(challenge);
    }
    try sink.mixLastLayer(try root.felts(&model, fri.last_layer_poly.coeffs));
    try sink.absorbQueryPow();
    try std.testing.expectEqual(stark.proof_of_work, model.last_nonce);
    const queries = try model.alloc(u32, p.cfg.fri_config.n_queries);
    try sink.drawQueries(queries, p.cfg.trace_lifting_log_size);
    const got = try model.wordsOf(queries);
    for (p.capture.queries.raw, got) |want, q| try std.testing.expectEqual(want, @as(usize, q));
    std.debug.print("  transcript: host channel and device-sink model reproduce every CPU challenge ({d} statement mixes, {d} device transcript calls, query nonce {d})\n", .{ statement.calls(), model.calls, model.last_nonce });
}

test "cuda resident: plans and transcript reproduce CPU block proofs (uniform and tiered)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var cat = try catalog_mod.Catalog.init(a, airs);
    defer cat.deinit();
    for ([_]Case{ .{ .profile = .uniform, .min_log = 0 }, .{ .profile = .tiered, .min_log = bs.TIERED_MIN_L } }) |c| {
        const p = try proveSample(a, airs, c);
        try checkPlans(a, &cat, &p);
        try checkHostTranscript(a, &p);
        try checkDeviceSinkModel(a, &p);
        _ = try perComponentSums(a, &p.parts, p.proof.claimed_sums);
    }
}
