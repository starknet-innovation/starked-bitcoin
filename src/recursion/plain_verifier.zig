//! In-circuit verifier for `prove_rec` proofs of an IR AIR: multi-offset masks, no LogUp phase
//! (roadmap REC-MASK, decision D-024; docs/design/recursion.md).
//!
//! stwo-zig's circuit verifier (a byte-parity port of StarkWare's) supports one OODS sample per
//! trace column and always runs an interaction phase. This is a parallel path built from its
//! public pieces (channel, FRI, Merkle paths, `computeFriInput`, `friDecommit`), leaving the
//! parity path untouched. It replays exactly the native transcript of `src/air/prove_rec.zig`
//! (`core.verifier` with the `proving_5a7c5ed` Blake2sM31 profile):
//!
//! FRI config → preprocessed root (a constant) → statement words (`prove.mixStatement`) → main
//! root → composition coefficient → composition root → OODS point → all OODS samples (tree,
//! column, mask order) → composition check → DEEP coefficient → FRI commit → PoW → queries →
//! Merkle decommitment (three trees) → DEEP quotients → FRI decommitment.
//!
//! Tree indices follow the circuit's four-tree layout with an empty interaction tree:
//! 0 = preprocessed, 1 = main, 2 = (unused), 3 = composition.
//! The constraint evaluation runs the AIR's exported DAG (proven to evaluate to the constraints
//! in any commutative ring: `dag_correct`, lean/StarkedAir/Dag.lean).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const ir = @import("../air/ir.zig");

const builder = circuit.builder;
const sv = circuit.stark_verifier;
const Var = builder.Var;
const Context = builder.Context;
const HashValue = builder.blake.HashValue;
const M31Wrapper = builder.wrappers.M31Wrapper;
const U32Wrapper = builder.wrappers.U32Wrapper;
const Point = sv.circle.Point;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
pub const FriConfig = core.pcs.config_v2.FriConfigV2;

pub const N_COMPOSITION_COLUMNS: usize = 8;
const TREE_PRE: usize = 0;
const TREE_MAIN: usize = 1;
const TREE_COMPOSITION: usize = 3;

/// Shape of a plain proof: trace size, FRI parameters, and the AIR's columns and offsets.
pub const PlainConfig = struct {
    log_trace_size: u32,
    fri: FriConfig,
    n_preprocessed: usize,
    /// Sorted mask offsets of every main column (as the native component samples them).
    main_offsets: []const []const i32,

    pub fn logEvaluationDomainSize(self: PlainConfig) usize {
        return self.log_trace_size + self.fri.log_blowup_factor;
    }
    pub fn nQueries(self: PlainConfig) usize {
        return self.fri.n_queries;
    }
};

/// The proof values the circuit consumes (over `QM31` for witnesses, over `Var` in-circuit).
pub fn PlainProof(comptime T: type) type {
    return struct {
        trace_root: HashValue(T),
        composition_root: HashValue(T),
        preprocessed_at_oods: []T,
        /// Per main column, one value per mask offset (in `main_offsets` order).
        trace_at_oods: [][]T,
        composition_eval_at_oods: [N_COMPOSITION_COLUMNS]T,
        eval_domain_samples: sv.proof.EvalDomainSamples(T),
        eval_domain_auth_paths: sv.proof.AuthPaths(T),
        pow_nonce: T,
        fri: sv.proof.FriProof(T),
    };
}

// ---------------------------------------------------------------- native proof → values

/// Builds the circuit's proof values from a native proof and the native verifier's capture
/// (`core.verifier.verifyWithProofCapture`). Everything lives in `a` (an arena).
pub fn fromCapture(
    a: std.mem.Allocator,
    comptime H: type,
    proof: *const core.proof.StarkProof(H),
    capture: *const core.verifier.ProofCapture(H),
    config: PlainConfig,
) !PlainProof(QM31) {
    const stark = &proof.commitment_scheme_proof;
    if (stark.commitments.items.len != 3 or stark.sampled_values.items.len != 3) return error.InvalidPlainProof;
    const n_queries = config.nQueries();
    const queries = capture.queries.raw;
    if (queries.len != n_queries) return error.InvalidPlainProof;

    var out: PlainProof(QM31) = undefined;
    out.trace_root = builder.blake.hashValueFromDigest(QM31, stark.commitments.items[1]);
    out.composition_root = builder.blake.hashValueFromDigest(QM31, stark.commitments.items[2]);

    const pre = stark.sampled_values.items[0];
    if (pre.len != config.n_preprocessed) return error.InvalidPlainProof;
    out.preprocessed_at_oods = try a.alloc(QM31, pre.len);
    for (pre, out.preprocessed_at_oods) |samples, *v| {
        if (samples.len != 1) return error.InvalidPlainProof;
        v.* = samples[0];
    }
    const main = stark.sampled_values.items[1];
    if (main.len != config.main_offsets.len) return error.InvalidPlainProof;
    out.trace_at_oods = try a.alloc([]QM31, main.len);
    for (main, config.main_offsets, out.trace_at_oods) |samples, offsets, *v| {
        if (samples.len != offsets.len) return error.InvalidPlainProof;
        v.* = try a.dupe(QM31, samples);
    }
    const comp = stark.sampled_values.items[2];
    if (comp.len != N_COMPOSITION_COLUMNS) return error.InvalidPlainProof;
    for (comp, &out.composition_eval_at_oods) |samples, *v| {
        if (samples.len != 1) return error.InvalidPlainProof;
        v.* = samples[0];
    }

    // Eval-domain samples per (tree, column, query), from `queried_values` (per sorted unique position).
    const sorted = try a.dupe(usize, queries);
    std.mem.sort(usize, sorted, {}, std.sort.asc(usize));
    var n_unique: usize = 0;
    for (sorted, 0..) |q, i| {
        if (i == 0 or q != sorted[n_unique - 1]) {
            sorted[n_unique] = q;
            n_unique += 1;
        }
    }
    const unique = sorted[0..n_unique];
    out.eval_domain_samples.n_queries = n_queries;
    const native_tree = [4]?usize{ 0, 1, null, 2 };
    for (native_tree, 0..) |nt, tree| {
        if (nt == null) {
            out.eval_domain_samples.data[tree] = &.{};
            continue;
        }
        const queried = stark.queried_values.items[nt.?];
        const samples = try a.alloc(M31Wrapper(QM31), queried.len * n_queries);
        for (queried, 0..) |column, c| {
            if (column.len != unique.len) return error.InvalidPlainProof;
            for (queries, 0..) |position, q| {
                const rank = std.sort.binarySearch(usize, unique, position, struct {
                    fn order(x: usize, y: usize) std.math.Order {
                        return std.math.order(x, y);
                    }
                }.order) orelse return error.MissingDecommitmentValue;
                samples[c * n_queries + q] = builder.wrappers.m31Value(QM31, column[rank]);
            }
        }
        out.eval_domain_samples.data[tree] = samples;
    }

    // Eval-domain authentication paths.
    const depth = config.logEvaluationDomainSize();
    if (capture.trace_paths.len != 3) return error.InvalidPlainProof;
    const trees = try a.alloc([]HashValue(QM31), 4);
    for (native_tree, 0..) |nt, tree| {
        if (nt == null) {
            trees[tree] = &.{};
            continue;
        }
        const path = capture.trace_paths[nt.?];
        if (path.path_depth != depth or path.positions.len != n_queries) return error.InvalidPlainProof;
        const nodes = try a.alloc(HashValue(QM31), n_queries * depth);
        for (queries, 0..) |query, q| {
            if (path.positions[q] != query) return error.InvalidPlainProof;
            for (path.path(q), 0..) |node, level| nodes[q * depth + level] = builder.blake.hashValueFromDigest(QM31, node);
        }
        trees[tree] = nodes;
    }
    out.eval_domain_auth_paths = .{ .n_queries = n_queries, .trees = trees };
    out.pow_nonce = QM31.fromM31(M31.fromU64(stark.proof_of_work & 0xffff_ffff), M31.fromU64(stark.proof_of_work >> 32), M31.zero(), M31.zero());

    // FRI: layer commitments, last layer, and per layer the query paths and fold cosets.
    const layers = capture.fri.layers;
    if (stark.fri_proof.inner_layers.len + 1 != layers.len) return error.InvalidPlainProof;
    const commitments = try a.alloc(HashValue(QM31), layers.len);
    commitments[0] = builder.blake.hashValueFromDigest(QM31, stark.fri_proof.first_layer.commitment);
    for (stark.fri_proof.inner_layers, commitments[1..]) |layer, *c| c.* = builder.blake.hashValueFromDigest(QM31, layer.commitment);
    const fri_trees = try a.alloc([]HashValue(QM31), layers.len);
    const witness = try a.alloc([]QM31, layers.len);
    var fold_sum: usize = 0;
    for (layers, 0..) |layer, l| {
        const nodes = try a.alloc(HashValue(QM31), n_queries * layer.path_depth);
        const coset = try a.alloc(QM31, n_queries * layer.fold_width);
        if (layer.query_count != n_queries) return error.InvalidPlainProof;
        for (queries, 0..) |query, q| {
            if (layer.positions[q] != query >> @intCast(fold_sum)) return error.InvalidPlainProof;
            for (layer.queryPath(q), 0..) |node, i| nodes[q * layer.path_depth + i] = builder.blake.hashValueFromDigest(QM31, node);
            @memcpy(coset[q * layer.fold_width ..][0..layer.fold_width], layer.queryValues(q));
        }
        fri_trees[l] = nodes;
        witness[l] = coset;
        fold_sum += std.math.log2_int(usize, layer.fold_width);
    }
    out.fri = .{
        .layer_commitments = commitments,
        .last_layer_coefs = try a.dupe(QM31, stark.fri_proof.last_layer_poly.coeffs),
        .auth_paths = .{ .n_queries = n_queries, .trees = fri_trees },
        .witness = witness,
    };
    return out;
}

// ---------------------------------------------------------------- guessing into the circuit

pub fn guess(comptime V: type, ctx: *Context(V), p: *const PlainProof(V)) !PlainProof(Var) {
    const s = ctx.scratch();
    var out: PlainProof(Var) = undefined;
    out.trace_root = try builder.blake.guessHash(V, ctx, p.trace_root);
    out.composition_root = try builder.blake.guessHash(V, ctx, p.composition_root);
    out.preprocessed_at_oods = try s.alloc(Var, p.preprocessed_at_oods.len);
    for (out.preprocessed_at_oods, p.preprocessed_at_oods) |*w, v| w.* = try ctx.guess(v);
    out.trace_at_oods = try s.alloc([]Var, p.trace_at_oods.len);
    for (out.trace_at_oods, p.trace_at_oods) |*ws, vs| {
        ws.* = try s.alloc(Var, vs.len);
        for (ws.*, vs) |*w, v| w.* = try ctx.guess(v);
    }
    for (&out.composition_eval_at_oods, p.composition_eval_at_oods) |*w, v| w.* = try ctx.guess(v);
    out.eval_domain_samples.n_queries = p.eval_domain_samples.n_queries;
    for (&out.eval_domain_samples.data, p.eval_domain_samples.data) |*ws, vs| {
        ws.* = try s.alloc(M31Wrapper(Var), vs.len);
        for (ws.*, vs) |*w, v| w.* = try builder.wrappers.guessM31(V, ctx, v);
    }
    out.eval_domain_auth_paths = try guessPaths(V, ctx, p.eval_domain_auth_paths);
    out.pow_nonce = try ctx.guess(p.pow_nonce);
    out.fri.layer_commitments = try s.alloc(HashValue(Var), p.fri.layer_commitments.len);
    for (out.fri.layer_commitments, p.fri.layer_commitments) |*w, v| w.* = try builder.blake.guessHash(V, ctx, v);
    out.fri.last_layer_coefs = try s.alloc(Var, p.fri.last_layer_coefs.len);
    for (out.fri.last_layer_coefs, p.fri.last_layer_coefs) |*w, v| w.* = try ctx.guess(v);
    out.fri.auth_paths = try guessPaths(V, ctx, p.fri.auth_paths);
    out.fri.witness = try s.alloc([]Var, p.fri.witness.len);
    for (out.fri.witness, p.fri.witness) |*ws, vs| {
        ws.* = try s.alloc(Var, vs.len);
        for (ws.*, vs) |*w, v| w.* = try ctx.guess(v);
    }
    return out;
}

fn guessPaths(comptime V: type, ctx: *Context(V), paths: sv.proof.AuthPaths(V)) !sv.proof.AuthPaths(Var) {
    const trees = try ctx.scratch().alloc([]HashValue(Var), paths.trees.len);
    for (trees, paths.trees) |*ws, nodes| {
        ws.* = try ctx.scratch().alloc(HashValue(Var), nodes.len);
        for (ws.*, nodes) |*w, node| w.* = try builder.blake.guessHash(V, ctx, node);
    }
    return .{ .n_queries = paths.n_queries, .trees = trees };
}

// ---------------------------------------------------------------- the statement

/// What a plain proof claims: the AIR (its DAG, digest and preprocessed root) and its public
/// inputs (circuit wires, so a leaf can expose them).
pub const PlainStatement = struct {
    air: *const ir.Air,
    digest: [32]u8,
    preprocessed_root: [32]u8,
    pubs: []const Var,
};

/// The AIR's constraint DAG at the OODS point, Horner-combined with `coeff` and divided by
/// the trace domain's vanishing polynomial (as the native component does).
fn compositionAtOods(
    comptime V: type,
    ctx: *Context(V),
    st: *const PlainStatement,
    config: PlainConfig,
    p: *const PlainProof(Var),
    oods_x: Var,
    coeff: Var,
) !Var {
    const air = st.air;
    const vals = try ctx.scratch().alloc(Var, air.exprs.len);
    for (air.exprs, 0..) |node, k| vals[k] = switch (node) {
        .col => |c| switch (c.tree) {
            .preprocessed => blk: {
                if (c.offset != 0) return error.PreprocessedOffset;
                break :blk p.preprocessed_at_oods[c.index];
            },
            .main => blk: {
                const offs = config.main_offsets[c.index];
                const at = std.mem.indexOfScalar(i32, offs, c.offset) orelse return error.UnknownMaskOffset;
                break :blk p.trace_at_oods[c.index][at];
            },
        },
        .constant => |v| try ctx.constant(QM31.fromBase(M31.fromCanonical(v))),
        .add => |ab| try ctx.add(vals[ab[0]], vals[ab[1]]),
        .sub => |ab| try ctx.sub(vals[ab[0]], vals[ab[1]]),
        .mul => |ab| try ctx.mul(vals[ab[0]], vals[ab[1]]),
        .neg => |x| try ctx.sub(ctx.zero(), vals[x]),
        .@"pub" => |i| st.pubs[i],
    };
    var acc = ctx.zero();
    for (air.constraints) |root| acc = try ctx.add(try ctx.mul(acc, coeff), vals[root]);
    return ctx.mul(acc, try sv.circle.denomInverse(V, ctx, oods_x, config.log_trace_size));
}

fn hashLeafM31s(comptime V: type, ctx: *Context(V), values: []const M31Wrapper(Var)) !HashValue(Var) {
    const words = try ctx.scratch().alloc(U32Wrapper(Var), values.len);
    for (words, values) |*word, value| word.* = try builder.blake.m31ToU32(V, ctx, value.get());
    return builder.blake.blake2sU32s(V, ctx, words, 4 * values.len);
}

// ---------------------------------------------------------------- verification

pub fn verifyPlain(
    comptime V: type,
    ctx: *Context(V),
    p: *const PlainProof(Var),
    config: PlainConfig,
    st: *const PlainStatement,
) !void {
    const log_trace = config.log_trace_size;
    var channel = sv.channel.Channel.init(V, ctx);
    try sv.fri.mixFriConfig(V, ctx, &channel, config.fri);

    const pre_root = try builder.blake.constantHash(V, ctx, builder.blake.hashValueFromDigest(QM31, st.preprocessed_root));
    try channel.mixCommitment(V, ctx, pre_root);

    // Statement: [log_size, digest (8 words), n_pubs], then one call per public input.
    var words: [10]U32Wrapper(Var) = undefined;
    words[0] = try builder.wrappers.constU32(V, ctx, log_trace);
    for (0..8) |i| words[1 + i] = try builder.wrappers.constU32(V, ctx, std.mem.readInt(u32, st.digest[4 * i ..][0..4], .little));
    words[9] = try builder.wrappers.constU32(V, ctx, @intCast(st.pubs.len));
    try channel.mixU32s(V, ctx, &words);
    for (st.pubs) |pv| try channel.mixU32s(V, ctx, &.{try builder.blake.m31ToU32(V, ctx, pv)});

    try channel.mixCommitment(V, ctx, p.trace_root);
    const coeff = try channel.drawQm31(V, ctx);
    try channel.mixCommitment(V, ctx, p.composition_root);
    const oods = try channel.drawPoint(V, ctx);

    // All OODS samples: preprocessed, main (mask order), composition.
    var values: std.ArrayListUnmanaged(Var) = .empty;
    try values.appendSlice(ctx.scratch(), p.preprocessed_at_oods);
    for (p.trace_at_oods) |col| try values.appendSlice(ctx.scratch(), col);
    try values.appendSlice(ctx.scratch(), &p.composition_eval_at_oods);
    try channel.mixQm31s(V, ctx, values.items);

    const computed = try compositionAtOods(V, ctx, st, config, p, oods.x, coeff);
    const expected = try sv.oods.extractExpectedCompositionEval(V, ctx, &p.composition_eval_at_oods, oods, log_trace + 1);
    try ctx.eq(computed, expected);

    const quotient_coef = try channel.drawQm31(V, ctx);
    const fri_alphas = try sv.fri.friCommit(V, ctx, &channel, &p.fri);
    try channel.pow(V, ctx, config.fri.pow_bits, p.pow_nonce);
    const sel = try sv.select_queries.getQuerySelectionInputFromChannel(V, ctx, &channel, config.nQueries());
    const queries = try sv.select_queries.selectQueries(V, ctx, sel, config.logEvaluationDomainSize());
    const bits = try ctx.scratch().alloc([]const Var, queries.bits.len);
    for (bits, queries.bits) |*u, b| u.* = try builder.simd.unpack(V, ctx, b);

    // Merkle decommitment of the three trees (all at the evaluation-domain height; no sorting).
    const roots = [4]?HashValue(Var){ pre_root, p.trace_root, null, p.composition_root };
    const bits_for_query = try ctx.scratch().alloc(Var, bits.len);
    for (roots, 0..) |maybe_root, tree| {
        const root = maybe_root orelse continue;
        const n_columns = p.eval_domain_samples.nColumns(tree);
        const leaf_values = try ctx.scratch().alloc(M31Wrapper(Var), n_columns);
        for (0..config.nQueries()) |q| {
            for (leaf_values, 0..) |*v, c| v.* = p.eval_domain_samples.at(tree, c, q);
            const leaf = try hashLeafM31s(V, ctx, leaf_values);
            for (bits_for_query, bits) |*b, qb| b.* = qb[q];
            try sv.merkle.verifyMerklePath(V, ctx, leaf, bits_for_query, root, p.eval_domain_auth_paths.at(tree, q));
        }
    }

    // DEEP quotient inputs, in the native sample order (tree, column, mask; a two-sample column
    // is preceded by its periodicity sample, which coincides with the first one here).
    const trace_gen = core.poly.circle.canonic.CanonicCoset.new(log_trace).coset_value.step;
    var responses: std.ArrayListUnmanaged(sv.oods.OodsResponse) = .empty;
    for (p.preprocessed_at_oods, 0..) |v, c|
        try responses.append(ctx.scratch(), .{ .trace_idx = TREE_PRE, .column_idx = c, .pt = oods, .value = v });
    var shifted = std.AutoHashMapUnmanaged(i32, Point(Var)).empty;
    for (config.main_offsets, p.trace_at_oods, 0..) |offs, vals, c| {
        const pts = try ctx.scratch().alloc(Point(Var), offs.len);
        for (offs, pts) |off, *pt| {
            if (off == 0) {
                pt.* = oods;
                continue;
            }
            const got = try shifted.getOrPut(ctx.scratch(), off);
            if (!got.found_existing) {
                const g = trace_gen.mulSigned(@intCast(off));
                got.value_ptr.* = try sv.circle.addPoints(V, ctx, oods, .{
                    .x = try ctx.constant(QM31.fromBase(g.x)),
                    .y = try ctx.constant(QM31.fromBase(g.y)),
                });
            }
            pt.* = got.value_ptr.*;
        }
        if (offs.len == 2) try responses.append(ctx.scratch(), .{ .trace_idx = TREE_MAIN, .column_idx = c, .pt = pts[1], .value = vals[1] });
        for (pts, vals) |pt, v| try responses.append(ctx.scratch(), .{ .trace_idx = TREE_MAIN, .column_idx = c, .pt = pt, .value = v });
    }
    for (p.composition_eval_at_oods, 0..) |v, c|
        try responses.append(ctx.scratch(), .{ .trace_idx = TREE_COMPOSITION, .column_idx = c, .pt = oods, .value = v });

    const fri_input = try sv.oods.computeFriInput(V, ctx, responses.items, queries, &p.eval_domain_samples, quotient_coef);
    try sv.fri.friDecommit(V, ctx, &p.fri, log_trace, config.fri, fri_input, bits, queries, fri_alphas);
}

// ---------------------------------------------------------------- tests

const prove_base = @import("../air/prove.zig");
const prove_rec = @import("../air/prove_rec.zig");

/// The sorted main-column offsets of `air` (as the native component computes them).
pub fn mainOffsets(a: std.mem.Allocator, air: ir.Air) ![]const []const i32 {
    const offs = try air.columnOffsets(a, .main);
    for (offs) |o| std.mem.sort(i32, o, {}, std.sort.asc(i32));
    return offs;
}

fn runCircuit(a: std.mem.Allocator, values: *const PlainProof(QM31), config: PlainConfig, air: *const ir.Air, digest: [32]u8, pre_root: [32]u8, pubs: []const M31) !bool {
    var ctx = try Context(QM31).init(a, 0);
    defer ctx.deinit();
    const pv = try guess(QM31, &ctx, values);
    const pub_vars = try a.alloc(Var, pubs.len);
    for (pub_vars, pubs) |*w, v| w.* = try ctx.guess(QM31.fromBase(v));
    const st = PlainStatement{ .air = air, .digest = digest, .preprocessed_root = pre_root, .pubs = pub_vars };
    try verifyPlain(QM31, &ctx, &pv, config, &st);
    try ctx.finalizeGuessedVars();
    if (std.process.hasEnvVarConstant("PLAIN_VERIFIER_STATS"))
        std.debug.print("plain verifier circuit: {d} vars\n", .{ctx.circuit.n_vars});
    return ctx.isCircuitValid();
}

test "plain in-circuit verifier accepts a recursion-profile header-chain proof, rejects tampering" {
    const H = @import("../btc/header_chain.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, H.lean_json)).value;
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const log_size: u32 = 12;
    const wit = try H.generate(a, log_size, headers);
    const cfg = try prove_rec.config(log_size);
    const digest = try air.digest(a);
    const statement = prove_base.AirStatement{ .log_size = log_size, .digest = digest, .pubs = &wit.pubs, .air = &air, .allocator = a };
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    // Proving is deterministic: one copy is consumed by the native verifier, one is converted.
    const proof_a = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    const proof_b = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try prove_rec.verifyCapture(a, cfg, air, log_size, &wit.pubs, proof_a, &capture);

    const config = PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .n_preprocessed = air.n_preprocessed, .main_offsets = try mainOffsets(a, air) };
    const pre_root: [32]u8 = std.mem.toBytes(try prove_rec.preprocessedRoot(a, cfg, air, log_size));
    var values = try fromCapture(a, prove_rec.Hasher, &proof_b, &capture, config);
    try std.testing.expect(try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));

    // A wrong public input, a tampered OODS sample, or a tampered decommitted value is rejected.
    var bad_pubs = wit.pubs;
    bad_pubs[16] = bad_pubs[16].add(M31.one());
    try std.testing.expect(!try runCircuit(a, &values, config, &air, digest, pre_root, &bad_pubs));
    {
        const saved = values.trace_at_oods[5][0];
        values.trace_at_oods[5][0] = saved.add(QM31.one());
        try std.testing.expect(!try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));
        values.trace_at_oods[5][0] = saved;
    }
    {
        const tree = &values.eval_domain_samples.data[TREE_MAIN];
        const saved = tree.*[7];
        tree.*[7] = builder.wrappers.m31Value(QM31, saved.get().toM31Array()[0].add(M31.one()));
        try std.testing.expect(!try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));
        tree.*[7] = saved;
    }
    {
        const saved = values.fri.witness[0][3];
        values.fri.witness[0][3] = saved.add(QM31.one());
        try std.testing.expect(!try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));
        values.fri.witness[0][3] = saved;
    }
    {
        const saved = values.composition_root;
        values.composition_root = builder.blake.hashValueFromDigest(QM31, [_]u8{1} ** 32);
        try std.testing.expect(!try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));
        values.composition_root = saved;
    }
    // Still accepted after restoring everything.
    try std.testing.expect(try runCircuit(a, &values, config, &air, digest, pre_root, &wit.pubs));
}

test "plain verifier circuit size for one header-chain segment (2^12 rows)" {
    // Informational: printed, not asserted.
}
