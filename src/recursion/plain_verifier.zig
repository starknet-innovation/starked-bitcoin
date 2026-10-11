//! In-circuit verifier for `prove_rec` proofs of an IR AIR, and for `air/system.zig` proofs of
//! several components with LogUp (roadmap REC-MASK, IR-LOGUP; decision D-024;
//! docs/design/recursion.md).
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
//! Tree indices follow the circuit's four-tree layout: 0 = preprocessed, 1 = main,
//! 2 = interaction (empty without lookups), 3 = composition. With lookups (system proofs), after
//! the main root: lookup elements `(z, α)`, the check that the claimed sums add to zero, the
//! claimed sums and the interaction root are mixed, and each component's LogUp constraints
//! (`component.logupConstraintValues`, Lean `logup_sum`) join its composition.
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
const TREE_INTER: usize = 2;
const TREE_COMPOSITION: usize = 3;

/// One component's columns: preprocessed count, sorted main mask offsets, interaction columns.
pub const PartConfig = struct {
    n_preprocessed: usize,
    /// Sorted mask offsets of every main column (as the native component samples them).
    main_offsets: []const []const i32,
    /// `4 · nBatches`: LogUp cumulative-sum limbs (the last 4 sampled at the previous row too).
    n_inter: usize = 0,
};

/// Shape of a plain proof: trace size, FRI parameters, and the components' columns.
pub const PlainConfig = struct {
    log_trace_size: u32,
    fri: FriConfig,
    parts: []const PartConfig,
    /// A system proof (`air/system.zig`): the statement starts with the component count.
    system: bool = false,

    pub fn single(log_trace_size: u32, fri: FriConfig, n_preprocessed: usize, main_offsets: []const []const i32, a: std.mem.Allocator) !PlainConfig {
        return .{ .log_trace_size = log_trace_size, .fri = fri, .parts = try a.dupe(PartConfig, &.{.{ .n_preprocessed = n_preprocessed, .main_offsets = main_offsets }}) };
    }
    pub fn hasLookups(self: PlainConfig) bool {
        for (self.parts) |pc| if (pc.n_inter != 0) return true;
        return false;
    }

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
        /// Present iff the proof has lookups.
        interaction_root: ?HashValue(T) = null,
        composition_root: HashValue(T),
        /// All components' columns, in component order.
        preprocessed_at_oods: []T,
        /// Per main column, one value per mask offset (in `main_offsets` order).
        trace_at_oods: [][]T,
        /// Per interaction column: one value, or `[prev, cur]` for a component's last 4 limbs.
        interaction_at_oods: [][]T = &.{},
        /// Claimed LogUp sums of the components with lookups.
        claimed_sums: []T = &.{},
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
    claimed_sums: []const QM31,
) !PlainProof(QM31) {
    const stark = &proof.commitment_scheme_proof;
    const lookups = config.hasLookups();
    const n_native: usize = if (lookups) 4 else 3;
    if (stark.commitments.items.len != n_native or stark.sampled_values.items.len != n_native) return error.InvalidPlainProof;
    var n_pre: usize = 0;
    var n_main: usize = 0;
    var n_inter: usize = 0;
    for (config.parts) |pc| {
        n_pre += pc.n_preprocessed;
        n_main += pc.main_offsets.len;
        n_inter += pc.n_inter;
    }
    const n_queries = config.nQueries();
    const queries = capture.queries.raw;
    if (queries.len != n_queries) return error.InvalidPlainProof;

    var out: PlainProof(QM31) = undefined;
    out.trace_root = builder.blake.hashValueFromDigest(QM31, stark.commitments.items[1]);
    out.interaction_root = if (lookups) builder.blake.hashValueFromDigest(QM31, stark.commitments.items[2]) else null;
    out.composition_root = builder.blake.hashValueFromDigest(QM31, stark.commitments.items[n_native - 1]);
    out.claimed_sums = try a.dupe(QM31, claimed_sums);
    out.interaction_at_oods = &.{};

    const pre = stark.sampled_values.items[0];
    if (pre.len != n_pre) return error.InvalidPlainProof;
    out.preprocessed_at_oods = try a.alloc(QM31, pre.len);
    for (pre, out.preprocessed_at_oods) |samples, *v| {
        if (samples.len != 1) return error.InvalidPlainProof;
        v.* = samples[0];
    }
    const main = stark.sampled_values.items[1];
    if (main.len != n_main) return error.InvalidPlainProof;
    out.trace_at_oods = try a.alloc([]QM31, main.len);
    {
        var k: usize = 0;
        for (config.parts) |pc| for (pc.main_offsets) |offsets| {
            if (main[k].len != offsets.len) return error.InvalidPlainProof;
            out.trace_at_oods[k] = try a.dupe(QM31, main[k]);
            k += 1;
        };
    }
    if (lookups) {
        const inter = stark.sampled_values.items[2];
        if (inter.len != n_inter) return error.InvalidPlainProof;
        out.interaction_at_oods = try a.alloc([]QM31, n_inter);
        var k: usize = 0;
        for (config.parts) |pc| for (0..pc.n_inter) |c| {
            if (inter[k].len != (if (c + 4 >= pc.n_inter) @as(usize, 2) else 1)) return error.InvalidPlainProof;
            out.interaction_at_oods[k] = try a.dupe(QM31, inter[k]);
            k += 1;
        };
    }
    const comp = stark.sampled_values.items[n_native - 1];
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
    const native_tree: [4]?usize = if (lookups) .{ 0, 1, 2, 3 } else .{ 0, 1, null, 2 };
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
    if (capture.trace_paths.len != n_native) return error.InvalidPlainProof;
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
    out.interaction_root = if (p.interaction_root) |r| try builder.blake.guessHash(V, ctx, r) else null;
    out.interaction_at_oods = try s.alloc([]Var, p.interaction_at_oods.len);
    for (out.interaction_at_oods, p.interaction_at_oods) |*ws, vs| {
        ws.* = try s.alloc(Var, vs.len);
        for (ws.*, vs) |*w, v| w.* = try ctx.guess(v);
    }
    out.claimed_sums = try s.alloc(Var, p.claimed_sums.len);
    for (out.claimed_sums, p.claimed_sums) |*w, v| w.* = try ctx.guess(v);
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

/// One component's claim: its AIR (DAG and digest) and public inputs (circuit wires, so a leaf
/// can expose them).
pub const PartStatement = struct {
    air: *const ir.Air,
    digest: [32]u8,
    pubs: []const Var,
};

/// A public lookup entry, in-circuit: its values are wires (e.g. public inputs).
pub const ExtEntry = struct {
    rel: u32,
    vals: []const Var,
    mult: M31,
};

/// What a plain proof claims: the components, in order, the preprocessed root, and the public
/// lookup entries the relations balance with.
pub const PlainStatement = struct {
    parts: []const PartStatement,
    preprocessed_root: [32]u8,
    ext: []const ExtEntry = &.{},
    /// The composition check as a Lean-generated program (`Circuit/CompositionLogUp.lean`, proven in
    /// `CompositionSound.lean`); null: the hand-written `compositionAtOods` (the parity reference).
    composition: ?*const glue.Program = null,
    /// The LogUp balance check as a Lean program (`Circuit/Balance.lean`, `balance_sound`); null: the
    /// hand-written code. Hook 0 binds the claimed sums, the public entries' values, `z`, `α`.
    balance: ?*const glue.Program = null,
    /// The statement mixing as a Lean program (`Circuit/Statement.lean`, `pub_mixed`): hook 0 binds the
    /// public inputs; hook 3 is the channel's `mixU32s`; hook 4 creates a component's header constants.
    statement: ?*const glue.Program = null,
    /// Merkle leaf hashing as Lean programs (`Circuit/LeafHash.lean`, `leaf_sound`), one per row width;
    /// a width without a program uses the hand-written `hashLeafM31s`.
    leaf_hashes: []const *const glue.Program = &.{},
    /// The DEEP response table (`Circuit/Deep.lean`, `deep_sound`/`deep_complete`); null: the
    /// hand-written response loop.
    deep: ?*const DeepTable = null,
    /// One Merkle level as a Lean program (`Circuit/Merkle.lean`, `node_sound`; the levels and the
    /// root check below mirror `path`/`pathCheck`, `path_check_sound`); null: stwo-zig's
    /// `verifyMerklePath`.
    merkle_node: ?*const glue.Program = null,
    /// The channel operations as Lean programs (`Circuit/Channel.lean`); an operation without a
    /// matching program uses stwo-zig's.
    channel: ChannelProgs = .{},
    /// The transcript order (`Circuit/Transcript.lean`, the `*_bound` theorems): `verifyPlain` checks
    /// its channel events against it, in order; null: no check.
    transcript: ?[]const []const u8 = null,
    /// The shifted OODS points as Lean programs (`Circuit/Oods.lean`, `shift_sound`), per log size and
    /// offset; a pair without a program uses stwo-zig's `mulSigned` and `addPoints`.
    shifts: ?*const ShiftTable = null,
};

/// The Lean-exported shifted-point programs (`lean/Export.lean oods_shift_*`).
pub const ShiftTable = struct {
    pub const Entry = struct { log: u32, off: i32, x: u32, y: u32, prog: glue.Program };
    entries: []const Entry,

    pub fn parse(a: std.mem.Allocator, json: []const u8) !ShiftTable {
        const items = (try std.json.parseFromSliceLeaky(std.json.Value, a, json, .{})).array.items;
        const out = try a.alloc(Entry, items.len);
        for (out, items) |*e, item| {
            const o = item.object;
            e.* = .{
                .log = @intCast(o.get("log").?.integer),
                .off = @intCast(o.get("off").?.integer),
                .x = @intCast(o.get("x").?.integer),
                .y = @intCast(o.get("y").?.integer),
                .prog = try glue.parseValue(a, o.get("program").?.object),
            };
        }
        return .{ .entries = out };
    }

    pub fn find(self: *const ShiftTable, log: u32, off: i32) ?*const Entry {
        for (self.entries) |*e| if (e.log == log and e.off == off) return e;
        return null;
    }
};

/// `oods + off·g_log`: the Lean program when the table has one, else stwo-zig's constants and
/// `addPoints`.
fn shiftPoint(comptime V: type, ctx: *Context(V), table: ?*const ShiftTable, log: u32, off: i32, oods: Point(Var)) !Point(Var) {
    if (table) |t| if (t.find(log, off)) |e| {
        const Hooks = struct {
            inputs: []const Var,
            pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
                return if (id == 0) self.inputs else error.UnknownHook;
            }
        };
        const res = try glue.run(V, ctx, &e.prog, &.{}, Hooks{ .inputs = &.{ oods.x, oods.y } });
        return .{ .x = res[0], .y = res[1] };
    };
    const g = core.poly.circle.canonic.CanonicCoset.new(log).coset_value.step.mulSigned(off);
    return sv.circle.addPoints(V, ctx, oods, .{
        .x = try ctx.constant(QM31.fromBase(g.x)),
        .y = try ctx.constant(QM31.fromBase(g.y)),
    });
}

/// Parses a `starked-transcript-v1` event list.
pub fn parseTranscript(a: std.mem.Allocator, json: []const u8) ![]const []const u8 {
    const root = (try std.json.parseFromSliceLeaky(std.json.Value, a, json, .{})).object;
    if (!std.mem.eql(u8, root.get("schema").?.string, "starked-transcript-v1")) return error.BadTranscript;
    const items = root.get("events").?.array.items;
    const out = try a.alloc([]const u8, items.len);
    for (out, items) |*o, it| o.* = it.string;
    return out;
}

/// Steps through the Lean transcript next to each channel event.
const TranscriptCheck = struct {
    events: ?[]const []const u8,
    at: usize = 0,
    fn step(self: *TranscriptCheck, name: []const u8) !void {
        const evs = self.events orelse return;
        if (self.at >= evs.len or !std.mem.eql(u8, evs[self.at], name)) return error.TranscriptOrder;
        self.at += 1;
    }
    fn done(self: *const TranscriptCheck) !void {
        const evs = self.events orelse return;
        if (self.at != evs.len) return error.TranscriptOrder;
    }
};

/// Lean channel programs (`Circuit/Channel.lean`): hook 0 binds the digest halves, then the inputs.
pub const ChannelProgs = struct {
    /// `mixU32sP` (`mixU32s_sound`), one per word count (8 is `mix_commitment`).
    mix_u32s: []const *const glue.Program = &.{},
    /// `mixQm31sP` (`mixQm31s_sound`), one per value count.
    mix_qm31s: []const *const glue.Program = &.{},
    /// `drawP` (`draw_sound`), `drawQm31P`, `drawPointP` (`drawPoint_sound`): right after a mix.
    draw: ?*const glue.Program = null,
    draw_qm31: ?*const glue.Program = null,
    draw_point: ?*const glue.Program = null,
    /// `powMixP` (`powMix_sound`): the digest update after the proof of work.
    pow_mix: ?*const glue.Program = null,
    /// `powCheckP` (`Circuit/Pow.lean`, `powCheck_sound`): the proof-of-work check, one per `n_bits`.
    pow_check: []const PowCheck = &.{},
};

pub const PowCheck = struct { n_bits: u32, prog: *const glue.Program };

/// stwo-zig's channel state, driven by the Lean programs where one matches (gate-identical: tested).
const LeanChannel = struct {
    ch: *sv.channel.Channel,
    progs: *const ChannelProgs,

    const InputHooks = struct {
        inputs: []const Var,
        pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
            return if (id == 0) self.inputs else error.UnknownHook;
        }
    };

    fn find(list: []const *const glue.Program, n_in: usize) ?*const glue.Program {
        for (list) |prog| if (prog.ops.len != 0 and prog.ops[0] == .hook and prog.ops[0].hook.outs.len == 2 + n_in) return prog;
        return null;
    }

    fn run(self: LeanChannel, comptime V: type, ctx: *Context(V), prog: *const glue.Program, data: []const Var) ![]Var {
        const ins = try ctx.scratch().alloc(Var, 2 + data.len);
        ins[0] = self.ch.digest.low;
        ins[1] = self.ch.digest.high;
        @memcpy(ins[2..], data);
        return glue.run(V, ctx, prog, &.{}, InputHooks{ .inputs = ins });
    }

    fn setDigest(self: LeanChannel, res: []const Var) void {
        self.ch.digest = .{ .low = res[0], .high = res[1] };
        self.ch.n_draws = 0;
    }

    fn mixU32s(self: LeanChannel, comptime V: type, ctx: *Context(V), words: []const U32Wrapper(Var)) !void {
        const prog = find(self.progs.mix_u32s, words.len) orelse return self.ch.mixU32s(V, ctx, words);
        const data = try ctx.scratch().alloc(Var, words.len);
        for (data, words) |*d, w| d.* = w.get();
        self.setDigest(try self.run(V, ctx, prog, data));
    }

    fn mixCommitment(self: LeanChannel, comptime V: type, ctx: *Context(V), root: HashValue(Var)) !void {
        if (find(self.progs.mix_u32s, 8) == null) return self.ch.mixCommitment(V, ctx, root);
        return self.mixU32s(V, ctx, &root.words);
    }

    fn mixQm31s(self: LeanChannel, comptime V: type, ctx: *Context(V), values: []const Var) !void {
        const prog = find(self.progs.mix_qm31s, values.len) orelse return self.ch.mixQm31s(V, ctx, values);
        self.setDigest(try self.run(V, ctx, prog, values));
    }

    fn drawTwoQm31s(self: LeanChannel, comptime V: type, ctx: *Context(V)) ![2]Var {
        const prog = self.progs.draw orelse return self.ch.drawTwoQm31s(V, ctx);
        if (self.ch.n_draws != 0) return self.ch.drawTwoQm31s(V, ctx);
        const res = try self.run(V, ctx, prog, &.{});
        self.ch.n_draws += 1;
        return .{ res[0], res[1] };
    }

    fn drawQm31(self: LeanChannel, comptime V: type, ctx: *Context(V)) !Var {
        const prog = self.progs.draw_qm31 orelse return self.ch.drawQm31(V, ctx);
        if (self.ch.n_draws != 0) return self.ch.drawQm31(V, ctx);
        const res = try self.run(V, ctx, prog, &.{});
        self.ch.n_draws += 1;
        return res[0];
    }

    fn drawPoint(self: LeanChannel, comptime V: type, ctx: *Context(V)) !Point(Var) {
        const prog = self.progs.draw_point orelse return self.ch.drawPoint(V, ctx);
        if (self.ch.n_draws != 0) return self.ch.drawPoint(V, ctx);
        const res = try self.run(V, ctx, prog, &.{});
        self.ch.n_draws += 1;
        return .{ .x = res[0], .y = res[1] };
    }

    /// The proof-of-work check: the Lean program for `n_bits` when there is one (`powCheck_sound`),
    /// else stwo-zig's (`Channel.pow`, copied); the digest update is the Lean program.
    fn pow(self: LeanChannel, comptime V: type, ctx: *Context(V), n_bits: u32, nonce: Var) !void {
        const prog = self.progs.pow_mix orelse return self.ch.pow(V, ctx, n_bits, nonce);
        std.debug.assert(n_bits <= 30);
        const check: ?*const glue.Program = for (self.progs.pow_check) |pc| {
            if (pc.n_bits == n_bits) break pc.prog;
        } else null;
        if (check) |c| {
            _ = try self.run(V, ctx, c, &.{nonce});
        } else {
            const ivalue = builder.ivalue;
            const prefix = try ctx.constant(ivalue.qm31FromU32s(0x12345678, 0, 0, 0));
            const bits_word = try ctx.constant(ivalue.qm31FromU32s(n_bits, 0, 0, 0));
            const prefixed = try builder.blake.blake2sM31(V, ctx, &.{ prefix, self.ch.digest.low, self.ch.digest.high, bits_word }, 52);
            const high_mask = try ctx.constant(ivalue.qm31FromU32s(0, 0, 1, 1));
            const masked_nonce = try ctx.pointwiseMul(nonce, high_mask);
            try ctx.eq(masked_nonce, ctx.zero());
            const res = try builder.blake.blake2sM31(V, ctx, &.{ prefixed.low, prefixed.high, nonce }, 40);
            try ctx.markAsUnused(res.high);
            const first_word = try ctx.pointwiseMul(res.low, ctx.one());
            const bits = try builder.extract_bits.extractBits(V, ctx, .fromPacked(&.{first_word}, 1), 31);
            for (bits[0..n_bits]) |bit| try ctx.eq(bit.data[0], ctx.zero());
        }
        self.setDigest(try self.run(V, ctx, prog, &.{nonce}));
    }
};

/// `verifyMerklePath` by replaying the Lean level program: hook 0 binds the node, the sibling, the bit.
fn merklePathVia(comptime V: type, ctx: *Context(V), prog: *const glue.Program, leaf: HashValue(Var), bits: []const Var, root: HashValue(Var), auth_path: []const HashValue(Var)) !void {
    if (bits.len != auth_path.len) return error.InvalidPlainProof;
    const Hooks = struct {
        inputs: []const Var,
        pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
            return if (id == 0) self.inputs else error.UnknownHook;
        }
    };
    var node = leaf;
    const ins = try ctx.scratch().alloc(Var, 17);
    for (bits, auth_path) |bit, sibling| {
        for (ins[0..8], node.words) |*w, x| w.* = x.get();
        for (ins[8..16], sibling.words) |*w, x| w.* = x.get();
        ins[16] = bit;
        const res = try glue.run(V, ctx, prog, &.{}, Hooks{ .inputs = ins });
        for (&node.words, res) |*w, v| w.* = .newUnsafe(v);
    }
    for (node.words, root.words) |recomputed, expected| try ctx.eq(recomputed.get(), expected.get());
}

/// One DEEP response: tree, global column, mask offset, and the index of its value among the mixed
/// OODS samples.
pub const DeepResp = struct { tree: u32, col: u32, off: i32, idx: u32 };

pub const DeepTable = struct {
    n_samples: u32,
    responses: []const DeepResp,

    /// Parses a `starked-deep-v1` table (exported by `lean/Export.lean deep_*`).
    pub fn parse(a: std.mem.Allocator, json: []const u8) !DeepTable {
        const root = (try std.json.parseFromSliceLeaky(std.json.Value, a, json, .{})).object;
        if (!std.mem.eql(u8, root.get("schema").?.string, "starked-deep-v1")) return error.BadDeep;
        const items = root.get("responses").?.array.items;
        const out = try a.alloc(DeepResp, items.len);
        for (out, items) |*r, item| {
            const f = item.array.items;
            if (f.len != 4) return error.BadDeep;
            r.* = .{ .tree = @intCast(f[0].integer), .col = @intCast(f[1].integer), .off = @intCast(f[2].integer), .idx = @intCast(f[3].integer) };
        }
        return .{ .n_samples = @intCast(root.get("n_samples").?.integer), .responses = out };
    }
};

fn leafHashVia(comptime V: type, ctx: *Context(V), progs: []const *const glue.Program, values: []const M31Wrapper(Var)) !?HashValue(Var) {
    for (progs) |prog| {
        if (prog.ops.len == 0 or prog.ops[0] != .hook or prog.ops[0].hook.outs.len != values.len) continue;
        const ins = try ctx.scratch().alloc(Var, values.len);
        for (ins, values) |*w, v| w.* = v.get();
        const Hooks = struct {
            inputs: []const Var,
            pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
                return if (id == 0) self.inputs else error.UnknownHook;
            }
        };
        const res = try glue.run(V, ctx, prog, &.{}, Hooks{ .inputs = ins });
        var out: HashValue(Var) = undefined;
        for (&out.words, res) |*w, v| w.* = .newUnsafe(v);
        return out;
    }
    return null;
}

const glue = @import("glue.zig");

/// The composition check by replaying the Lean program: hook 0 binds the inputs in the Lean layout's
/// order (preprocessed, main, interaction samples, public inputs, claimed sums, coefficient, z, α,
/// OODS x), hook 1 is `1/Z(oods)` (stwo-zig), hook 2 the constant `1/2^L`.
fn compositionViaProgram(
    comptime V: type,
    ctx: *Context(V),
    prog: *const glue.Program,
    st: *const PlainStatement,
    config: PlainConfig,
    p: *const PlainProof(Var),
    oods_x: Var,
    coeff: Var,
    elements: ?[2]Var,
) !Var {
    var ins: std.ArrayListUnmanaged(Var) = .empty;
    const s = ctx.scratch();
    try ins.appendSlice(s, p.preprocessed_at_oods);
    for (p.trace_at_oods) |col| try ins.appendSlice(s, col);
    for (p.interaction_at_oods) |col| try ins.appendSlice(s, col);
    for (st.parts) |part| try ins.appendSlice(s, part.pubs);
    try ins.appendSlice(s, p.claimed_sums);
    const el = elements orelse .{ ctx.zero(), ctx.zero() };
    try ins.appendSlice(s, &.{ coeff, el[0], el[1], oods_x });
    const Hooks = struct {
        ctx: *Context(V),
        inputs: []const Var,
        log: u32,
        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            const out = try self.ctx.scratch().alloc(Var, 1);
            switch (id) {
                0 => return self.inputs,
                1 => out[0] = try sv.circle.denomInverse(V, self.ctx, args[0], self.log),
                2 => out[0] = try self.ctx.constant(QM31.fromBase(try M31.fromU64(@as(u64, 1) << @intCast(self.log)).inv())),
                else => return error.UnknownHook,
            }
            return out;
        }
    };
    const res = try glue.run(V, ctx, prog, &.{}, Hooks{ .ctx = ctx, .inputs = ins.items, .log = config.log_trace_size });
    return res[0];
}

/// `Σ eᵢ αⁱ − z` over `e = (rel, vals…)`, in-circuit (`component.denominator`).
fn denominatorVar(comptime V: type, ctx: *Context(V), rel: u32, vals: []const Var, z: Var, alpha: Var) !Var {
    var acc = ctx.zero();
    var i = vals.len;
    while (i > 0) {
        i -= 1;
        acc = try ctx.add(try ctx.mul(acc, alpha), vals[i]);
    }
    acc = try ctx.add(try ctx.mul(acc, alpha), try ctx.constant(QM31.fromBase(M31.fromCanonical(rel))));
    return ctx.sub(acc, z);
}

/// A secure column from its 4 limb samples (`QM31.fromPartialEvals`).
fn secure(comptime V: type, ctx: *Context(V), limbs: [4]Var) !Var {
    var out = limbs[0];
    const basis = [3]QM31{ QM31.fromU32Unchecked(0, 1, 0, 0), QM31.fromU32Unchecked(0, 0, 1, 0), QM31.fromU32Unchecked(0, 0, 0, 1) };
    for (basis, limbs[1..]) |e, l| out = try ctx.add(out, try ctx.mul(l, try ctx.constant(e)));
    return out;
}

/// Every component's constraints (AIR DAG, then LogUp) at the OODS point, Horner-combined with
/// `coeff` across components in order, divided by the trace domain's vanishing polynomial (all
/// components share the trace size).
fn compositionAtOods(
    comptime V: type,
    ctx: *Context(V),
    st: *const PlainStatement,
    config: PlainConfig,
    p: *const PlainProof(Var),
    oods_x: Var,
    coeff: Var,
    elements: ?[2]Var,
) !Var {
    var acc = ctx.zero();
    var pre_at: usize = 0;
    var main_at: usize = 0;
    var inter_at: usize = 0;
    var sum_at: usize = 0;
    for (st.parts, config.parts) |part, pc| {
        const air = part.air;
        const vals = try ctx.scratch().alloc(Var, air.exprs.len);
        for (air.exprs, 0..) |node, k| vals[k] = switch (node) {
            .col => |c| switch (c.tree) {
                .preprocessed => blk: {
                    if (c.offset != 0) return error.PreprocessedOffset;
                    break :blk p.preprocessed_at_oods[pre_at + c.index];
                },
                .main => blk: {
                    const offs = pc.main_offsets[c.index];
                    const at = std.mem.indexOfScalar(i32, offs, c.offset) orelse return error.UnknownMaskOffset;
                    break :blk p.trace_at_oods[main_at + c.index][at];
                },
            },
            .constant => |v| try ctx.constant(QM31.fromBase(M31.fromCanonical(v))),
            .add => |ab| try ctx.add(vals[ab[0]], vals[ab[1]]),
            .sub => |ab| try ctx.sub(vals[ab[0]], vals[ab[1]]),
            .mul => |ab| try ctx.mul(vals[ab[0]], vals[ab[1]]),
            .neg => |x| try ctx.sub(ctx.zero(), vals[x]),
            .@"pub" => |i| part.pubs[i],
        };
        for (air.constraints) |root| acc = try ctx.add(try ctx.mul(acc, coeff), vals[root]);

        if (air.lookups.len != 0) {
            const el = elements orelse return error.MissingLookupElements;
            const B = (air.lookups.len + 1) / 2;
            if (pc.n_inter != 4 * B) return error.InvalidPlainProof;
            const inter = p.interaction_at_oods[inter_at..][0 .. 4 * B];
            const mults = try ctx.scratch().alloc(Var, air.lookups.len);
            const dens = try ctx.scratch().alloc(Var, air.lookups.len);
            for (air.lookups, mults, dens) |l, *m, *d| {
                m.* = vals[l.mult];
                const e = try ctx.scratch().alloc(Var, l.vals.len);
                for (l.vals, e) |v, *x| x.* = vals[v];
                d.* = try denominatorVar(V, ctx, l.rel, e, el[0], el[1]);
            }
            const S = try ctx.scratch().alloc(Var, B);
            for (S, 0..) |*sv_, b| {
                const at: usize = if (b + 1 == B) 1 else 0;
                sv_.* = try secure(V, ctx, .{ inter[4 * b][at], inter[4 * b + 1][at], inter[4 * b + 2][at], inter[4 * b + 3][at] });
            }
            const last = 4 * (B - 1);
            const s_prev = try secure(V, ctx, .{ inter[last][0], inter[last + 1][0], inter[last + 2][0], inter[last + 3][0] });
            // shift = claimed_sum / 2^log_size
            const n_inv = try ctx.constant(QM31.fromBase(try M31.fromU64(@as(u64, 1) << @intCast(config.log_trace_size)).inv()));
            const shift = try ctx.mul(p.claimed_sums[sum_at], n_inv);
            for (0..B) |b| {
                const j = 2 * b;
                const pair = j + 1 < mults.len;
                const N = if (pair) try ctx.add(try ctx.mul(mults[j], dens[j + 1]), try ctx.mul(mults[j + 1], dens[j])) else mults[j];
                const D = if (pair) try ctx.mul(dens[j], dens[j + 1]) else dens[j];
                const diff = if (b + 1 < B)
                    try ctx.sub(S[b], if (b == 0) ctx.zero() else S[b - 1])
                else
                    try ctx.add(try ctx.sub(try ctx.sub(S[b], s_prev), if (B == 1) ctx.zero() else S[B - 2]), shift);
                acc = try ctx.add(try ctx.mul(acc, coeff), try ctx.sub(try ctx.mul(diff, D), N));
            }
            sum_at += 1;
        }
        pre_at += pc.n_preprocessed;
        main_at += pc.main_offsets.len;
        inter_at += pc.n_inter;
    }
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
    const lc = LeanChannel{ .ch = &channel, .progs = &st.channel };
    var tr = TranscriptCheck{ .events = st.transcript };
    try tr.step("fri_config");
    try sv.fri.mixFriConfig(V, ctx, &channel, config.fri);

    const pre_root = try builder.blake.constantHash(V, ctx, builder.blake.hashValueFromDigest(QM31, st.preprocessed_root));
    try tr.step("pre");
    try lc.mixCommitment(V, ctx, pre_root);

    if (st.parts.len != config.parts.len) return error.InvalidPlainProof;
    try tr.step("stmt");
    // Statement (system proofs start with the component count); per component:
    // [log_size, digest (8 words), n_pubs], then one call per public input.
    if (st.statement) |prog| {
        var ins: std.ArrayListUnmanaged(Var) = .empty;
        for (st.parts) |part| try ins.appendSlice(ctx.scratch(), part.pubs);
        const Hooks = struct {
            ctx: *Context(V),
            channel: LeanChannel,
            st: *const PlainStatement,
            log: u32,
            inputs: []const Var,
            next_part: *usize,
            pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
                switch (id) {
                    0 => return self.inputs,
                    3 => {
                        const words = try self.ctx.scratch().alloc(U32Wrapper(Var), args.len);
                        for (words, args) |*w, v| w.* = .newUnsafe(v);
                        try self.channel.mixU32s(V, self.ctx, words);
                        return &.{};
                    },
                    4 => {
                        const part = self.st.parts[self.next_part.*];
                        self.next_part.* += 1;
                        const out = try self.ctx.scratch().alloc(Var, 10);
                        out[0] = (try builder.wrappers.constU32(V, self.ctx, self.log)).get();
                        for (0..8) |i| out[1 + i] = (try builder.wrappers.constU32(V, self.ctx, std.mem.readInt(u32, part.digest[4 * i ..][0..4], .little))).get();
                        out[9] = (try builder.wrappers.constU32(V, self.ctx, @intCast(part.pubs.len))).get();
                        return out;
                    },
                    else => return error.UnknownHook,
                }
            }
        };
        var next_part: usize = 0;
        _ = try glue.run(V, ctx, prog, &.{}, Hooks{ .ctx = ctx, .channel = lc, .st = st, .log = log_trace, .inputs = ins.items, .next_part = &next_part });
    } else {
        if (config.system) try lc.mixU32s(V, ctx, &.{try builder.wrappers.constU32(V, ctx, @intCast(st.parts.len))});
        for (st.parts) |part| {
            var words: [10]U32Wrapper(Var) = undefined;
            words[0] = try builder.wrappers.constU32(V, ctx, log_trace);
            for (0..8) |i| words[1 + i] = try builder.wrappers.constU32(V, ctx, std.mem.readInt(u32, part.digest[4 * i ..][0..4], .little));
            words[9] = try builder.wrappers.constU32(V, ctx, @intCast(part.pubs.len));
            try lc.mixU32s(V, ctx, &words);
            for (part.pubs) |pv| try lc.mixU32s(V, ctx, &.{try builder.blake.m31ToU32(V, ctx, pv)});
        }
    }

    try tr.step("trace");
    try lc.mixCommitment(V, ctx, p.trace_root);
    var elements: ?[2]Var = null;
    if (config.hasLookups()) {
        try tr.step("elements");
        elements = try lc.drawTwoQm31s(V, ctx);
        var n_with: usize = 0;
        for (st.parts) |part| {
            if (part.air.lookups.len != 0) n_with += 1;
        }
        if (p.claimed_sums.len != n_with) return error.InvalidPlainProof;
        // The relations balance: the claimed sums and the public entries add to zero.
        if (st.balance) |prog| {
            var ins: std.ArrayListUnmanaged(Var) = .empty;
            try ins.appendSlice(ctx.scratch(), p.claimed_sums);
            for (st.ext) |e| try ins.appendSlice(ctx.scratch(), e.vals);
            try ins.appendSlice(ctx.scratch(), &elements.?);
            const Hooks = struct {
                inputs: []const Var,
                pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
                    return if (id == 0) self.inputs else error.UnknownHook;
                }
            };
            _ = try glue.run(V, ctx, prog, &.{}, Hooks{ .inputs = ins.items });
        } else {
            var total = ctx.zero();
            for (p.claimed_sums) |c| total = try ctx.add(total, c);
            for (st.ext) |e| {
                const d = try denominatorVar(V, ctx, e.rel, e.vals, elements.?[0], elements.?[1]);
                total = try ctx.add(total, try ctx.mul(try ctx.constant(QM31.fromBase(e.mult)), try ctx.inv(d)));
            }
            try ctx.eq(total, ctx.zero());
        }
        try tr.step("claimed");
        try lc.mixQm31s(V, ctx, p.claimed_sums);
        try tr.step("inter");
        try lc.mixCommitment(V, ctx, p.interaction_root orelse return error.InvalidPlainProof);
    }
    try tr.step("coeff");
    const coeff = try lc.drawQm31(V, ctx);
    try tr.step("comp");
    try lc.mixCommitment(V, ctx, p.composition_root);
    try tr.step("oods");
    const oods = try lc.drawPoint(V, ctx);

    // All OODS samples: preprocessed, main (mask order), composition.
    var values: std.ArrayListUnmanaged(Var) = .empty;
    try values.appendSlice(ctx.scratch(), p.preprocessed_at_oods);
    for (p.trace_at_oods) |col| try values.appendSlice(ctx.scratch(), col);
    for (p.interaction_at_oods) |col| try values.appendSlice(ctx.scratch(), col);
    try values.appendSlice(ctx.scratch(), &p.composition_eval_at_oods);
    try tr.step("samples");
    try lc.mixQm31s(V, ctx, values.items);

    const computed = if (st.composition) |prog|
        try compositionViaProgram(V, ctx, prog, st, config, p, oods.x, coeff, elements)
    else
        try compositionAtOods(V, ctx, st, config, p, oods.x, coeff, elements);
    const expected = try sv.oods.extractExpectedCompositionEval(V, ctx, &p.composition_eval_at_oods, oods, log_trace + 1);
    try ctx.eq(computed, expected);

    try tr.step("quotient");
    const quotient_coef = try lc.drawQm31(V, ctx);
    try tr.step("fri");
    const fri_alphas = try sv.fri.friCommit(V, ctx, &channel, &p.fri);
    try tr.step("pow");
    try lc.pow(V, ctx, config.fri.pow_bits, p.pow_nonce);
    try tr.step("queries");
    const sel = try sv.select_queries.getQuerySelectionInputFromChannel(V, ctx, &channel, config.nQueries());
    try tr.done();
    const queries = try sv.select_queries.selectQueries(V, ctx, sel, config.logEvaluationDomainSize());
    const bits = try ctx.scratch().alloc([]const Var, queries.bits.len);
    for (bits, queries.bits) |*u, b| u.* = try builder.simd.unpack(V, ctx, b);

    // Merkle decommitment (all trees at the evaluation-domain height; no sorting).
    const roots = [4]?HashValue(Var){ pre_root, p.trace_root, p.interaction_root, p.composition_root };
    const bits_for_query = try ctx.scratch().alloc(Var, bits.len);
    for (roots, 0..) |maybe_root, tree| {
        const root = maybe_root orelse continue;
        const n_columns = p.eval_domain_samples.nColumns(tree);
        const leaf_values = try ctx.scratch().alloc(M31Wrapper(Var), n_columns);
        for (0..config.nQueries()) |q| {
            for (leaf_values, 0..) |*v, c| v.* = p.eval_domain_samples.at(tree, c, q);
            const leaf = (try leafHashVia(V, ctx, st.leaf_hashes, leaf_values)) orelse try hashLeafM31s(V, ctx, leaf_values);
            for (bits_for_query, bits) |*b, qb| b.* = qb[q];
            if (st.merkle_node) |prog|
                try merklePathVia(V, ctx, prog, leaf, bits_for_query, root, p.eval_domain_auth_paths.at(tree, q))
            else
                try sv.merkle.verifyMerklePath(V, ctx, leaf, bits_for_query, root, p.eval_domain_auth_paths.at(tree, q));
        }
    }

    // The points: the OODS point shifted by each main offset (in first-use order), and by −1 for
    // the interaction tree.
    var shifted = std.AutoHashMapUnmanaged(i32, Point(Var)).empty;
    var all_offsets: std.ArrayListUnmanaged([]const i32) = .empty;
    for (config.parts) |pc| try all_offsets.appendSlice(ctx.scratch(), pc.main_offsets);
    for (all_offsets.items) |offs| for (offs) |off| {
        if (off == 0) continue;
        const got = try shifted.getOrPut(ctx.scratch(), off);
        if (!got.found_existing) got.value_ptr.* = try shiftPoint(V, ctx, st.shifts, log_trace, off, oods);
    };
    const prev: ?Point(Var) = if (p.interaction_at_oods.len != 0)
        try shiftPoint(V, ctx, st.shifts, log_trace, -1, oods)
    else
        null;

    var responses: std.ArrayListUnmanaged(sv.oods.OodsResponse) = .empty;
    if (st.deep) |table| {
        // The Lean table: each value is a mixed sample, at its label's point (`deep_sound`), and every
        // mixed sample is used (`deep_complete`).
        if (table.n_samples != values.items.len) return error.InvalidPlainProof;
        for (table.responses) |r| {
            const pt = if (r.off == 0) oods else switch (r.tree) {
                TREE_MAIN => shifted.get(r.off) orelse return error.InvalidPlainProof,
                TREE_INTER => if (r.off == -1) prev orelse return error.InvalidPlainProof else return error.InvalidPlainProof,
                else => return error.InvalidPlainProof,
            };
            if (r.idx >= values.items.len) return error.InvalidPlainProof;
            try responses.append(ctx.scratch(), .{ .trace_idx = r.tree, .column_idx = r.col, .pt = pt, .value = values.items[r.idx] });
        }
    } else {
        // DEEP quotient inputs, in the native sample order (tree, column, mask; a two-sample column
        // is preceded by its periodicity sample, which coincides with the first one here).
        for (p.preprocessed_at_oods, 0..) |v, c|
            try responses.append(ctx.scratch(), .{ .trace_idx = TREE_PRE, .column_idx = c, .pt = oods, .value = v });
        for (all_offsets.items, p.trace_at_oods, 0..) |offs, vals, c| {
            const pts = try ctx.scratch().alloc(Point(Var), offs.len);
            for (offs, pts) |off, *pt| pt.* = if (off == 0) oods else shifted.get(off).?;
            if (offs.len == 2) try responses.append(ctx.scratch(), .{ .trace_idx = TREE_MAIN, .column_idx = c, .pt = pts[1], .value = vals[1] });
            for (pts, vals) |pt, v| try responses.append(ctx.scratch(), .{ .trace_idx = TREE_MAIN, .column_idx = c, .pt = pt, .value = v });
        }
        for (p.interaction_at_oods, 0..) |vals, c| {
            if (vals.len == 2) {
                // [prev, cur], preceded by the periodicity sample (as for two-offset main columns).
                try responses.append(ctx.scratch(), .{ .trace_idx = TREE_INTER, .column_idx = c, .pt = oods, .value = vals[1] });
                try responses.append(ctx.scratch(), .{ .trace_idx = TREE_INTER, .column_idx = c, .pt = prev.?, .value = vals[0] });
                try responses.append(ctx.scratch(), .{ .trace_idx = TREE_INTER, .column_idx = c, .pt = oods, .value = vals[1] });
            } else try responses.append(ctx.scratch(), .{ .trace_idx = TREE_INTER, .column_idx = c, .pt = oods, .value = vals[0] });
        }
        for (p.composition_eval_at_oods, 0..) |v, c|
            try responses.append(ctx.scratch(), .{ .trace_idx = TREE_COMPOSITION, .column_idx = c, .pt = oods, .value = v });
    }

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
    const st = PlainStatement{ .parts = &.{.{ .air = air, .digest = digest, .pubs = pub_vars }}, .preprocessed_root = pre_root };
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

    const config = try PlainConfig.single(log_size, cfg.fri_config, air.n_preprocessed, try mainOffsets(a, air), a);
    const pre_root: [32]u8 = std.mem.toBytes(try prove_rec.preprocessedRoot(a, cfg, air, log_size));
    var values = try fromCapture(a, prove_rec.Hasher, &proof_b, &capture, config, &.{});
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

test "plain in-circuit verifier accepts a LogUp system proof, rejects unbalanced or tampered ones" {
    const system = @import("../air/system.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try system.byteSystem(a);
    const log_size: u32 = 8;
    const parts = [_]system.Part{ .{ .air = &airs[0], .log_size = log_size }, .{ .air = &airs[1], .log_size = log_size } };
    const cfg = prove_rec.Config.fromFriAndTraceSize(try FriConfig.init(10, 0, 1, 3, 1), log_size);
    var prng = std.Random.DefaultPrng.init(11);
    const x = try a.alloc(M31, 256);
    const mult = try a.alloc(M31, 256);
    @memset(mult, M31.zero());
    for (x) |*v| {
        const b = prng.random().int(u8);
        v.* = M31.fromCanonical(b);
        mult[b] = mult[b].add(M31.one());
    }

    const config = PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .system = true, .parts = &.{
        .{ .n_preprocessed = 1, .main_offsets = try mainOffsets(a, airs[0]), .n_inter = 4 },
        .{ .n_preprocessed = 0, .main_offsets = try mainOffsets(a, airs[1]), .n_inter = 4 },
    } };
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    const Run = struct {
        fn run(al: std.mem.Allocator, airs_: *const [2]ir.Air, values: *const PlainProof(QM31), cfg_: PlainConfig, root: [32]u8) !bool {
            var ctx = try Context(QM31).init(al, 0);
            defer ctx.deinit();
            const pv = try guess(QM31, &ctx, values);
            const st = PlainStatement{ .preprocessed_root = root, .parts = &.{
                .{ .air = &airs_[0], .digest = try airs_[0].digest(al), .pubs = &.{} },
                .{ .air = &airs_[1], .digest = try airs_[1].digest(al), .pubs = &.{} },
            } };
            verifyPlain(QM31, &ctx, &pv, cfg_, &st) catch |e| switch (e) {
                error.EqFailedOnEval => return false,
                else => return e,
            };
            try ctx.finalizeGuessedVars();
            return ctx.isCircuitValid();
        }
    };
    const valuesFor = struct {
        fn f(al: std.mem.Allocator, cfg_: prove_rec.Config, parts_: []const system.Part, mains: []const []const []const M31, config_: PlainConfig) !PlainProof(QM31) {
            const E_ = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
            const pa = try system.prove(E_, al, cfg_, parts_, mains);
            const pb = try system.prove(E_, al, cfg_, parts_, mains);
            // Proving is deterministic: one copy is consumed by the native verifier.
            var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
            try system.verifyCapture(al, cfg_, parts_, &.{}, pa, &capture);
            return fromCapture(al, prove_rec.Hasher, &pb.stark, &capture, config_, pb.claimed_sums);
        }
    }.f;

    const mains = [_][]const []const M31{ &.{mult}, &.{x} };
    var values = try valuesFor(a, cfg, &parts, &mains, config);
    try std.testing.expect(try Run.run(a, &airs, &values, config, pre_root));

    // Claimed sums that do not add to zero are rejected.
    {
        const saved = values.claimed_sums[0];
        values.claimed_sums[0] = saved.add(QM31.one());
        try std.testing.expect(!try Run.run(a, &airs, &values, config, pre_root));
        // Still adding to zero, but not the committed ones.
        values.claimed_sums[1] = values.claimed_sums[1].sub(QM31.one());
        try std.testing.expect(!try Run.run(a, &airs, &values, config, pre_root));
        values.claimed_sums[0] = saved;
        values.claimed_sums[1] = values.claimed_sums[1].add(QM31.one());
    }
    // A tampered cumulative-sum sample is rejected.
    {
        const saved = values.interaction_at_oods[3][1];
        values.interaction_at_oods[3][1] = saved.add(QM31.one());
        try std.testing.expect(!try Run.run(a, &airs, &values, config, pre_root));
        values.interaction_at_oods[3][1] = saved;
    }
    try std.testing.expect(try Run.run(a, &airs, &values, config, pre_root));
}

test "plain verifier circuit size for one header-chain segment (2^12 rows)" {
    // Informational: printed, not asserted.
}

test "composition check: the Lean program (Circuit/Composition.lean) replays gate for gate as compositionAtOods" {
    const H = @import("../btc/header_chain.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, H.lean_json)).value;
    const log_size: u32 = 12;
    const offs = try mainOffsets(a, air);
    const config = try PlainConfig.single(log_size, try FriConfig.init(10, 0, 1, 3, 1), air.n_preprocessed, offs, a);
    var n_main_samples: usize = 0;
    for (offs) |o| n_main_samples += o.len;
    const n_in = air.n_preprocessed + n_main_samples + H.N_PUB + 2;
    // The same pseudo-random input values in both circuits.
    const vals = try a.alloc(QM31, n_in);
    var prng = std.Random.DefaultPrng.init(5);
    for (vals) |*v| v.* = QM31.fromU32Unchecked(prng.random().int(u31), prng.random().int(u31), prng.random().int(u31), prng.random().int(u31));

    const Built = struct { ctx: Context(QM31), res: Var };
    const guessAll = struct {
        fn f(ctx: *Context(QM31), vs: []const QM31, al: std.mem.Allocator) ![]Var {
            const out = try al.alloc(Var, vs.len);
            for (out, vs) |*w, v| w.* = try ctx.guess(v);
            return out;
        }
    }.f;
    // 1. The hand-written function.
    var ctx_a = try Context(QM31).init(a, 0);
    defer ctx_a.deinit();
    const in_a = try guessAll(&ctx_a, vals, a);
    var p: PlainProof(Var) = undefined;
    p.preprocessed_at_oods = in_a[0..air.n_preprocessed];
    p.trace_at_oods = try a.alloc([]Var, offs.len);
    {
        var at: usize = air.n_preprocessed;
        for (offs, p.trace_at_oods) |o, *col| {
            col.* = in_a[at .. at + o.len];
            at += o.len;
        }
    }
    const pubs_at = air.n_preprocessed + n_main_samples;
    const st = PlainStatement{ .parts = &.{.{ .air = &air, .digest = [_]u8{0} ** 32, .pubs = in_a[pubs_at .. pubs_at + H.N_PUB] }}, .preprocessed_root = [_]u8{0} ** 32 };
    const res_a = try compositionAtOods(QM31, &ctx_a, &st, config, &p, in_a[pubs_at + H.N_PUB + 1], in_a[pubs_at + H.N_PUB], null);
    // 2. The replayed Lean program.
    var ctx_b = try Context(QM31).init(a, 0);
    defer ctx_b.deinit();
    const in_b = try guessAll(&ctx_b, vals, a);
    const prog = try glue.parse(a, @embedFile("air:composition_header_chain"));
    const Hooks = struct {
        ctx: *Context(QM31),
        inputs: []const Var,
        log: u32,
        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            return switch (id) {
                0 => self.inputs,
                1 => blk: {
                    const out = try self.ctx.scratch().alloc(Var, 1);
                    out[0] = try sv.circle.denomInverse(QM31, self.ctx, args[0], self.log);
                    break :blk out;
                },
                else => error.UnknownHook,
            };
        }
    };
    const res_b = try glue.run(QM31, &ctx_b, &prog, &.{}, Hooks{ .ctx = &ctx_b, .inputs = in_b, .log = log_size });
    _ = Built;
    try std.testing.expect(ctx_a.get(res_a).eql(ctx_b.get(res_b[0])));
    try glue.expectSameCircuit(&ctx_a.circuit, &ctx_b.circuit);
}

test "composition check with LogUp: the Lean program replays gate for gate (byte system, 2 components)" {
    const system = @import("../air/system.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try system.byteSystem(a);
    const log_size: u32 = 8;
    const offs0 = try mainOffsets(a, airs[0]);
    const offs1 = try mainOffsets(a, airs[1]);
    const config = PlainConfig{ .log_trace_size = log_size, .fri = try FriConfig.init(10, 0, 1, 3, 1), .system = true, .parts = &.{
        .{ .n_preprocessed = 1, .main_offsets = offs0, .n_inter = 4 },
        .{ .n_preprocessed = 0, .main_offsets = offs1, .n_inter = 4 },
    } };
    // Inputs, in the Lean layout's order: preprocessed, main, interaction (prev, cur for each of the
    // four columns), claimed sums, coefficient, z, α, OODS x.
    var n_main: usize = 0;
    for (offs0) |o| n_main += o.len;
    for (offs1) |o| n_main += o.len;
    const n_in = 1 + n_main + 2 * 8 + 2 + 4;
    const vals = try a.alloc(QM31, n_in);
    var prng = std.Random.DefaultPrng.init(9);
    for (vals) |*v| v.* = QM31.fromU32Unchecked(prng.random().int(u31), prng.random().int(u31), prng.random().int(u31), prng.random().int(u31));
    const guessAll = struct {
        fn f(ctx: *Context(QM31), vs: []const QM31, al: std.mem.Allocator) ![]Var {
            const out = try al.alloc(Var, vs.len);
            for (out, vs) |*w, v| w.* = try ctx.guess(v);
            return out;
        }
    }.f;
    var ctx_a = try Context(QM31).init(a, 0);
    defer ctx_a.deinit();
    const in_a = try guessAll(&ctx_a, vals, a);
    var p: PlainProof(Var) = undefined;
    p.preprocessed_at_oods = in_a[0..1];
    p.trace_at_oods = try a.alloc([]Var, offs0.len + offs1.len);
    var at: usize = 1;
    for (try std.mem.concat(a, []const i32, &.{ offs0, offs1 }), p.trace_at_oods) |o, *col| {
        col.* = in_a[at .. at + o.len];
        at += o.len;
    }
    p.interaction_at_oods = try a.alloc([]Var, 8);
    for (p.interaction_at_oods) |*col| {
        col.* = in_a[at .. at + 2];
        at += 2;
    }
    p.claimed_sums = in_a[at .. at + 2];
    at += 2;
    const coeff = in_a[at];
    const z = in_a[at + 1];
    const alpha = in_a[at + 2];
    const oods_x = in_a[at + 3];
    const st = PlainStatement{ .preprocessed_root = [_]u8{0} ** 32, .parts = &.{
        .{ .air = &airs[0], .digest = [_]u8{0} ** 32, .pubs = &.{} },
        .{ .air = &airs[1], .digest = [_]u8{0} ** 32, .pubs = &.{} },
    } };
    const res_a = try compositionAtOods(QM31, &ctx_a, &st, config, &p, oods_x, coeff, .{ z, alpha });

    var ctx_b = try Context(QM31).init(a, 0);
    defer ctx_b.deinit();
    const in_b = try guessAll(&ctx_b, vals, a);
    const prog = try glue.parse(a, @embedFile("air:composition_bytesys"));
    const Hooks = struct {
        ctx: *Context(QM31),
        inputs: []const Var,
        log: u32,
        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            return switch (id) {
                0 => self.inputs,
                1 => blk: {
                    const out = try self.ctx.scratch().alloc(Var, 1);
                    out[0] = try sv.circle.denomInverse(QM31, self.ctx, args[0], self.log);
                    break :blk out;
                },
                2 => blk: {
                    const out = try self.ctx.scratch().alloc(Var, 1);
                    out[0] = try self.ctx.constant(QM31.fromBase(try M31.fromU64(@as(u64, 1) << @intCast(self.log)).inv()));
                    break :blk out;
                },
                else => error.UnknownHook,
            };
        }
    };
    const res_b = try glue.run(QM31, &ctx_b, &prog, &.{}, Hooks{ .ctx = &ctx_b, .inputs = in_b, .log = log_size });
    try std.testing.expect(ctx_a.get(res_a).eql(ctx_b.get(res_b[0])));
    try glue.expectSameCircuit(&ctx_a.circuit, &ctx_b.circuit);
}

test "Merkle leaf hashing: the Lean program (Circuit/LeafHash.lean) replays gate for gate as hashLeafM31s" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const progs = [_]glue.Program{ try glue.parse(a, @embedFile("air:leafhash_8")), try glue.parse(a, @embedFile("air:leafhash_434")) };
    for (progs, [_]usize{ 8, 434 }) |prog, k| {
        var prng = std.Random.DefaultPrng.init(k);
        const vals = try a.alloc(M31, k);
        for (vals) |*v| v.* = M31.fromCanonical(prng.random().int(u31) % 0x7fffffff);
        var ctx_a = try Context(QM31).init(a, 0);
        defer ctx_a.deinit();
        var ctx_b = try Context(QM31).init(a, 0);
        defer ctx_b.deinit();
        const wa = try a.alloc(M31Wrapper(Var), k);
        const wb = try a.alloc(M31Wrapper(Var), k);
        for (wa, wb, vals) |*x, *y, v| {
            x.* = try builder.wrappers.guessM31(QM31, &ctx_a, builder.wrappers.m31Value(QM31, v));
            y.* = try builder.wrappers.guessM31(QM31, &ctx_b, builder.wrappers.m31Value(QM31, v));
        }
        const ha = try hashLeafM31s(QM31, &ctx_a, wa);
        const hb = (try leafHashVia(QM31, &ctx_b, &.{&prog}, wb)) orelse return error.TestUnexpectedResult;
        for (ha.words, hb.words) |x, y| try std.testing.expect(ctx_a.get(x.get()).eql(ctx_b.get(y.get())));
        try glue.expectSameCircuit(&ctx_a.circuit, &ctx_b.circuit);
    }
}

test "Merkle path: the Lean level program (Circuit/Merkle.lean) replays gate for gate as verifyMerklePath" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const prog = try glue.parse(a, @embedFile("air:merkle_node"));
    const W = builder.wrappers;
    const depth = 6;
    var prng = std.Random.DefaultPrng.init(7);
    var leaf_w: [8]u32 = undefined;
    for (&leaf_w) |*w| w.* = prng.random().int(u32);
    var sib_w: [depth][8]u32 = undefined;
    for (&sib_w) |*s| for (s) |*w| {
        w.* = prng.random().int(u32);
    };
    var bit_v: [depth]u32 = undefined;
    for (&bit_v) |*b| b.* = prng.random().int(u1);
    // The root, computed by stwo-zig's level function in a scratch context.
    var root_w: [8]u32 = undefined;
    {
        var ctx = try Context(QM31).init(a, 0);
        defer ctx.deinit();
        var node: HashValue(Var) = undefined;
        for (&node.words, leaf_w) |*x, w| x.* = try W.guessU32(QM31, &ctx, W.u32Value(QM31, w));
        for (sib_w, bit_v) |s, b| {
            var sib: HashValue(Var) = undefined;
            for (&sib.words, s) |*x, w| x.* = try W.guessU32(QM31, &ctx, W.u32Value(QM31, w));
            node = try sv.merkle.merkleNode(QM31, &ctx, node, sib, try ctx.guess(QM31.fromBase(M31.fromCanonical(b))));
        }
        for (&root_w, node.words) |*w, x| w.* = builder.ivalue.unpackU32(QM31, ctx.get(x.get()));
    }
    for ([_]bool{ true, false }) |honest| {
        var ctxs: [2]Context(QM31) = .{ try Context(QM31).init(a, 0), try Context(QM31).init(a, 0) };
        defer for (&ctxs) |*c| c.deinit();
        for (&ctxs, 0..) |*ctx, which| {
            var leaf: HashValue(Var) = undefined;
            for (&leaf.words, leaf_w) |*x, w| x.* = try W.guessU32(QM31, ctx, W.u32Value(QM31, w));
            var root: HashValue(Var) = undefined;
            for (&root.words, root_w, 0..) |*x, w, k| x.* = try W.guessU32(QM31, ctx, W.u32Value(QM31, if (!honest and k == 3) w ^ 1 else w));
            var path: [depth]HashValue(Var) = undefined;
            var bits: [depth]Var = undefined;
            for (&path, &bits, sib_w, bit_v) |*p, *b, s, bv| {
                for (&p.words, s) |*x, w| x.* = try W.guessU32(QM31, ctx, W.u32Value(QM31, w));
                b.* = try ctx.guess(QM31.fromBase(M31.fromCanonical(bv)));
            }
            if (which == 0)
                try sv.merkle.verifyMerklePath(QM31, ctx, leaf, &bits, root, &path)
            else
                try merklePathVia(QM31, ctx, &prog, leaf, &bits, root, &path);
            try std.testing.expectEqual(honest, try ctx.isCircuitValid());
        }
        try glue.expectSameCircuit(&ctxs[0].circuit, &ctxs[1].circuit);
    }
}

test "channel: the Lean programs (Circuit/Channel.lean) replay gate for gate as stwo-zig's channel" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const P = struct {
        fn parse(al: std.mem.Allocator, comptime name: []const u8) !*const glue.Program {
            const p = try al.create(glue.Program);
            p.* = try glue.parse(al, @embedFile("air:channel_" ++ name));
            return p;
        }
    };
    const progs = ChannelProgs{
        .mix_u32s = &.{ try P.parse(a, "mix_u32s_1"), try P.parse(a, "mix_u32s_8"), try P.parse(a, "mix_u32s_10") },
        .mix_qm31s = &.{try P.parse(a, "mix_qm31s_2")},
        .draw = try P.parse(a, "draw"),
        .draw_qm31 = try P.parse(a, "draw_qm31"),
        .draw_point = try P.parse(a, "draw_point"),
        .pow_mix = try P.parse(a, "pow_mix"),
    };
    var prng = std.Random.DefaultPrng.init(11);
    const r = prng.random();
    const rq = struct {
        fn f(rr: std.Random) QM31 {
            return QM31.fromU32Unchecked(rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff);
        }
    }.f;
    const d_lo = rq(r);
    const d_hi = rq(r);
    var words: [10]u32 = undefined;
    for (&words) |*w| w.* = r.int(u32);
    const qs = [2]QM31{ rq(r), rq(r) };
    const nonce = QM31.fromU32Unchecked(r.int(u31) % 0x7fffffff, r.int(u31) % 0x7fffffff, 0, 0);

    var ctxs: [2]Context(QM31) = .{ try Context(QM31).init(a, 0), try Context(QM31).init(a, 0) };
    defer for (&ctxs) |*c| c.deinit();
    var outs: [2]std.ArrayListUnmanaged(QM31) = .{ .empty, .empty };
    for (&ctxs, &outs, 0..) |*ctx, *out, which| {
        var ch = sv.channel.Channel{ .digest = .{ .low = try ctx.guess(d_lo), .high = try ctx.guess(d_hi) }, .n_draws = 0 };
        const lc = LeanChannel{ .ch = &ch, .progs = &progs };
        const ws = try a.alloc(U32Wrapper(Var), words.len);
        for (ws, words) |*w, v| w.* = try builder.wrappers.guessU32(QM31, ctx, builder.wrappers.u32Value(QM31, v));
        const qv = [2]Var{ try ctx.guess(qs[0]), try ctx.guess(qs[1]) };
        const nv = try ctx.guess(nonce);
        var root: HashValue(Var) = undefined;
        @memcpy(&root.words, ws[0..8]);
        if (which == 0) {
            try ch.mixU32s(QM31, ctx, ws[0..1]);
            const d2 = try ch.drawTwoQm31s(QM31, ctx);
            try ch.mixU32s(QM31, ctx, ws[0..10]);
            const d1 = try ch.drawQm31(QM31, ctx);
            try ch.mixCommitment(QM31, ctx, root);
            const pt = try ch.drawPoint(QM31, ctx);
            try ch.mixQm31s(QM31, ctx, &qv);
            try ch.pow(QM31, ctx, 0, nv);
            for ([_]Var{ d2[0], d2[1], d1, pt.x, pt.y, ch.digest.low, ch.digest.high }) |v| try out.append(a, ctx.get(v));
        } else {
            try lc.mixU32s(QM31, ctx, ws[0..1]);
            const d2 = try lc.drawTwoQm31s(QM31, ctx);
            try lc.mixU32s(QM31, ctx, ws[0..10]);
            const d1 = try lc.drawQm31(QM31, ctx);
            try lc.mixCommitment(QM31, ctx, root);
            const pt = try lc.drawPoint(QM31, ctx);
            try lc.mixQm31s(QM31, ctx, &qv);
            try lc.pow(QM31, ctx, 0, nv);
            for ([_]Var{ d2[0], d2[1], d1, pt.x, pt.y, ch.digest.low, ch.digest.high }) |v| try out.append(a, ctx.get(v));
        }
    }
    for (outs[0].items, outs[1].items) |x, y| try std.testing.expect(x.eql(y));
    try glue.expectSameCircuit(&ctxs[0].circuit, &ctxs[1].circuit);
}

test "proof-of-work check: the Lean program (Circuit/Pow.lean) replays gate for gate as stwo-zig's, same verdicts" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const mix = try a.create(glue.Program);
    mix.* = try glue.parse(a, @embedFile("air:channel_pow_mix"));
    var checks: [3]glue.Program = undefined;
    inline for (.{ "0", "4", "26" }, 0..) |name, i| checks[i] = try glue.parse(a, @embedFile("air:channel_pow_check_" ++ name));
    const pcs = [3]PowCheck{ .{ .n_bits = 0, .prog = &checks[0] }, .{ .n_bits = 4, .prog = &checks[1] }, .{ .n_bits = 26, .prog = &checks[2] } };
    const progs = ChannelProgs{ .pow_mix = mix, .pow_check = &pcs };
    var prng = std.Random.DefaultPrng.init(17);
    const r = prng.random();
    const rq = struct {
        fn f(rr: std.Random) QM31 {
            return QM31.fromU32Unchecked(rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff, rr.int(u31) % 0x7fffffff);
        }
    }.f;
    const d_lo = rq(r);
    const d_hi = rq(r);
    const Run = struct {
        /// Builds the check with stwo-zig's channel (`which == 0`) or the Lean programs; returns validity.
        fn build(al: std.mem.Allocator, ctx: *Context(QM31), lo: QM31, hi: QM31, n_bits: u32, nonce: QM31, which: usize, pr: *const ChannelProgs) !bool {
            _ = al;
            var ch = sv.channel.Channel{ .digest = .{ .low = try ctx.guess(lo), .high = try ctx.guess(hi) }, .n_draws = 0 };
            const nv = try ctx.guess(nonce);
            if (which == 0) try ch.pow(QM31, ctx, n_bits, nv) else try (LeanChannel{ .ch = &ch, .progs = pr }).pow(QM31, ctx, n_bits, nv);
            return ctx.isCircuitValid();
        }
    };
    // A nonce that passes 4 bits, found with stwo-zig's own check.
    var good4: QM31 = undefined;
    var k: u32 = 0;
    while (true) : (k += 1) {
        var ctx = try Context(QM31).init(a, 0);
        defer ctx.deinit();
        const cand = QM31.fromU32Unchecked(k, 0, 0, 0);
        if (try Run.build(a, &ctx, d_lo, d_hi, 4, cand, 0, &progs)) {
            good4 = cand;
            break;
        }
        try std.testing.expect(k < 10_000);
    }
    const cases = [_]struct { n_bits: u32, nonce: QM31, valid: bool }{
        .{ .n_bits = 0, .nonce = QM31.fromU32Unchecked(12345, 678, 0, 0), .valid = true },
        .{ .n_bits = 0, .nonce = QM31.fromU32Unchecked(12345, 678, 1, 0), .valid = false },
        .{ .n_bits = 4, .nonce = good4, .valid = true },
        .{ .n_bits = 4, .nonce = good4.add(QM31.one()), .valid = false },
        .{ .n_bits = 26, .nonce = QM31.fromU32Unchecked(99, 0, 0, 0), .valid = false },
    };
    for (cases) |c| {
        var ctxs: [2]Context(QM31) = .{ try Context(QM31).init(a, 0), try Context(QM31).init(a, 0) };
        defer for (&ctxs) |*cx| cx.deinit();
        var verdicts: [2]bool = undefined;
        for (&ctxs, &verdicts, 0..) |*ctx, *v, which| v.* = try Run.build(a, ctx, d_lo, d_hi, c.n_bits, c.nonce, which, &progs);
        try glue.expectSameCircuit(&ctxs[0].circuit, &ctxs[1].circuit);
        try std.testing.expectEqual(verdicts[0], verdicts[1]);
        // `good4 + 1` may pass 4 bits by chance; skip that verdict check if stwo-zig accepts it.
        if (!(c.n_bits == 4 and !c.valid and verdicts[0])) try std.testing.expectEqual(c.valid, verdicts[1]);
    }
}

test "shifted OODS points: the Lean table (Circuit/Oods.lean) matches stwo-zig's mulSigned and addPoints gate for gate" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const table = try ShiftTable.parse(a, @embedFile("air:oods_shift_leaf"));
    try std.testing.expect(table.entries.len > 0);
    const oods_v = [2]QM31{ QM31.fromU32Unchecked(11, 22, 33, 44), QM31.fromU32Unchecked(55, 66, 77, 88) };
    for (table.entries) |*e| {
        // The Lean constant is stwo-zig's `off·g_log`.
        const g = core.poly.circle.canonic.CanonicCoset.new(e.log).coset_value.step.mulSigned(e.off);
        try std.testing.expectEqual(g.x.toU32(), e.x);
        try std.testing.expectEqual(g.y.toU32(), e.y);
        // The program's gates and values are `addPoints`'.
        var ctxs: [2]Context(QM31) = .{ try Context(QM31).init(a, 0), try Context(QM31).init(a, 0) };
        defer for (&ctxs) |*c| c.deinit();
        var pts: [2][2]QM31 = undefined;
        for (&ctxs, &pts, 0..) |*ctx, *pt, which| {
            const oods = Point(Var){ .x = try ctx.guess(oods_v[0]), .y = try ctx.guess(oods_v[1]) };
            const r = try shiftPoint(QM31, ctx, if (which == 0) null else &table, e.log, e.off, oods);
            pt.* = .{ ctx.get(r.x), ctx.get(r.y) };
        }
        try std.testing.expect(pts[0][0].eql(pts[1][0]) and pts[0][1].eql(pts[1][1]));
        try glue.expectSameCircuit(&ctxs[0].circuit, &ctxs[1].circuit);
    }
}

test "transcript: the Lean order is accepted step by step, a swapped one is refused" {
    const a = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(a);
    defer arena.deinit();
    const evs = try parseTranscript(arena.allocator(), @embedFile("air:transcript_lookups"));
    var ok = TranscriptCheck{ .events = evs };
    for (evs) |e| try ok.step(e);
    try ok.done();
    var bad = TranscriptCheck{ .events = evs };
    try bad.step("fri_config");
    try bad.step("pre");
    try bad.step("stmt");
    try std.testing.expectError(error.TranscriptOrder, bad.step("elements"));
}

test "channel: mix_qm31s at the leaf's sample count (3757) replays gate for gate" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const prog = try a.create(glue.Program);
    prog.* = try glue.parse(a, @embedFile("air:channel_mix_qm31s_3757"));
    const progs = ChannelProgs{ .mix_qm31s = &.{prog} };
    var prng = std.Random.DefaultPrng.init(5);
    const r = prng.random();
    const vals = try a.alloc(QM31, 3757);
    for (vals) |*v| v.* = QM31.fromU32Unchecked(r.int(u31) % 0x7fffffff, r.int(u31) % 0x7fffffff, r.int(u31) % 0x7fffffff, r.int(u31) % 0x7fffffff);
    var ctxs: [2]Context(QM31) = .{ try Context(QM31).init(a, 0), try Context(QM31).init(a, 0) };
    defer for (&ctxs) |*c| c.deinit();
    var digests: [2][2]QM31 = undefined;
    for (&ctxs, &digests, 0..) |*ctx, *dg, which| {
        var ch = sv.channel.Channel{ .digest = .{ .low = try ctx.guess(QM31.one()), .high = try ctx.guess(QM31.one()) }, .n_draws = 0 };
        const vs = try a.alloc(Var, vals.len);
        for (vs, vals) |*w, v| w.* = try ctx.guess(v);
        if (which == 0) try ch.mixQm31s(QM31, ctx, vs) else try (LeanChannel{ .ch = &ch, .progs = &progs }).mixQm31s(QM31, ctx, vs);
        dg.* = .{ ctx.get(ch.digest.low), ctx.get(ch.digest.high) };
    }
    try std.testing.expect(digests[0][0].eql(digests[1][0]) and digests[0][1].eql(digests[1][1]));
    try glue.expectSameCircuit(&ctxs[0].circuit, &ctxs[1].circuit);
}
