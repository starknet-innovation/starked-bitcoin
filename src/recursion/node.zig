//! A recursion node (roadmap REC-FOLD / AGG): verifies two child circuit proofs (leaves or
//! nodes) in-circuit, checks that the right child's segment continues the left one, and outputs
//! the digest of the combined segment.
//!
//! Children and nodes are padded to one shared target (`Shape`), so one node circuit verifies
//! both kinds. A child's output is `pubsDigest(key, pubs)`; the node guesses each child's key
//! and public inputs, recomputes that digest and binds it to the verified proof. It outputs
//! `pubsDigest(K, combine(pL, pR))` with `K = Blake2s(hL ‖ kL ‖ hR ‖ kR)` (`h` the children's
//! circuit hashes), so the root's key commits to the circuit identity of every proof in the
//! tree; the outer verifier recomputes it from the tree shape (`expectedKey`).
//!
//! The link checks are exactly `PubLink` in lean/StarkedAir/Gadgets/Aggregate.lean, and
//! `combine` is its `combine`; `pub_compose` proves that they preserve validity.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const leaf = @import("leaf.zig");

const builder = circuit.builder;
const finalize = circuit.common.finalize;
const component_list = circuit.common.component_list;
const multiverifier = circuit.statements.multiverifier;
const circuit_statement = circuit.statements.circuit_statement;
const stark_proof = circuit.stark_verifier.proof;
const verify_mod = circuit.stark_verifier.verify;
const Var = builder.Var;
const Context = builder.Context;
const NoValue = builder.NoValue;
const U32Wrapper = builder.wrappers.U32Wrapper;
const HashValue = builder.blake.HashValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const ComponentSizes = leaf.ComponentSizes;
const N_PUB = leaf.N_PUB;
const Key = leaf.Key;

/// The input-state indices (`isIn` in Aggregate.lean).
pub fn isIn(k: usize) bool {
    return k < 16 or (32 <= k and k < 38) or k == 44 or k == 45 or (48 <= k and k < 68) or (88 <= k and k < 98);
}

/// The left child's input state and the right child's output state.
pub fn combine(pl: [N_PUB]M31, pr: [N_PUB]M31) [N_PUB]M31 {
    var out: [N_PUB]M31 = undefined;
    for (&out, 0..) |*o, k| o.* = if (isIn(k)) pl[k] else pr[k];
    return out;
}

/// A node's key: Blake2s(hL ‖ kL ‖ hR ‖ kR).
pub fn nodeKey(hl: [8]u32, kl: Key, hr: [8]u32, kr: Key) Key {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    for ([_][8]u32{ hl, kl, hr, kr }) |ws| for (ws) |w| {
        std.mem.writeInt(u32, &b, w, .little);
        h.update(&b);
    };
    var d: [32]u8 = undefined;
    h.final(&d);
    var out: Key = undefined;
    for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return out;
}

/// The node's view of a child: its proof values, preprocessed root, key and public inputs.
pub fn ChildInput(comptime V: type) type {
    return struct {
        proof: *const stark_proof.Proof(V),
        preprocessed_root: HashValue(V),
        key: HashValue(V),
        pubs: [N_PUB]V,
    };
}

/// `x < 2^16`: its u32 form `(x mod 2^16, x >> 16, 0, 0)` equals `(x, 0, 0, 0)`.
fn rangeCheck16(comptime V: type, ctx: *Context(V), x: Var) !void {
    const u = try builder.blake.m31ToU32(V, ctx, x);
    try ctx.eq(u.get(), x);
}

/// `PubLink pL pR` (Aggregate.lean), constraint by constraint.
fn linkChecks(comptime V: type, ctx: *Context(V), pl: []const Var, pr: []const Var, carry: V) !void {
    for (0..16) |k| try ctx.eq(pr[k], pl[16 + k]);
    for ([_][2]usize{ .{ 34, 40 }, .{ 35, 41 }, .{ 36, 42 }, .{ 37, 43 }, .{ 44, 46 }, .{ 45, 47 } }) |p| try ctx.eq(pr[p[0]], pl[p[1]]);
    for (0..20) |k| try ctx.eq(pr[48 + k], pl[68 + k]);
    for (0..10) |l| try ctx.eq(pr[88 + l], pl[98 + l]);
    try rangeCheck16(V, ctx, pr[32]);
    try rangeCheck16(V, ctx, pr[33]);
    try rangeCheck16(V, ctx, pl[38]);
    try rangeCheck16(V, ctx, pl[39]);
    // c ∈ {0, 1}; pR32 = pL38 + 1 - 65536 c; pR33 = pL39 + c.
    const c = try ctx.guessM31(carry);
    try ctx.eq(try ctx.mul(c, try ctx.sub(c, ctx.one())), ctx.zero());
    const base = try ctx.constant(QM31.fromBase(M31.fromCanonical(65536)));
    try ctx.eq(pr[32], try ctx.sub(try ctx.add(pl[38], ctx.one()), try ctx.mul(base, c)));
    try ctx.eq(pr[33], try ctx.add(pl[39], c));
}

/// The finalized (unpadded) node circuit over `children`, whose proofs share `shared`.
/// `carry` is the height carry's value (`QM31` value mode) or `.{}` (topology mode).
pub fn buildNodeCircuit(
    comptime V: type,
    gpa: std.mem.Allocator,
    table: *const circuit.air_eval.component_table.Table,
    children: [2]ChildInput(V),
    shared: *const multiverifier.SharedConfig,
    carry: V,
) !Context(V) {
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const config: circuit_statement.CircuitConfig = .{
        .config = shared.pcs_config,
        .preprocessed_column_log_sizes = shared.preprocessed_column_log_sizes,
    };
    var pubs: [2][N_PUB]Var = undefined;
    var key_words: [32]U32Wrapper(Var) = undefined;
    for (children, 0..) |child, i| {
        for (&pubs[i], child.pubs) |*v, value| v.* = try ctx.guessM31(value);
        const key = try builder.blake.guessHash(V, &ctx, child.key);
        const digest = try leaf.pubsDigestVars(V, &ctx, key.words, &pubs[i]);
        const root = try builder.blake.guessHash(V, &ctx, child.preprocessed_root);
        const statement = try circuit_statement.CircuitStatement(V).init(&ctx, table, &config, root, digest);
        const proof_vars = try stark_proof.guess(V, &ctx, child.proof);
        try verify_mod.verify(V, &ctx, &proof_vars, shared.proof_config, &statement, verify_mod.NoStages{});
        @memcpy(key_words[16 * i ..][0..8], &statement.circuit_hash.words);
        @memcpy(key_words[16 * i + 8 ..][0..8], &key.words);
    }
    try linkChecks(V, &ctx, &pubs[0], &pubs[1], carry);
    const node_key = try builder.blake.blake2sU32s(V, &ctx, &key_words, 4 * key_words.len);
    var out: [N_PUB]Var = undefined;
    for (&out, 0..) |*o, k| o.* = if (isIn(k)) pubs[0][k] else pubs[1][k];
    try leaf.finish(V, &ctx, try leaf.pubsDigestVars(V, &ctx, node_key.words, &out));
    return ctx;
}

/// The shared shape of every leaf and node: padding target and the children's proof config.
pub const Shape = struct {
    target: ComponentSizes,
    shared: multiverifier.SharedConfig,
    fri: FriConfigV2,

    /// The smallest target covering `start` (the leaves' padded sizes) and the node circuit
    /// that verifies proofs of that target (`sharedTargetFixpoint`, for our node).
    pub fn init(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, start: ComponentSizes, fri: FriConfigV2) !Shape {
        var target = start;
        while (true) {
            var shared = try multiverifier.foldSharedConfig(gpa, target, fri);
            errdefer shared.deinit(gpa);
            var ctx = try buildTopology(gpa, table, &shared);
            defer ctx.deinit();
            const grown = target.elementwiseMax(finalize.computePaddedSizes(.fromBuilder(&ctx.circuit)));
            if (std.meta.eql(grown, target)) return .{ .target = target, .shared = shared, .fri = fri };
            shared.deinit(gpa);
            target = grown;
        }
    }

    pub fn deinit(self: *Shape, gpa: std.mem.Allocator) void {
        self.shared.deinit(gpa);
    }
};

fn buildTopology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const empty = try stark_proof.emptyProof(arena.allocator(), shared.proof_config);
    var pubs: [N_PUB]NoValue = undefined;
    @memset(&pubs, .{});
    const child: ChildInput(NoValue) = .{ .proof = &empty, .preprocessed_root = undefined, .key = undefined, .pubs = pubs };
    return buildNodeCircuit(NoValue, gpa, table, .{ child, child }, shared, .{});
}

/// A proved subtree: its proof, key and public inputs.
pub const Proved = struct {
    proof: leaf.CircuitProof,
    key: Key,
    pubs: [N_PUB]M31,

    pub fn digest(self: *const Proved) [8]u32 {
        return leaf.pubsDigest(self.key, &self.pubs);
    }
};

/// Proves the node over `left` and `right` (both proved under `shape`) and verifies it natively.
pub fn proveNode(
    gpa: std.mem.Allocator,
    a: std.mem.Allocator,
    tables: *const leaf.Tables,
    shape: *const Shape,
    left: *const Proved,
    right: *const Proved,
) !Proved {
    var inputs: [2]ChildInput(QM31) = undefined;
    var values: [2]stark_proof.Proof(QM31) = undefined;
    for ([_]*const Proved{ left, right }, &inputs, &values) |child, *input, *v| {
        v.* = try circuit_cpu.verifier_proof.circuitVerifierValues(a, &child.proof.prepared.proof, child.proof.prepared.config);
        var pubs: [N_PUB]QM31 = undefined;
        for (&pubs, child.pubs) |*p, x| p.* = QM31.fromBase(x);
        input.* = .{
            .proof = v,
            .preprocessed_root = builder.blake.hashValue(QM31, child.proof.request.preprocessed_root),
            .key = builder.blake.hashValue(QM31, child.key),
            .pubs = pubs,
        };
    }
    const carry: u32 = if (left.pubs[38].toU32() == 0xffff) 1 else 0;
    var ctx = try buildNodeCircuit(QM31, gpa, &tables.table, inputs, &shape.shared, QM31.fromBase(M31.fromCanonical(carry)));
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shape.target, shape.fri);
    errdefer cp.deinit();
    const node: Proved = .{
        .proof = cp,
        .key = nodeKey(left.proof.circuit_hash, left.key, right.proof.circuit_hash, right.key),
        .pubs = combine(left.pubs, right.pubs),
    };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &node.digest())) return error.NodeDigestMismatch;
    return node;
}

/// A circuit's identity: preprocessed root and circuit hash (as the in-circuit statement
/// computes it), both as 8 words.
pub const Identity = struct { root: [8]u32, hash: [8]u32 };

/// The node circuit's identity, derived from its topology alone (no proof needed).
pub fn nodeIdentity(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, shape: *const Shape) !Identity {
    var ctx = try buildTopology(gpa, table, &shape.shared);
    defer ctx.deinit();
    try finalize.padToTargets(NoValue, &ctx, shape.target);
    var pp = try circuit.common.preprocessed.PreprocessedCircuit.fromBuilderCircuit(gpa, &ctx.circuit);
    defer pp.deinit(gpa);
    const id = try circuit_cpu.recursion.circuit_params.identity(gpa, &pp, shape.fri.log_blowup_factor);
    return .{
        .root = core.vcs.blake2_hash.digestToU32s(id.preprocessed_root),
        .hash = core.vcs.blake2_hash.digestToU32s(id.circuit_hash),
    };
}

/// Folds `items` (in chain order, consumed) into one root: each layer pairs entries left to
/// right and carries an unpaired last entry up unchanged.
pub fn foldAll(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, items: []Proved) !Proved {
    if (items.len == 0) return error.NothingToFold;
    var layer = items;
    while (layer.len > 1) {
        const next = try a.alloc(Proved, (layer.len + 1) / 2);
        for (next, 0..) |*n, i| {
            if (2 * i + 1 < layer.len) {
                n.* = try proveNode(gpa, a, tables, shape, &layer[2 * i], &layer[2 * i + 1]);
                layer[2 * i].proof.deinit();
                layer[2 * i + 1].proof.deinit();
            } else n.* = layer[2 * i];
        }
        layer = next;
    }
    return layer[0];
}

/// The root's identity and key for the tree `foldAll` builds over leaves with circuit hashes
/// `leaf_hashes`, given the node circuit hash.
pub fn expectedRoot(a: std.mem.Allocator, leaf_hashes: []const [8]u32, node_hash: [8]u32) !struct { hash: [8]u32, key: Key } {
    if (leaf_hashes.len == 0) return error.NothingToFold;
    const E = struct { hash: [8]u32, key: Key };
    var layer = try a.alloc(E, leaf_hashes.len);
    for (layer, leaf_hashes) |*e, h| e.* = .{ .hash = h, .key = leaf.zero_key };
    while (layer.len > 1) {
        const next = try a.alloc(E, (layer.len + 1) / 2);
        for (next, 0..) |*n, i| n.* = if (2 * i + 1 < layer.len)
            .{ .hash = node_hash, .key = nodeKey(layer[2 * i].hash, layer[2 * i].key, layer[2 * i + 1].hash, layer[2 * i + 1].key) }
        else
            layer[2 * i];
        layer = next;
    }
    return .{ .hash = layer[0].hash, .key = layer[0].key };
}

/// What the outer verifier trusts: the node circuit's identity and each leaf's circuit hash
/// (by segment, in chain order; a leaf's hash depends only on its log size).
pub const Vk = struct { node: Identity, leaf_hashes: []const [8]u32 };

/// **The outer verifier.** Accepts `proof` as the root of a tree over `vk.leaf_hashes.len >= 2`
/// segments with public inputs `pubs`, starting at genesis. On success, `chain_from_genesis`
/// (Aggregate.lean) applies: the headers form a valid chain from genesis to the tip in
/// `pubs[16..32]`, at height `pubs[38..40]`, with chainwork `pubs[98..108]`.
pub fn verifyRoot(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: Vk, proof: *const leaf.CircuitProof, pubs: [N_PUB]M31) !void {
    if (vk.leaf_hashes.len < 2) return error.RootIsNotANode;
    const expected = try expectedRoot(a, vk.leaf_hashes, vk.node.hash);
    if (!std.mem.eql(u32, &proof.request.preprocessed_root, &vk.node.root)) return error.WrongRootCircuit;
    const out = try leaf.verifyCircuit(gpa, tables, proof);
    if (!std.mem.eql(u32, &out, &leaf.pubsDigest(expected.key, &pubs))) return error.WrongRootDigest;
    // Genesis input state: prev-hash 0, height 0, sentinel window, work 0.
    const H = @import("../btc/header_chain.zig");
    for (0..16) |k| if (pubs[k].toU32() != 0) return error.NotFromGenesis;
    if (pubs[32].toU32() != 0 or pubs[33].toU32() != 0) return error.NotFromGenesis;
    for (H.SENTINEL, 0..) |w, k| {
        const at: usize = if (k == 0) 44 else 48 + 2 * (k - 1);
        if (pubs[at].toU32() != (w & 0xffff) or pubs[at + 1].toU32() != (w >> 16)) return error.NotFromGenesis;
    }
    for (88..98) |k| if (pubs[k].toU32() != 0) return error.NotFromGenesis;
}

test "two chained segments fold into one node proof; a non-chained pair is rejected" {
    const H = @import("../btc/header_chain.zig");
    const segments = @import("../btc/segments.zig");
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const all = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const fri = try FriConfigV2.init(10, 0, 1, 3, 1);

    // The shape: covers the leaves (2^12 rows, 16 headers) and the node itself.
    var sl0 = try leaf.buildSegmentLeaf(gpa, a, 12, all[0..16], H.genesis_start);
    var sl1 = try leaf.buildSegmentLeaf(gpa, a, 12, all[16..32], segments.startAt(all, 16, segments.workBefore(all, 16)));
    var shape = try Shape.init(gpa, &tables.table, sl0.paddedSizes().elementwiseMax(sl1.paddedSizes()), fri);
    defer shape.deinit(gpa);
    var l0 = try leaf.proveSegmentLeaf(gpa, a, tables, &sl0, shape.target, fri);
    defer l0.proof.deinit();
    var l1 = try leaf.proveSegmentLeaf(gpa, a, tables, &sl1, shape.target, fri);
    defer l1.proof.deinit();
    const p0: Proved = .{ .proof = l0.proof, .key = leaf.zero_key, .pubs = l0.pubs };
    const p1: Proved = .{ .proof = l1.proof, .key = leaf.zero_key, .pubs = l1.pubs };

    var timer = try std.time.Timer.start();
    var n = try proveNode(gpa, a, tables, &shape, &p0, &p1);
    defer n.proof.deinit();
    std.debug.print("node: proved and verified in {d:.1}s, {d} bytes\n", .{ @as(f64, @floatFromInt(timer.read())) / 1e9, n.proof.bytes.len });
    try std.testing.expectEqual(@as(u32, 0), n.pubs[32].toU32());
    try std.testing.expectEqual(@as(u32, 31), n.pubs[38].toU32());

    // Circuit identities: a leaf's depends only on its log size; the node's comes from topology.
    try std.testing.expectEqualSlices(u32, &l0.proof.circuit_hash, &l1.proof.circuit_hash);
    const node_id = try nodeIdentity(gpa, &tables.table, &shape);
    try std.testing.expectEqualSlices(u32, &node_id.root, &n.proof.request.preprocessed_root);
    try std.testing.expectEqualSlices(u32, &node_id.hash, &n.proof.circuit_hash);

    // The outer verifier accepts the root, and rejects other public inputs or a wrong VK.
    const vk: Vk = .{ .node = node_id, .leaf_hashes = &.{ l0.proof.circuit_hash, l1.proof.circuit_hash } };
    try verifyRoot(gpa, a, tables, vk, &n.proof, n.pubs);
    var other = n.pubs;
    other[38] = M31.fromCanonical(32);
    try std.testing.expectError(error.WrongRootDigest, verifyRoot(gpa, a, tables, vk, &n.proof, other));
    var bad_vk = vk;
    bad_vk.leaf_hashes = &.{ l0.proof.circuit_hash, node_id.hash };
    try std.testing.expectError(error.WrongRootDigest, verifyRoot(gpa, a, tables, bad_vk, &n.proof, n.pubs));

    // Not chained: the node circuit is unsatisfiable.
    try std.testing.expectError(error.CircuitUnsatisfied, proveNode(gpa, a, tables, &shape, &p1, &p0));
}
