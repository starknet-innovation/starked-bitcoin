//! The set tree (set-pass step 4, docs/design/set-pass.md § The tree): segment proofs of the coin-set
//! pass folded into one proof.
//!
//! A **set leaf** verifies a segment proof (the 9-component segment system, `block/set_seg.zig`) with
//! the plain verifier and outputs the digest of its 32-limb summary: the 16-bit halves of the Blake2s
//! digests of its incoming and outgoing state vectors (challenge, then carried state; Lean
//! `Circuit/SetTree.lean`, `setLeafOut`). A **set node** is the Lean glue `setNodeProgram` replayed with
//! the recursive verifier at its two hooks (`node.RecHook`): the right child's incoming digest is the
//! left's outgoing one; the output is (left's incoming, right's outgoing). Leaves and nodes share one
//! padded shape; every leaf of a pass has the same component logs (`set_seg.buildAt`), hence one
//! identity, and the tree over `k` leaves splits at the largest power of two below `k`.
//!
//! The verifier rebuilds the start state (`set_seg.begin`) and takes the final state, and compares their
//! digests with the root's summary (`verifyRoot`).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const postcard = @import("stwo_postcard");
const leaf = @import("leaf.zig");
const node_mod = @import("node.zig");
const pv = @import("plain_verifier.zig");
const glue = @import("glue.zig");
const BF = @import("block_forest.zig");
const store = @import("store.zig");
const ir = @import("../air/ir.zig");
const system = @import("../air/system.zig");
const rec = @import("../air/prove_rec.zig");
const component = @import("../air/component.zig");
const SS = @import("../block/set_seg.zig");
const coin = @import("../block/coin.zig");

const builder = circuit.builder;
const finalize = circuit.common.finalize;
const component_list = circuit.common.component_list;
const multiverifier = circuit.statements.multiverifier;
const stark_proof = circuit.stark_verifier.proof;
const Var = builder.Var;
const Context = builder.Context;
const NoValue = builder.NoValue;
const HashValue = builder.blake.HashValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const ComponentSizes = leaf.ComponentSizes;
const Key = leaf.Key;
const N_COMP = SS.N_COMP;
const N_PUB = SS.N_PUB;

pub const Logs = [N_COMP]u32;

// ---------------------------------------------------------------------------------------------
// Segment proof files

pub const SEG_MAGIC = "SBSEGMT\x00";

/// One segment's STARK, its component logs and public inputs.
pub const SegFile = struct {
    logs: Logs,
    pubs: [N_PUB]M31,
    proof: system.Proof,
};

pub fn maxLog(logs: Logs) u32 {
    var l: u32 = 0;
    for (logs) |x| l = @max(l, x);
    return l;
}

pub fn partsOf(airs: *const [N_COMP]ir.Air, logs: Logs, pubs: *const [N_PUB]M31) [N_COMP]system.Part {
    var out: [N_COMP]system.Part = undefined;
    for (&out, airs, logs) |*p, *air, l| p.* = .{ .air = air, .log_size = l, .pubs = pubs[0..air.n_pub] };
    return out;
}

/// Proves segment `b` (consumes its witness).
pub fn proveSeg(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const SS.Built, fri: FriConfigV2) !SegFile {
    const ps = partsOf(airs, b.logs, &b.pubs);
    const cfg = rec.Config.fromFriAndTraceSize(fri, maxLog(b.logs));
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var mains: [N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    const proof = try system.proveOpts(E, a, cfg, &ps, &mains, .{ .storage = .compact, .discard_mains = true });
    return .{ .logs = b.logs, .pubs = b.pubs, .proof = proof };
}

/// Verifies a segment's STARK under the pinned `fri` (consumes the proof).
pub fn verifySeg(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, f: *const SegFile, fri: FriConfigV2) !void {
    const c = f.proof.stark.commitment_scheme_proof.config;
    if (c.pow_bits != fri.pow_bits or c.fri_config.log_blowup_factor != fri.log_blowup_factor or
        c.fri_config.n_queries != fri.n_queries or c.fri_config.log_last_layer_degree_bound != fri.log_last_layer_degree_bound)
        return error.ConfigMismatch;
    const ps = partsOf(airs, f.logs, &f.pubs);
    try system.verifyExt(a, rec.Config.fromFriAndTraceSize(fri, maxLog(f.logs)), &ps, &.{}, f.proof);
}

pub fn encodeSeg(a: std.mem.Allocator, f: *const SegFile) ![]u8 {
    var e: store.Enc = .{ .a = a };
    try e.buf.appendSlice(a, SEG_MAGIC);
    try e.int(u32, store.VERSION);
    for (f.logs) |l| try e.int(u32, l);
    for (f.pubs) |p| try e.int(u32, p.toU32());
    try e.int(u32, @intCast(f.proof.claimed_sums.len));
    for (f.proof.claimed_sums) |s| for (s.toM31Array()) |x| try e.int(u32, x.toU32());
    var pb = std.ArrayList(u8).empty;
    try postcard.serializeProof(rec.Hasher, pb.writer(a), f.proof.stark);
    try e.blob(pb.items);
    return store.seal(&e);
}

fn m31(x: u32) !M31 {
    if (x >= 0x7fffffff) return error.NonCanonical;
    return M31.fromCanonical(x);
}

pub fn decodeSeg(a: std.mem.Allocator, bytes: []const u8) !SegFile {
    var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
    try d.magic(SEG_MAGIC);
    var f: SegFile = undefined;
    for (&f.logs) |*l| {
        l.* = try d.int(u32);
        if (l.* > 24) return error.LogSizeOutOfRange;
    }
    for (&f.pubs) |*p| p.* = try m31(try d.int(u32));
    const n_sums = try d.int(u32);
    if (n_sums > N_COMP) return error.TooManySums;
    const sums = try a.alloc(QM31, n_sums);
    for (sums) |*s| {
        var v: [4]M31 = undefined;
        for (&v) |*x| x.* = try m31(try d.int(u32));
        s.* = QM31.fromM31Array(v);
    }
    const pb = try d.blob();
    var pfbs = std.io.fixedBufferStream(pb);
    const stark = try postcard.deserializeProof(rec.Hasher, a, pfbs.reader());
    if (pfbs.pos != pb.len) return error.TrailingProofBytes;
    if (d.pos != d.bytes.len) return error.TrailingBytes;
    f.proof = .{ .stark = stark, .claimed_sums = sums };
    return f;
}

// ---------------------------------------------------------------------------------------------
// Summaries (Lean `SetTree.inIdx`, `outIdx`, `setLeafOut`)

pub const NS = 32;
pub const Summary = [NS]M31;
pub const NV = 331;
pub const Vec = [NV]M31;

fn vecOf(pubs: *const [N_PUB]M31, comptime out: bool) Vec {
    var v: Vec = undefined;
    var k: usize = 0;
    const put = struct {
        fn f(vv: *Vec, kk: *usize, x: M31) void {
            vv[kk.*] = x;
            kk.* += 1;
        }
    }.f;
    for (0..112) |j| put(&v, &k, pubs[SS.PUB_G + j]);
    if (out) {
        put(&v, &k, pubs[SS.PUB_I_OUT]);
        put(&v, &k, M31.one());
        for (0..36) |j| put(&v, &k, pubs[SS.PUB_LAST_OUT + j]);
        put(&v, &k, pubs[SS.PUB_MAXH_OUT]);
        for (0..4) |j| put(&v, &k, pubs[SS.PUB_SUM_OUT + j]);
        for (0..12) |j| put(&v, &k, pubs[SS.PUB_AMT_OUT + j]);
        for (0..82) |j| put(&v, &k, pubs[SS.B2_OUT + j]);
        for (0..82) |j| put(&v, &k, pubs[SS.SHA_OUT + j]);
    } else {
        put(&v, &k, pubs[SS.PUB_I_IN]);
        put(&v, &k, pubs[SS.PUB_HASLAST]);
        for (0..36) |j| put(&v, &k, pubs[SS.PUB_LAST_IN + j]);
        put(&v, &k, pubs[SS.PUB_MAXH_IN]);
        for (0..4) |j| put(&v, &k, pubs[SS.PUB_SUM_IN + j]);
        for (0..12) |j| put(&v, &k, pubs[SS.PUB_AMT_IN + j]);
        for (0..82) |j| put(&v, &k, pubs[SS.B2_IN + j]);
        for (0..82) |j| put(&v, &k, pubs[SS.SHA_IN + j]);
    }
    std.debug.assert(k == NV);
    return v;
}

/// The incoming state vector of a segment's public inputs.
pub fn inVec(pubs: *const [N_PUB]M31) Vec {
    return vecOf(pubs, false);
}

/// The outgoing state vector (its `HASLAST` is 1).
pub fn outVec(pubs: *const [N_PUB]M31) Vec {
    return vecOf(pubs, true);
}

/// The state vector of `st` under `ch`: `SS.statePubs` placed as incoming inputs.
pub fn stateVec(ch: coin.Challenge, st: SS.State) Vec {
    var pubs: [N_PUB]M31 = undefined;
    SS.statePubsIn(&pubs, ch, st);
    return inVec(&pubs);
}

/// Blake2s over the limbs as little-endian u32 words (the Lean `pubsDigest` with no key).
pub fn vecDigest(v: []const M31) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    for (v) |x| {
        std.mem.writeInt(u32, &b, x.toU32(), .little);
        h.update(&b);
    }
    var d: [32]u8 = undefined;
    h.final(&d);
    var out: [8]u32 = undefined;
    for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return out;
}

fn limbs16(d: [8]u32, out: []M31) void {
    for (d, 0..) |w, i| {
        out[2 * i] = M31.fromCanonical(w & 0xffff);
        out[2 * i + 1] = M31.fromCanonical(w >> 16);
    }
}

/// The summary of two state digests.
pub fn summaryOf(din: [8]u32, dout: [8]u32) Summary {
    var s: Summary = undefined;
    limbs16(din, s[0..16]);
    limbs16(dout, s[16..32]);
    return s;
}

/// A segment's summary (what the leaf circuit outputs).
pub fn leafSummary(pubs: *const [N_PUB]M31) Summary {
    return summaryOf(vecDigest(&inVec(pubs)), vecDigest(&outVec(pubs)));
}

/// Two linked ranges' summary (what the node circuit outputs).
pub fn joinSummary(l: Summary, r: Summary) !Summary {
    for (0..16) |j| if (!l[16 + j].eql(r[j])) return error.NotLinked;
    var s: Summary = undefined;
    @memcpy(s[0..16], l[0..16]);
    @memcpy(s[16..32], r[16..32]);
    return s;
}

// ---------------------------------------------------------------------------------------------
// The leaf

/// The plain-verifier configuration of a segment proof at `logs`.
pub fn configOf(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, logs: Logs, fri: FriConfigV2) !pv.PlainConfig {
    const L = maxLog(logs);
    const ps = try a.alloc(pv.PartConfig, N_COMP);
    for (ps, airs, logs) |*p, *air, l| p.* = .{
        .n_preprocessed = air.n_preprocessed,
        .main_offsets = try pv.mainOffsets(a, air.*),
        .n_inter = 4 * component.nBatches(air.*),
        .log_size = if (l == L) null else l,
    };
    return .{ .log_trace_size = L, .fri = rec.Config.fromFriAndTraceSize(fri, L).fri_config, .system = true, .parts = ps };
}

pub const LeafInputs = struct {
    values: pv.PlainProof(QM31),
    config: pv.PlainConfig,
    digests: [N_COMP][32]u8,
    pre_root: [32]u8,
};

/// A segment proof verified natively with capture, and what its leaf circuit is built from.
pub fn leafInputs(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, f: *const SegFile, fri: FriConfigV2) !LeafInputs {
    const ps = partsOf(airs, f.logs, &f.pubs);
    const cfg = rec.Config.fromFriAndTraceSize(fri, maxLog(f.logs));
    var capture: core.verifier.ProofCapture(rec.Hasher) = undefined;
    try system.verifyCaptureBorrowedPre(a, cfg, &ps, &.{}, &f.proof, &capture, null);
    const pc = try configOf(a, airs, f.logs, fri);
    var in: LeafInputs = .{
        .values = try pv.fromCapture(a, rec.Hasher, &f.proof.stark, &capture, pc, f.proof.claimed_sums),
        .config = pc,
        .digests = undefined,
        .pre_root = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &ps)),
    };
    for (&in.digests, airs) |*d, *air| d.* = try air.digest(a);
    return in;
}

const InputHooks = struct {
    inputs: []const Var,
    pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
        return if (id == 0) self.inputs else error.UnknownHook;
    }
};

/// The set leaf circuit (finalized, unpadded): the plain verifier, then the Lean output program
/// `setLeafOut` (hook 0 returns the segment's public inputs).
pub fn buildLeafCircuit(gpa: std.mem.Allocator, in: *const LeafInputs, airs: *const [N_COMP]ir.Air, pubs: *const [N_PUB]M31) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const g = try pv.guess(QM31, &ctx, &in.values);
    var pub_vars: [N_PUB]Var = undefined;
    for (&pub_vars, pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
    var parts: [N_COMP]pv.PartStatement = undefined;
    for (&parts, airs, &in.digests) |*p, *air, d| p.* = .{ .air = air, .digest = d, .pubs = pub_vars[0..air.n_pub] };
    const st = pv.PlainStatement{ .parts = &parts, .preprocessed_root = in.pre_root };
    try pv.verifyPlain(QM31, &ctx, &g, in.config, &st);
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:set_leaf_out"));
    try ctx.setOutputs(try glue.run(QM31, &ctx, &prog, &.{}, InputHooks{ .inputs = &pub_vars }));
    try ctx.finalize(false);
    return ctx;
}

pub fn leafCircuitOf(gpa: std.mem.Allocator, a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, f: *const SegFile, fri: FriConfigV2) !Context(QM31) {
    const in = try leafInputs(a, airs, f, fri);
    return buildLeafCircuit(gpa, &in, airs, &f.pubs);
}

// ---------------------------------------------------------------------------------------------
// The node

pub fn ChildInput(comptime V: type) type {
    return struct {
        proof: *const stark_proof.Proof(V),
        preprocessed_root: HashValue(V),
        key: HashValue(V),
        sum: [NS]V,
    };
}

/// The set node circuit (finalized, unpadded): the Lean glue `setNodeProgram` with the children's
/// verifiers at its hooks.
pub fn buildNodeCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, children: [2]ChildInput(V), shared: *const multiverifier.SharedConfig) !Context(V) {
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:set_node_glue"));
    const per = NS + 16;
    const ext = try ctx.scratch().alloc(V, 2 * per);
    for (children, 0..) |child, i| {
        @memcpy(ext[per * i ..][0..NS], &child.sum);
        for (child.key.words, 0..) |w, k| ext[per * i + NS + k] = w.get();
        for (child.preprocessed_root.words, 0..) |w, k| ext[per * i + NS + 8 + k] = w.get();
    }
    try glue.runOutputs(V, &ctx, &prog, ext, node_mod.RecHook(V){ .ctx = &ctx, .table = table, .proofs = .{ children[0].proof, children[1].proof }, .shared = shared });
    return ctx;
}

pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const empty = try stark_proof.emptyProof(arena.allocator(), shared.proof_config);
    var sum: [NS]NoValue = undefined;
    @memset(&sum, .{});
    const child: ChildInput(NoValue) = .{ .proof = &empty, .preprocessed_root = undefined, .key = undefined, .sum = sum };
    return buildNodeCircuit(NoValue, gpa, table, .{ child, child }, shared);
}

/// The shared shape of set leaves and nodes: the leaf's padded sizes, grown to a fixpoint with the node.
pub const Shape = struct {
    target: ComponentSizes,
    shared: multiverifier.SharedConfig,
    fri: FriConfigV2,

    pub fn init(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, start: ComponentSizes, fri: FriConfigV2) !Shape {
        var target = start;
        while (true) {
            var shared = try multiverifier.foldSharedConfig(gpa, target, fri);
            errdefer shared.deinit(gpa);
            var ctx = try topology(gpa, table, &shared);
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

/// A proved range of segments: its circuit proof, key and summary.
pub const Proved = struct {
    proof: leaf.CircuitProof,
    key: Key,
    sum: Summary,

    pub fn digest(self: *const Proved) [8]u32 {
        return leaf.pubsDigest(self.key, &self.sum);
    }
};

fn childInputs(a: std.mem.Allocator, children: [2]*const Proved, values: *[2]stark_proof.Proof(QM31)) ![2]ChildInput(QM31) {
    var inputs: [2]ChildInput(QM31) = undefined;
    for (children, &inputs, values) |child, *input, *v| {
        v.* = try circuit_cpu.verifier_proof.circuitVerifierValues(a, &child.proof.prepared.proof, child.proof.prepared.config);
        var sum: [NS]QM31 = undefined;
        for (&sum, child.sum) |*p, x| p.* = QM31.fromBase(x);
        input.* = .{
            .proof = v,
            .preprocessed_root = builder.blake.hashValue(QM31, child.proof.request.preprocessed_root),
            .key = builder.blake.hashValue(QM31, child.key),
            .sum = sum,
        };
    }
    return inputs;
}

pub fn nodeCircuitOf(gpa: std.mem.Allocator, scratch: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, left: *const Proved, right: *const Proved) !Context(QM31) {
    var values: [2]stark_proof.Proof(QM31) = undefined;
    const inputs = try childInputs(scratch, .{ left, right }, &values);
    return buildNodeCircuit(QM31, gpa, &tables.table, inputs, &shape.shared);
}

/// Proves the node over two linked ranges and verifies it natively; its digest must be the native join's.
pub fn proveNode(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, left: *const Proved, right: *const Proved) !Proved {
    const sum = try joinSummary(left.sum, right.sum);
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    var ctx = try nodeCircuitOf(gpa, scratch.allocator(), tables, shape, left, right);
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shape.target, shape.fri);
    errdefer cp.deinit();
    const node: Proved = .{
        .proof = cp,
        .key = node_mod.nodeKey(left.proof.circuit_hash, left.key, right.proof.circuit_hash, right.key),
        .sum = sum,
    };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &node.digest())) return error.NodeDigestMismatch;
    return node;
}

/// Proves a set leaf under `shape`, verifies it natively, and checks its digest.
pub fn proveLeaf(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, airs: *const [N_COMP]ir.Air, f: *const SegFile, fri: FriConfigV2) !Proved {
    var ctx = try leafCircuitOf(gpa, a, airs, f, fri);
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shape.target, shape.fri);
    errdefer cp.deinit();
    const p: Proved = .{ .proof = cp, .key = leaf.zero_key, .sum = leafSummary(&f.pubs) };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &p.digest())) return error.LeafDigestMismatch;
    return p;
}

// ---------------------------------------------------------------------------------------------
// The tree

/// Where the tree over `k ≥ 2` leaves splits: the largest power of two below `k`.
pub fn split(k: usize) usize {
    std.debug.assert(k >= 2);
    return @as(usize, 1) << @intCast(std.math.log2_int(usize, k - 1));
}

/// Proves the tree over `files` (each proof's leaf circuit is built, proved and dropped as it goes).
pub fn proveTree(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, airs: *const [N_COMP]ir.Air, files: []const SegFile, fri: FriConfigV2) !Proved {
    if (files.len == 0) return error.NoSegments;
    if (files.len == 1) return proveLeaf(gpa, a, tables, shape, airs, &files[0], fri);
    const s = split(files.len);
    var l = try proveTree(gpa, a, tables, shape, airs, files[0..s], fri);
    defer l.proof.deinit();
    var r = try proveTree(gpa, a, tables, shape, airs, files[s..], fri);
    defer r.proof.deinit();
    return proveNode(gpa, a, tables, shape, &l, &r);
}

/// The set tree's verification key: the circuits' FRI, the segments' FRI and component logs, the leaf's
/// and the node's identities.
pub const Vk = struct {
    fri: FriConfigV2,
    seg_fri: FriConfigV2,
    logs: Logs,
    trace_log: u32,
    leaf: BF.Id,
    node: BF.Id,

    pub const MAGIC = "SBSETVK\x00";

    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.fri(self.seg_fri);
        for (self.logs) |l| try e.int(u32, l);
        try e.int(u32, self.trace_log);
        for ([_]BF.Id{ self.leaf, self.node }) |id| {
            try e.words(&id.root);
            try e.words(&id.hash);
        }
        return store.seal(&e);
    }

    pub fn decode(bytes: []const u8) !Vk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(MAGIC);
        const fri = try d.fri();
        const seg_fri = try d.fri();
        var vk: Vk = .{ .fri = fri, .seg_fri = seg_fri, .logs = undefined, .trace_log = 0, .leaf = undefined, .node = undefined };
        for (&vk.logs) |*l| l.* = try d.int(u32);
        vk.trace_log = try d.int(u32);
        vk.leaf = .{ .root = try d.words(8), .hash = try d.words(8) };
        vk.node = .{ .root = try d.words(8), .hash = try d.words(8) };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// The shape and the VK from one segment proof at the pass's logs (every leaf has the same identity).
pub fn setup(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, airs: *const [N_COMP]ir.Air, sample: *const SegFile, seg_fri: FriConfigV2, fri: FriConfigV2) !struct { shape: Shape, vk: Vk } {
    var start_ctx = try leafCircuitOf(gpa, a, airs, sample, seg_fri);
    defer start_ctx.deinit();
    var shape = try Shape.init(gpa, &tables.table, finalize.computePaddedSizes(.fromBuilder(&start_ctx.circuit)), fri);
    errdefer shape.deinit(gpa);
    const li = try BF.identityOf(gpa, QM31, &start_ctx, shape.target, fri.log_blowup_factor);
    var topo = try topology(gpa, &tables.table, &shape.shared);
    defer topo.deinit();
    const ni = try BF.identityOf(gpa, NoValue, &topo, shape.target, fri.log_blowup_factor);
    if (ni.trace_log != li.trace_log) return error.ShapeMismatch;
    return .{ .shape = shape, .vk = .{ .fri = fri, .seg_fri = seg_fri, .logs = sample.logs, .trace_log = li.trace_log, .leaf = li.id, .node = ni.id } };
}

/// The key and circuit hash a tree over `k` leaves must have.
pub fn expected(vk: *const Vk, k: usize) struct { key: Key, hash: [8]u32 } {
    if (k == 1) return .{ .key = leaf.zero_key, .hash = vk.leaf.hash };
    const s = split(k);
    const l = expected(vk, s);
    const r = expected(vk, k - s);
    return .{ .key = node_mod.nodeKey(l.hash, l.key, r.hash, r.key), .hash = vk.node.hash };
}

/// **Verifies a set root** over `k` segments: the proof is the VK's circuit at the expected key, and
/// its summary is the digests of the pass's start state (`begin(n)`) and of `final`, under `ch`.
pub fn verifyRoot(gpa: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, root: *const Proved, k: usize, ch: coin.Challenge, count: [4]u8, final: SS.State) !void {
    if (k == 0) return error.NoSegments;
    const want = expected(vk, k);
    const id = if (k == 1) vk.leaf else vk.node;
    if (!std.mem.eql(u32, &root.proof.request.preprocessed_root, &id.root)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &root.proof.circuit_hash, &want.hash)) return error.WrongCircuit;
    if (!std.meta.eql(root.proof.request.pcs_config, PcsConfigV2.fromFriAndTraceSize(vk.fri, vk.trace_log))) return error.ConfigNotPinned;
    const out = try leaf.verifyCircuit(gpa, tables, &root.proof);
    const sum = summaryOf(vecDigest(&stateVec(ch, SS.begin(count))), vecDigest(&outStateVec(ch, final)));
    if (!std.mem.eql(u32, &out, &leaf.pubsDigest(want.key, &sum))) return error.WrongDigest;
}

/// The outgoing state vector of `st` (its `HASLAST` is 1).
pub fn outStateVec(ch: coin.Challenge, st: SS.State) Vec {
    var v = stateVec(ch, st);
    v[113] = M31.one();
    return v;
}

// ---------------------------------------------------------------------------------------------

test "set tree: state vectors match the segment's public inputs; summaries link" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const EP = @import("../block/epoch.zig");
    const ch = EP.challenge(@splat(7));
    const file = std.fs.cwd().readFileAlloc(a, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    var st = SS.begin(file[0..4].*);
    var at: usize = 4;
    var prev: ?Summary = null;
    var first: ?Summary = null;
    var k: usize = 0;
    while (at < file.len) : (k += 1) {
        var end = at;
        for (0..3) |_| if (end < file.len) {
            end += SS.HEAD + std.mem.readInt(u32, file[end + 45 ..][0..4], .little);
        };
        const b = try SS.build(a, ch, st, file[at..end]);
        try std.testing.expectEqualSlices(M31, &stateVec(ch, st), &inVec(&b.pubs));
        try std.testing.expectEqualSlices(M31, &outStateVec(ch, b.out), &outVec(&b.pubs));
        const s = leafSummary(&b.pubs);
        if (prev) |p| prev = try joinSummary(p, s) else {
            prev = s;
            first = s;
        }
        st = b.out;
        at = end;
    }
    const want = summaryOf(vecDigest(&stateVec(ch, SS.begin(file[0..4].*))), vecDigest(&outStateVec(ch, st)));
    try std.testing.expectEqualSlices(M31, &want, &prev.?);
    std.debug.print("set-170: {d} segments, summaries chain to begin/final\n", .{k});
}

test "set tree: three segments of set-170 proved, folded and verified; unlinked children and a wrong final state are rejected" {
    const gpa = std.heap.page_allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const EP = @import("../block/epoch.zig");
    const PF = @import("../block/proof_file.zig");
    const ch = EP.challenge(@splat(7));
    const file = std.fs.cwd().readFileAlloc(a, "data/epoch/set-170.bin", 1 << 30) catch return error.SkipZigTest;
    const airs = try SS.parseAirs(a);
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const sfri = PF.testFri();
    const cfri = try FriConfigV2.init(10, 0, 1, 3, 1);
    const logs: Logs = .{ 10, 8, 6, 6, 10, 8, 11, 10, 11 };
    const ends = try SS.cut(a, file, logs);
    var timer = try std.time.Timer.start();
    var files: [3]SegFile = undefined;
    var st = SS.begin(file[0..4].*);
    var at: usize = 4;
    for (&files, ends[0..3]) |*f, end| {
        const b = try SS.buildAt(a, ch, st, file[at..end], logs);
        st = b.out;
        const p = try proveSeg(a, &airs, &b, sfri);
        const bytes = try encodeSeg(a, &p);
        f.* = try decodeSeg(a, bytes);
        var g = try decodeSeg(a, bytes);
        try verifySeg(a, &airs, &g, sfri);
        at = end;
    }
    std.debug.print("3 segments ({d} records) proved in {d} ms\n", .{ st.i, timer.lap() / std.time.ns_per_ms });
    var su = try setup(gpa, a, tables, &airs, &files[0], sfri, cfri);
    defer su.shape.deinit(gpa);
    std.debug.print("shape and VK in {d} ms\n", .{timer.lap() / std.time.ns_per_ms});
    try std.testing.expectEqualDeep(su.vk, try Vk.decode(try su.vk.encode(a)));
    var l0 = try proveLeaf(gpa, a, tables, &su.shape, &airs, &files[0], sfri);
    defer l0.proof.deinit();
    var l1 = try proveLeaf(gpa, a, tables, &su.shape, &airs, &files[1], sfri);
    defer l1.proof.deinit();
    var l2 = try proveLeaf(gpa, a, tables, &su.shape, &airs, &files[2], sfri);
    defer l2.proof.deinit();
    std.debug.print("3 leaves in {d} ms\n", .{timer.lap() / std.time.ns_per_ms});
    // Unlinked children: the right child's incoming state is not the left's outgoing one.
    {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        var c = try nodeCircuitOf(gpa, scratch.allocator(), tables, &su.shape, &l1, &l0);
        defer c.deinit();
        try std.testing.expect(!try c.isCircuitValid());
    }
    var n01 = try proveNode(gpa, a, tables, &su.shape, &l0, &l1);
    defer n01.proof.deinit();
    var root = try proveNode(gpa, a, tables, &su.shape, &n01, &l2);
    defer root.proof.deinit();
    std.debug.print("2 nodes in {d} ms\n", .{timer.lap() / std.time.ns_per_ms});
    try verifyRoot(gpa, tables, &su.vk, &root, 3, ch, file[0..4].*, st);
    var bad = st;
    bad.amount += 1;
    try std.testing.expectError(error.WrongDigest, verifyRoot(gpa, tables, &su.vk, &root, 3, ch, file[0..4].*, bad));
    try std.testing.expectError(error.WrongDigest, verifyRoot(gpa, tables, &su.vk, &root, 4, ch, file[0..4].*, st));
    try std.testing.expectError(error.WrongCircuit, verifyRoot(gpa, tables, &su.vk, &n01, 1, ch, file[0..4].*, st));
}
