//! The leaf of the recursion tree (roadmap REC-LEAF): a header-chain segment proof, verified by
//! the plain in-circuit verifier (`plain_verifier.zig`), and that circuit's execution proved by
//! stwo-zig's circuit prover. Also the circuit-proof helpers shared with `node.zig`.
//!
//! Every leaf and node outputs `pubsDigest(key, pubs)`: Blake2s of the 8-word key followed by
//! the 108 public inputs as 32-bit words. A leaf's key is zero; a node's key commits to its
//! children's circuit hashes and keys (see `node.zig`).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const ir = @import("../air/ir.zig");
const pv = @import("plain_verifier.zig");
const H = @import("../btc/header_chain.zig");

const builder = circuit.builder;
const preprocessed = circuit.common.preprocessed;
const finalize = circuit.common.finalize;
const component_list = circuit.common.component_list;
const Var = builder.Var;
const Context = builder.Context;
const U32Wrapper = builder.wrappers.U32Wrapper;
const HashValue = builder.blake.HashValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
pub const ComponentSizes = finalize.ComponentSizes;

pub const bundle_bytes = @embedFile("circuit:air_programs");
pub const constraints_bytes = @embedFile("circuit:compiled_constraints");

pub const N_PUB = H.N_PUB;
pub const Key = [8]u32;
pub const zero_key: Key = @splat(0);

/// Blake2s of `key` then `pubs`, all as little-endian 32-bit words.
pub fn pubsDigest(key: Key, pubs: []const M31) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    for (key) |w| {
        std.mem.writeInt(u32, &b, w, .little);
        h.update(&b);
    }
    for (pubs) |p| {
        std.mem.writeInt(u32, &b, p.toU32(), .little);
        h.update(&b);
    }
    var d: [32]u8 = undefined;
    h.final(&d);
    var out: [8]u32 = undefined;
    for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return out;
}

/// In-circuit `pubsDigest`. `pubs` must be M31 variables (`guessM31`), so `m31ToU32` is
/// injective on them.
pub fn pubsDigestVars(comptime V: type, ctx: *Context(V), key: [8]U32Wrapper(Var), pubs: []const Var) !HashValue(Var) {
    const words = try ctx.scratch().alloc(U32Wrapper(Var), 8 + pubs.len);
    @memcpy(words[0..8], &key);
    for (words[8..], pubs) |*w, v| w.* = try builder.blake.m31ToU32(V, ctx, v);
    return builder.blake.blake2sU32s(V, ctx, words, 4 * words.len);
}

/// Sets the circuit's eight outputs to `digest` and finalizes it.
pub fn finish(comptime V: type, ctx: *Context(V), digest: HashValue(Var)) !void {
    var outputs: [8]Var = undefined;
    for (&outputs, digest.words) |*o, w| o.* = w.get();
    try ctx.setOutputs(&outputs);
    try ctx.finalize(false);
}

/// The finalized (unpadded) leaf circuit: verifies `values` against the AIR with public inputs
/// `pubs`, and outputs `pubsDigest(zero_key, pubs)`.
pub fn buildLeafCircuit(
    gpa: std.mem.Allocator,
    values: *const pv.PlainProof(QM31),
    config: pv.PlainConfig,
    air: *const ir.Air,
    digest: [32]u8,
    pre_root: [32]u8,
    pubs: []const M31,
) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const proof_vars = try pv.guess(QM31, &ctx, values);
    const pub_vars = try ctx.scratch().alloc(Var, pubs.len);
    for (pub_vars, pubs) |*w, v| w.* = try ctx.guessM31(QM31.fromBase(v));
    const st = pv.PlainStatement{ .parts = &.{.{ .air = air, .digest = digest, .pubs = pub_vars }}, .preprocessed_root = pre_root };
    try pv.verifyPlain(QM31, &ctx, &proof_vars, config, &st);
    var key: [8]U32Wrapper(Var) = undefined;
    for (&key) |*k| k.* = try builder.wrappers.constU32(QM31, &ctx, 0);
    try finish(QM31, &ctx, try pubsDigestVars(QM31, &ctx, key, pub_vars));
    return ctx;
}

/// The circuit AIR's evaluator table (for in-circuit and native verification of circuit proofs).
pub const Tables = struct {
    projection: circuit.air_eval.projection.Projection,
    table: circuit.air_eval.component_table.Table,

    pub fn init(gpa: std.mem.Allocator) !*Tables {
        const self = try gpa.create(Tables);
        errdefer gpa.destroy(self);
        self.projection = try circuit.air_eval.projection.parse(gpa, constraints_bytes);
        errdefer self.projection.deinit();
        self.table = try circuit.air_eval.circuit_components.build(gpa, &self.projection);
        return self;
    }

    pub fn deinit(self: *Tables, gpa: std.mem.Allocator) void {
        self.table.deinit();
        self.projection.deinit();
        gpa.destroy(self);
    }
};

/// A proof of a circuit's execution, as the native and in-circuit verifiers take it.
pub const CircuitProof = struct {
    prepared: circuit_cpu.verifier_proof.VerifierProof,
    bytes: []u8,
    request: circuit_cpu.verify.Request,
    circuit_hash: [8]u32,

    pub fn deinit(self: *CircuitProof) void {
        self.prepared.deinit();
    }
};

/// Pads a finalized, satisfied circuit to `target` (when given) and proves it under `fri`.
/// Allocations of the result's bytes and request use `a`.
pub fn proveCircuit(gpa: std.mem.Allocator, a: std.mem.Allocator, ctx: *Context(QM31), target: ?ComponentSizes, fri: FriConfigV2) !CircuitProof {
    if (target) |t| try finalize.padToTargets(QM31, ctx, t);
    if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
    var pp = try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, ctx);
    defer pp.deinit(gpa);
    var bundle = try circuit_cpu.air.parse(gpa, bundle_bytes);
    defer bundle.deinit();
    const pcs = PcsConfigV2.fromFriAndTraceSize(fri, pp.traceLogSize());
    var proof = try circuit_cpu.Internal.prove(gpa, ctx.values(), &pp, &bundle, pcs, .{}, {});
    defer proof.deinit();
    var prepared = try circuit_cpu.verifier_proof.prepare(gpa, &proof);
    errdefer prepared.deinit();

    const layout = pp.layout();
    const Column = @typeInfo(@TypeOf(@as(circuit_cpu.verify.Request, undefined).preprocessed_column_log_sizes)).pointer.child;
    const columns = try a.alloc(Column, layout.entries.len);
    for (layout.entries, columns) |entry, *c| c.* = .{ .id = try a.dupe(u8, entry.id), .log_size = entry.log_size };
    var digest: [8]u32 = undefined;
    for (proof.output_values, &digest) |value, *w| {
        const limbs = value.toM31Array();
        w.* = limbs[0].toU32() | (limbs[1].toU32() << 16);
    }
    return .{
        .bytes = try prepared.serialize(a),
        .prepared = prepared,
        .circuit_hash = core.vcs.blake2_hash.digestToU32s(proof.circuit_hash),
        .request = .{
            .pcs_config = proof.pcs_config,
            .preprocessed_column_log_sizes = columns,
            .preprocessed_root = core.vcs.blake2_hash.digestToU32s(proof.stark_proof.proof.commitment_scheme_proof.commitments.items[0]),
            .output_digest = digest,
        },
    };
}

/// Natively verifies a circuit proof (stwo-zig's circuit verifier) and returns its output
/// digest, `request.output_digest`, which acceptance binds to the proof. (`verifyProofBytes`
/// itself returns the verifier circuit's output, Blake2s(statement root ‖ output digest).)
/// The caller must also check the circuit's identity, `request.preprocessed_root`.
pub fn verifyCircuit(gpa: std.mem.Allocator, tables: *const Tables, cp: *const CircuitProof) ![8]u32 {
    const verdict = try circuit_cpu.verify.verifyProofBytes(gpa, &tables.table, &cp.request, cp.bytes);
    return switch (verdict) {
        .accepted => cp.request.output_digest,
        .rejected => |r| {
            std.debug.print("circuit proof rejected at {s}: {s}\n", .{ @tagName(r.stage), @errorName(r.reason) });
            return error.CircuitProofRejected;
        },
    };
}

pub const Timings = struct { segment_ns: u64 = 0, build_ns: u64 = 0, prove_ns: u64 = 0, verify_ns: u64 = 0, n_vars: usize = 0 };

/// A proved segment: its leaf proof, public inputs and timings.
pub const Leaf = struct { proof: CircuitProof, pubs: [N_PUB]M31, timings: Timings };

/// The leaf circuit (finalized, unpadded, with values) for the header-chain segment `headers`
/// (`2^log_size` rows) starting from `start`.
pub const SegmentLeaf = struct {
    ctx: Context(QM31),
    pubs: [N_PUB]M31,
    timings: Timings,

    /// The leaf's sizes padded to powers of two: a lower bound for the shared target.
    pub fn paddedSizes(self: *const SegmentLeaf) ComponentSizes {
        return finalize.computePaddedSizes(.fromBuilder(&self.ctx.circuit));
    }
};

pub fn buildSegmentLeaf(gpa: std.mem.Allocator, a: std.mem.Allocator, log_size: u32, headers: []const H.Header, start: H.ChainStart) !SegmentLeaf {
    const prove_base = @import("../air/prove.zig");
    const prove_rec = @import("../air/prove_rec.zig");
    var timer = try std.time.Timer.start();
    const air = (try ir.Air.parseJson(a, H.lean_json)).value;
    const wit = try H.generateFrom(a, log_size, headers, start);
    const cfg = try prove_rec.config(log_size);
    const digest = try air.digest(a);
    const statement = prove_base.AirStatement{ .log_size = log_size, .digest = digest, .pubs = &wit.pubs, .air = &air, .allocator = a };
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    // Proved twice: the capture consumes one copy (see plain_verifier tests).
    const proof_a = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    const proof_b = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try prove_rec.verifyCapture(a, cfg, air, log_size, &wit.pubs, proof_a, &capture);
    const config = try pv.PlainConfig.single(log_size, cfg.fri_config, air.n_preprocessed, try pv.mainOffsets(a, air), a);
    const pre_root: [32]u8 = std.mem.toBytes(try prove_rec.preprocessedRoot(a, cfg, air, log_size));
    const values = try pv.fromCapture(a, prove_rec.Hasher, &proof_b, &capture, config, &.{});
    var t: Timings = .{};
    t.segment_ns = timer.lap();
    const ctx = try buildLeafCircuit(gpa, &values, config, &air, digest, pre_root, &wit.pubs);
    t.n_vars = ctx.circuit.n_vars;
    t.build_ns = timer.lap();
    return .{ .ctx = ctx, .pubs = wit.pubs, .timings = t };
}

/// Proves a segment leaf (consumed) padded to `target` under `fri`, and verifies it natively.
pub fn proveSegmentLeaf(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const Tables, sl: *SegmentLeaf, target: ?ComponentSizes, fri: FriConfigV2) !Leaf {
    defer sl.ctx.deinit();
    var t = sl.timings;
    var timer = try std.time.Timer.start();
    var cp = try proveCircuit(gpa, a, &sl.ctx, target, fri);
    errdefer cp.deinit();
    t.prove_ns = timer.lap();
    const out = try verifyCircuit(gpa, tables, &cp);
    t.verify_ns = timer.lap();
    if (!std.mem.eql(u32, &out, &pubsDigest(zero_key, &sl.pubs))) return error.LeafDigestMismatch;
    return .{ .proof = cp, .pubs = sl.pubs, .timings = t };
}

/// `buildSegmentLeaf` then `proveSegmentLeaf`.
pub fn wrapSegment(
    gpa: std.mem.Allocator,
    a: std.mem.Allocator,
    tables: *const Tables,
    log_size: u32,
    headers: []const H.Header,
    start: H.ChainStart,
    target: ?ComponentSizes,
    fri: FriConfigV2,
) !Leaf {
    var sl = try buildSegmentLeaf(gpa, a, log_size, headers, start);
    return proveSegmentLeaf(gpa, a, tables, &sl, target, fri);
}

/// The identity (preprocessed root, circuit hash) of the leaf circuit for `2^log_size`-row
/// segments, padded to `target`, derived by the verifier from public data alone: the circuit is
/// built for the first segment from genesis (`genesis_headers`), and its topology does not
/// depend on the segment (tested in node.zig). No prover input is used.
pub fn leafIdentity(gpa: std.mem.Allocator, log_size: u32, genesis_headers: []const H.Header, target: ComponentSizes, log_blowup: u32) !struct { root: [8]u32, hash: [8]u32 } {
    var tmp = std.heap.ArenaAllocator.init(gpa);
    defer tmp.deinit();
    const n = @as(usize, 1) << @intCast(log_size - 8);
    var sl = try buildSegmentLeaf(gpa, tmp.allocator(), log_size, genesis_headers[0..n], H.genesis_start);
    defer sl.ctx.deinit();
    try finalize.padToTargets(QM31, &sl.ctx, target);
    var pp = try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, &sl.ctx);
    defer pp.deinit(gpa);
    const id = try circuit_cpu.recursion.circuit_params.identity(gpa, &pp, log_blowup);
    return .{ .root = core.vcs.blake2_hash.digestToU32s(id.preprocessed_root), .hash = core.vcs.blake2_hash.digestToU32s(id.circuit_hash) };
}

test "a header-chain segment proof is wrapped into a verified leaf proof" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const tables = try Tables.init(gpa);
    defer tables.deinit(gpa);
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    // Test-strength FRI for speed here (3 queries); production uses 70 queries / 26 bits.
    const fri = try FriConfigV2.init(10, 0, 1, 3, 1);
    var leaf = try wrapSegment(gpa, a, tables, 12, headers, H.genesis_start, null, fri);
    defer leaf.proof.deinit();
    try std.testing.expectEqualSlices(u32, &pubsDigest(zero_key, &leaf.pubs), &leaf.proof.request.output_digest);

    // A claimed digest for other public inputs is rejected.
    var forged = leaf.proof;
    forged.request.output_digest[0] ^= 1;
    try std.testing.expectError(error.CircuitProofRejected, verifyCircuit(gpa, tables, &forged));
}
