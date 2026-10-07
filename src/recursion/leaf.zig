//! The leaf of the recursion tree (roadmap REC-LEAF): a header-chain segment proof, verified by
//! the plain in-circuit verifier (`plain_verifier.zig`), and that circuit's execution proved by
//! stwo-zig's circuit prover. The leaf's public output is Blake2s of the segment's public inputs
//! (as 32-bit words), so an aggregator can link segments by recomputing it.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const ir = @import("../air/ir.zig");
const pv = @import("plain_verifier.zig");

const builder = circuit.builder;
const preprocessed = circuit.common.preprocessed;
const component_list = circuit.common.component_list;
const Var = builder.Var;
const Context = builder.Context;
const U32Wrapper = builder.wrappers.U32Wrapper;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

pub const bundle_bytes = @embedFile("circuit:air_programs");
pub const constraints_bytes = @embedFile("circuit:compiled_constraints");

/// Blake2s of the public inputs as little-endian 32-bit words: the leaf's output digest.
pub fn outputDigest(pubs: []const M31) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    for (pubs) |p| {
        var b: [4]u8 = undefined;
        std.mem.writeInt(u32, &b, p.toU32(), .little);
        h.update(&b);
    }
    var d: [32]u8 = undefined;
    h.final(&d);
    var out: [8]u32 = undefined;
    for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return out;
}

/// The finalized leaf circuit, with values: verifies `values` against the AIR and outputs
/// `outputDigest(pubs)`.
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
    for (pub_vars, pubs) |*w, v| w.* = try ctx.guess(QM31.fromBase(v));
    const st = pv.PlainStatement{ .air = air, .digest = digest, .preprocessed_root = pre_root, .pubs = pub_vars };
    try pv.verifyPlain(QM31, &ctx, &proof_vars, config, &st);

    const words = try ctx.scratch().alloc(U32Wrapper(Var), pubs.len);
    for (words, pub_vars) |*w, v| w.* = try builder.blake.m31ToU32(QM31, &ctx, v);
    const hash = try builder.blake.blake2sU32s(QM31, &ctx, words, 4 * words.len);
    var outputs: [8]Var = undefined;
    for (&outputs, hash.words) |*o, w| o.* = w.get();
    try ctx.setOutputs(&outputs);
    try ctx.finalize(false);
    return ctx;
}

pub const LeafProof = struct {
    bytes: []u8,
    request: circuit_cpu.verify.Request,
};

/// Proves a finalized leaf circuit (it must be satisfied) under `pcs`-style FRI parameters.
pub fn proveLeaf(
    gpa: std.mem.Allocator,
    a: std.mem.Allocator,
    ctx: *Context(QM31),
    fri: core.pcs.config_v2.FriConfigV2,
) !LeafProof {
    if (!try ctx.isCircuitValid()) return error.CircuitRejectsProof;
    var pp = try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, ctx);
    defer pp.deinit(gpa);
    var bundle = try circuit_cpu.air.parse(gpa, bundle_bytes);
    defer bundle.deinit();
    const pcs = core.pcs.config_v2.PcsConfigV2.fromFriAndTraceSize(fri, pp.traceLogSize());
    var proof = try circuit_cpu.Internal.prove(gpa, ctx.values(), &pp, &bundle, pcs, .{}, {});
    defer proof.deinit();
    var converted = try circuit_cpu.verifier_proof.prepare(gpa, &proof);
    defer converted.deinit();

    const layout = pp.layout();
    const columns = try a.alloc(@typeInfo(@TypeOf(@as(circuit_cpu.verify.Request, undefined).preprocessed_column_log_sizes)).pointer.child, layout.entries.len);
    for (layout.entries, columns) |entry, *c| c.* = .{ .id = try a.dupe(u8, entry.id), .log_size = entry.log_size };
    var digest: [8]u32 = undefined;
    for (proof.output_values, &digest) |value, *w| {
        const limbs = value.toM31Array();
        w.* = limbs[0].toU32() | (limbs[1].toU32() << 16);
    }
    return .{
        .bytes = try converted.serialize(a),
        .request = .{
            .pcs_config = proof.pcs_config,
            .preprocessed_column_log_sizes = columns,
            .preprocessed_root = core.vcs.blake2_hash.digestToU32s(proof.stark_proof.proof.commitment_scheme_proof.commitments.items[0]),
            .output_digest = digest,
        },
    };
}

/// Natively verifies a leaf proof (stwo-zig's circuit verifier) and returns the leaf's output
/// digest, `request.output_digest`, which acceptance binds to the proof. (`verifyProofBytes`
/// itself returns the verifier circuit's output, Blake2s(statement root ‖ output digest).)
pub fn verifyLeaf(gpa: std.mem.Allocator, leaf: *const LeafProof) ![8]u32 {
    var projection = try circuit.air_eval.projection.parse(gpa, constraints_bytes);
    defer projection.deinit();
    var table = try circuit.air_eval.circuit_components.build(gpa, &projection);
    defer table.deinit();
    const verdict = try circuit_cpu.verify.verifyProofBytes(gpa, &table, &leaf.request, leaf.bytes);
    return switch (verdict) {
        .accepted => leaf.request.output_digest,
        .rejected => |r| {
            std.debug.print("leaf rejected at {s}: {s}\n", .{ @tagName(r.stage), @errorName(r.reason) });
            return error.LeafRejected;
        },
    };
}

test "a header-chain segment proof is wrapped into a verified leaf proof" {
    const H = @import("../btc/header_chain.zig");
    const prove_base = @import("../air/prove.zig");
    const prove_rec = @import("../air/prove_rec.zig");
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
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
    const proof_a = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    const proof_b = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try prove_rec.verifyCapture(a, cfg, air, log_size, &wit.pubs, proof_a, &capture);
    const config = pv.PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .n_preprocessed = air.n_preprocessed, .main_offsets = try pv.mainOffsets(a, air) };
    const pre_root: [32]u8 = std.mem.toBytes(try prove_rec.preprocessedRoot(a, cfg, air, log_size));
    const values = try pv.fromCapture(a, prove_rec.Hasher, &proof_b, &capture, config);

    var ctx = try buildLeafCircuit(gpa, &values, config, &air, digest, pre_root, &wit.pubs);
    defer ctx.deinit();
    std.debug.print("leaf circuit: {d} vars\n", .{ctx.circuit.n_vars});
    // Test-strength FRI for speed here (3 queries); production uses 70 queries / 26 bits.
    const fri = try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1);
    const leaf = try proveLeaf(gpa, a, &ctx, fri);
    const out = try verifyLeaf(gpa, &leaf);
    try std.testing.expectEqualSlices(u32, &outputDigest(&wit.pubs), &out);

    // A claimed digest for other public inputs is rejected.
    var forged = leaf;
    forged.request.output_digest[0] ^= 1;
    try std.testing.expectError(error.LeafRejected, verifyLeaf(gpa, &forged));
}
