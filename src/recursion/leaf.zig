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
const HT = @import("../btc/header_tree.zig");
const glue = @import("glue.zig");

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

/// A leaf's public inputs: the header chain's 108, then the segment's tree root `T` (16 limbs).
pub const T_BASE = H.N_PUB;
pub const N_PUB = H.N_PUB + 16;
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

/// The hand-written leaf circuit the glue program replaced; kept as the parity reference.
pub fn buildLeafCircuitRef(
    gpa: std.mem.Allocator,
    values: *const pv.PlainProof(QM31),
    config: pv.PlainConfig,
    airs: [2]*const ir.Air,
    digests: [2][32]u8,
    pre_root: [32]u8,
    k: u32,
    pubs: []const M31,
) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const proof_vars = try pv.guess(QM31, &ctx, values);
    const pub_vars = try ctx.scratch().alloc(Var, pubs.len);
    for (pub_vars, pubs) |*w, v| w.* = try ctx.guessM31(QM31.fromBase(v));
    const entry_vals = try ctx.scratch().alloc(Var, 18);
    entry_vals[0] = try ctx.constant(QM31.fromBase(M31.fromCanonical(k)));
    entry_vals[1] = ctx.zero();
    @memcpy(entry_vals[2..], pub_vars[T_BASE..]);
    const st = pv.PlainStatement{
        .parts = &.{ .{ .air = airs[0], .digest = digests[0], .pubs = pub_vars[0..T_BASE] }, .{ .air = airs[1], .digest = digests[1], .pubs = &.{} } },
        .preprocessed_root = pre_root,
        .ext = &.{.{ .rel = HT.REL_NODE, .vals = entry_vals, .mult = M31.zero().sub(M31.one()) }},
    };
    try pv.verifyPlain(QM31, &ctx, &proof_vars, config, &st);
    var key: [8]U32Wrapper(Var) = undefined;
    for (&key) |*kk| kk.* = try builder.wrappers.constU32(QM31, &ctx, 0);
    try finish(QM31, &ctx, try pubsDigestVars(QM31, &ctx, key, pub_vars));
    return ctx;
}

/// The finalized (unpadded) leaf circuit: verifies the (headers, tree) system proof `values` whose
/// relations balance with the public entry `node(k, 0, T)`, and outputs `pubsDigest(0, pubs)`
/// (`pubs` = the header chain's public inputs, then `T`'s limbs). The Lean-defined glue program
/// (`leafProgram`, Circuit/Gadgets.lean) with the verifier at its hooks.
pub fn buildLeafCircuit(
    gpa: std.mem.Allocator,
    values: *const pv.PlainProof(QM31),
    config: pv.PlainConfig,
    airs: [2]*const ir.Air,
    digests: [2][32]u8,
    pre_root: [32]u8,
    k: u32,
    pubs: []const M31,
) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), glue.leaf_json);
    // The composition check: the Lean program (Circuit/CompositionLogUp.lean, proven in
    // CompositionSound.lean); the reference builder keeps the hand-written one.
    const comp = try glue.parse(ctx.scratch(), @embedFile("air:composition_leaf"));
    const bal = try glue.parse(ctx.scratch(), @embedFile("air:balance_leaf"));
    const stm = try glue.parse(ctx.scratch(), @embedFile("air:statement_leaf"));
    var lh: [4]glue.Program = undefined;
    lh[0] = try glue.parse(ctx.scratch(), @embedFile("air:leafhash_104"));
    lh[1] = try glue.parse(ctx.scratch(), @embedFile("air:leafhash_434"));
    lh[2] = try glue.parse(ctx.scratch(), @embedFile("air:leafhash_12"));
    lh[3] = try glue.parse(ctx.scratch(), @embedFile("air:leafhash_8"));
    const lhp = [4]*const glue.Program{ &lh[0], &lh[1], &lh[2], &lh[3] };
    const deep = try pv.DeepTable.parse(ctx.scratch(), @embedFile("air:deep_leaf"));
    const shifts = try pv.ShiftTable.parse(ctx.scratch(), @embedFile("air:oods_shift_leaf"));
    const mnode = try glue.parse(ctx.scratch(), @embedFile("air:merkle_node"));
    // The channel operations (Circuit/Channel.lean), at the sizes the leaf uses.
    var chp: [9]glue.Program = undefined;
    inline for (.{ "mix_u32s_1", "mix_u32s_8", "mix_u32s_10", "mix_qm31s_2", "mix_qm31s_3757", "draw", "draw_qm31", "draw_point", "pow_mix" }, 0..) |name, i|
        chp[i] = try glue.parse(ctx.scratch(), @embedFile("air:channel_" ++ name));
    const chu = [3]*const glue.Program{ &chp[0], &chp[1], &chp[2] };
    const chq = [2]*const glue.Program{ &chp[3], &chp[4] };
    const transcript = try pv.parseTranscript(ctx.scratch(), @embedFile("air:transcript_lookups"));
    // The proof-of-work check (Circuit/Pow.lean), at the grinding bits we use.
    var pwp: [2]glue.Program = undefined;
    inline for (.{ "0", "26" }, 0..) |name, i|
        pwp[i] = try glue.parse(ctx.scratch(), @embedFile("air:channel_pow_check_" ++ name));
    const pw = [2]pv.PowCheck{ .{ .n_bits = 0, .prog = &pwp[0] }, .{ .n_bits = 26, .prog = &pwp[1] } };
    const channel = pv.ChannelProgs{ .mix_u32s = &chu, .mix_qm31s = &chq, .draw = &chp[5], .draw_qm31 = &chp[6], .draw_point = &chp[7], .pow_mix = &chp[8], .pow_check = &pw };
    const ext = try ctx.scratch().alloc(QM31, pubs.len);
    for (ext, pubs) |*e, v| e.* = QM31.fromBase(v);
    const Hooks = struct {
        ctx: *Context(QM31),
        values: *const pv.PlainProof(QM31),
        config: pv.PlainConfig,
        airs: [2]*const ir.Air,
        digests: [2][32]u8,
        pre_root: [32]u8,
        k: u32,
        proof_vars: *pv.PlainProof(Var),
        comp: *const glue.Program,
        bal: *const glue.Program,
        stm: *const glue.Program,
        lh: []const *const glue.Program,
        deep: *const pv.DeepTable,
        shifts: *const pv.ShiftTable,
        mnode: *const glue.Program,
        channel: *const pv.ChannelProgs,
        transcript: []const []const u8,
        /// 0: guess the proof; 1: verify it, with the public entry `node(k, 0, pubs[T_BASE..])`.
        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            if (id == 0) {
                self.proof_vars.* = try pv.guess(QM31, self.ctx, self.values);
                return &.{};
            }
            const entry_vals = try self.ctx.scratch().alloc(Var, 18);
            entry_vals[0] = try self.ctx.constant(QM31.fromBase(M31.fromCanonical(self.k)));
            entry_vals[1] = self.ctx.zero();
            @memcpy(entry_vals[2..], args[T_BASE..]);
            const st = pv.PlainStatement{
                .parts = &.{ .{ .air = self.airs[0], .digest = self.digests[0], .pubs = args[0..T_BASE] }, .{ .air = self.airs[1], .digest = self.digests[1], .pubs = &.{} } },
                .preprocessed_root = self.pre_root,
                .ext = &.{.{ .rel = HT.REL_NODE, .vals = entry_vals, .mult = M31.zero().sub(M31.one()) }},
                .composition = self.comp,
                .balance = self.bal,
                .statement = self.stm,
                .leaf_hashes = self.lh,
                .deep = self.deep,
                .shifts = self.shifts,
                .merkle_node = self.mnode,
                .channel = self.channel.*,
                .transcript = self.transcript,
            };
            try pv.verifyPlain(QM31, self.ctx, self.proof_vars, self.config, &st);
            return &.{};
        }
    };
    var proof_vars: pv.PlainProof(Var) = undefined;
    try glue.runOutputs(QM31, &ctx, &prog, ext, Hooks{ .ctx = &ctx, .values = values, .config = config, .airs = airs, .digests = digests, .pre_root = pre_root, .k = k, .proof_vars = &proof_vars, .comp = &comp, .bal = &bal, .stm = &stm, .lh = &lhp, .deep = &deep, .shifts = &shifts, .mnode = &mnode, .channel = &channel, .transcript = transcript });
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

/// A preprocessed column of a verify request: its id and log size.
pub const Column = @typeInfo(@FieldType(circuit_cpu.verify.Request, "preprocessed_column_log_sizes")).pointer.child;

/// A circuit's preprocessed columns, as a verify request lists them (allocated in `a`).
pub fn requestColumns(a: std.mem.Allocator, pp: *const preprocessed.PreprocessedCircuit) ![]Column {
    const layout = pp.layout();
    const columns = try a.alloc(Column, layout.entries.len);
    for (layout.entries, columns) |entry, *c| c.* = .{ .id = try a.dupe(u8, entry.id), .log_size = entry.log_size };
    return columns;
}

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

    const columns = try requestColumns(a, &pp);
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
    return buildSegmentLeafWith(gpa, a, log_size, headers, start, false);
}

/// `reference`: build the circuit with the hand-written builder (glue parity test).
fn buildSegmentLeafWith(gpa: std.mem.Allocator, a: std.mem.Allocator, log_size: u32, headers: []const H.Header, start: H.ChainStart, comptime reference: bool) !SegmentLeaf {
    const system = @import("../air/system.zig");
    const prove_rec = @import("../air/prove_rec.zig");
    var timer = try std.time.Timer.start();
    const hair = (try ir.Air.parseJson(a, HT.header_json)).value;
    const tair = (try ir.Air.parseJson(a, HT.tree_json)).value;
    const hw = try H.generateFrom(a, log_size, headers, start);
    const tw = try HT.generate(a, log_size, hw);
    const k: u32 = log_size - 8;
    const parts = [_]system.Part{ .{ .air = &hair, .log_size = log_size, .pubs = &hw.pubs }, .{ .air = &tair, .log_size = log_size } };
    const mains = [_][]const []const M31{ @ptrCast(tw.header_main), @ptrCast(tw.tree_main) };
    const ext = [_]system.PubEntry{try HT.rootEntry(a, k, tw.root)};
    const cfg = try prove_rec.config(log_size);
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    // One proof: verified natively with a borrowed capture (it stays intact), then converted.
    const proof_b = try system.prove(E, a, cfg, &parts, &mains);
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &parts, &ext, &proof_b, &capture);
    const config = pv.PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .system = true, .parts = &.{
        .{ .n_preprocessed = hair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, hair), .n_inter = 4 },
        .{ .n_preprocessed = tair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, tair), .n_inter = 8 },
    } };
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    const values = try pv.fromCapture(a, prove_rec.Hasher, &proof_b.stark, &capture, config, proof_b.claimed_sums);
    var pubs: [N_PUB]M31 = undefined;
    @memcpy(pubs[0..T_BASE], &hw.pubs);
    @memcpy(pubs[T_BASE..], &HT.limbs(tw.root));
    var t: Timings = .{};
    t.segment_ns = timer.lap();
    const ctx = try (if (reference) buildLeafCircuitRef else buildLeafCircuit)(gpa, &values, config, .{ &hair, &tair }, .{ try hair.digest(a), try tair.digest(a) }, pre_root, k, &pubs);
    t.n_vars = ctx.circuit.n_vars;
    t.build_ns = timer.lap();
    return .{ .ctx = ctx, .pubs = pubs, .timings = t };
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

test "the leaf circuit's identity is the pinned mainnet VK's (segment log 9)" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const store = @import("store.zig");
    const vk = try store.Vk.decode(a, @embedFile("vk:mainnet_test"));
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_1024"));
    const id = try leafIdentity(gpa, 9, headers, vk.target, vk.fri.log_blowup_factor);
    const want = vk.leafId(9);
    try std.testing.expectEqualSlices(u32, &want.root, &id.root);
    try std.testing.expectEqualSlices(u32, &want.hash, &id.hash);
}

test "glue parity: the replayed leaf circuit equals the hand-written one" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    var new = try buildSegmentLeafWith(gpa, a, 12, headers, H.genesis_start, false);
    defer new.ctx.deinit();
    var ref = try buildSegmentLeafWith(gpa, a, 12, headers, H.genesis_start, true);
    defer ref.ctx.deinit();
    try glue.expectSameCircuit(&ref.ctx.circuit, &new.ctx.circuit);
    try std.testing.expectEqualSlices(QM31, ref.ctx.values(), new.ctx.values());
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
