//! The epoch join (docs/design/block-rec.md § The epoch join): epochs chained into one running proof.
//! The glue is the Lean program `epochJoin v` (`Circuit/EpochJoin.lean`, exported as
//! `airs/epoch_join_<variant>.json`): the left child (an epoch root in the `base` variants, a join in
//! `step`) and the right child (an epoch root from a previous set) verified at its hooks, their output
//! digests recomputed from their openings, the links (heights, the shared set digest), and the output:
//! the key, the start and end sets, the range and `acc`, a running hash over the epoch roots' outputs.
//!
//! Epoch roots are proved at one fixed size (the chain's root shape) so a join verifies any of them;
//! a join's left child is a join of its own shape (a fixpoint, as the tree's nodes).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const leaf = @import("leaf.zig");
const glue = @import("glue.zig");
const ER = @import("epoch_root.zig");

const builder = circuit.builder;
const component_list = circuit.common.component_list;
const multiverifier = circuit.statements.multiverifier;
const circuit_statement = circuit.statements.circuit_statement;
const stark_proof = circuit.stark_verifier.proof;
const verify_mod = circuit.stark_verifier.verify;
const Var = builder.Var;
const Context = builder.Context;
const NoValue = builder.NoValue;
const HashValue = builder.blake.HashValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Key = leaf.Key;

pub const Variant = enum { base_prev, base_genesis, step };

pub fn programJson(v: Variant) ![]const u8 {
    return switch (v) {
        .base_prev => @embedFile("air:epoch_join_base_prev"),
        .base_genesis => @embedFile("air:epoch_join_base_genesis"),
        .step => @embedFile("air:epoch_join_step"),
    };
}

/// External values per child (`EXT` in Lean).
pub const EXT = 42;

/// What a join reads of an epoch root: its fixed part (the key, both set digests, the range) and
/// `rest` (`epoch_root.restOf`).
pub const RootOpen = struct { key: Key, ep: ER.Epoch, rest: [8]u32 };

/// What a join reads of a join: its key, start and end sets, range and `acc`.
pub const JoinOpen = struct { key: Key, start: [8]u32, end: [8]u32, a: u32, b: u32, acc: [8]u32 };

pub const Open = union(enum) { root: RootOpen, join: JoinOpen };

/// The output digest of a join opening (the Lean program's message): key ‖ start ‖ end ‖ a ‖ b ‖ acc.
pub fn joinOut(o: *const JoinOpen) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    const put = struct {
        fn f(hh: *std.crypto.hash.blake2.Blake2s256, bb: *[4]u8, w: u32) void {
            std.mem.writeInt(u32, bb, w, .little);
            hh.update(bb);
        }
    }.f;
    for (o.key) |w| put(&h, &b, w);
    for (o.start) |w| put(&h, &b, w);
    for (o.end) |w| put(&h, &b, w);
    put(&h, &b, o.a);
    put(&h, &b, o.b);
    for (o.acc) |w| put(&h, &b, w);
    var d: [32]u8 = undefined;
    h.final(&d);
    return ER.digestWords(d);
}

fn hash2(x: [8]u32, y: [8]u32) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    for (x ++ y) |w| {
        std.mem.writeInt(u32, &b, w, .little);
        h.update(&b);
    }
    var d: [32]u8 = undefined;
    h.final(&d);
    return ER.digestWords(d);
}

/// The output of a child opening: an epoch root's digest or a join's.
pub fn outOf(o: *const Open) [8]u32 {
    return switch (o.*) {
        .root => |r| ER.outOf(r.key, r.ep, r.rest),
        .join => |j| joinOut(&j),
    };
}

/// The native view of a join over `left` (circuit hash `lh`) and `right` (an epoch root from a previous
/// set, circuit hash `rh`): checks the links and returns the join's opening (its digest is `joinOut`).
pub fn expected(left: *const Open, lh: [8]u32, right: *const RootOpen, rh: [8]u32) !JoinOpen {
    const rprev = right.ep.prev orelse return error.RightFromGenesis;
    const l_end: [8]u32, const l_b: u32, const l_a: u32, const l_start: [8]u32, const l_key: Key = switch (left.*) {
        .root => |r| .{ ER.digestWords(r.ep.fin), r.ep.to, r.ep.from, if (r.ep.prev) |p| ER.digestWords(p) else @splat(0), r.key },
        .join => |j| .{ j.end, j.b, j.a, j.start, j.key },
    };
    if (!std.mem.eql(u32, &l_end, &ER.digestWords(rprev))) return error.SetsDoNotLink;
    if (right.ep.from != l_b + 1) return error.HeightsDoNotLink;
    if (right.ep.to >= 1 << 30) return error.RangeTooLarge;
    const r_out = ER.outOf(right.key, right.ep, right.rest);
    const acc = switch (left.*) {
        .root => hash2(outOf(left), r_out),
        .join => |j| hash2(j.acc, r_out),
    };
    const key = @import("block_node_k.zig").key(&.{ lh, rh }, &.{ l_key, right.key });
    return .{ .key = key, .start = l_start, .end = ER.digestWords(right.ep.fin), .a = l_a, .b = right.ep.to, .acc = acc };
}

/// A child for the circuit: its verifier proof (values), preprocessed root, the shared configuration
/// its proofs verify under, and its opening.
pub fn ChildIn(comptime V: type) type {
    return struct {
        proof: *const stark_proof.Proof(V),
        preprocessed_root: [8]u32,
        shared: *const multiverifier.SharedConfig,
        open: Open,
    };
}

/// The verifier at hook `i` with child `i`'s own configuration (a join's children differ in shape).
pub fn Hook(comptime V: type) type {
    return struct {
        ctx: *Context(V),
        table: *const circuit.air_eval.component_table.Table,
        proofs: []const *const stark_proof.Proof(V),
        shareds: []const *const multiverifier.SharedConfig,

        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            if (id >= self.proofs.len or args.len != 16) return error.GlueHookArity;
            const shared = self.shareds[id];
            const config: circuit_statement.CircuitConfig = .{
                .config = shared.pcs_config,
                .preprocessed_column_log_sizes = shared.preprocessed_column_log_sizes,
            };
            var root: HashValue(Var) = undefined;
            var digest: HashValue(Var) = undefined;
            for (&root.words, args[0..8]) |*w, v| w.* = .newUnsafe(v);
            for (&digest.words, args[8..16]) |*w, v| w.* = .newUnsafe(v);
            const statement = try circuit_statement.CircuitStatement(V).init(self.ctx, self.table, &config, root, digest);
            const proof_vars = try stark_proof.guess(V, self.ctx, self.proofs[id]);
            try verify_mod.verify(V, self.ctx, &proof_vars, shared.proof_config, &statement, verify_mod.NoStages{});
            const out = try self.ctx.scratch().alloc(Var, 8);
            for (out, statement.circuit_hash.words) |*o, w| o.* = w.get();
            return out;
        }
    };
}

fn putWords(comptime V: type, ext: []V, at: usize, ws: [8]u32) void {
    if (V != QM31) return;
    const hv = builder.blake.hashValue(QM31, ws);
    for (hv.words, 0..) |w, k| ext[at + k] = w.get();
}

fn putM31(comptime V: type, ext: []V, at: usize, x: u32) void {
    if (V != QM31) return;
    ext[at] = QM31.fromBase(M31.fromCanonical(x));
}

/// The join circuit (finalized, unpadded) over `left` and `right`.
pub fn buildCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, v: Variant, left: ChildIn(V), right: ChildIn(V)) !Context(V) {
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), try programJson(v));
    const ext = try ctx.scratch().alloc(V, 2 * EXT);
    if (V != QM31) @memset(ext, .{});
    for ([_]ChildIn(V){ left, right }, 0..) |c, i| {
        const e = EXT * i;
        switch (c.open) {
            .root => |r| {
                putWords(V, ext, e, r.key);
                putWords(V, ext, e + 8, ER.digestWords(r.ep.fin));
                putWords(V, ext, e + 16, if (r.ep.prev) |p| ER.digestWords(p) else @splat(0));
                putM31(V, ext, e + 24, r.ep.from);
                putM31(V, ext, e + 25, r.ep.to);
                putWords(V, ext, e + 26, r.rest);
            },
            .join => |j| {
                putWords(V, ext, e, j.key);
                putWords(V, ext, e + 8, j.start);
                putWords(V, ext, e + 16, j.end);
                putM31(V, ext, e + 24, j.a);
                putM31(V, ext, e + 25, j.b);
                putWords(V, ext, e + 26, j.acc);
            },
        }
        putWords(V, ext, e + 34, c.preprocessed_root);
    }
    const proofs = [_]*const stark_proof.Proof(V){ left.proof, right.proof };
    const shareds = [_]*const multiverifier.SharedConfig{ left.shared, right.shared };
    try glue.runOutputs(V, &ctx, &prog, ext, Hook(V){ .ctx = &ctx, .table = table, .proofs = &proofs, .shareds = &shareds });
    return ctx;
}

const circuit_cpu = @import("stwo_circuit_cpu_integration");
const wk = @import("block_node_k.zig");

/// A proved child as the join circuit takes it: its verifier values (allocated in `a`).
pub fn childOf(a: std.mem.Allocator, cp: *const leaf.CircuitProof, shared: *const multiverifier.SharedConfig, open: Open) !ChildIn(QM31) {
    const v = try a.create(stark_proof.Proof(QM31));
    v.* = try circuit_cpu.verifier_proof.circuitVerifierValues(a, &cp.prepared.proof, cp.prepared.config);
    return .{ .proof = v, .preprocessed_root = cp.request.preprocessed_root, .shared = shared, .open = open };
}

/// Builds the join over `left` (circuit hash `lh`) and `right` (an epoch root, circuit hash `rh`), checks
/// it is satisfied with the native digest, and proves it (CPU) padded to `target` when `prove`.
pub fn proveJoin(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, v: Variant, left: ChildIn(QM31), lh: [8]u32, right: ChildIn(QM31), rh: [8]u32, fri: core.pcs.config_v2.FriConfigV2, target: ?circuit.common.finalize.ComponentSizes, prove: bool) !struct { open: JoinOpen, n_vars: usize, proof: ?leaf.CircuitProof } {
    const want = try expected(&left.open, lh, &right.open.root, rh);
    var ctx = try buildCircuit(QM31, gpa, &tables.table, v, left, right);
    defer ctx.deinit();
    if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
    const out = wk.outputDigest(&ctx);
    if (!std.mem.eql(u32, &out, &joinOut(&want))) return error.JoinDigestMismatch;
    const n_vars = ctx.circuit.n_vars;
    if (!prove) return .{ .open = want, .n_vars = n_vars, .proof = null };
    var cp = try leaf.proveCircuit(gpa, a, &ctx, target, fri);
    errdefer cp.deinit();
    const got = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &got, &joinOut(&want))) return error.JoinDigestMismatch;
    return .{ .open = want, .n_vars = n_vars, .proof = cp };
}

/// The verifier configuration for children padded to `target` (a chain's root shape, or the join shape).
pub fn sharedFor(gpa: std.mem.Allocator, target: circuit.common.finalize.ComponentSizes, fri: core.pcs.config_v2.FriConfigV2) !multiverifier.SharedConfig {
    return multiverifier.foldSharedConfig(gpa, target, fri);
}
