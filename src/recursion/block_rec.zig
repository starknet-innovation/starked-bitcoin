//! BLOCK-REC: the block-proof aggregation tree (docs/design/block-rec.md, D-043 proposed).
//!
//! A **block leaf** verifies a block proof (the 15-component block system) with the plain verifier,
//! runs the leaf's own checks (`Circuit/BlockLeaf.lean`: `αₖ = α₁ᵏ`, the BIP30 flag; the seed leaf),
//! and outputs the digest of its range summary (51 limbs, `Circuit/BlockNode.lean`): height, count 1,
//! partial sum, input count, `(γ, z, α)`, the block hash (a leaf of the header tree) and the seed
//! leaf `Blake2s(hash ‖ C_h)`. A **block node** verifies two child circuit proofs in-circuit and runs
//! the Lean node glue (`blockNodeProgram`, `node_sound`): adjacent equal-size ranges with one
//! challenge, sums added, both roots folded. Leaves and nodes are padded to one shared shape, as in
//! the header-chain tree (`node.zig`).
//!
//! Not yet: the outer verifier (aligned forest against the seed v3 and the chain's `T`), the
//! previous-block MTP (D-043 option A).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const leaf = @import("leaf.zig");
const pv = @import("plain_verifier.zig");
const glue = @import("glue.zig");
const bl = @import("block_leaf.zig");
const HT = @import("../btc/header_tree.zig");
const ir = @import("../air/ir.zig");
const system = @import("../air/system.zig");
const rec = @import("../air/prove_rec.zig");
const bs = @import("../block/system.zig");
const coin = @import("../block/coin.zig");
const PF = @import("../block/proof_file.zig");

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
const Key = leaf.Key;

pub const NS = 51;
pub const Summary = [NS]M31;

const HR = 19;
const SR = 35;

fn wordsAt(s: []const M31, at: usize) HT.Words {
    var w: HT.Words = undefined;
    for (&w, 0..) |*x, i| x.* = s[at + 2 * i].toU32() | (s[at + 2 * i + 1].toU32() << 16);
    return w;
}

/// A block's summary from its public inputs (what the leaf circuit outputs).
pub fn leafSummary(pubs: *const [bs.N_PUB]M31) Summary {
    var s: Summary = undefined;
    s[0] = pubs[2];
    s[1] = M31.one();
    @memcpy(s[2..6], pubs[coin.PUB_S..][0..4]);
    s[6] = pubs[coin.PUB_NIN];
    @memcpy(s[7..15], pubs[coin.PUB_G..][0..8]);
    @memcpy(s[15..19], pubs[coin.PUB_ALPHA + 4 ..][0..4]);
    @memcpy(s[HR..][0..16], pubs[bs.PUB_HASH..][0..16]);
    @memcpy(s[SR..][0..16], &HT.limbs(HT.node(wordsAt(pubs, bs.PUB_HASH), wordsAt(pubs, 9))));
    return s;
}

/// Two adjacent ranges' summary (what the node circuit outputs).
pub fn joinSummary(l: Summary, r: Summary) Summary {
    var s: Summary = undefined;
    s[0] = l[0];
    s[1] = l[1].add(l[1]);
    for (2..7) |i| s[i] = l[i].add(r[i]);
    @memcpy(s[7..19], l[7..19]);
    @memcpy(s[HR..][0..16], &HT.limbs(HT.node(wordsAt(&l, HR), wordsAt(&r, HR))));
    @memcpy(s[SR..][0..16], &HT.limbs(HT.node(wordsAt(&l, SR), wordsAt(&r, SR))));
    return s;
}

const InputHooks = struct {
    inputs: []const Var,
    pub fn call(self: @This(), id: u32, _: []const Var) ![]const Var {
        return if (id == 0) self.inputs else error.UnknownHook;
    }
};

/// The block leaf circuit (finalized, unpadded) over a block proof's plain values.
pub fn buildLeafCircuit(gpa: std.mem.Allocator, values: *const pv.PlainProof(QM31), config: pv.PlainConfig, airs: *const [bs.N_COMP]ir.Air, digests: *const [bs.N_COMP][32]u8, pre_root: [32]u8, pubs: *const [bs.N_PUB]M31) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const g = try pv.guess(QM31, &ctx, values);
    var pub_vars: [bs.N_PUB]Var = undefined;
    for (&pub_vars, pubs) |*v, x| v.* = try ctx.guessM31(QM31.fromBase(x));
    var parts: [bs.N_COMP]pv.PartStatement = undefined;
    for (&parts, airs, digests, 0..) |*p, *air, d, i| p.* = .{ .air = air, .digest = d, .pubs = pub_vars[0..bs.n_pubs[i]] };
    const st = pv.PlainStatement{ .parts = &parts, .preprocessed_root = pre_root };
    try pv.verifyPlain(QM31, &ctx, &g, config, &st);
    try bl.leafChecks(&ctx, &pub_vars);
    try bl.leafCtx(&ctx, &pub_vars);
    const seed = try bl.seedLeafVars(&ctx, &pub_vars);
    const sum_prog = try glue.parse(ctx.scratch(), @embedFile("air:block_leaf_sum"));
    const one = (try glue.run(QM31, &ctx, &sum_prog, &.{}, InputHooks{ .inputs = &.{ pub_vars[2], pub_vars[coin.PUB_NIN] } }))[0];
    var s: [NS]Var = undefined;
    s[0] = pub_vars[2];
    s[1] = one;
    @memcpy(s[2..6], pub_vars[coin.PUB_S..][0..4]);
    s[6] = pub_vars[coin.PUB_NIN];
    @memcpy(s[7..15], pub_vars[coin.PUB_G..][0..8]);
    @memcpy(s[15..19], pub_vars[coin.PUB_ALPHA + 4 ..][0..4]);
    @memcpy(s[HR..][0..16], pub_vars[bs.PUB_HASH..][0..16]);
    @memcpy(s[SR..][0..16], &seed);
    var key: [8]U32Wrapper(Var) = undefined;
    for (&key) |*k| k.* = try builder.wrappers.constU32(QM31, &ctx, 0);
    try leaf.finish(QM31, &ctx, try leaf.pubsDigestVars(QM31, &ctx, key, &s));
    return ctx;
}

/// A node's view of a child.
pub fn ChildInput(comptime V: type) type {
    return struct {
        proof: *const stark_proof.Proof(V),
        preprocessed_root: HashValue(V),
        key: HashValue(V),
        sum: [NS]V,
    };
}

/// The block node circuit (finalized, unpadded): the Lean glue (`blockNodeProgram`) with the
/// children's verifiers at its hooks.
pub fn buildNodeCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, children: [2]ChildInput(V), shared: *const multiverifier.SharedConfig) !Context(V) {
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), @embedFile("air:block_node_glue"));
    const per = NS + 16;
    const ext = try ctx.scratch().alloc(V, 2 * per);
    for (children, 0..) |child, i| {
        @memcpy(ext[per * i ..][0..NS], &child.sum);
        for (child.key.words, 0..) |w, k| ext[per * i + NS + k] = w.get();
        for (child.preprocessed_root.words, 0..) |w, k| ext[per * i + NS + 8 + k] = w.get();
    }
    const Hooks = struct {
        ctx: *Context(V),
        table: *const circuit.air_eval.component_table.Table,
        children: [2]ChildInput(V),
        shared: *const multiverifier.SharedConfig,
        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            const config: circuit_statement.CircuitConfig = .{
                .config = self.shared.pcs_config,
                .preprocessed_column_log_sizes = self.shared.preprocessed_column_log_sizes,
            };
            var root: HashValue(Var) = undefined;
            var digest: HashValue(Var) = undefined;
            for (&root.words, args[0..8]) |*w, v| w.* = .newUnsafe(v);
            for (&digest.words, args[8..16]) |*w, v| w.* = .newUnsafe(v);
            const statement = try circuit_statement.CircuitStatement(V).init(self.ctx, self.table, &config, root, digest);
            const proof_vars = try stark_proof.guess(V, self.ctx, self.children[id].proof);
            try verify_mod.verify(V, self.ctx, &proof_vars, self.shared.proof_config, &statement, verify_mod.NoStages{});
            const out = try self.ctx.scratch().alloc(Var, 8);
            for (out, statement.circuit_hash.words) |*o, w| o.* = w.get();
            return out;
        }
    };
    const res = try glue.run(V, &ctx, &prog, ext, Hooks{ .ctx = &ctx, .table = table, .children = children, .shared = shared });
    var digest: HashValue(Var) = undefined;
    for (&digest.words, res) |*w, v| w.* = .newUnsafe(v);
    try leaf.finish(V, &ctx, digest);
    return ctx;
}

/// The shared shape of block leaves and nodes (`node.Shape` for the block node).
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

pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const empty = try stark_proof.emptyProof(arena.allocator(), shared.proof_config);
    var sum: [NS]NoValue = undefined;
    @memset(&sum, .{});
    const child: ChildInput(NoValue) = .{ .proof = &empty, .preprocessed_root = undefined, .key = undefined, .sum = sum };
    return buildNodeCircuit(NoValue, gpa, table, .{ child, child }, shared);
}

/// A proved range: its circuit proof, key and summary.
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

/// Proves the node over `left` and `right` and verifies it natively; its digest must be the native
/// join's.
pub fn proveNode(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, left: *const Proved, right: *const Proved) !Proved {
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    var values: [2]stark_proof.Proof(QM31) = undefined;
    const inputs = try childInputs(scratch.allocator(), .{ left, right }, &values);
    var ctx = try buildNodeCircuit(QM31, gpa, &tables.table, inputs, &shape.shared);
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shape.target, shape.fri);
    errdefer cp.deinit();
    const node: Proved = .{
        .proof = cp,
        .key = @import("node.zig").nodeKey(left.proof.circuit_hash, left.key, right.proof.circuit_hash, right.key),
        .sum = joinSummary(left.sum, right.sum),
    };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &node.digest())) return error.NodeDigestMismatch;
    return node;
}

/// A block leaf from a block proof file: verified natively (with capture), its leaf circuit built.
pub fn leafCircuitOf(gpa: std.mem.Allocator, a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, f: *const PF.File, fri: FriConfigV2) !Context(QM31) {
    const parts = PF.partsOf(airs, f.log_size, &f.pubs);
    const cfg = rec.Config.fromFriAndTraceSize(fri, f.log_size);
    var capture: core.verifier.ProofCapture(rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &parts, &.{}, &f.proof, &capture);
    const pc = try bl.config(a, airs, f.log_size, fri);
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    const values = try pv.fromCapture(a, rec.Hasher, &f.proof.stark, &capture, pc, f.proof.claimed_sums);
    var digests: [bs.N_COMP][32]u8 = undefined;
    for (&digests, airs) |*d, *air| d.* = try air.digest(a);
    return buildLeafCircuit(gpa, &values, pc, airs, &digests, pre_root, &f.pubs);
}

/// Proves a block leaf under `shape`, verifies it natively, and checks its digest.
pub fn proveLeaf(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const Shape, airs: *const [bs.N_COMP]ir.Air, f: *const PF.File, fri: FriConfigV2) !Proved {
    var ctx = try leafCircuitOf(gpa, a, airs, f, fri);
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shape.target, shape.fri);
    errdefer cp.deinit();
    const p: Proved = .{ .proof = cp, .key = leaf.zero_key, .sum = leafSummary(&f.pubs) };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &p.digest())) return error.LeafDigestMismatch;
    return p;
}

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

/// Two consecutive epoch block proofs (`dir/proofs/<h>.sbblock`, `<h+1>`), two leaves and a node.
pub fn demo(gpa: std.mem.Allocator, dir: []const u8, h: u32) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const fri = PF.productionFri();
    const cfri = try FriConfigV2.init(26, 0, 1, 70, 1);
    var timer = try std.time.Timer.start();
    var files: [2]PF.File = undefined;
    for (&files, 0..) |*f, i| {
        const path = try std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ dir, h + @as(u32, @intCast(i)) });
        f.* = try PF.decode(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
    }
    // The shape: the larger leaf's padded sizes, grown to a fixpoint with the block node.
    var start: ComponentSizes = undefined;
    for (&files, 0..) |*f, i| {
        var ctx = try leafCircuitOf(gpa, a, &airs, f, fri);
        defer ctx.deinit();
        const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        start = if (i == 0) sz else start.elementwiseMax(sz);
    }
    var shape = try Shape.init(gpa, &tables.table, start, cfri);
    defer shape.deinit(gpa);
    std.debug.print("shape fixed in {d:.1}s\n", .{secs(timer.lap())});
    var leaves: [2]Proved = undefined;
    for (&leaves, &files) |*l, *f| l.* = try proveLeaf(gpa, a, tables, &shape, &airs, f, fri);
    std.debug.print("2 block leaves proved and verified in {d:.1}s ({d} + {d} bytes)\n", .{ secs(timer.lap()), leaves[0].proof.bytes.len, leaves[1].proof.bytes.len });
    var node = try proveNode(gpa, a, tables, &shape, &leaves[0], &leaves[1]);
    defer node.proof.deinit();
    for (&leaves) |*l| l.proof.deinit();
    std.debug.print("node proved and verified in {d:.1}s: blocks {d}..{d}, inputs {d}, proof {d} bytes\n", .{
        secs(timer.lap()), node.sum[0].toU32(), node.sum[0].toU32() + node.sum[1].toU32() - 1, node.sum[6].toU32(), node.proof.bytes.len,
    });
}
