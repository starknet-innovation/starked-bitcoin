//! The wide block node (docs/design/block-rec.md § Wide nodes): `2^a` child circuit proofs verified in
//! one circuit, their summaries joined. The glue is the Lean program `blockNodeK a`
//! (`Circuit/BlockNodeK.lean`, exported as `airs/block_node_k<a>.json`): each child's guessed summary,
//! key and preprocessed root, the digest its verifier hook checks, the balanced join of the summaries
//! (the binary node's `nodeOut` at every inner vertex), the key `Blake2s(h₀ ‖ k₀ ‖ … )` and the output
//! digest; `nodeK_sound`, and end to end `treeK_sound`/`forestK_soundP` (VL-NODE).
//!
//! Children are block leaves or nodes padded to one shared shape, so a node mixes blocks of any size:
//! block sizes change from block to block (the chain survey), which is why the width is here and not
//! in the leaf (packing k block proofs into one leaf circuit gives a circuit per tuple of sizes).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const leaf = @import("leaf.zig");
const glue = @import("glue.zig");
const br = @import("block_rec.zig");

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
const HashValue = builder.blake.HashValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const ComponentSizes = leaf.ComponentSizes;
const Key = leaf.Key;
const NS = br.NS;
const Summary = br.Summary;

/// The widest node (`2^MAX_A` children); `blockNodeK a` is exported for `a = 1 … MAX_A`.
pub const MAX_A = 4;

pub fn programJson(a: u32) ![]const u8 {
    return switch (a) {
        1 => @embedFile("air:block_node_k1"),
        2 => @embedFile("air:block_node_k2"),
        3 => @embedFile("air:block_node_k3"),
        4 => @embedFile("air:block_node_k4"),
        else => error.NodeArity,
    };
}

/// stwo-zig's recursive verifier at hook `i` (child `i`'s proof): args the guessed preprocessed root
/// and the child's digest, outputs the child's circuit hash (`node.RecHook`, any number of children).
pub fn Hook(comptime V: type) type {
    return struct {
        ctx: *Context(V),
        table: *const circuit.air_eval.component_table.Table,
        proofs: []const *const stark_proof.Proof(V),
        shared: *const multiverifier.SharedConfig,

        pub fn call(self: @This(), id: u32, args: []const Var) ![]const Var {
            if (id >= self.proofs.len or args.len != 16) return error.GlueHookArity;
            const config: circuit_statement.CircuitConfig = .{
                .config = self.shared.pcs_config,
                .preprocessed_column_log_sizes = self.shared.preprocessed_column_log_sizes,
            };
            var root: HashValue(Var) = undefined;
            var digest: HashValue(Var) = undefined;
            for (&root.words, args[0..8]) |*w, v| w.* = .newUnsafe(v);
            for (&digest.words, args[8..16]) |*w, v| w.* = .newUnsafe(v);
            const statement = try circuit_statement.CircuitStatement(V).init(self.ctx, self.table, &config, root, digest);
            const proof_vars = try stark_proof.guess(V, self.ctx, self.proofs[id]);
            try verify_mod.verify(V, self.ctx, &proof_vars, self.shared.proof_config, &statement, verify_mod.NoStages{});
            const out = try self.ctx.scratch().alloc(Var, 8);
            for (out, statement.circuit_hash.words) |*o, w| o.* = w.get();
            return out;
        }
    };
}

/// The wide node circuit (finalized, unpadded) over `2^a` children.
pub fn buildCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, a: u32, children: []const br.ChildInput(V), shared: *const multiverifier.SharedConfig) !Context(V) {
    if (children.len != @as(usize, 1) << @intCast(a)) return error.NodeArity;
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), try programJson(a));
    const per = NS + 16;
    const ext = try ctx.scratch().alloc(V, children.len * per);
    const proofs = try ctx.scratch().alloc(*const stark_proof.Proof(V), children.len);
    for (children, proofs, 0..) |child, *p, i| {
        @memcpy(ext[per * i ..][0..NS], &child.sum);
        for (child.key.words, 0..) |w, k| ext[per * i + NS + k] = w.get();
        for (child.preprocessed_root.words, 0..) |w, k| ext[per * i + NS + 8 + k] = w.get();
        p.* = child.proof;
    }
    try glue.runOutputs(V, &ctx, &prog, ext, Hook(V){ .ctx = &ctx, .table = table, .proofs = proofs, .shared = shared });
    return ctx;
}

pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, a: u32, shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const empty = try stark_proof.emptyProof(arena.allocator(), shared.proof_config);
    var sum: [NS]NoValue = undefined;
    @memset(&sum, .{});
    const children = try arena.allocator().alloc(br.ChildInput(NoValue), @as(usize, 1) << @intCast(a));
    @memset(children, .{ .proof = &empty, .preprocessed_root = undefined, .key = undefined, .sum = sum });
    return buildCircuit(NoValue, gpa, table, a, children, shared);
}

/// The shared shape of block leaves and wide nodes of `2^a` children: `start` grown to a fixpoint
/// with the node's topology (`block_rec.Shape.init` for the wide node).
pub fn shape(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, a: u32, start: ComponentSizes, fri: FriConfigV2) !br.Shape {
    var target = start;
    while (true) {
        var shared = try multiverifier.foldSharedConfig(gpa, target, fri);
        errdefer shared.deinit(gpa);
        var ctx = try topology(gpa, table, a, &shared);
        defer ctx.deinit();
        const grown = target.elementwiseMax(finalize.computePaddedSizes(.fromBuilder(&ctx.circuit)));
        if (std.meta.eql(grown, target)) return .{ .target = target, .shared = shared, .fri = fri };
        shared.deinit(gpa);
        target = grown;
    }
}

/// The wide node's key: Blake2s over each child's circuit hash, then its key (`keyOfK`).
pub fn key(hashes: []const [8]u32, keys: []const Key) Key {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    for (hashes, keys) |ch, k| for ([_][8]u32{ ch, k }) |ws| for (ws) |w| {
        std.mem.writeInt(u32, &b, w, .little);
        h.update(&b);
    };
    var d: [32]u8 = undefined;
    h.final(&d);
    var out: Key = undefined;
    for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return out;
}

/// The balanced join of `sums` (a power of two of them; `joinT`).
pub fn join(sums: []const Summary) Summary {
    if (sums.len == 1) return sums[0];
    const h = sums.len / 2;
    return br.joinSummary(join(sums[0..h]), join(sums[h..]));
}

fn childInputs(a: std.mem.Allocator, children: []const *const br.Proved) ![]br.ChildInput(QM31) {
    const inputs = try a.alloc(br.ChildInput(QM31), children.len);
    for (children, inputs) |child, *input| {
        const v = try a.create(stark_proof.Proof(QM31));
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

/// The native view of a wide node over `children`: its key and summary.
pub fn expected(a: std.mem.Allocator, children: []const *const br.Proved) !struct { key: Key, sum: Summary } {
    const hashes = try a.alloc([8]u32, children.len);
    const keys = try a.alloc(Key, children.len);
    const sums = try a.alloc(Summary, children.len);
    for (children, hashes, keys, sums) |c, *h, *k, *s| {
        h.* = c.proof.circuit_hash;
        k.* = c.key;
        s.* = c.sum;
    }
    return .{ .key = key(hashes, keys), .sum = join(sums) };
}

/// The wide node circuit over proved `children` (values), for checks and proving.
pub fn circuitOf(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, arity: u32, shp: *const br.Shape, children: []const *const br.Proved) !Context(QM31) {
    const inputs = try childInputs(a, children);
    return buildCircuit(QM31, gpa, &tables.table, arity, inputs, &shp.shared);
}

/// Proves the wide node over `children` and verifies it natively; its digest must be the native
/// join's under the native key.
pub fn prove(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, arity: u32, shp: *const br.Shape, children: []const *const br.Proved) !br.Proved {
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    var ctx = try circuitOf(gpa, scratch.allocator(), tables, arity, shp, children);
    defer ctx.deinit();
    var cp = try leaf.proveCircuit(gpa, a, &ctx, shp.target, shp.fri);
    errdefer cp.deinit();
    const want = try expected(scratch.allocator(), children);
    const node: br.Proved = .{ .proof = cp, .key = want.key, .sum = want.sum };
    const out = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &out, &node.digest())) return error.NodeDigestMismatch;
    return node;
}

test "wide node key over two children is the binary node key" {
    const h0: [8]u32 = .{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const h1: [8]u32 = .{ 9, 10, 11, 12, 13, 14, 15, 16 };
    const k0: Key = .{ 17, 18, 19, 20, 21, 22, 23, 24 };
    const k1: Key = @splat(0);
    const node_mod = @import("node.zig");
    try std.testing.expectEqualSlices(u32, &node_mod.nodeKey(h0, k0, h1, k1), &key(&.{ h0, h1 }, &.{ k0, k1 }));
}

test "wide node programs parse, with one hook per child" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    for (1..MAX_A + 1) |a| {
        const prog = try glue.parse(arena.allocator(), try programJson(@intCast(a)));
        var hooks: usize = 0;
        for (prog.ops) |op| if (op == .hook) {
            hooks += 1;
        };
        try std.testing.expectEqual(@as(usize, 1) << @intCast(a), hooks);
        try std.testing.expectEqual(@as(usize, 8), prog.results.len);
    }
}

/// The last 8 output words of a finalized context with values (the digest; the outputs start with a
/// reserved one).
pub fn outputDigest(ctx: *const Context(QM31)) [8]u32 {
    var d: [8]u32 = @splat(0);
    const outs = ctx.circuit.output.items;
    if (outs.len < 8) return d;
    for (outs[outs.len - 8 ..], &d) |idx, *w| {
        const limbs = ctx.get(.{ .idx = idx }).toM31Array();
        w.* = limbs[0].toU32() | (limbs[1].toU32() << 16);
    }
    return d;
}

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

/// `blockpack widenode <dir> <from> <a> [prove]`: `2^a` consecutive block proofs as block leaves (proved
/// at the binary node's shared shape), then the wide node over them: its circuit is checked satisfied
/// with output the native join's digest; reordered children and a wrong child key are rejected; with
/// `prove` (`a = 1` fits the shape) the node is proved and verified.
pub fn demo(gpa: std.mem.Allocator, dir: []const u8, from: u32, arity: u32, prove_node: bool) !void {
    const bs = @import("../block/system.zig");
    const PF = @import("../block/proof_file.zig");
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const fri = PF.productionFri();
    const n = @as(usize, 1) << @intCast(arity);
    var timer = try std.time.Timer.start();
    const files = try a.alloc(PF.File, n);
    var start: ComponentSizes = undefined;
    for (files, 0..) |*f, i| {
        const path = try std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ dir, from + @as(u32, @intCast(i)) });
        f.* = try PF.decode(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
        var ctx = try br.leafCircuitOf(gpa, a, &airs, f, fri);
        defer ctx.deinit();
        const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        start = if (i == 0) sz else start.elementwiseMax(sz);
    }
    // `SB_FOLD` (default 1): the circuits' FRI fold step (last layer 0; a remainder fold when the trace log isn't a multiple).
    const fold: u32 = if (std.posix.getenv("SB_FOLD")) |v| try std.fmt.parseInt(u32, v, 10) else 1;
    var shp = try br.Shape.init(gpa, &tables.table, start, try FriConfigV2.init(26, 0, 1, 70, fold));
    defer shp.deinit(gpa);
    const leaves = try a.alloc(br.Proved, n);
    const refs = try a.alloc(*const br.Proved, n);
    for (leaves, refs, files) |*l, *r, *f| {
        l.* = try br.proveLeaf(gpa, a, tables, &shp, &airs, f, fri);
        r.* = l;
    }
    defer for (leaves) |*l| l.proof.deinit();
    std.debug.print("{d} block leaves (blocks {d}..{d}) proved and verified in {d:.1}s\n", .{ n, from, from + n - 1, secs(timer.lap()) });
    {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        var ctx = try circuitOf(gpa, scratch.allocator(), tables, arity, &shp, refs);
        defer ctx.deinit();
        if (!try ctx.isCircuitValid()) return error.NodeUnsatisfied;
        const want = try expected(scratch.allocator(), refs);
        const d = leaf.pubsDigest(want.key, &want.sum);
        const got = outputDigest(&ctx);
        if (!std.mem.eql(u32, &got, &d)) return error.NodeDigestMismatch;
        std.debug.print("wide node a={d} ({d} children): {d} vars, satisfied, output = native digest; built in {d:.1}s\n", .{ arity, n, ctx.circuit.n_vars, secs(timer.lap()) });
    }
    // Tamper: the first two children swapped (the link checks fail), a wrong key on the last child (its hook's
    // digest no longer matches its proof).
    for ([_][]const u8{ "the first two children swapped", "a wrong key on the last child" }, 0..) |what, t| {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        const inputs = try childInputs(scratch.allocator(), refs);
        if (t == 0) std.mem.swap(br.ChildInput(QM31), &inputs[0], &inputs[1]) else {
            var bad = leaf.zero_key;
            bad[0] ^= 1;
            inputs[n - 1].key = builder.blake.hashValue(QM31, bad);
        }
        var c = try buildCircuit(QM31, gpa, &tables.table, arity, inputs, &shp.shared);
        defer c.deinit();
        if (try c.isCircuitValid()) return error.TamperAccepted;
        std.debug.print("wide node with {s}: circuit unsatisfied (rejected)\n", .{what});
    }
    if (!prove_node) return;
    _ = timer.lap();
    var node = try prove(gpa, a, tables, arity, &shp, refs);
    defer node.proof.deinit();
    std.debug.print("wide node proved and verified in {d:.1}s: blocks {d}..{d}, proof {d} bytes\n", .{
        secs(timer.lap()), node.sum[0].toU32(), node.sum[0].toU32() + node.sum[1].toU32() - 1, node.proof.bytes.len,
    });
}
