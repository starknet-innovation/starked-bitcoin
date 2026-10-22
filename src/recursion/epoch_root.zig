//! The epoch root (docs/design/block-rec.md § The epoch root): one circuit over an epoch's `M` aligned
//! subtrees. The glue is the Lean program `epochRoot M prevV` (`Circuit/EpochRoot.lean`, exported as
//! `airs/epoch_root_<M>[_prev].json`): the children's proofs verified at its hooks (as the wide node),
//! the ranges, one challenge, the sums, each count a power of two, then the seed (`epoch.seedOfRoots`)
//! and the challenge (`epoch.challenge`) recomputed in-circuit. Its output digest is `expected`'s.
//!
//! Children are node-shaped: a forest root of one block (a leaf) is first lifted by a one-child node
//! (`block_node_k`, `a = 0`).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const leaf = @import("leaf.zig");
const glue = @import("glue.zig");
const br = @import("block_rec.zig");
const wk = @import("block_node_k.zig");
const EP = @import("../block/epoch.zig");

const builder = circuit.builder;
const component_list = circuit.common.component_list;
const multiverifier = circuit.statements.multiverifier;
const stark_proof = circuit.stark_verifier.proof;
const Context = builder.Context;
const NoValue = builder.NoValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const NS = br.NS;
const Summary = br.Summary;
const Key = leaf.Key;

/// The child counts exported from Lean (`airs/epoch_root_<M>[_prev].json`); export more with
/// `lake env lean --run Export.lean epoch_root <M> [prev]` and add them here and in build.zig.
pub fn programJson(m: usize, prev: bool) ![]const u8 {
    if (prev) return switch (m) {
        1 => @embedFile("air:epoch_root_1_prev"),
        2 => @embedFile("air:epoch_root_2_prev"),
        16 => @embedFile("air:epoch_root_16_prev"),
        else => error.EpochRootNotExported,
    };
    return switch (m) {
        1 => @embedFile("air:epoch_root_1"),
        2 => @embedFile("air:epoch_root_2"),
        else => error.EpochRootNotExported,
    };
}

/// What the root binds besides its children: the range and the two set digests (`prev` null for an
/// epoch from genesis).
pub const Epoch = struct { from: u32, to: u32, prev: ?[32]u8, fin: [32]u8 };

/// A digest's 8 little-endian words (the seed's and the output digest's encoding).
pub fn digestWords(d: [32]u8) [8]u32 {
    var w: [8]u32 = undefined;
    for (&w, 0..) |*x, i| x.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
    return w;
}

/// The root circuit (finalized, unpadded) over node-shaped `children`, whose proofs verify under
/// `shared`.
pub fn buildCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, children: []const br.ChildInput(V), shared: *const multiverifier.SharedConfig, ep: Epoch) !Context(V) {
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), try programJson(children.len, ep.prev != null));
    const per = NS + 16;
    const base = children.len * per;
    const ext = try ctx.scratch().alloc(V, base + 18);
    const proofs = try ctx.scratch().alloc(*const stark_proof.Proof(V), children.len);
    for (children, proofs, 0..) |child, *p, i| {
        @memcpy(ext[per * i ..][0..NS], &child.sum);
        for (child.key.words, 0..) |w, k| ext[per * i + NS + k] = w.get();
        for (child.preprocessed_root.words, 0..) |w, k| ext[per * i + NS + 8 + k] = w.get();
        p.* = child.proof;
    }
    if (V == QM31) {
        ext[base] = QM31.fromBase(M31.fromCanonical(ep.from));
        ext[base + 1] = QM31.fromBase(M31.fromCanonical(ep.to));
        const fin = builder.blake.hashValue(QM31, digestWords(ep.fin));
        for (fin.words, 0..) |w, k| ext[base + 2 + k] = w.get();
        const prev = builder.blake.hashValue(QM31, if (ep.prev) |p| digestWords(p) else @as([8]u32, @splat(0)));
        for (prev.words, 0..) |w, k| ext[base + 10 + k] = w.get();
    } else @memset(ext[base..], .{});
    try glue.runOutputs(V, &ctx, &prog, ext, wk.Hook(V){ .ctx = &ctx, .table = table, .proofs = proofs, .shared = shared });
    return ctx;
}

/// The root's topology over `m` node-shaped children (no values): its identity.
pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, m: usize, prev: bool, shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const empty = try stark_proof.emptyProof(arena.allocator(), shared.proof_config);
    var sum: [NS]NoValue = undefined;
    @memset(&sum, .{});
    const children = try arena.allocator().alloc(br.ChildInput(NoValue), m);
    @memset(children, .{ .proof = &empty, .preprocessed_root = undefined, .key = undefined, .sum = sum });
    return buildCircuit(NoValue, gpa, table, children, shared, .{ .from = 0, .to = 0, .prev = if (prev) @splat(0) else null, .fin = @splat(0) });
}

/// The native view of the root over children with circuit hashes `hashes`, keys `keys` and summaries
/// `sums`: its key, the summed partial sum and input count, and its output digest (the Lean program's:
/// Blake2s over the key, the final and previous set digests, then `from`, `to`, the partial sum, the
/// input count and each child's block-hash root limbs, one word each).
pub fn expected(hashes: []const [8]u32, keys: []const Key, sums: []const Summary, ep: Epoch) struct { key: Key, s: [4]M31, nin: M31, digest: [8]u32 } {
    const key = wk.key(hashes, keys);
    var s: [4]M31 = @splat(M31.zero());
    var nin = M31.zero();
    for (sums) |c| {
        for (&s, 0..) |*x, j| x.* = x.add(c[2 + j]);
        nin = nin.add(c[6]);
    }
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    var b: [4]u8 = undefined;
    const put = struct {
        fn f(hh: *std.crypto.hash.blake2.Blake2s256, bb: *[4]u8, w: u32) void {
            std.mem.writeInt(u32, bb, w, .little);
            hh.update(bb);
        }
    }.f;
    for (key) |w| put(&h, &b, w);
    for (digestWords(ep.fin)) |w| put(&h, &b, w);
    if (ep.prev) |p| for (digestWords(p)) |w| put(&h, &b, w);
    put(&h, &b, ep.from);
    put(&h, &b, ep.to);
    for (s) |x| put(&h, &b, x.toU32());
    put(&h, &b, nin.toU32());
    for (sums) |c| for (c[19..35]) |x| put(&h, &b, x.toU32());
    var d: [32]u8 = undefined;
    h.final(&d);
    return .{ .key = key, .s = s, .nin = nin, .digest = digestWords(d) };
}

/// The challenge the root recomputes, from the children's seed roots: `epoch.challenge` of
/// `epoch.seedOfRoots` (for the native checks and tests).
pub fn challengeOf(sums: []const Summary, ep: Epoch) !@import("../block/coin.zig").Challenge {
    var roots: [64]EP.SubRoot = undefined;
    if (sums.len > roots.len) return error.TooManyRoots;
    for (sums, roots[0..sums.len]) |c, *r| {
        const n = c[1].toU32();
        if (n == 0 or !std.math.isPowerOfTwo(n)) return error.BadCount;
        var w: [8]u32 = undefined;
        for (&w, 0..) |*x, i| x.* = c[35 + 2 * i].toU32() | (c[36 + 2 * i].toU32() << 16);
        r.* = .{ .x = c[0].toU32(), .k = @intCast(std.math.log2_int(u32, n)), .root = w };
    }
    return EP.challenge(EP.seedOfRoots(ep.from, ep.to, ep.prev, ep.fin, roots[0..sums.len]));
}

test "epoch root programs parse, one hook per child" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    for ([_]struct { m: usize, prev: bool }{ .{ .m = 1, .prev = false }, .{ .m = 2, .prev = false }, .{ .m = 1, .prev = true }, .{ .m = 2, .prev = true }, .{ .m = 16, .prev = true } }) |c| {
        const prog = try glue.parse(arena.allocator(), try programJson(c.m, c.prev));
        var hooks: usize = 0;
        for (prog.ops) |op| if (op == .hook) {
            hooks += 1;
        };
        try std.testing.expectEqual(c.m, hooks);
        try std.testing.expectEqual(@as(usize, 8), prog.results.len);
    }
}

/// Builds the root over node-shaped `children` (forest roots, one-block ones already lifted), checks it
/// is satisfied with the native digest, and proves it at its natural size (CPU) when `prove`.
pub fn proveRoot(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, node_shared: *const multiverifier.SharedConfig, fri: core.pcs.config_v2.FriConfigV2, children: []const *const br.Proved, ep: Epoch, prove: bool) !struct { digest: [8]u32, n_vars: usize, proof: ?leaf.CircuitProof } {
    var scratch = std.heap.ArenaAllocator.init(gpa);
    defer scratch.deinit();
    const sa = scratch.allocator();
    const inputs = try wk.childInputs(sa, children);
    var ctx = try buildCircuit(QM31, gpa, &tables.table, inputs, node_shared, ep);
    defer ctx.deinit();
    const hashes = try sa.alloc([8]u32, children.len);
    const keys = try sa.alloc(Key, children.len);
    const sums = try sa.alloc(Summary, children.len);
    for (children, hashes, keys, sums) |c, *h, *k, *s| {
        h.* = c.proof.circuit_hash;
        k.* = c.key;
        s.* = c.sum;
    }
    const want = expected(hashes, keys, sums, ep);
    if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
    const out = wk.outputDigest(&ctx);
    if (!std.mem.eql(u32, &out, &want.digest)) return error.RootDigestMismatch;
    const n_vars = ctx.circuit.n_vars;
    if (!prove) return .{ .digest = out, .n_vars = n_vars, .proof = null };
    var cp = try leaf.proveCircuit(gpa, a, &ctx, null, fri);
    errdefer cp.deinit();
    const got = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &got, &want.digest)) return error.RootDigestMismatch;
    return .{ .digest = out, .n_vars = n_vars, .proof = cp };
}
