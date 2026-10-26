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
        3 => @embedFile("air:epoch_root_3_prev"),
        16 => @embedFile("air:epoch_root_16_prev"),
        else => error.EpochRootNotExported,
    };
    return switch (m) {
        1 => @embedFile("air:epoch_root_1"),
        2 => @embedFile("air:epoch_root_2"),
        3 => @embedFile("air:epoch_root_3"),
        16 => @embedFile("air:epoch_root_16"),
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
    var pubs: Public = .{ .s = s, .nin = nin, .challenge = undefined, .hash_roots = undefined };
    if (sums.len > 0) @memcpy(&pubs.challenge, sums[0][7..19]);
    var roots: [64][16]M31 = undefined;
    for (sums, 0..) |c, i| @memcpy(&roots[i], c[19..35]);
    pubs.hash_roots = roots[0..sums.len];
    return .{ .key = key, .s = s, .nin = nin, .digest = digestOf(key, ep, &pubs) };
}

/// The root's public values besides the epoch: the summed partial sum and input count, the challenge
/// (12 limbs, `(γ, z, α)`) and each child's block-hash root (16 limbs).
pub const Public = struct { s: [4]M31, nin: M31, challenge: [12]M31, hash_roots: []const [16]M31 };

fn putWord(h: *std.crypto.hash.blake2.Blake2s256, w: u32) void {
    var b: [4]u8 = undefined;
    std.mem.writeInt(u32, &b, w, .little);
    h.update(&b);
}

fn finalWords(h: *std.crypto.hash.blake2.Blake2s256) [8]u32 {
    var d: [32]u8 = undefined;
    h.final(&d);
    return digestWords(d);
}

/// The digest of the root's variable part (the Lean program's `rest`): Blake2s over the partial sum, the
/// input count, the challenge and the block-hash root limbs, one little-endian word each.
pub fn restOf(pubs: *const Public) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    for (pubs.s) |x| putWord(&h, x.toU32());
    putWord(&h, pubs.nin.toU32());
    for (pubs.challenge) |x| putWord(&h, x.toU32());
    for (pubs.hash_roots) |r| for (r) |x| putWord(&h, x.toU32());
    return finalWords(&h);
}

/// The root's output digest from its fixed part and `rest` (what a join opens): Blake2s over the key,
/// the final set's digest, the previous set's (the `prev` variant), `from`, `to`, then `rest`.
pub fn outOf(key: Key, ep: Epoch, rest: [8]u32) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    for (key) |w| putWord(&h, w);
    for (digestWords(ep.fin)) |w| putWord(&h, w);
    if (ep.prev) |p| for (digestWords(p)) |w| putWord(&h, w);
    putWord(&h, ep.from);
    putWord(&h, ep.to);
    for (rest) |w| putWord(&h, w);
    return finalWords(&h);
}

/// The root's output digest (the Lean program's): `outOf(key, ep, restOf(pubs))`.
pub fn digestOf(key: Key, ep: Epoch, pubs: *const Public) [8]u32 {
    return outOf(key, ep, restOf(pubs));
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
pub fn proveRoot(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, node_shared: *const multiverifier.SharedConfig, fri: core.pcs.config_v2.FriConfigV2, children: []const *const br.Proved, ep: Epoch, prove: bool) !RootProof {
    return proveRootAt(gpa, a, tables, node_shared, fri, children, ep, prove, null);
}

pub const RootProof = struct { digest: [8]u32, n_vars: usize, proof: ?leaf.CircuitProof, key: Key, rest: [8]u32 };

/// `proveRoot`, padded to `target` when given (a chain's fixed root shape, so a join verifies any root).
pub fn proveRootAt(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, node_shared: *const multiverifier.SharedConfig, fri: core.pcs.config_v2.FriConfigV2, children: []const *const br.Proved, ep: Epoch, prove: bool, target: ?finalize.ComponentSizes) !RootProof {
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
    var roots: [64][16]M31 = undefined;
    for (sums, 0..) |c, i| @memcpy(&roots[i], c[19..35]);
    var pubs: Public = .{ .s = want.s, .nin = want.nin, .challenge = undefined, .hash_roots = roots[0..sums.len] };
    @memcpy(&pubs.challenge, sums[0][7..19]);
    const rest = restOf(&pubs);
    if (!prove) return .{ .digest = out, .n_vars = n_vars, .proof = null, .key = want.key, .rest = rest };
    var cp = try leaf.proveCircuit(gpa, a, &ctx, target, fri);
    errdefer cp.deinit();
    const got = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &got, &want.digest)) return error.RootDigestMismatch;
    return .{ .digest = out, .n_vars = n_vars, .proof = cp, .key = want.key, .rest = rest };
}

/// The natural padded size of the root over `m` children (`prev` variant), for a chain's root shape.
pub fn naturalSize(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, m: usize, prev: bool, node_shared: *const multiverifier.SharedConfig) !finalize.ComponentSizes {
    var topo = try topology(gpa, table, m, prev, node_shared);
    defer topo.deinit();
    return finalize.computePaddedSizes(.fromBuilder(&topo.circuit));
}

const BF = @import("block_forest.zig");
const BT = @import("block_tree.zig");
const store = @import("store.zig");
const HT = @import("../btc/header_tree.zig");
const coin = @import("../block/coin.zig");
const finalize = circuit.common.finalize;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;

pub const VK_MAGIC = "SBROOTVK";
pub const FILE_MAGIC = "SBEROOT1";

/// The epoch root's verifying key, beside the tree VK: the one-child lift's identity (at the node size)
/// and the root's for this epoch's `M` and variant, with its trace size.
pub const RootVk = struct {
    fri: FriConfigV2,
    node_log: u32,
    lift: BF.Id,
    m: u32,
    prev: bool,
    root_log: u32,
    root: BF.Id,

    pub fn encode(self: *const RootVk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, VK_MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.node_log);
        try e.words(&self.lift.root);
        try e.words(&self.lift.hash);
        try e.int(u32, self.m);
        try e.int(u8, @intFromBool(self.prev));
        try e.int(u32, self.root_log);
        try e.words(&self.root.root);
        try e.words(&self.root.hash);
        return store.seal(&e);
    }

    pub fn decode(bytes: []const u8) !RootVk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: RootVk = undefined;
        vk.fri = try d.fri();
        vk.node_log = try d.int(u32);
        vk.lift = .{ .root = try d.words(8), .hash = try d.words(8) };
        vk.m = try d.int(u32);
        vk.prev = switch (try d.int(u8)) {
            0 => false,
            1 => true,
            else => return error.BadVk,
        };
        vk.root_log = try d.int(u32);
        vk.root = .{ .root = try d.words(8), .hash = try d.words(8) };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// The lift's and the root's identities under `shapes`: the lift at the node size (over a leaf), the
/// root at its own natural size (nothing verifies it in-circuit).
pub fn setupVk(gpa: std.mem.Allocator, tables: *const leaf.Tables, shapes: *const BT.Shapes, m: usize, prev: bool) !RootVk {
    const fri = shapes.node.fri;
    const lview = shapes.nodeView(.over_leaves);
    var ltopo = try wk.topology(gpa, &tables.table, 0, &lview.shared);
    defer ltopo.deinit();
    const lift = try BF.identityOf(gpa, NoValue, &ltopo, shapes.node.target, fri.log_blowup_factor);
    var rtopo = try topology(gpa, &tables.table, m, prev, &shapes.node.shared);
    defer rtopo.deinit();
    const natural = finalize.computePaddedSizes(.fromBuilder(&rtopo.circuit));
    const root = try BF.identityOf(gpa, NoValue, &rtopo, natural, fri.log_blowup_factor);
    return .{ .fri = fri, .node_log = lift.trace_log, .lift = lift.id, .m = @intCast(m), .prev = prev, .root_log = root.trace_log, .root = root.id };
}

/// One child of the root as the file records it: its aligned subtree, its block-hash root and that
/// root's path in the chain's header tree.
pub const Child = struct { x: u32, k: u32, hash_root: [16]M31, path: []const HT.Step };

/// An epoch root's public part (all but the proof): the range, the blocks' size keys (the identities
/// the key commits to), the children and the public values. A chain of joined epochs carries one per
/// epoch.
pub const Head = struct {
    from: u32,
    to: u32,
    logs: []const u8,
    children: []Child,
    s: [4]M31,
    nin: M31,
    challenge: [12]M31,

    pub fn encode(self: *const Head, e: *store.Enc) !void {
        try e.int(u32, self.from);
        try e.int(u32, self.to);
        try e.blob(self.logs);
        try e.int(u32, @intCast(self.children.len));
        for (self.children) |c| {
            try e.int(u32, c.x);
            try e.int(u32, c.k);
            for (c.hash_root) |x| try e.int(u32, x.toU32());
            try e.int(u32, @intCast(c.path.len));
            for (c.path) |st| {
                try e.words(&st.sibling);
                try e.int(u8, @intFromBool(st.left));
            }
        }
        for (self.s) |x| try e.int(u32, x.toU32());
        try e.int(u32, self.nin.toU32());
        for (self.challenge) |x| try e.int(u32, x.toU32());
    }

    pub fn decode(a: std.mem.Allocator, d: *store.Dec) !Head {
        var f: Head = undefined;
        f.from = try d.int(u32);
        f.to = try d.int(u32);
        f.logs = try a.dupe(u8, try d.blob());
        const n = try d.int(u32);
        if (n == 0 or n > 64) return error.BadFile;
        f.children = try a.alloc(Child, n);
        for (f.children) |*c| {
            c.x = try d.int(u32);
            c.k = try d.int(u32);
            for (&c.hash_root) |*x| x.* = try m31(d);
            const steps = try a.alloc(HT.Step, try d.int(u32));
            for (steps) |*st| {
                st.sibling = try d.words(8);
                st.left = switch (try d.int(u8)) {
                    0 => false,
                    1 => true,
                    else => return error.BadStep,
                };
            }
            c.path = steps;
        }
        for (&f.s) |*x| x.* = try m31(d);
        f.nin = try m31(d);
        for (&f.challenge) |*x| x.* = try m31(d);
        return f;
    }

    fn m31(d: *store.Dec) !M31 {
        const v = try d.int(u32);
        if (v >= 0x7fffffff) return error.NonCanonical;
        return M31.fromCanonical(v);
    }
};

/// An epoch's root proof: its public part and the circuit proof.
pub const File = struct {
    head: Head,
    proof: leaf.CircuitProof,

    pub fn encode(self: *const File, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, FILE_MAGIC);
        try e.int(u32, store.VERSION);
        try self.head.encode(&e);
        try store.encodeCircuit(&e, &self.proof, leaf.zero_key, &.{});
        return store.seal(&e);
    }

    pub fn decode(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !File {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(FILE_MAGIC);
        var f: File = undefined;
        f.head = try Head.decode(a, &d);
        var none: [0]M31 = .{};
        const c = try store.decodeCircuit(gpa, a, &d, &none);
        f.proof = c.proof;
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return f;
    }
};

/// The expected circuit hash and key of child `(x, k)` at block index `at`: the tree's, or for one
/// block the lift's (circuit hash `lift`) over the block's leaf.
fn childId(tvk: *const BT.Vk, lift: [8]u32, logs: []const u8, at: usize, k: u32) !struct { hash: [8]u32, key: Key } {
    if (k == 0) {
        const l = try tvk.leafFor(logs[at]);
        return .{ .hash = lift, .key = wk.key(&.{l.hash}, &.{leaf.zero_key}) };
    }
    const e = try BT.expected(tvk, logs, at, k);
    return .{ .hash = e.hash, .key = e.key };
}

pub const Verified = struct { sum: QM31, nin: u64, challenge: coin.Challenge };

/// What an epoch root's public part opens to: its key, `rest`, output digest (`outOf`), and the values
/// for the balance against the sets.
pub const Opened = struct { key: Key, rest: [8]u32, out: [8]u32, verified: Verified };

/// **An epoch root's public part, checked.** The children against the aligned decomposition of
/// `from..to`, their identities (the tree VK, the lift's circuit hash `lift`, the blocks' size keys)
/// into the root's key, each block-hash root against the chain's `T`; returns the opening: the root
/// proof (checked by the caller: alone, or through a join) must output `out`.
pub fn openHead(a: std.mem.Allocator, tvk: *const BT.Vk, lift: [8]u32, f: *const Head, ep: Epoch, n_headers: usize, t: HT.Words) !Opened {
    if (f.from != ep.from or f.to != ep.to or f.to < f.from) return error.WrongEpoch;
    if ((ep.prev != null) != (ep.from != 0)) return error.PrevSetRequired;
    if (f.to >= n_headers) return error.BeyondChain;
    const nb: usize = f.to - f.from + 1;
    if (f.logs.len != nb) return error.BadLogs;
    var sizes_buf: [64]u8 = undefined;
    const sizes = EP.alignedSizes(f.from, nb, &sizes_buf);
    if (sizes.len != f.children.len) return error.WrongRoot;
    const hashes = try a.alloc([8]u32, sizes.len);
    const keys = try a.alloc(Key, sizes.len);
    const roots = try a.alloc([16]M31, sizes.len);
    var at: usize = 0;
    for (sizes, f.children, hashes, keys, roots) |k, c, *h, *ky, *r| {
        const x: u32 = f.from + @as(u32, @intCast(at));
        if (c.x != x or c.k != k) return error.WrongForest;
        const id = try childId(tvk, lift, f.logs, at, k);
        h.* = id.hash;
        ky.* = id.key;
        r.* = c.hash_root;
        // The block-hash root is the chain's.
        var w: HT.Words = undefined;
        for (&w, 0..) |*q, i| q.* = c.hash_root[2 * i].toU32() | (c.hash_root[2 * i + 1].toU32() << 16);
        for (c.hash_root) |q| if (q.toU32() >= 1 << 16) return error.BadLimb;
        const sides = try HT.inclusionSides(a, x, n_headers);
        if (sides.len != k + c.path.len) return error.BadPath;
        for (sides[0..k]) |sd| if (sd) return error.BadPath;
        for (sides[k..], c.path) |sd, st| if (sd != st.left) return error.BadPath;
        if (!HT.verifyInclusion(w, c.path, t)) return error.HashesNotTheChain;
        at += @as(usize, 1) << @intCast(k);
    }
    const key = wk.key(hashes, keys);
    const pubs: Public = .{ .s = f.s, .nin = f.nin, .challenge = f.challenge, .hash_roots = roots };
    const rest = restOf(&pubs);
    return .{ .key = key, .rest = rest, .out = outOf(key, ep, rest), .verified = verifiedOf(f) };
}

/// **The epoch root's verifier.** The public part (`openHead`), then the root proof against the pinned
/// identity for `M` (preprocessed root, circuit hash, configuration) with the opening's output digest.
/// Returns the summed partial sum, input count and challenge, for the balance against the sets.
pub fn verify(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, tvk: *const BT.Vk, rvk: *const RootVk, f: *const File, ep: Epoch, n_headers: usize, t: HT.Words) !Verified {
    if (!std.meta.eql(rvk.fri, BT.circuitFri()) or !std.meta.eql(tvk.fri, rvk.fri) or tvk.node_log != rvk.node_log) return error.ConfigNotPinned;
    if (f.head.children.len != rvk.m or (ep.prev != null) != rvk.prev) return error.WrongRoot;
    const o = try openHead(a, tvk, rvk.lift.hash, &f.head, ep, n_headers, t);
    const p = &f.proof;
    if (!std.mem.eql(u32, &p.request.preprocessed_root, &rvk.root.root)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &p.circuit_hash, &rvk.root.hash)) return error.WrongCircuit;
    if (!std.meta.eql(p.request.pcs_config, PcsConfigV2.fromFriAndTraceSize(rvk.fri, rvk.root_log))) return error.ConfigNotPinned;
    const out = try leaf.verifyCircuit(gpa, tables, p);
    if (!std.mem.eql(u32, &out, &o.out)) return error.WrongDigest;
    return o.verified;
}

/// The public part's values for the balance: the summed partial sum, the input count, the challenge.
fn verifiedOf(f: *const Head) Verified {
    var ch: coin.Challenge = undefined;
    const q = struct {
        fn qm(l: []const M31) QM31 {
            return QM31.fromM31(l[0], l[1], l[2], l[3]);
        }
    }.qm;
    ch.gamma = q(f.challenge[0..4]);
    ch.z = q(f.challenge[4..8]);
    const alpha = q(f.challenge[8..12]);
    var x = QM31.one();
    for (&ch.alpha) |*w| {
        w.* = x;
        x = x.mul(alpha);
    }
    return .{ .sum = QM31.fromM31(f.s[0], f.s[1], f.s[2], f.s[3]), .nin = f.nin.toU32(), .challenge = ch };
}
