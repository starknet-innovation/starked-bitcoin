//! BLOCK-REC: an epoch's block proofs as a forest of recursion trees, one per aligned perfect
//! subtree of the seed v3 decomposition (`epoch.alignedSizes`), and its outer verifier.
//!
//! **Setup** (`setup`): the shared shape of block leaves and nodes, the block leaf's identity per
//! block trace size (its topology does not depend on the block: tested), the block node's
//! identity; written as a VK file. **Prove** (`proveForest`): per aligned subtree, the leaves then
//! the nodes, bottom up; the roots with each one's inclusion path in the chain's header tree, as a
//! forest file. **Verify** (`verifyForest`): per root, the pinned identity and the expected key
//! (from the blocks' trace sizes), the circuit proof, its summary's range; the challenge from the
//! seed over the roots' seed subtrees and both sets' digests; the balance against the final set;
//! each block-hash subtree against the chain's `T`. The previous-block MTP is not yet bound
//! (D-043 part 3).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const leaf = @import("leaf.zig");
const node = @import("node.zig");
const store = @import("store.zig");
const br = @import("block_rec.zig");
const HT = @import("../btc/header_tree.zig");
const ir = @import("../air/ir.zig");
const bs = @import("../block/system.zig");
const PF = @import("../block/proof_file.zig");
const EP = @import("../block/epoch.zig");

const finalize = circuit.common.finalize;
const preprocessed = circuit.common.preprocessed;
const Context = circuit.builder.Context;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const ComponentSizes = leaf.ComponentSizes;

pub const VK_MAGIC = "SBBLKVK\x00";
pub const FOREST_MAGIC = "SBFOREST";

/// A circuit's identity: preprocessed root and circuit hash.
pub const Id = struct { root: [8]u32, hash: [8]u32 };

/// The block tree's verifying key.
pub const Vk = struct {
    /// The circuits' FRI configuration, and their (shared) padded trace size.
    fri: FriConfigV2,
    trace_log: u32,
    /// The block leaf's identity per block trace size (null: not set up).
    leaf: [25]?Id,
    node: Id,

    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, VK_MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.trace_log);
        for (self.leaf) |l| {
            try e.int(u8, @intFromBool(l != null));
            if (l) |id| {
                try e.words(&id.root);
                try e.words(&id.hash);
            }
        }
        try e.words(&self.node.root);
        try e.words(&self.node.hash);
        return store.seal(&e);
    }

    pub fn decode(bytes: []const u8) !Vk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: Vk = undefined;
        vk.fri = try d.fri();
        vk.trace_log = try d.int(u32);
        for (&vk.leaf) |*l| l.* = switch (try d.int(u8)) {
            0 => null,
            1 => .{ .root = try d.words(8), .hash = try d.words(8) },
            else => return error.BadVk,
        };
        vk.node = .{ .root = try d.words(8), .hash = try d.words(8) };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

fn identityOf(gpa: std.mem.Allocator, comptime V: type, ctx: *Context(V), target: ComponentSizes, log_blowup: u32) !struct { id: Id, trace_log: u32 } {
    try finalize.padToTargets(V, ctx, target);
    var pp = if (V == QM31)
        try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, ctx)
    else
        try preprocessed.PreprocessedCircuit.fromBuilderCircuit(gpa, &ctx.circuit);
    defer pp.deinit(gpa);
    const id = try circuit_cpu.recursion.circuit_params.identity(gpa, &pp, log_blowup);
    return .{
        .id = .{ .root = core.vcs.blake2_hash.digestToU32s(id.preprocessed_root), .hash = core.vcs.blake2_hash.digestToU32s(id.circuit_hash) },
        .trace_log = pp.traceLogSize(),
    };
}

/// The circuits' FRI configuration (as the header chain's: 70 queries, 26 PoW bits).
pub fn circuitFri() FriConfigV2 {
    return FriConfigV2.init(26, 0, 1, 70, 1) catch unreachable;
}

/// Setup from an epoch's block proofs: the shared shape (the leaves of every trace size present, the
/// node) and the identities.
pub fn setup(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, airs: *const [bs.N_COMP]ir.Air, files: []const PF.File, bfri: FriConfigV2) !struct { shape: br.Shape, vk: Vk } {
    var first: [25]?usize = @splat(null);
    for (files, 0..) |f, i| {
        if (f.log_size >= 25) return error.LogSizeOutOfRange;
        if (first[f.log_size] == null) first[f.log_size] = i;
    }
    var start: ?ComponentSizes = null;
    for (first) |fi| if (fi) |i| {
        var ctx = try br.leafCircuitOf(gpa, a, airs, &files[i], bfri);
        defer ctx.deinit();
        const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        start = if (start) |s| s.elementwiseMax(sz) else sz;
    };
    const fri = circuitFri();
    var shape = try br.Shape.init(gpa, &tables.table, start orelse return error.NoBlocks, fri);
    errdefer shape.deinit(gpa);
    var vk: Vk = .{ .fri = fri, .trace_log = 0, .leaf = @splat(null), .node = undefined };
    for (first, 0..) |fi, log| if (fi) |i| {
        var ctx = try br.leafCircuitOf(gpa, a, airs, &files[i], bfri);
        defer ctx.deinit();
        const r = try identityOf(gpa, QM31, &ctx, shape.target, fri.log_blowup_factor);
        vk.leaf[log] = r.id;
        vk.trace_log = r.trace_log;
    };
    var topo = try br.topology(gpa, &tables.table, &shape.shared);
    defer topo.deinit();
    const r = try identityOf(gpa, circuit.builder.NoValue, &topo, shape.target, fri.log_blowup_factor);
    if (r.trace_log != vk.trace_log) return error.ShapeMismatch;
    vk.node = r.id;
    return .{ .shape = shape, .vk = vk };
}

/// Proves the aligned subtree of `2^k` blocks starting at `files[i]`.
pub fn proveSubtree(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const br.Shape, airs: *const [bs.N_COMP]ir.Air, files: []const PF.File, i: usize, k: u32, bfri: FriConfigV2, progress: *usize) !br.Proved {
    if (k == 0) {
        const p = try br.proveLeaf(gpa, a, tables, shape, airs, &files[i], bfri);
        progress.* += 1;
        if (progress.* % 10 == 0) std.debug.print("  {d} leaves proved\n", .{progress.*});
        return p;
    }
    var l = try proveSubtree(gpa, a, tables, shape, airs, files, i, k - 1, bfri, progress);
    defer l.proof.deinit();
    var r = try proveSubtree(gpa, a, tables, shape, airs, files, i + (@as(usize, 1) << @intCast(k - 1)), k - 1, bfri, progress);
    defer r.proof.deinit();
    return br.proveNode(gpa, a, tables, shape, &l, &r);
}

/// A forest root: its subtree, its proof, and its block-hash root's path in the chain's header tree.
pub const Root = struct { x: u32, k: u32, proved: br.Proved, path: []const HT.Step };

pub const Forest = struct {
    from: u32,
    to: u32,
    /// Each block's trace log size (the leaf identities the keys commit to).
    logs: []const u8,
    roots: []Root,

    pub fn encode(self: *const Forest, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, FOREST_MAGIC);
        try e.int(u32, store.VERSION);
        try e.int(u32, self.from);
        try e.int(u32, self.to);
        try e.blob(self.logs);
        try e.int(u32, @intCast(self.roots.len));
        for (self.roots) |*r| {
            try e.int(u32, r.x);
            try e.int(u32, r.k);
            try e.int(u32, @intCast(r.path.len));
            for (r.path) |s| {
                try e.words(&s.sibling);
                try e.int(u8, @intFromBool(s.left));
            }
            try store.encodeCircuit(&e, &r.proved.proof, r.proved.key, &r.proved.sum);
        }
        return store.seal(&e);
    }

    pub fn decode(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !Forest {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(FOREST_MAGIC);
        var f: Forest = undefined;
        f.from = try d.int(u32);
        f.to = try d.int(u32);
        f.logs = try a.dupe(u8, try d.blob());
        const n = try d.int(u32);
        if (n > 64) return error.TooManyRoots;
        const roots = try a.alloc(Root, n);
        for (roots) |*r| {
            r.x = try d.int(u32);
            r.k = try d.int(u32);
            const steps = try a.alloc(HT.Step, try d.int(u32));
            for (steps) |*s| {
                s.sibling = try d.words(8);
                s.left = switch (try d.int(u8)) {
                    0 => false,
                    1 => true,
                    else => return error.BadStep,
                };
            }
            r.path = steps;
            const c = try store.decodeCircuit(gpa, a, &d, &r.proved.sum);
            r.proved.proof = c.proof;
            r.proved.key = c.key;
        }
        f.roots = roots;
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return f;
    }
};

/// Proves the forest of blocks `files` (heights `from …`); `leaves` are the chain's block hashes.
pub fn proveForest(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const br.Shape, airs: *const [bs.N_COMP]ir.Air, files: []const PF.File, from: u32, bfri: FriConfigV2, leaves: []const HT.Words) !Forest {
    var sizes_buf: [64]u8 = undefined;
    const sizes = EP.alignedSizes(from, files.len, &sizes_buf);
    const roots = try a.alloc(Root, sizes.len);
    const logs = try a.alloc(u8, files.len);
    for (logs, files) |*l, f| l.* = @intCast(f.log_size);
    var at: usize = 0;
    var progress: usize = 0;
    for (sizes, roots) |k, *r| {
        const x: u32 = from + @as(u32, @intCast(at));
        const full = try HT.inclusionProof(a, leaves, x);
        r.* = .{ .x = x, .k = k, .proved = try proveSubtree(gpa, a, tables, shape, airs, files, at, k, bfri, &progress), .path = full[k..] };
        std.debug.print("subtree {d}..{d} proved\n", .{ x, x + (@as(u32, 1) << @intCast(k)) - 1 });
        at += @as(usize, 1) << @intCast(k);
    }
    return .{ .from = from, .to = from + @as(u32, @intCast(files.len)) - 1, .logs = logs, .roots = roots };
}

/// The expected circuit hash and key of the aligned subtree of `2^k` blocks from index `i`.
fn expected(vk: *const Vk, logs: []const u8, i: usize, k: u32) !struct { hash: [8]u32, key: leaf.Key } {
    if (k == 0) {
        if (i >= logs.len or logs[i] >= 25) return error.BadLogs;
        const id = vk.leaf[logs[i]] orelse return error.LeafSizeNotSetUp;
        return .{ .hash = id.hash, .key = leaf.zero_key };
    }
    const l = try expected(vk, logs, i, k - 1);
    const r = try expected(vk, logs, i + (@as(usize, 1) << @intCast(k - 1)), k - 1);
    return .{ .hash = vk.node.hash, .key = node.nodeKey(l.hash, l.key, r.hash, r.key) };
}

fn words(s: []const M31, at: usize) HT.Words {
    var w: HT.Words = undefined;
    for (&w, 0..) |*x, i| x.* = s[at + 2 * i].toU32() | (s[at + 2 * i + 1].toU32() << 16);
    return w;
}

fn qm(s: []const M31, at: usize) QM31 {
    return QM31.fromM31(s[at], s[at + 1], s[at + 2], s[at + 3]);
}

pub const Verified = struct { sum: QM31, nin: u64, challenge: @import("../block/coin.zig").Challenge };

/// **The outer verifier of an epoch's block forest.** `n_headers`, `t`: the verified chain's length and
/// header-tree root; `prev`, `fin`: the initial set's digest (an epoch from a previous set) and the
/// final set's. Checks every root's identity, key, proof and range; that all share the challenge the
/// seed over their seed subtrees gives; and that each block-hash subtree is the chain's. Returns the
/// summed partial sum and input count, and the challenge, for the balance check.
pub fn verifyForest(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, f: *const Forest, n_headers: usize, t: HT.Words, prev: ?[32]u8, fin: [32]u8) !Verified {
    if (f.to < f.from) return error.EmptyEpoch;
    const nb: usize = f.to - f.from + 1;
    if (f.logs.len != nb) return error.BadLogs;
    if (f.to >= n_headers) return error.BeyondChain;
    var sizes_buf: [64]u8 = undefined;
    const sizes = EP.alignedSizes(f.from, nb, &sizes_buf);
    if (sizes.len != f.roots.len) return error.WrongForest;
    const pcs = PcsConfigV2.fromFriAndTraceSize(vk.fri, vk.trace_log);
    var subroots: [64]EP.SubRoot = undefined;
    var at: usize = 0;
    var total = QM31.zero();
    var nin: u64 = 0;
    for (sizes, f.roots, 0..) |k, *r, idx| {
        const x: u32 = f.from + @as(u32, @intCast(at));
        if (r.x != x or r.k != k) return error.WrongForest;
        const want = try expected(vk, f.logs, at, k);
        const id = if (k == 0) (vk.leaf[f.logs[at]] orelse return error.LeafSizeNotSetUp) else vk.node;
        const p = &r.proved;
        if (!std.mem.eql(u32, &p.proof.request.preprocessed_root, &id.root)) return error.WrongCircuit;
        if (!std.mem.eql(u32, &p.proof.circuit_hash, &want.hash)) return error.WrongCircuit;
        if (!std.meta.eql(p.proof.request.pcs_config, pcs)) return error.ConfigNotPinned;
        const out = try leaf.verifyCircuit(gpa, tables, &p.proof);
        if (!std.mem.eql(u32, &out, &leaf.pubsDigest(want.key, &p.sum))) return error.WrongDigest;
        // The range.
        if (p.sum[0].toU32() != x or p.sum[1].toU32() != (@as(u32, 1) << @intCast(k))) return error.WrongRange;
        // One challenge.
        if (idx > 0) for (7..19) |i| if (!p.sum[i].eql(f.roots[0].proved.sum[i])) return error.ChallengeMismatch;
        subroots[idx] = .{ .x = x, .k = k, .root = words(&p.sum, 35) };
        // The block hashes are the chain's.
        const sides = try HT.inclusionSides(a, x, n_headers);
        if (sides.len != k + r.path.len) return error.BadPath;
        for (sides[0..k]) |s| if (s) return error.BadPath;
        for (sides[k..], r.path) |s, st| if (s != st.left) return error.BadPath;
        if (!HT.verifyInclusion(words(&p.sum, 19), r.path, t)) return error.HashesNotTheChain;
        total = total.add(qm(&p.sum, 2));
        nin += p.sum[6].toU32();
        at += @as(usize, 1) << @intCast(k);
    }
    const ch = EP.challenge(EP.seedOfRoots(f.from, f.to, prev, fin, subroots[0..sizes.len]));
    const s0 = &f.roots[0].proved.sum;
    if (!qm(s0, 7).eql(ch.gamma) or !qm(s0, 11).eql(ch.z) or !qm(s0, 15).eql(ch.alpha[1])) return error.ChallengeMismatch;
    return .{ .sum = total, .nin = nin, .challenge = ch };
}
