//! BLOCK-REC with wide nodes and per-level shapes (docs/design/block-rec.md § Wide nodes): an epoch's
//! block proofs as a forest of recursion trees, one per aligned perfect subtree of the seed v3
//! decomposition (`epoch.alignedSizes`), as `block_forest.zig` does with binary nodes at one shared
//! shape. Here:
//!
//! - **Leaves** are block leaves (`block_rec.leafCircuitOf`) padded to the leaf level's size only.
//! - **Nodes** are wide nodes (`block_node_k`, Lean `blockNodeK a`) of `2^a` children. In the aligned
//!   subtree of `2^k` blocks the top node has `a = topArity(k)` (1 to 3), its children are the aligned
//!   subtrees of `2^(k−a)` blocks, so every node below a top is 8-wide.
//! - **Two node circuits per arity** (`Kind`): over leaves (its hooks verify leaf-shaped proofs) and
//!   over nodes (node-shaped). All nodes share one padded size, the fixpoint of every node variant's
//!   topology. Their identities differ, and the key carries each child's circuit hash, so the outer
//!   verifier expects a variant per level from the subtree's size alone (Lean: `TreeK` with the node
//!   hash indexed by arity and kind).
//!
//! Circuits are proved at FRI fold 4, last layer 0 (short last rounds: stwo-zig's remainder fold,
//! which the CPU, native, in-circuit and CUDA provers all accept since `aacbb85cb`).
//!
//! **Proving** (`proveForest`) walks each subtree bottom-up through a `Prover` (the CPU here,
//! `src/gpu/cuda/epoch_tree.zig` on a GPU), writing every proof to `<dir>/tree/<k>-<x>.sbproof` and
//! reusing those already there (a stopped run resumes). **Verifying** (`verifyForest`): per root, the
//! pinned identity and the key expected from the blocks' size keys, the circuit proof, its range; the
//! challenge from the seed over the roots' seed subtrees and both sets' digests; each block-hash
//! subtree against the chain's `T`; the caller checks the balance against the final set.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const leaf = @import("leaf.zig");
const store = @import("store.zig");
const br = @import("block_rec.zig");
const wk = @import("block_node_k.zig");
const BF = @import("block_forest.zig");
const HT = @import("../btc/header_tree.zig");
const ir = @import("../air/ir.zig");
const bs = @import("../block/system.zig");
const PF = @import("../block/proof_file.zig");
const EP = @import("../block/epoch.zig");

const finalize = circuit.common.finalize;
const multiverifier = circuit.statements.multiverifier;
const Context = circuit.builder.Context;
const NoValue = circuit.builder.NoValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const ComponentSizes = leaf.ComponentSizes;
const Id = BF.Id;

pub const VK_MAGIC = "SBTREEVK";
pub const FOREST_MAGIC = "SBFORSTK";

/// The widest node: `2^MAX_A` children.
pub const MAX_A = 3;

/// The circuits' FRI configuration: 70 queries, 26 PoW bits, blowup 2, fold 4, last layer 0.
pub fn circuitFri() FriConfigV2 {
    return FriConfigV2.init(26, 0, 1, 70, 4) catch unreachable;
}

/// The arity (log) of the top node of an aligned subtree of `2^k` blocks, `k ≥ 1`: 8-wide nodes below,
/// the remainder of `k` at the top.
pub fn topArity(k: u32) u32 {
    std.debug.assert(k >= 1);
    return (k - 1) % MAX_A + 1;
}

/// What a node's children are.
pub const Kind = enum(u1) { over_leaves = 0, over_nodes = 1 };

/// The kind of the top node of the subtree of `2^k` blocks.
pub fn kindOf(k: u32) Kind {
    return if (k == topArity(k)) .over_leaves else .over_nodes;
}

/// The per-level shapes: each level's padded size (`target`) and the verifier configuration a node
/// uses for children of that level (`shared`).
pub const Shapes = struct {
    leaf: br.Shape,
    node: br.Shape,

    /// From the leaves' common size (the elementwise maximum of the epoch's leaf circuits): the node
    /// size is the fixpoint of every node variant's topology.
    pub fn init(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, leaf_start: ComponentSizes, fri: FriConfigV2) !Shapes {
        var lshape: br.Shape = .{ .target = leaf_start, .shared = try multiverifier.foldSharedConfig(gpa, leaf_start, fri), .fri = fri };
        errdefer lshape.deinit(gpa);
        var target: ?ComponentSizes = null;
        for (1..MAX_A + 1) |a| {
            var ctx = try wk.topology(gpa, table, @intCast(a), &lshape.shared);
            defer ctx.deinit();
            const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
            target = if (target) |t| t.elementwiseMax(sz) else sz;
        }
        var t = target.?;
        while (true) {
            var shared = try multiverifier.foldSharedConfig(gpa, t, fri);
            errdefer shared.deinit(gpa);
            var grown = t;
            for (1..MAX_A + 1) |a| {
                var ctx = try wk.topology(gpa, table, @intCast(a), &shared);
                defer ctx.deinit();
                grown = grown.elementwiseMax(finalize.computePaddedSizes(.fromBuilder(&ctx.circuit)));
            }
            if (std.meta.eql(grown, t)) return .{ .leaf = lshape, .node = .{ .target = t, .shared = shared, .fri = fri } };
            shared.deinit(gpa);
            t = grown;
        }
    }

    pub fn deinit(self: *Shapes, gpa: std.mem.Allocator) void {
        self.leaf.deinit(gpa);
        self.node.deinit(gpa);
    }

    /// The view a node of `kind` is built and proved under: the node size, the children's verifier
    /// configuration. Borrowed: not to be deinitialized.
    pub fn nodeView(self: *const Shapes, kind: Kind) br.Shape {
        return .{ .target = self.node.target, .shared = if (kind == .over_leaves) self.leaf.shared else self.node.shared, .fri = self.node.fri };
    }
};

/// The tree's verifying key.
pub const Vk = struct {
    fri: FriConfigV2,
    leaf_log: u32,
    node_log: u32,
    /// The block leaf's identity per size key (`block_forest.sizeKey`; null: not set up).
    leaf: [256]?Id,
    /// The node identities by kind and arity (`node[kind][a − 1]`).
    node: [2][MAX_A]Id,

    pub fn leafFor(self: *const Vk, key: u8) !Id {
        if (!BF.keyOk(key)) return error.BadLogs;
        return self.leaf[key] orelse error.LeafSizeNotSetUp;
    }

    pub fn nodeFor(self: *const Vk, kind: Kind, a: u32) Id {
        return self.node[@intFromEnum(kind)][a - 1];
    }

    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, VK_MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.leaf_log);
        try e.int(u32, self.node_log);
        var n: u32 = 0;
        for (self.leaf) |l| n += @intFromBool(l != null);
        try e.int(u32, n);
        for (self.leaf, 0..) |l, key| if (l) |id| {
            try e.int(u8, @intCast(key));
            try e.words(&id.root);
            try e.words(&id.hash);
        };
        for (self.node) |row| for (row) |id| {
            try e.words(&id.root);
            try e.words(&id.hash);
        };
        return store.seal(&e);
    }

    pub fn decode(bytes: []const u8) !Vk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: Vk = undefined;
        vk.fri = try d.fri();
        vk.leaf_log = try d.int(u32);
        vk.node_log = try d.int(u32);
        vk.leaf = @splat(null);
        const n = try d.int(u32);
        if (n > 256) return error.BadVk;
        var last: ?u8 = null;
        for (0..n) |_| {
            const key = try d.int(u8);
            if (last) |l| if (key <= l) return error.BadVk;
            if (!BF.keyOk(key)) return error.BadVk;
            last = key;
            vk.leaf[key] = .{ .root = try d.words(8), .hash = try d.words(8) };
        }
        for (&vk.node) |*row| for (row) |*id| {
            id.* = .{ .root = try d.words(8), .hash = try d.words(8) };
        };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// The leaves' common size: the elementwise maximum of the leaf circuits of `firsts` (one block proof
/// per size key).
pub fn leafStart(gpa: std.mem.Allocator, a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, firsts: []const *const PF.File, bfri: FriConfigV2, roots: ?*PF.PreRoots) !ComponentSizes {
    if (firsts.len == 0) return error.NoBlocks;
    var start: ?ComponentSizes = null;
    for (firsts) |f| {
        if (!BF.keyOk(BF.sizeKey(f.log_size, f.profile))) return error.LogSizeOutOfRange;
        var ctx = try br.leafCircuitOfRoots(gpa, a, airs, f, bfri, roots);
        defer ctx.deinit();
        const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        start = if (start) |s| s.elementwiseMax(sz) else sz;
    }
    return start.?;
}

/// The identities under `shapes`: each size key's leaf (from its first block), each node variant.
pub fn identities(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, airs: *const [bs.N_COMP]ir.Air, firsts: []const *const PF.File, bfri: FriConfigV2, roots: ?*PF.PreRoots, shapes: *const Shapes) !Vk {
    const fri = shapes.node.fri;
    var vk: Vk = .{ .fri = fri, .leaf_log = 0, .node_log = 0, .leaf = @splat(null), .node = undefined };
    for (firsts) |f| {
        var ctx = try br.leafCircuitOfRoots(gpa, a, airs, f, bfri, roots);
        defer ctx.deinit();
        const r = try BF.identityOf(gpa, QM31, &ctx, shapes.leaf.target, fri.log_blowup_factor);
        vk.leaf[BF.sizeKey(f.log_size, f.profile)] = r.id;
        vk.leaf_log = r.trace_log;
    }
    for ([_]Kind{ .over_leaves, .over_nodes }) |kind| for (1..MAX_A + 1) |ar| {
        const view = shapes.nodeView(kind);
        var topo = try wk.topology(gpa, &tables.table, @intCast(ar), &view.shared);
        defer topo.deinit();
        const r = try BF.identityOf(gpa, NoValue, &topo, shapes.node.target, fri.log_blowup_factor);
        if (vk.node_log != 0 and r.trace_log != vk.node_log) return error.ShapeMismatch;
        vk.node_log = r.trace_log;
        vk.node[@intFromEnum(kind)][ar - 1] = r.id;
    };
    return vk;
}

/// Setup from one block proof per size key (`firsts`): the per-level shapes and the identities. A leaf
/// of another block whose topology differed from its key's first block would carry another circuit
/// hash and fail the keys, never pass.
pub fn setup(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, airs: *const [bs.N_COMP]ir.Air, firsts: []const *const PF.File, bfri: FriConfigV2, roots: ?*PF.PreRoots) !struct { shapes: Shapes, vk: Vk } {
    var shapes = try Shapes.init(gpa, &tables.table, try leafStart(gpa, a, airs, firsts, bfri, roots), circuitFri());
    errdefer shapes.deinit(gpa);
    return .{ .shapes = shapes, .vk = try identities(gpa, a, tables, airs, firsts, bfri, roots, &shapes) };
}

/// The expected circuit hash and key of the aligned subtree of `2^k` blocks from index `i`.
pub fn expected(vk: *const Vk, logs: []const u8, i: usize, k: u32) !struct { hash: [8]u32, key: leaf.Key } {
    if (k == 0) {
        if (i >= logs.len) return error.BadLogs;
        return .{ .hash = (try vk.leafFor(logs[i])).hash, .key = leaf.zero_key };
    }
    const ar = topArity(k);
    var hashes: [1 << MAX_A][8]u32 = undefined;
    var keys: [1 << MAX_A]leaf.Key = undefined;
    const n = @as(usize, 1) << @intCast(ar);
    for (0..n) |j| {
        const c = try expected(vk, logs, i + (j << @intCast(k - ar)), k - ar);
        hashes[j] = c.hash;
        keys[j] = c.key;
    }
    return .{ .hash = vk.nodeFor(kindOf(k), ar).hash, .key = wk.key(hashes[0..n], keys[0..n]) };
}

/// Proves block leaves and nodes. `CpuProver` here; the GPU's in `src/gpu/cuda/epoch_tree.zig`.
/// Both return proofs verified natively whose output digest is the native one.
pub const CpuProver = struct {
    gpa: std.mem.Allocator,
    tables: *const leaf.Tables,
    shapes: *const Shapes,
    airs: *const [bs.N_COMP]ir.Air,
    bfri: FriConfigV2,
    roots: ?*PF.PreRoots = null,

    pub fn proveLeaf(self: *CpuProver, a: std.mem.Allocator, f: *const PF.File) !br.Proved {
        var ctx = try br.leafCircuitOfRoots(self.gpa, a, self.airs, f, self.bfri, self.roots);
        defer ctx.deinit();
        var cp = try leaf.proveCircuit(self.gpa, a, &ctx, self.shapes.leaf.target, self.shapes.leaf.fri);
        errdefer cp.deinit();
        const p: br.Proved = .{ .proof = cp, .key = leaf.zero_key, .sum = br.leafSummary(&f.pubs) };
        const out = try leaf.verifyCircuit(self.gpa, self.tables, &cp);
        if (!std.mem.eql(u32, &out, &p.digest())) return error.LeafDigestMismatch;
        return p;
    }

    pub fn proveNode(self: *CpuProver, a: std.mem.Allocator, kind: Kind, ar: u32, children: []const *const br.Proved) !br.Proved {
        const view = self.shapes.nodeView(kind);
        return wk.prove(self.gpa, a, self.tables, ar, &view, children);
    }
};

/// Where the epoch's block proofs and tree proofs live: `<dir>/proofs/<h>.sbblock`,
/// `<dir>/tree/<k>-<x>.sbproof` (the aligned subtree of `2^k` blocks from height `x`).
pub const Dir = struct {
    dir: []const u8,

    pub fn blockPath(self: Dir, a: std.mem.Allocator, h: u32) ![]u8 {
        return std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ self.dir, h });
    }

    pub fn treePath(self: Dir, a: std.mem.Allocator, k: u32, x: u32) ![]u8 {
        return std.fmt.allocPrint(a, "{s}/tree/{d}-{d}.sbproof", .{ self.dir, k, x });
    }

    pub fn loadBlock(self: Dir, a: std.mem.Allocator, h: u32) !PF.File {
        return PF.decode(a, try store.readFile(a, try self.blockPath(a, h)));
    }
};

/// A block proof file's size key (`block_forest.sizeKey`) from its header, without decoding the proof.
pub fn sizeKeyOfFile(path: []const u8) !u8 {
    var file = try std.fs.cwd().openFile(path, .{});
    defer file.close();
    var head: [20]u8 = undefined;
    if (try file.readAll(&head) != head.len) return error.Truncated;
    if (!std.mem.eql(u8, head[0..8], PF.MAGIC)) return error.BadMagic;
    // As `proof_file.decode`: version 2 files are uniform and carry no profile.
    const version = std.mem.readInt(u32, head[8..12], .little);
    if (version != PF.VERSION and version != 2) return error.BadVersion;
    const log = std.mem.readInt(u32, head[12..16], .little);
    const profile: bs.Profile = if (version == 2) .uniform else std.meta.intToEnum(bs.Profile, std.mem.readInt(u32, head[16..20], .little)) catch return error.BadProfile;
    if (log >= 25) return error.LogSizeOutOfRange;
    return BF.sizeKey(log, profile);
}

/// The epoch's block size keys and one block proof per key (the first of each), for the setup.
pub fn epochKeys(a: std.mem.Allocator, dir: Dir, from: u32, nb: u32) !struct { logs: []u8, firsts: []*const PF.File } {
    const logs = try a.alloc(u8, nb);
    var first: [256]?u32 = @splat(null);
    for (logs, 0..) |*l, i| {
        const h = from + @as(u32, @intCast(i));
        l.* = try sizeKeyOfFile(try dir.blockPath(a, h));
        if (first[l.*] == null) first[l.*] = h;
    }
    var firsts: std.ArrayList(*const PF.File) = .empty;
    for (first) |fh| if (fh) |h| {
        const f = try a.create(PF.File);
        f.* = try dir.loadBlock(a, h);
        try firsts.append(a, f);
    };
    return .{ .logs = logs, .firsts = firsts.items };
}

/// The trace log of a padded size.
pub fn traceLogOf(target: ComponentSizes) !u32 {
    const layout = try circuit.common.preprocessed.ColumnLayout.fromComponentSizes(target);
    return layout.traceLogSize();
}

/// The tree VK at `<dir>/treevk.bin` if it is there and matches `shapes` (a resumed run), else
/// computed (`identities`) and written there.
pub fn loadOrSetupVk(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, airs: *const [bs.N_COMP]ir.Air, firsts: []const *const PF.File, bfri: FriConfigV2, roots: ?*PF.PreRoots, shapes: *const Shapes, dir: Dir) !Vk {
    const path = try std.fmt.allocPrint(a, "{s}/treevk.bin", .{dir.dir});
    if (store.readFile(a, path)) |bytes| {
        const vk = try Vk.decode(bytes);
        if (!std.meta.eql(vk.fri, shapes.node.fri) or vk.leaf_log != try traceLogOf(shapes.leaf.target) or vk.node_log != try traceLogOf(shapes.node.target)) return error.TreeVkMismatch;
        for (firsts) |f| _ = try vk.leafFor(BF.sizeKey(f.log_size, f.profile));
        std.debug.print("tree VK reused from {s}\n", .{path});
        return vk;
    } else |e| if (e != error.FileNotFound) return e;
    const vk = try identities(gpa, a, tables, airs, firsts, bfri, roots, shapes);
    try store.writeFileAtomic(path, try vk.encode(a));
    return vk;
}

const PROVED_MAGIC = "SBTPROOF";

pub fn encodeProved(a: std.mem.Allocator, p: *const br.Proved) ![]u8 {
    var e: store.Enc = .{ .a = a };
    try e.buf.appendSlice(a, PROVED_MAGIC);
    try e.int(u32, store.VERSION);
    try store.encodeCircuit(&e, &p.proof, p.key, &p.sum);
    return store.seal(&e);
}

pub fn decodeProved(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !br.Proved {
    var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
    try d.magic(PROVED_MAGIC);
    var p: br.Proved = undefined;
    const c = try store.decodeCircuit(gpa, a, &d, &p.sum);
    p.proof = c.proof;
    p.key = c.key;
    if (d.pos != d.bytes.len) return error.TrailingBytes;
    return p;
}

pub const Progress = struct {
    leaves: usize = 0,
    nodes: usize = 0,
    reused: usize = 0,
    timer: std.time.Timer,
    total_leaves: usize,

    fn tick(self: *Progress) void {
        const done = self.leaves + self.nodes;
        if (done % 50 == 0) std.debug.print("  {d} leaves, {d} nodes proved ({d} reused), {d:.0}s; {d} leaves in all\n", .{ self.leaves, self.nodes, self.reused, @as(f64, @floatFromInt(self.timer.read())) / 1e9, self.total_leaves });
    }
};

/// The proof of the aligned subtree of `2^k` blocks from height `x`: read from `<dir>/tree` when there,
/// else proved (children first) and written there. Allocations of the result use `a`.
pub fn proveSubtree(prover: anytype, gpa: std.mem.Allocator, a: std.mem.Allocator, dir: Dir, x: u32, k: u32, progress: *Progress) !br.Proved {
    const path = try dir.treePath(a, k, x);
    if (store.readFile(a, path)) |bytes| {
        progress.reused += 1;
        return decodeProved(gpa, a, bytes);
    } else |e| if (e != error.FileNotFound) return e;
    var p: br.Proved = undefined;
    if (k == 0) {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        const f = try dir.loadBlock(scratch.allocator(), x);
        if (f.pubs[2].toU32() != x) return error.WrongHeight;
        p = try prover.proveLeaf(a, &f);
        progress.leaves += 1;
    } else {
        const ar = topArity(k);
        const n = @as(usize, 1) << @intCast(ar);
        // The children live only until their node is proved.
        var kid_arena = std.heap.ArenaAllocator.init(gpa);
        defer kid_arena.deinit();
        var kids: [1 << MAX_A]br.Proved = undefined;
        var refs: [1 << MAX_A]*const br.Proved = undefined;
        var got: usize = 0;
        defer for (kids[0..got]) |*c| c.proof.deinit();
        for (0..n) |j| {
            kids[j] = try proveSubtree(prover, gpa, kid_arena.allocator(), dir, x + @as(u32, @intCast(j << @intCast(k - ar))), k - ar, progress);
            got += 1;
            refs[j] = &kids[j];
        }
        p = try prover.proveNode(a, kindOf(k), ar, refs[0..n]);
        progress.nodes += 1;
    }
    {
        var enc = std.heap.ArenaAllocator.init(gpa);
        defer enc.deinit();
        try store.writeFileAtomic(path, try encodeProved(enc.allocator(), &p));
    }
    progress.tick();
    return p;
}

/// One proof of the forest: the aligned subtree of `2^k` blocks from height `x`.
pub const Task = struct { k: u32, x: u32 };

/// Every proof of the forest of the `n` blocks from `from`, children before parents: by `k`
/// ascending (a child's `k` is below its parent's), then by height.
pub fn tasks(a: std.mem.Allocator, from: u32, n: usize) ![]Task {
    var list: std.ArrayList(Task) = .empty;
    var sizes_buf: [64]u8 = undefined;
    var at: u32 = from;
    for (EP.alignedSizes(from, n, &sizes_buf)) |k| {
        try collect(a, &list, at, k);
        at += @as(u32, 1) << @intCast(k);
    }
    std.mem.sort(Task, list.items, {}, struct {
        fn lt(_: void, l: Task, r: Task) bool {
            return l.k < r.k or (l.k == r.k and l.x < r.x);
        }
    }.lt);
    return list.items;
}

fn collect(a: std.mem.Allocator, list: *std.ArrayList(Task), x: u32, k: u32) !void {
    try list.append(a, .{ .k = k, .x = x });
    if (k == 0) return;
    const ar = topArity(k);
    for (0..@as(usize, 1) << @intCast(ar)) |j| try collect(a, list, x + @as(u32, @intCast(j << @intCast(k - ar))), k - ar);
}

/// A forest root: its subtree, its proof, and its block-hash root's path in the chain's header tree.
pub const Root = BF.Root;

pub const Forest = struct {
    from: u32,
    to: u32,
    /// Each block's size key (the leaf identities the keys commit to).
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

/// Proves (or resumes) the forest of the `n` blocks from height `from` in `dir`; `logs` are their size
/// keys, `leaves` the chain's block hashes.
pub fn proveForest(prover: anytype, gpa: std.mem.Allocator, a: std.mem.Allocator, dir: Dir, from: u32, logs: []const u8, leaves: []const HT.Words) !Forest {
    try std.fs.cwd().makePath(try std.fmt.allocPrint(a, "{s}/tree", .{dir.dir}));
    var sizes_buf: [64]u8 = undefined;
    const sizes = EP.alignedSizes(from, logs.len, &sizes_buf);
    const roots = try a.alloc(Root, sizes.len);
    var progress: Progress = .{ .timer = try std.time.Timer.start(), .total_leaves = logs.len };
    var at: usize = 0;
    for (sizes, roots) |k, *r| {
        const x: u32 = from + @as(u32, @intCast(at));
        const full = try HT.inclusionProof(a, leaves, x);
        r.* = .{ .x = x, .k = k, .proved = try proveSubtree(prover, gpa, a, dir, x, k, &progress), .path = full[k..] };
        std.debug.print("subtree {d}..{d} proved ({d:.0}s)\n", .{ x, x + (@as(u32, 1) << @intCast(k)) - 1, @as(f64, @floatFromInt(progress.timer.read())) / 1e9 });
        at += @as(usize, 1) << @intCast(k);
    }
    return .{ .from = from, .to = from + @as(u32, @intCast(logs.len)) - 1, .logs = logs, .roots = roots };
}

fn words(s: []const M31, at: usize) HT.Words {
    var w: HT.Words = undefined;
    for (&w, 0..) |*x, i| x.* = s[at + 2 * i].toU32() | (s[at + 2 * i + 1].toU32() << 16);
    return w;
}

fn qm(s: []const M31, at: usize) QM31 {
    return QM31.fromM31(s[at], s[at + 1], s[at + 2], s[at + 3]);
}

/// **The outer verifier of an epoch's block forest with wide nodes.** As `block_forest.verifyForest`:
/// `n_headers`, `t`, the verified chain's length and header-tree root; `prev`, `fin`, the initial and
/// final sets' digests. Checks every root's identity (leaf or node of the variant its size gives), key,
/// pinned configuration, proof and range; one challenge, the seed's over the roots' seed subtrees;
/// each block-hash subtree against `T`. Returns the summed partial sum, input count and challenge.
pub fn verifyForest(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, f: *const Forest, n_headers: usize, t: HT.Words, prev: ?[32]u8, fin: [32]u8) !BF.Verified {
    if (f.to < f.from) return error.EmptyEpoch;
    const nb: usize = f.to - f.from + 1;
    if (f.logs.len != nb) return error.BadLogs;
    if (f.to >= n_headers) return error.BeyondChain;
    if (!std.meta.eql(vk.fri, circuitFri())) return error.ConfigNotPinned;
    var sizes_buf: [64]u8 = undefined;
    const sizes = EP.alignedSizes(f.from, nb, &sizes_buf);
    if (sizes.len != f.roots.len) return error.WrongForest;
    var subroots: [64]EP.SubRoot = undefined;
    var at: usize = 0;
    var total = QM31.zero();
    var nin: u64 = 0;
    for (sizes, f.roots, 0..) |k, *r, idx| {
        const x: u32 = f.from + @as(u32, @intCast(at));
        if (r.x != x or r.k != k) return error.WrongForest;
        const want = try expected(vk, f.logs, at, k);
        const id = if (k == 0) try vk.leafFor(f.logs[at]) else vk.nodeFor(kindOf(k), topArity(k));
        const pcs = PcsConfigV2.fromFriAndTraceSize(vk.fri, if (k == 0) vk.leaf_log else vk.node_log);
        const p = &r.proved;
        if (!std.mem.eql(u32, &p.proof.request.preprocessed_root, &id.root)) return error.WrongCircuit;
        if (!std.mem.eql(u32, &p.proof.circuit_hash, &want.hash)) return error.WrongCircuit;
        if (!std.meta.eql(p.proof.request.pcs_config, pcs)) return error.ConfigNotPinned;
        const out = try leaf.verifyCircuit(gpa, tables, &p.proof);
        if (!std.mem.eql(u32, &out, &leaf.pubsDigest(want.key, &p.sum))) return error.WrongDigest;
        if (p.sum[0].toU32() != x or p.sum[1].toU32() != (@as(u32, 1) << @intCast(k))) return error.WrongRange;
        if (idx > 0) for (7..19) |i| if (!p.sum[i].eql(f.roots[0].proved.sum[i])) return error.ChallengeMismatch;
        subroots[idx] = .{ .x = x, .k = @intCast(k), .root = words(&p.sum, 35) };
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

test "tree layout: 8-wide below, the remainder at the top" {
    try std.testing.expectEqual(@as(u32, 1), topArity(1));
    try std.testing.expectEqual(@as(u32, 3), topArity(3));
    try std.testing.expectEqual(@as(u32, 1), topArity(4));
    try std.testing.expectEqual(@as(u32, 3), topArity(12));
    try std.testing.expectEqual(@as(u32, 2), topArity(11));
    try std.testing.expectEqual(Kind.over_leaves, kindOf(2));
    try std.testing.expectEqual(Kind.over_nodes, kindOf(4));
    try std.testing.expectEqual(Kind.over_nodes, kindOf(12));
}

test "tree tasks: children before parents, every subtree once" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const ts = try tasks(arena.allocator(), 935001, 10000);
    var leaves: usize = 0;
    for (ts, 0..) |t, i| {
        if (t.k == 0) leaves += 1;
        if (i > 0) try std.testing.expect(ts[i - 1].k <= t.k);
    }
    try std.testing.expectEqual(@as(usize, 10000), leaves);
    try std.testing.expectEqual(@as(usize, 10000 + 1432), ts.len);
}

test "tree VK round trip; expected keys fold as the wide nodes do" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var vk: Vk = .{ .fri = circuitFri(), .leaf_log = 22, .node_log = 24, .leaf = @splat(null), .node = undefined };
    for (&vk.node, 0..) |*row, kind| for (row, 0..) |*id, ar| {
        id.* = .{ .root = @splat(@intCast(100 + kind * 10 + ar)), .hash = @splat(@intCast(200 + kind * 10 + ar)) };
    };
    const t23 = BF.sizeKey(23, .tiered);
    const t12 = BF.sizeKey(12, .tiered);
    vk.leaf[t23] = .{ .root = @splat(1), .hash = @splat(2) };
    vk.leaf[t12] = .{ .root = @splat(3), .hash = @splat(4) };
    const back = try Vk.decode(try vk.encode(a));
    try std.testing.expect(std.meta.eql(back, vk));
    // 16 blocks: k = 4 is a 2-wide top (over_nodes) over two 8-wide nodes over leaves.
    var logs: [16]u8 = @splat(t23);
    logs[5] = t12;
    const lo = try expected(&vk, &logs, 0, 3);
    var hs: [8][8]u32 = undefined;
    var ks: [8]leaf.Key = undefined;
    for (0..8) |j| {
        hs[j] = (try vk.leafFor(logs[j])).hash;
        ks[j] = leaf.zero_key;
    }
    try std.testing.expectEqualSlices(u32, &wk.key(&hs, &ks), &lo.key);
    try std.testing.expectEqualSlices(u32, &vk.nodeFor(.over_leaves, 3).hash, &lo.hash);
    const hi = try expected(&vk, &logs, 8, 3);
    const top = try expected(&vk, &logs, 0, 4);
    try std.testing.expectEqualSlices(u32, &vk.nodeFor(.over_nodes, 1).hash, &top.hash);
    try std.testing.expectEqualSlices(u32, &wk.key(&.{ lo.hash, hi.hash }, &.{ lo.key, hi.key }), &top.key);
    // Another block's size changes the key; a size not set up is refused.
    logs[5] = t23;
    try std.testing.expect(!std.mem.eql(u32, &lo.key, &(try expected(&vk, &logs, 0, 3)).key));
    logs[5] = BF.sizeKey(13, .tiered);
    try std.testing.expectError(error.LeafSizeNotSetUp, expected(&vk, &logs, 0, 4));
}
