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

// ---------------------------------------------------------------------------------------------
// Shapes, the verifying key, the chain file and its verifier.

const finalize = circuit.common.finalize;
const ComponentSizes = finalize.ComponentSizes;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const BF = @import("block_forest.zig");
const BT = @import("block_tree.zig");
const br = @import("block_rec.zig");
const store = @import("store.zig");
const HT = @import("../btc/header_tree.zig");

/// The join's topology (no values) over children verified under `left` and `right`: its size, its
/// identity.
pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, v: Variant, left: *const multiverifier.SharedConfig, right: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const el = try stark_proof.emptyProof(arena.allocator(), left.proof_config);
    const er = try stark_proof.emptyProof(arena.allocator(), right.proof_config);
    const zero: [8]u32 = @splat(0);
    const root: Open = .{ .root = .{ .key = zero, .ep = .{ .from = 0, .to = 0, .prev = @splat(0), .fin = @splat(0) }, .rest = zero } };
    const lo: Open = if (v == .step) .{ .join = .{ .key = zero, .start = zero, .end = zero, .a = 0, .b = 0, .acc = zero } } else root;
    return buildCircuit(NoValue, gpa, table, v, .{ .proof = &el, .preprocessed_root = zero, .shared = left, .open = lo }, .{ .proof = &er, .preprocessed_root = zero, .shared = right, .open = root });
}

fn naturalOf(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, v: Variant, left: *const multiverifier.SharedConfig, right: *const multiverifier.SharedConfig) !ComponentSizes {
    var ctx = try topology(gpa, table, v, left, right);
    defer ctx.deinit();
    return finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
}

/// A chain's root shape: every epoch root is proved padded to it, so a join verifies any of them. The
/// elementwise maximum of the roots over `max_m` children (both variants) under each epoch's node
/// configuration (more children only add to a root). Fixed for the chain: a later epoch must fit it.
pub fn rootTarget(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, max_m: usize, node_shareds: []const *const multiverifier.SharedConfig) !ComponentSizes {
    var t: ?ComponentSizes = null;
    for (node_shareds) |sh| for ([_]bool{ false, true }) |prev| {
        const sz = try ER.naturalSize(gpa, table, max_m, prev, sh);
        t = if (t) |x| x.elementwiseMax(sz) else sz;
    };
    return t orelse error.NoEpochs;
}

/// The chain's shapes: the root shape (given) and the join shape, the fixpoint of the three variants
/// (a step verifies a join of its own shape).
pub const Shapes = struct {
    root: br.Shape,
    join: br.Shape,

    pub fn init(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, root_target: ComponentSizes, fri: FriConfigV2) !Shapes {
        var rs: br.Shape = .{ .target = root_target, .shared = try multiverifier.foldSharedConfig(gpa, root_target, fri), .fri = fri };
        errdefer rs.deinit(gpa);
        var t = (try naturalOf(gpa, table, .base_prev, &rs.shared, &rs.shared)).elementwiseMax(try naturalOf(gpa, table, .base_genesis, &rs.shared, &rs.shared));
        while (true) {
            var shared = try multiverifier.foldSharedConfig(gpa, t, fri);
            errdefer shared.deinit(gpa);
            const grown = t.elementwiseMax(try naturalOf(gpa, table, .step, &shared, &rs.shared));
            if (std.meta.eql(grown, t)) return .{ .root = rs, .join = .{ .target = t, .shared = shared, .fri = fri } };
            shared.deinit(gpa);
            t = grown;
        }
    }

    pub fn deinit(self: *Shapes, gpa: std.mem.Allocator) void {
        self.root.deinit(gpa);
        self.join.deinit(gpa);
    }

    /// The configuration a variant's left child verifies under.
    pub fn leftShared(self: *const Shapes, v: Variant) *const multiverifier.SharedConfig {
        return if (v == .step) &self.join.shared else &self.root.shared;
    }
};

/// The node shape an epoch's tree was built at, as its tree VK pins it: the over-nodes binary node's
/// circuit hash (the node circuit at its size).
pub fn nodeTag(tvk: *const BT.Vk) [8]u32 {
    return tvk.nodeFor(.over_nodes, 1).hash;
}

/// An epoch root's identity at the chain's root shape: for `m` children (`prev` variant) over trees of
/// node shape `node` (`nodeTag`), with the lift (a one-block root as a node) of that shape.
pub const RootEntry = struct { m: u32, prev: bool, node: [8]u32, lift: BF.Id, id: BF.Id };

pub const VK_MAGIC = "SBJOINVK";
pub const FILE_MAGIC = "SBEJOIN1";

/// **The chain's verifying key**: the configuration, the root and join sizes, the epoch roots'
/// identities at the root shape and the three join variants' at the join shape.
pub const Vk = struct {
    fri: FriConfigV2,
    root_log: u32,
    join_log: u32,
    roots: []const RootEntry,
    /// By `Variant`.
    join: [3]BF.Id,

    pub fn rootFor(self: *const Vk, m: usize, prev: bool, node: [8]u32) !RootEntry {
        for (self.roots) |e| if (e.m == m and e.prev == prev and std.mem.eql(u32, &e.node, &node)) return e;
        return error.RootNotSetUp;
    }

    pub fn joinFor(self: *const Vk, v: Variant) BF.Id {
        return self.join[@intFromEnum(v)];
    }

    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, VK_MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.root_log);
        try e.int(u32, self.join_log);
        try e.int(u32, @intCast(self.roots.len));
        for (self.roots) |r| {
            try e.int(u32, r.m);
            try e.int(u8, @intFromBool(r.prev));
            try e.words(&r.node);
            for ([_]BF.Id{ r.lift, r.id }) |id| {
                try e.words(&id.root);
                try e.words(&id.hash);
            }
        }
        for (self.join) |id| {
            try e.words(&id.root);
            try e.words(&id.hash);
        }
        return store.seal(&e);
    }

    pub fn decode(a: std.mem.Allocator, bytes: []const u8) !Vk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: Vk = undefined;
        vk.fri = try d.fri();
        vk.root_log = try d.int(u32);
        vk.join_log = try d.int(u32);
        const n = try d.int(u32);
        if (n > 1024) return error.BadVk;
        const roots = try a.alloc(RootEntry, n);
        for (roots) |*r| {
            r.m = try d.int(u32);
            r.prev = switch (try d.int(u8)) {
                0 => false,
                1 => true,
                else => return error.BadVk,
            };
            r.node = try d.words(8);
            r.lift = .{ .root = try d.words(8), .hash = try d.words(8) };
            r.id = .{ .root = try d.words(8), .hash = try d.words(8) };
        }
        vk.roots = roots;
        for (&vk.join) |*id| id.* = .{ .root = try d.words(8), .hash = try d.words(8) };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// An epoch as the chain's setup sees it: its tree shapes and VK, its root's child count and variant.
pub const EpochSetup = struct { tshapes: *const BT.Shapes, tvk: *const BT.Vk, m: usize, prev: bool };

/// The chain's VK for `epochs` (each distinct root identity once) under `shapes`.
pub fn setupVk(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shapes: *const Shapes, epochs: []const EpochSetup) !Vk {
    const fri = shapes.join.fri;
    var roots: std.ArrayList(RootEntry) = .empty;
    var root_log: u32 = 0;
    for (epochs) |ep| {
        const tag = nodeTag(ep.tvk);
        if (for (roots.items) |r| {
            if (r.m == ep.m and r.prev == ep.prev and std.mem.eql(u32, &r.node, &tag)) break true;
        } else false) continue;
        const lview = ep.tshapes.nodeView(.over_leaves);
        var ltopo = try wk.topology(gpa, &tables.table, 0, &lview.shared);
        defer ltopo.deinit();
        const lift = try BF.identityOf(gpa, NoValue, &ltopo, ep.tshapes.node.target, fri.log_blowup_factor);
        var rtopo = try ER.topology(gpa, &tables.table, ep.m, ep.prev, &ep.tshapes.node.shared);
        defer rtopo.deinit();
        const id = try BF.identityOf(gpa, NoValue, &rtopo, shapes.root.target, fri.log_blowup_factor);
        root_log = id.trace_log;
        try roots.append(a, .{ .m = @intCast(ep.m), .prev = ep.prev, .node = tag, .lift = lift.id, .id = id.id });
    }
    var vk: Vk = .{ .fri = fri, .root_log = root_log, .join_log = undefined, .roots = roots.items, .join = undefined };
    for ([_]Variant{ .base_prev, .base_genesis, .step }) |v| {
        var topo = try topology(gpa, &tables.table, v, shapes.leftShared(v), &shapes.root.shared);
        defer topo.deinit();
        const id = try BF.identityOf(gpa, NoValue, &topo, shapes.join.target, fri.log_blowup_factor);
        vk.join[@intFromEnum(v)] = id.id;
        vk.join_log = id.trace_log;
    }
    return vk;
}

/// **A chain proof**: every epoch root's public part, in chain order, and the last join's proof (its
/// left child the chain up to the last epoch, its right child the last epoch's root).
pub const ChainFile = struct {
    heads: []ER.Head,
    proof: leaf.CircuitProof,

    pub fn encode(self: *const ChainFile, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, FILE_MAGIC);
        try e.int(u32, store.VERSION);
        try e.int(u32, @intCast(self.heads.len));
        for (self.heads) |*h| try h.encode(&e);
        try store.encodeCircuit(&e, &self.proof, leaf.zero_key, &.{});
        return store.seal(&e);
    }

    pub fn decode(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !ChainFile {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(FILE_MAGIC);
        const n = try d.int(u32);
        if (n < 2 or n > 1 << 16) return error.BadFile;
        const heads = try a.alloc(ER.Head, n);
        for (heads) |*h| h.* = try ER.Head.decode(a, &d);
        var none: [0]M31 = .{};
        const c = try store.decodeCircuit(gpa, a, &d, &none);
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return .{ .heads = heads, .proof = c.proof };
    }
};

/// The variant joining epoch `i ≥ 1` onto the chain before it.
pub fn variantAt(i: usize, first: ER.Epoch) Variant {
    if (i > 1) return .step;
    return if (first.prev != null) .base_prev else .base_genesis;
}

/// An epoch as the verifier takes it: its tree VK and its range and set digests (from its sets).
pub const EpochIn = struct { tvk: *const BT.Vk, ep: ER.Epoch };

/// **The chain verifier.** Each epoch's public part opened (`ER.openHead`: its children, identities and
/// block-hash roots against the chain's `T`), the joins replayed natively (the links: heights and set
/// digests; the keys from the pinned root and join identities; `acc`), and the one proof, the last
/// join's, checked against its pinned identity with the replayed output digest. Returns each epoch's
/// values for its balance against its sets.
pub fn verifyChain(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, f: *const ChainFile, epochs: []const EpochIn, n_headers: usize, t: HT.Words) ![]ER.Verified {
    if (f.heads.len != epochs.len or epochs.len < 2) return error.WrongEpochs;
    if (!std.meta.eql(vk.fri, BT.circuitFri())) return error.ConfigNotPinned;
    const out = try a.alloc(ER.Verified, epochs.len);
    var left: Open = undefined;
    var lh: [8]u32 = undefined;
    var last: Variant = undefined;
    for (f.heads, epochs, out, 0..) |*h, e, *ver, i| {
        if (!std.meta.eql(e.tvk.fri, vk.fri)) return error.ConfigNotPinned;
        const entry = try vk.rootFor(h.children.len, e.ep.prev != null, nodeTag(e.tvk));
        const o = try ER.openHead(a, e.tvk, entry.lift.hash, h, e.ep, n_headers, t);
        ver.* = o.verified;
        const r: RootOpen = .{ .key = o.key, .ep = e.ep, .rest = o.rest };
        if (i == 0) {
            left = .{ .root = r };
            lh = entry.id.hash;
            continue;
        }
        last = variantAt(i, epochs[0].ep);
        // Not `left = .{ .join = expected(&left, …) }`: the result location aliases the argument.
        const jo = try expected(&left, lh, &r, entry.id.hash);
        left = .{ .join = jo };
        lh = vk.joinFor(last).hash;
    }
    const id = vk.joinFor(last);
    const p = &f.proof;
    if (!std.mem.eql(u32, &p.request.preprocessed_root, &id.root)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &p.circuit_hash, &id.hash)) return error.WrongCircuit;
    if (!std.meta.eql(p.request.pcs_config, PcsConfigV2.fromFriAndTraceSize(vk.fri, vk.join_log))) return error.ConfigNotPinned;
    const got = try leaf.verifyCircuit(gpa, tables, p);
    if (!std.mem.eql(u32, &got, &joinOut(&left.join))) return error.WrongDigest;
    return out;
}
