//! **Proof store (PROOF-STORE, D-036; docs/design/proof-store.md).** A chain proof as a file that
//! verifies standalone and extends at the tip.
//!
//! - **VK** (`setup`): the frozen node shape (it covers leaves of every segment log size, so an
//!   extension never changes the node circuit), the node identity with its pinned request (PCS
//!   config and preprocessed columns), and one leaf identity per segment log size.
//! - **Chain file**: the segment plan, the MMR peaks (what an extension pushes onto), the bagged
//!   root, the inclusion path of leaf 0 in `T` (Bitcoin's genesis hash), provenance, and a SHA-256
//!   trailer (corruption only; soundness comes from `verifyChain`).
//! - **Prover**: proves aligned segments, pushes them onto the peaks (`HT.pushPeak`), bags.
//!
//! Writes are atomic (temporary file, sync, rename).

const std = @import("std");
const core = @import("stwo_core");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const wire = @import("stwo_circuit_recursion_wire");
const leaf = @import("leaf.zig");
const node = @import("node.zig");
const H = @import("../btc/header_chain.zig");
const HT = @import("../btc/header_tree.zig");
const segments = @import("../btc/segments.zig");

const M31 = core.fields.m31.M31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const ComponentSizes = leaf.ComponentSizes;
const Proved = node.Proved;

pub const CHAIN_MAGIC = "SBCHAIN\x00";
pub const VK_MAGIC = "SBCHVK\x00\x00";
pub const VERSION: u32 = 1;

/// Bitcoin's genesis block hash `000000000019d6…8ce26f`, as the tree's leaves encode it
/// (`HT.blockHash`: SHA256d in internal byte order, read as big-endian words).
pub const GENESIS_HASH: HT.Words = .{ 0x6fe28c0a, 0xb6f1b372, 0xc1a6a246, 0xae63f74f, 0x931e8365, 0xe15a089c, 0x68d61900, 0x00000000 };

// ---------------------------------------------------------------------------------------------
// Binary encoding: little-endian integers, length-prefixed blobs.

pub const Enc = struct {
    a: std.mem.Allocator,
    buf: std.ArrayList(u8) = .empty,

    pub fn int(self: *Enc, comptime T: type, v: T) !void {
        var b: [@sizeOf(T)]u8 = undefined;
        std.mem.writeInt(T, &b, v, .little);
        try self.buf.appendSlice(self.a, &b);
    }
    pub fn blob(self: *Enc, b: []const u8) !void {
        try self.int(u64, b.len);
        try self.buf.appendSlice(self.a, b);
    }
    pub fn words(self: *Enc, ws: []const u32) !void {
        for (ws) |w| try self.int(u32, w);
    }
    pub fn fri(self: *Enc, f: FriConfigV2) !void {
        inline for (.{ "pow_bits", "log_blowup_factor", "log_last_layer_degree_bound", "n_queries", "fold_step" }) |name|
            try self.int(u32, @field(f, name));
    }
};

pub const Dec = struct {
    bytes: []const u8,
    pos: usize = 0,

    pub fn take(self: *Dec, n: u64) ![]const u8 {
        if (n > self.bytes.len - self.pos) return error.Truncated;
        const s = self.bytes[self.pos..][0..@intCast(n)];
        self.pos += @intCast(n);
        return s;
    }
    pub fn int(self: *Dec, comptime T: type) !T {
        return std.mem.readInt(T, (try self.take(@sizeOf(T)))[0..@sizeOf(T)], .little);
    }
    pub fn blob(self: *Dec) ![]const u8 {
        return self.take(try self.int(u64));
    }
    pub fn words(self: *Dec, comptime n: usize) ![n]u32 {
        var out: [n]u32 = undefined;
        for (&out) |*w| w.* = try self.int(u32);
        return out;
    }
    pub fn fri(self: *Dec) !FriConfigV2 {
        var f: FriConfigV2 = undefined;
        inline for (.{ "pow_bits", "log_blowup_factor", "log_last_layer_degree_bound", "n_queries", "fold_step" }) |name|
            @field(f, name) = try self.int(u32);
        return f;
    }
    pub fn magic(self: *Dec, comptime m: []const u8) !void {
        if (!std.mem.eql(u8, try self.take(m.len), m)) return error.BadMagic;
        if (try self.int(u32) != VERSION) return error.UnsupportedVersion;
    }
};

fn sha256(bytes: []const u8) [32]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return d;
}

/// Appends the SHA-256 trailer and returns the file bytes.
pub fn seal(e: *Enc) ![]u8 {
    const d = sha256(e.buf.items);
    try e.buf.appendSlice(e.a, &d);
    return e.buf.items;
}

/// Checks and strips the SHA-256 trailer.
pub fn unseal(bytes: []const u8) ![]const u8 {
    if (bytes.len < 32) return error.Truncated;
    const body = bytes[0 .. bytes.len - 32];
    if (!std.mem.eql(u8, &sha256(body), bytes[body.len..])) return error.ChecksumMismatch;
    return body;
}

/// Writes `bytes` to `path` atomically: a temporary file next to it, synced, then renamed.
pub fn writeFileAtomic(path: []const u8, bytes: []const u8) !void {
    var buf: [std.fs.max_path_bytes]u8 = undefined;
    const tmp = try std.fmt.bufPrint(&buf, "{s}.tmp", .{path});
    {
        const f = try std.fs.cwd().createFile(tmp, .{ .truncate = true });
        defer f.close();
        try f.writeAll(bytes);
        try f.sync();
    }
    try std.fs.cwd().rename(tmp, path);
}

pub fn readFile(a: std.mem.Allocator, path: []const u8) ![]u8 {
    return std.fs.cwd().readFileAlloc(a, path, 1 << 34);
}

// ---------------------------------------------------------------------------------------------
// The verifying key.

pub const LeafId = struct { root: [8]u32, hash: [8]u32 };

pub const Vk = struct {
    fri: FriConfigV2,
    max_log: u32,
    /// The frozen shape's target (the prover rebuilds the shape from it).
    target: ComponentSizes,
    node: node.Identity,
    /// Leaf identities by segment log size: index `log − HT.MIN_SEG_LOG`, up to `max_log`.
    leaves: []const LeafId,

    pub fn leafId(self: *const Vk, log: u32) LeafId {
        return self.leaves[log - HT.MIN_SEG_LOG];
    }

    fn encodeBody(self: *const Vk, e: *Enc) !void {
        try e.buf.appendSlice(e.a, VK_MAGIC);
        try e.int(u32, VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.max_log);
        inline for (std.meta.fields(ComponentSizes)) |f| try e.int(u64, @field(self.target, f.name));
        try e.words(&self.node.root);
        try e.words(&self.node.hash);
        try e.fri(self.node.pcs.fri_config);
        try e.int(u32, self.node.pcs.trace_lifting_log_size);
        try e.int(u32, self.node.pcs.preprocessed_lifting_log_size);
        try e.int(u32, @intCast(self.node.columns.len));
        for (self.node.columns) |c| {
            try e.blob(c.id);
            try e.int(u32, c.log_size);
        }
        try e.int(u32, @intCast(self.leaves.len));
        for (self.leaves) |l| {
            try e.words(&l.root);
            try e.words(&l.hash);
        }
    }

    /// The VK's file bytes (with trailer).
    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: Enc = .{ .a = a };
        try self.encodeBody(&e);
        return seal(&e);
    }

    /// Blake2s-256 of the VK's encoding (without trailer), as 8 words: what a chain file names.
    pub fn digest(self: *const Vk, a: std.mem.Allocator) ![8]u32 {
        var e: Enc = .{ .a = a };
        defer e.buf.deinit(a);
        try self.encodeBody(&e);
        var d: [32]u8 = undefined;
        std.crypto.hash.blake2.Blake2s256.hash(e.buf.items, &d, .{});
        var out: [8]u32 = undefined;
        for (&out, 0..) |*w, i| w.* = std.mem.readInt(u32, d[4 * i ..][0..4], .little);
        return out;
    }

    /// Parses VK file bytes; slices live in `a`.
    pub fn decode(a: std.mem.Allocator, bytes: []const u8) !Vk {
        var d: Dec = .{ .bytes = try unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: Vk = undefined;
        vk.fri = try d.fri();
        vk.max_log = try d.int(u32);
        if (vk.max_log < HT.MIN_SEG_LOG or vk.max_log > HT.MAX_SEG_LOG) return error.BadVk;
        inline for (std.meta.fields(ComponentSizes)) |f| @field(vk.target, f.name) = @intCast(try d.int(u64));
        vk.node.root = try d.words(8);
        vk.node.hash = try d.words(8);
        vk.node.pcs.fri_config = try d.fri();
        vk.node.pcs.trace_lifting_log_size = try d.int(u32);
        vk.node.pcs.preprocessed_lifting_log_size = try d.int(u32);
        const columns = try a.alloc(leaf.Column, try d.int(u32));
        for (columns) |*c| c.* = .{ .id = try a.dupe(u8, try d.blob()), .log_size = try d.int(u32) };
        vk.node.columns = columns;
        const leaves = try a.alloc(LeafId, try d.int(u32));
        if (leaves.len != vk.max_log - HT.MIN_SEG_LOG + 1) return error.BadVk;
        for (leaves) |*l| l.* = .{ .root = try d.words(8), .hash = try d.words(8) };
        vk.leaves = leaves;
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// **Setup**: the frozen shape (covering a genesis leaf of every segment log size in
/// `[MIN_SEG_LOG, max_log]`) and the VK. `genesis` holds at least `2^(max_log − 8)` headers from
/// height 0. Identity slices live in `a`.
pub fn setup(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, fri: FriConfigV2, max_log: u32, genesis: []const H.Header) !struct { shape: node.Shape, vk: Vk } {
    if (max_log < HT.MIN_SEG_LOG or max_log > HT.MAX_SEG_LOG) return error.BadMaxLog;
    if (genesis.len < HT.segHeaders(max_log)) return error.NotEnoughHeaders;
    var start: ?ComponentSizes = null;
    var ls: u32 = HT.MIN_SEG_LOG;
    while (ls <= max_log) : (ls += 1) {
        var tmp = std.heap.ArenaAllocator.init(gpa);
        defer tmp.deinit();
        var sl = try leaf.buildSegmentLeaf(gpa, tmp.allocator(), ls, genesis[0..HT.segHeaders(ls)], H.genesis_start);
        defer sl.ctx.deinit();
        const p = sl.paddedSizes();
        start = if (start) |s0| s0.elementwiseMax(p) else p;
    }
    var shape = try node.Shape.init(gpa, &tables.table, start.?, fri);
    errdefer shape.deinit(gpa);
    const id = try node.nodeIdentity(gpa, a, &tables.table, &shape);
    const leaves = try a.alloc(LeafId, max_log - HT.MIN_SEG_LOG + 1);
    for (leaves, HT.MIN_SEG_LOG..) |*l, log| {
        const li = try leaf.leafIdentity(gpa, @intCast(log), genesis, shape.target, fri.log_blowup_factor);
        l.* = .{ .root = li.root, .hash = li.hash };
    }
    return .{ .shape = shape, .vk = .{ .fri = fri, .max_log = max_log, .target = shape.target, .node = id, .leaves = leaves } };
}

/// The prover's shape from a VK: rebuilt from the stored target, and checked to give exactly the
/// VK's node identity (so proofs made with it fold with stored ones).
pub fn shapeFromVk(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk) !node.Shape {
    var shape = try node.Shape.init(gpa, &tables.table, vk.target, vk.fri);
    errdefer shape.deinit(gpa);
    if (!std.meta.eql(shape.target, vk.target)) return error.VkShapeMismatch;
    const id = try node.nodeIdentity(gpa, a, &tables.table, &shape);
    if (!std.mem.eql(u32, &id.root, &vk.node.root) or !std.mem.eql(u32, &id.hash, &vk.node.hash)) return error.VkShapeMismatch;
    var probe: circuit_cpu.verify.Request = undefined;
    probe.pcs_config = id.pcs;
    probe.preprocessed_column_log_sizes = id.columns;
    if (!node.requestPinned(vk.node, &probe)) return error.VkShapeMismatch;
    return shape;
}

// ---------------------------------------------------------------------------------------------
// Proofs.

/// A circuit proof with its key and public inputs (any count).
pub fn encodeCircuit(e: *Enc, cp: *const leaf.CircuitProof, key: leaf.Key, pubs: []const M31) !void {
    var text: std.Io.Writer.Allocating = .init(e.a);
    defer text.deinit();
    try wire.verify_request.writeVerifyRequest(&text.writer, cp.request);
    try e.blob(text.written());
    try e.words(&cp.circuit_hash);
    try e.words(&key);
    for (pubs) |x| try e.int(u32, x.toU32());
    try e.blob(cp.bytes);
}

fn encodeProved(e: *Enc, p: *const Proved) !void {
    try encodeCircuit(e, &p.proof, p.key, &p.pubs);
}

/// Decodes `encodeCircuit` output with `pubs.len` public inputs; the request strings and bytes live
/// in `a`, the in-circuit view in its own arena (`deinit`). All proof bytes must be consumed.
pub fn decodeCircuit(gpa: std.mem.Allocator, a: std.mem.Allocator, d: *Dec, pubs: []M31) !struct { proof: leaf.CircuitProof, key: leaf.Key } {
    var owned = try wire.verify_request.parseVerifyRequest(gpa, try d.blob());
    defer owned.deinit();
    var request = owned.request;
    const columns = try a.alloc(leaf.Column, request.preprocessed_column_log_sizes.len);
    for (columns, request.preprocessed_column_log_sizes) |*c, src| c.* = .{ .id = try a.dupe(u8, src.id), .log_size = src.log_size };
    request.preprocessed_column_log_sizes = columns;
    const circuit_hash = try d.words(8);
    const key = try d.words(8);
    for (pubs) |*x| {
        const v = try d.int(u32);
        if (v >= 0x7fffffff) return error.NonCanonicalPublicInput;
        x.* = M31.fromCanonical(v);
    }
    const bytes = try a.dupe(u8, try d.blob());
    const config = try circuit_cpu.verifier_proof.proofConfig(columns.len, request.pcs_config);
    var decoded = try wire.circuit_serialize.deserializeProof(gpa, bytes, config);
    errdefer decoded.deinit();
    if (decoded.consumed != bytes.len) return error.TrailingProofBytes;
    return .{
        .proof = .{
            .prepared = .{ .arena = decoded.arena, .proof = decoded.proof, .config = config },
            .bytes = bytes,
            .request = request,
            .circuit_hash = circuit_hash,
        },
        .key = key,
    };
}

/// Decodes a proof (`decodeCircuit` with the chain's public inputs).
fn decodeProved(gpa: std.mem.Allocator, a: std.mem.Allocator, d: *Dec) !Proved {
    var pubs: [leaf.N_PUB]M31 = undefined;
    const r = try decodeCircuit(gpa, a, d, &pubs);
    return .{ .proof = r.proof, .key = r.key, .pubs = pubs };
}

// ---------------------------------------------------------------------------------------------
// The chain file.

pub const RootKind = enum(u8) { none = 0, own = 1, peak = 2 };

pub const Chain = struct {
    fri: FriConfigV2,
    max_log: u32,
    vk_digest: [8]u32,
    /// Segment log sizes, in chain order from height 0.
    logs: []const u32,
    peaks: []Proved,
    /// The bagged root: its own proof, the single peak (one peak covers everything), or none
    /// (a checkpoint).
    root_kind: RootKind,
    root: ?Proved,
    /// Inclusion path of leaf 0 (the genesis hash) in `T`.
    genesis: []const HT.Step,
    provenance: []const u8,

    pub fn headers(self: *const Chain) usize {
        var n: usize = 0;
        for (self.logs) |l| n += HT.segHeaders(l);
        return n;
    }

    pub fn rootProved(self: *const Chain) ?*const Proved {
        return switch (self.root_kind) {
            .none => null,
            .own => if (self.root) |*r| r else null,
            .peak => if (self.peaks.len == 1) &self.peaks[0] else null,
        };
    }

    /// Frees the decoded proofs' in-circuit views (a decoded chain owns them).
    pub fn deinit(self: *Chain) void {
        for (self.peaks) |*p| p.proof.deinit();
        if (self.root) |*r| r.proof.deinit();
    }

    pub fn encode(self: *const Chain, a: std.mem.Allocator) ![]u8 {
        var e: Enc = .{ .a = a };
        try e.buf.appendSlice(a, CHAIN_MAGIC);
        try e.int(u32, VERSION);
        try e.fri(self.fri);
        try e.int(u32, self.max_log);
        try e.words(&self.vk_digest);
        try e.int(u32, @intCast(self.logs.len));
        for (self.logs) |l| try e.int(u32, l);
        try e.int(u32, @intCast(self.peaks.len));
        for (self.peaks) |*p| try encodeProved(&e, p);
        try e.int(u8, @intFromEnum(self.root_kind));
        if (self.root_kind == .own) try encodeProved(&e, &(self.root orelse return error.NoRoot));
        try e.int(u32, @intCast(self.genesis.len));
        for (self.genesis) |s| {
            try e.words(&s.sibling);
            try e.int(u8, @intFromBool(s.left));
        }
        try e.blob(self.provenance);
        return seal(&e);
    }

    /// Parses chain file bytes; slices live in `a`, proofs' in-circuit views in their own arenas
    /// (`deinit`). Parsing checks the format only; `verifyChain` checks the content.
    pub fn decode(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !Chain {
        var d: Dec = .{ .bytes = try unseal(bytes) };
        try d.magic(CHAIN_MAGIC);
        var c: Chain = undefined;
        c.fri = try d.fri();
        c.max_log = try d.int(u32);
        c.vk_digest = try d.words(8);
        const logs = try a.alloc(u32, try d.int(u32));
        for (logs) |*l| l.* = try d.int(u32);
        c.logs = logs;
        const n_peaks = try d.int(u32);
        if (n_peaks > 64) return error.TooManyPeaks;
        var peaks = std.ArrayList(Proved).empty;
        errdefer for (peaks.items) |*p| p.proof.deinit();
        for (0..n_peaks) |_| try peaks.append(a, try decodeProved(gpa, a, &d));
        c.peaks = peaks.items;
        c.root_kind = std.meta.intToEnum(RootKind, try d.int(u8)) catch return error.BadRootKind;
        c.root = if (c.root_kind == .own) try decodeProved(gpa, a, &d) else null;
        errdefer if (c.root) |*r| r.proof.deinit();
        const steps = try a.alloc(HT.Step, try d.int(u32));
        for (steps) |*s| {
            s.sibling = try d.words(8);
            s.left = switch (try d.int(u8)) {
                0 => false,
                1 => true,
                else => return error.BadStep,
            };
        }
        c.genesis = steps;
        c.provenance = try a.dupe(u8, try d.blob());
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return c;
    }
};

// ---------------------------------------------------------------------------------------------
// Verification.

pub const Summary = struct {
    headers: usize,
    tip_height: u32,
    /// The tip's block hash state words (as in the public inputs).
    tip: [8]u32,
    work: u256,
    t: HT.Words,
};

fn tipOf(pubs: [leaf.N_PUB]M31) struct { height: u32, tip: [8]u32, work: u256 } {
    var tip: [8]u32 = undefined;
    for (&tip, 0..) |*w, k| w.* = pubs[16 + 2 * k].toU32() | (pubs[17 + 2 * k].toU32() << 16);
    var work: u256 = 0;
    for (0..10) |l| work |= @as(u256, pubs[98 + l].toU32()) << @intCast(16 * l);
    return .{ .height = pubs[38].toU32() | (pubs[39].toU32() << 16), .tip = tip, .work = work };
}

/// What a peak (or the root) of a plan must be: circuit identity, key, header count.
const Expect = struct { root: [8]u32, hash: [8]u32, key: leaf.Key, n: usize };

fn expectMerge(vk: *const Vk, l: Expect, r: Expect) anyerror!Expect {
    return .{ .root = vk.node.root, .hash = vk.node.hash, .key = node.nodeKey(l.hash, l.key, r.hash, r.key), .n = l.n + r.n };
}

fn expectedPeaks(a: std.mem.Allocator, vk: *const Vk, logs: []const u32) ![]const HT.Peak(Expect) {
    var stack = std.ArrayList(HT.Peak(Expect)).empty;
    for (logs) |log| {
        const id = vk.leafId(log);
        const n = HT.segHeaders(log);
        try HT.pushPeak(Expect, a, &stack, .{ .root = id.root, .hash = id.hash, .key = leaf.zero_key, .n = n }, n, vk, expectMerge);
    }
    return stack.items;
}

/// Checks a stored proof against what the plan says it is, and verifies it natively.
fn checkProved(gpa: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, p: *const Proved, want: Expect) !void {
    if (!std.mem.eql(u32, &p.proof.request.preprocessed_root, &want.root)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &p.proof.circuit_hash, &want.hash)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &p.key, &want.key)) return error.WrongKey;
    // Leaves and nodes are padded to one target: one pinned request for both.
    if (!node.requestPinned(vk.node, &p.proof.request)) return error.ConfigNotPinned;
    if (node.headerCount(p.pubs) != want.n) return error.WrongHeaderCount;
    const out = try leaf.verifyCircuit(gpa, tables, &p.proof);
    if (!std.mem.eql(u32, &out, &p.digest())) return error.WrongDigest;
}

/// Steps 1–3 of `verifyChain`: the VK, the plan and every peak (all a checkpoint has).
pub fn checkPeaks(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, chain: *const Chain) !void {
    if (!std.mem.eql(u32, &chain.vk_digest, &try vk.digest(a))) return error.VkMismatch;
    if (!std.meta.eql(chain.fri, vk.fri) or chain.max_log != vk.max_log) return error.VkMismatch;
    if (!HT.validPlan(chain.logs, vk.max_log)) return error.BadSegmentPlan;
    const want = try expectedPeaks(a, vk, chain.logs);
    if (want.len != chain.peaks.len) return error.PeakCountMismatch;
    for (chain.peaks, want) |*p, w| try checkProved(gpa, tables, vk, p, w.e);
}

/// **The standalone verifier.** Accepts `chain` under the pinned `vk`:
/// 1. the file names this VK and its parameters;
/// 2. the segment plan is aligned (`HT.validPlan`), so `T` is the canonical MMR root;
/// 3. every peak is the proof the plan says, natively verified (extensions build on them);
/// 4. the root's public inputs are the peaks' combined ones, and the outer verifier
///    (`node.verifyRoot`: pinned request, identity, key, digest, genesis input state) accepts it;
/// 5. leaf 0 of `T` is Bitcoin's genesis hash (leftmost path of the implied depth).
/// The caller must still compare `Summary.work` with a trusted minimum.
pub fn verifyChain(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, chain: *const Chain) !Summary {
    try checkPeaks(gpa, a, tables, vk, chain);
    const n = chain.headers();

    const root = chain.rootProved() orelse return error.NoRoot;
    var pubs = chain.peaks[chain.peaks.len - 1].pubs;
    var i = chain.peaks.len - 1;
    while (i > 0) {
        i -= 1;
        pubs = node.combine(chain.peaks[i].pubs, pubs);
    }
    for (pubs, root.pubs) |x, y| if (x.toU32() != y.toU32()) return error.RootNotFromPeaks;

    const leaf_hashes = try a.alloc([8]u32, chain.logs.len);
    const sizes = try a.alloc(usize, chain.logs.len);
    for (chain.logs, leaf_hashes, sizes) |log, *h, *s| {
        h.* = vk.leafId(log).hash;
        s.* = HT.segHeaders(log);
    }
    try node.verifyRoot(gpa, a, tables, .{ .node = vk.node, .leaf_hashes = leaf_hashes, .sizes = sizes }, &root.proof, root.pubs);
    if (node.headerCount(root.pubs) != n) return error.WrongHeaderCount;

    const t = node.treeWords(root.pubs);
    if (!HT.verifyLeftmost(GENESIS_HASH, chain.genesis, n, t)) return error.NotBitcoinGenesis;
    const tip = tipOf(root.pubs);
    return .{ .headers = n, .tip_height = tip.height, .tip = tip.tip, .work = tip.work, .t = t };
}

// ---------------------------------------------------------------------------------------------
// Proving and extending.

pub const Prover = struct {
    gpa: std.mem.Allocator,
    /// Long-lived: proof bytes and requests.
    a: std.mem.Allocator,
    tables: *const leaf.Tables,
    shape: *const node.Shape,
    vk: *const Vk,
    vk_digest: [8]u32,
    logs: std.ArrayList(u32) = .empty,
    stack: std.ArrayList(HT.Peak(Proved)) = .empty,
    /// Headers proven so far, and the chainwork before the next one.
    next: usize = 0,
    work: u256 = 0,
    /// Log lines (progress).
    verbose: bool = false,

    pub fn init(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, shape: *const node.Shape, vk: *const Vk) !Prover {
        return .{ .gpa = gpa, .a = a, .tables = tables, .shape = shape, .vk = vk, .vk_digest = try vk.digest(a) };
    }

    /// Continues from a stored chain (its peaks verified by the caller, `checkPeaks`; moved in).
    /// `all` must agree with what it proves: its MMR root over the first `N` block hashes must equal
    /// the peaks' combined `T` (so new segments continue the same headers).
    pub fn continueFrom(self: *Prover, stored: *Chain, all: []const H.Header) !void {
        if (self.logs.items.len != 0 or self.stack.items.len != 0) return error.NotEmpty;
        if (!std.mem.eql(u32, &stored.vk_digest, &self.vk_digest)) return error.VkMismatch;
        const n = stored.headers();
        if (all.len < n) return error.NotEnoughHeaders;
        if (stored.peaks.len == 0) return error.NoPeaks;
        // The peaks' combined `T` must be the MMR root over `all`'s first `n` block hashes.
        var pubs = stored.peaks[stored.peaks.len - 1].pubs;
        var i = stored.peaks.len - 1;
        while (i > 0) {
            i -= 1;
            pubs = node.combine(stored.peaks[i].pubs, pubs);
        }
        const hashes = try self.gpa.alloc(HT.Words, n);
        defer self.gpa.free(hashes);
        for (hashes, all[0..n]) |*h, *hd| h.* = HT.blockHash(hd);
        if (!std.mem.eql(u32, &try HT.mmrRoot(self.gpa, hashes), &node.treeWords(pubs))) return error.HeadersDiffer;
        try self.logs.appendSlice(self.a, stored.logs);
        var at: usize = 0;
        for (stored.peaks) |p| {
            const k = node.headerCount(p.pubs);
            try self.stack.append(self.a, .{ .e = p, .n = k });
            at += k;
        }
        if (at != n) return error.WrongHeaderCount;
        stored.peaks = &.{};
        self.next = n;
        self.work = segments.workBefore(all, n);
    }

    const Merge = struct {
        p: *Prover,
        fn merge(c: @This(), l: Proved, r: Proved) anyerror!Proved {
            const n = try node.proveNode(c.p.gpa, c.p.a, c.p.tables, c.p.shape, &l, &r);
            var lp = l.proof;
            var rp = r.proof;
            lp.deinit();
            rp.deinit();
            return n;
        }
    };

    /// Proves the next segment (`2^(log − 8)` headers from `all[next..]`) and pushes it onto the
    /// peaks, merging equal neighbours.
    pub fn pushSegment(self: *Prover, all: []const H.Header, log: u32) !void {
        const h0 = self.next;
        const n = HT.segHeaders(log);
        if (log > self.vk.max_log or HT.nextSegment(h0, n, log) != log) return error.MisalignedSegment;
        if (all.len < h0 + n) return error.NotEnoughHeaders;
        var timer = try std.time.Timer.start();
        var tmp = std.heap.ArenaAllocator.init(self.gpa);
        defer tmp.deinit();
        var sl = try leaf.buildSegmentLeaf(self.gpa, tmp.allocator(), log, all[h0 .. h0 + n], segments.startAt(all, h0, self.work));
        const lf = try leaf.proveSegmentLeaf(self.gpa, self.a, self.tables, &sl, self.shape.target, self.vk.fri);
        if (!std.mem.eql(u32, &lf.proof.circuit_hash, &self.vk.leafId(log).hash)) return error.LeafIdentityMismatch;
        const t_leaf = timer.lap();
        try HT.pushPeak(Proved, self.a, &self.stack, .{ .proof = lf.proof, .key = leaf.zero_key, .pubs = lf.pubs }, n, Merge{ .p = self }, Merge.merge);
        try self.logs.append(self.a, log);
        self.work += segments.workBefore(all[h0 .. h0 + n], n);
        self.next = h0 + n;
        if (self.verbose) std.debug.print("  segment {d}..{d} (log {d}): leaf {d:.1}s, merges {d:.1}s; {d} peaks; peak RSS {d:.1} GB\n", .{ h0, h0 + n - 1, log, ns(t_leaf), ns(timer.read()), self.stack.items.len, peakRssGb() });
    }

    /// Bags the peaks into the root (proving the bagging nodes); the peaks stay. `null` when a
    /// single peak covers everything (it is the root).
    pub fn bag(self: *Prover) !?Proved {
        const s = self.stack.items;
        if (s.len == 0) return error.NothingProven;
        if (s.len == 1) return null;
        var acc = s[s.len - 1].e;
        var owned = false;
        var i = s.len - 1;
        while (i > 0) {
            i -= 1;
            const n = try node.proveNode(self.gpa, self.a, self.tables, self.shape, &s[i].e, &acc);
            if (owned) acc.proof.deinit();
            acc = n;
            owned = true;
        }
        return acc;
    }

    /// The chain file content (borrowing the prover's peaks). `all` gives the genesis path.
    pub fn chain(self: *Prover, root: ?Proved, all: []const H.Header, provenance: []const u8) !Chain {
        return self.chainIn(self.a, root, all, provenance, true);
    }

    /// The chain file content, allocated in `out`; `genesis`: include leaf 0's path (a checkpoint
    /// does not need it).
    fn chainIn(self: *Prover, out: std.mem.Allocator, root: ?Proved, all: []const H.Header, provenance: []const u8, genesis: bool) !Chain {
        const n = self.next;
        const peaks = try out.alloc(Proved, self.stack.items.len);
        for (peaks, self.stack.items) |*p, s| p.* = s.e;
        return .{
            .fri = self.vk.fri,
            .max_log = self.vk.max_log,
            .vk_digest = self.vk_digest,
            .logs = self.logs.items,
            .peaks = peaks,
            .root_kind = if (root != null) .own else if (peaks.len == 1) .peak else .none,
            .root = root,
            .genesis = if (genesis and n > 0) try genesisPath(out, all[0..n]) else &.{},
            .provenance = provenance,
        };
    }

    /// A checkpoint: the chain so far without a root (no bagging).
    pub fn checkpoint(self: *Prover, all: []const H.Header, path: []const u8) !void {
        var tmp = std.heap.ArenaAllocator.init(self.gpa);
        defer tmp.deinit();
        var c = try self.chainIn(tmp.allocator(), null, all, "checkpoint", false);
        c.root_kind = .none;
        try writeFileAtomic(path, try c.encode(tmp.allocator()));
    }

    pub fn deinit(self: *Prover) void {
        for (self.stack.items) |*p| p.e.proof.deinit();
        self.stack.items.len = 0;
    }
};

/// Leaf 0's inclusion path in the MMR over `headers`' block hashes (scratch freed; the path lives
/// in `out`).
fn genesisPath(out: std.mem.Allocator, headers: []const H.Header) ![]const HT.Step {
    var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer scratch.deinit();
    const hashes = try scratch.allocator().alloc(HT.Words, headers.len);
    for (hashes, headers) |*h, *hd| h.* = HT.blockHash(hd);
    return out.dupe(HT.Step, try HT.inclusionProof(scratch.allocator(), hashes, 0));
}

/// Peak resident memory of this process so far, in GB.
pub fn peakRssGb() f64 {
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    const bytes: f64 = @floatFromInt(ru.maxrss);
    // macOS reports bytes, Linux kilobytes.
    return if (@import("builtin").os.tag == .macos) bytes / 1e9 else bytes / 1e6;
}

fn ns(x: u64) f64 {
    return @as(f64, @floatFromInt(x)) / 1e9;
}

// ---------------------------------------------------------------------------------------------
// Tests (test-strength FRI; segment log sizes 9..10, i.e. 2 or 4 headers).

test "proof store: genesis hash constant" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const all = try H.loadHeaders(arena.allocator(), @embedFile("testdata:mainnet_headers_0_16"));
    try std.testing.expectEqualSlices(u32, &GENESIS_HASH, &HT.blockHash(&all[0]));
}

test "proof store: prove, save, reload, verify, extend; tampered files are rejected" {
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const all = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const fri = try FriConfigV2.init(10, 0, 1, 3, 1);
    var dir = std.testing.tmpDir(.{});
    defer dir.cleanup();
    const base = try dir.dir.realpathAlloc(a, ".");
    const p10 = try std.fs.path.join(a, &.{ base, "c10.sbchain" });
    const p16 = try std.fs.path.join(a, &.{ base, "c16.sbchain" });
    const pvk = try std.fs.path.join(a, &.{ base, "test.vk" });

    // Setup; the VK survives a file round trip with the same digest.
    var su = try setup(gpa, a, tables, fri, 10, all);
    defer su.shape.deinit(gpa);
    try writeFileAtomic(pvk, try su.vk.encode(a));
    const vk = try Vk.decode(a, try readFile(a, pvk));
    try std.testing.expectEqualSlices(u32, &try su.vk.digest(a), &try vk.digest(a));
    var shape = try shapeFromVk(gpa, a, tables, &vk);
    defer shape.deinit(gpa);

    // Prove headers 0..9 (segments 4, 4, 2), save, reload, verify.
    {
        var pr = try Prover.init(gpa, a, tables, &shape, &vk);
        defer pr.deinit();
        for (try HT.planSegments(a, 0, 10, vk.max_log)) |s| try pr.pushSegment(all, @intCast(s[1]));
        try std.testing.expectEqual(@as(usize, 2), pr.stack.items.len); // peaks 8 + 2
        const root = (try pr.bag()).?;
        var c = try pr.chain(root, all, "test");
        try writeFileAtomic(p10, try c.encode(a));
        var r = root;
        r.proof.deinit();
    }
    {
        var c = try Chain.decode(gpa, a, try readFile(a, p10));
        defer c.deinit();
        const s = try verifyChain(gpa, a, tables, &vk, &c);
        try std.testing.expectEqual(@as(usize, 10), s.headers);
        try std.testing.expectEqual(@as(u32, 9), s.tip_height);
        const hashes = try a.alloc(HT.Words, 10);
        for (hashes, all[0..10]) |*h, *hd| h.* = HT.blockHash(hd);
        try std.testing.expectEqualSlices(u32, &try HT.mmrRoot(a, hashes), &s.t);
        // A reloaded proof re-serializes to the same bytes.
        const again = try circuit_cpu.verifier_proof.VerifierProof.serialize(&c.peaks[0].proof.prepared, a);
        try std.testing.expectEqualSlices(u8, c.peaks[0].proof.bytes, again);
    }

    // Extend to 16 from the file (segments 2 at height 10, 4 at 12): one peak, which is the root.
    {
        var c = try Chain.decode(gpa, a, try readFile(a, p10));
        defer c.deinit();
        const s = try verifyChain(gpa, a, tables, &vk, &c);
        var pr = try Prover.init(gpa, a, tables, &shape, &vk);
        defer pr.deinit();
        _ = s;
        try pr.continueFrom(&c, all);
        for (try HT.planSegments(a, 10, 16, vk.max_log)) |seg| try pr.pushSegment(all, @intCast(seg[1]));
        try std.testing.expectEqual(@as(usize, 1), pr.stack.items.len);
        try std.testing.expect((try pr.bag()) == null);
        const c16 = try pr.chain(null, all, "test");
        try writeFileAtomic(p16, try c16.encode(a));
    }
    const good = try readFile(a, p16);
    {
        var c = try Chain.decode(gpa, a, good);
        defer c.deinit();
        const s = try verifyChain(gpa, a, tables, &vk, &c);
        try std.testing.expectEqual(@as(usize, 16), s.headers);
        const hashes = try a.alloc(HT.Words, 16);
        for (hashes, all[0..16]) |*h, *hd| h.* = HT.blockHash(hd);
        try std.testing.expectEqualSlices(u32, &try HT.mmrRoot(a, hashes), &s.t);
        try std.testing.expectEqualSlices(u32, &[_]u32{ 10, 10, 9, 9, 10 }, c.logs);
    }

    // Tampering. Corruption is caught by the trailer; re-sealed edits by verification.
    {
        var bad = try a.dupe(u8, good);
        bad[bad.len / 2] ^= 1;
        try std.testing.expectError(error.ChecksumMismatch, Chain.decode(gpa, a, bad));
        try std.testing.expectError(error.ChecksumMismatch, Chain.decode(gpa, a, good[0 .. good.len - 1]));
    }
    const Edit = enum { proof_byte, queries, pubs, plan, genesis, vk_digest };
    for (std.enums.values(Edit)) |edit| {
        var c = try Chain.decode(gpa, a, good);
        defer c.deinit();
        const p = &c.peaks[0];
        switch (edit) {
            .proof_byte => {
                const b = try a.dupe(u8, p.proof.bytes);
                b[b.len / 3] ^= 1;
                p.proof.bytes = b;
            },
            .queries => p.proof.request.pcs_config.fri_config.n_queries -= 1,
            .pubs => p.pubs[38] = M31.fromCanonical(p.pubs[38].toU32() + 1),
            .plan => c.logs = &.{ 10, 9, 10, 9, 10 },
            .genesis => {
                const g = try a.dupe(HT.Step, c.genesis);
                g[0].left = true;
                c.genesis = g;
            },
            .vk_digest => c.vk_digest[0] ^= 1,
        }
        // Re-encode (the trailer is recomputed) and decode: only verification can object.
        const bytes = c.encode(a) catch |err| {
            std.debug.print("edit {s}: encode failed {}\n", .{ @tagName(edit), err });
            return err;
        };
        var d = Chain.decode(gpa, a, bytes) catch |err| {
            // An edit may already break the proof's wire format (its size follows the config).
            std.debug.print("edit {s}: rejected at load ({})\n", .{ @tagName(edit), err });
            continue;
        };
        defer d.deinit();
        if (verifyChain(gpa, a, tables, &vk, &d)) |_| {
            std.debug.print("edit {s}: ACCEPTED\n", .{@tagName(edit)});
            return error.TamperAccepted;
        } else |err| std.debug.print("edit {s}: rejected ({})\n", .{ @tagName(edit), err });
    }
}
