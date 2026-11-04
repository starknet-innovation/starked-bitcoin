//! The chain seal (docs/design/chain-seal.md): one proof over a chain of epochs and its coin sets.
//! The glue is the Lean program `chainSeal ms gen` (`Circuit/ChainSeal.lean`, exported as
//! `airs/chain_seal_<ms>[_genesis].json`): the last join verified at hook 0, the set-pass roots at
//! hooks 1 … S, the joins' `acc` opened epoch by epoch, each epoch root's `rest` opened to its sum,
//! input count, challenge and block-hash roots, each set root's summary opened to its pass's start and
//! final state vectors, the balance of every epoch under its challenge, the set digests linked (the
//! pass's Blake2s state finishes to the digest the epoch root bound), the counts and heights in range.
//! The output digest: the key (every child's circuit hash and key), the chain's range, start and end
//! set digests, `acc`, the end set's count, amount, highest height and Merkle root, the Blake2s digests
//! of the end and start sets' SHA-256 states (finished natively to Core's `hash_serialized`).
//!
//! What stays native in the verifier (`verify`): the header chain root and the block-hash paths
//! (`ER.openHead`, as `verify-chain`), the keys from the pinned identities, the facts from the public
//! final states, Core's assumeUTXO anchor.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const circuit_cpu = @import("stwo_circuit_cpu_integration");
const leaf = @import("leaf.zig");
const glue = @import("glue.zig");
const ER = @import("epoch_root.zig");
const EJ = @import("epoch_join.zig");
const ST = @import("set_tree.zig");
const SS = @import("../block/set_seg.zig");
const BF = @import("block_forest.zig");
const BT = @import("block_tree.zig");
const store = @import("store.zig");
const wk = @import("block_node_k.zig");
const coin = @import("../block/coin.zig");
const HT = @import("../btc/header_tree.zig");

const builder = circuit.builder;
const preprocessed = circuit.common.preprocessed;
const finalize = circuit.common.finalize;
const component_list = circuit.common.component_list;
const multiverifier = circuit.statements.multiverifier;
const stark_proof = circuit.stark_verifier.proof;
const Context = builder.Context;
const NoValue = builder.NoValue;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const Key = leaf.Key;

/// The exported parameterizations (`lake env lean --run Export.lean chain_seal <m,m,…> [genesis]`).
pub fn programJson(ms: []const u32, gen: bool) ![]const u8 {
    if (gen and std.mem.eql(u32, ms, &.{ 1, 2, 3 })) return @embedFile("air:chain_seal_1_2_3_genesis");
    if (!gen and std.mem.eql(u32, ms, &.{ 16, 16 })) return @embedFile("air:chain_seal_16_16");
    return error.SealNotExported;
}

/// The external layout (`ChainSeal.lean` § Layout).
pub const JEXT = 42;
pub const SEXT = 64;
pub const NST = 222;
pub fn rootExt(m: usize) usize {
    return 51 + 16 * m;
}
pub fn nSets(n: usize, gen: bool) usize {
    return 2 * n - @intFromBool(gen);
}
pub fn startIdx(gen: bool, i: usize) usize {
    return 2 * i - @intFromBool(gen);
}
pub fn endIdx(gen: bool, i: usize) usize {
    return 2 * i + 1 - @intFromBool(gen);
}
pub fn hasStart(gen: bool, i: usize) bool {
    return i != 0 or !gen;
}
fn eRoot(ms: []const u32, gen: bool, i: usize) usize {
    var e: usize = JEXT + SEXT * nSets(ms.len, gen);
    for (ms[0..i]) |m| e += rootExt(m);
    return e;
}
fn eState(ms: []const u32, gen: bool, j: usize) usize {
    return eRoot(ms, gen, ms.len) + NST * j;
}

/// An epoch as the seal opens it: the root's opening (its key, range, set digests, `rest`) and
/// `rest`'s preimage (the summed partial sum, input count, challenge, the children's block-hash roots).
pub const EpochIn = struct { open: EJ.RootOpen, pubs: ER.Public };

/// A set child: its root proof, key and summary, and the pass's public part (the file's count bytes,
/// the final state).
pub const SetIn = struct { proof: *const leaf.CircuitProof, key: Key, sum: ST.Summary, count: [4]u8, final: SS.State };

/// What the seal outputs (its digest's message): see `sealOut`.
pub const Open = struct {
    key: Key,
    a: u32,
    b: u32,
    start: [8]u32,
    end: [8]u32,
    acc: [8]u32,
    count: u32,
    amount: u128,
    max_height: u32,
    mroot: [8]u32,
    sha_end: [8]u32,
    sha_start: [8]u32,
};

fn putWord(h: *std.crypto.hash.blake2.Blake2s256, w: u32) void {
    var b: [4]u8 = undefined;
    std.mem.writeInt(u32, &b, w, .little);
    h.update(&b);
}

/// The output digest of a seal opening (the Lean program's message, 63 words).
pub fn sealOut(o: *const Open) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    for (o.key) |w| putWord(&h, w);
    putWord(&h, o.a);
    putWord(&h, o.b);
    for (o.start) |w| putWord(&h, w);
    for (o.end) |w| putWord(&h, w);
    for (o.acc) |w| putWord(&h, w);
    putWord(&h, o.count);
    for (0..3) |k| putWord(&h, @truncate(o.amount >> @intCast(32 * k)));
    putWord(&h, o.max_height);
    for (o.mroot) |w| putWord(&h, w);
    for (o.sha_end) |w| putWord(&h, w);
    for (o.sha_start) |w| putWord(&h, w);
    var d: [32]u8 = undefined;
    h.final(&d);
    return ER.digestWords(d);
}

/// The Blake2s digest of a state's SHA-256 part (its 82 limbs as the state vector lays them out).
pub fn shaDigest(st: SS.State) [8]u32 {
    var limbs: [82]M31 = undefined;
    for (0..8) |w| {
        limbs[2 * w] = M31.fromCanonical(st.sha.h[w] & 0xffff);
        limbs[2 * w + 1] = M31.fromCanonical(st.sha.h[w] >> 16);
    }
    limbs[16] = M31.fromCanonical(st.sha.nb);
    limbs[17] = M31.fromCanonical(st.sha.plen);
    for (0..64) |j| limbs[18 + j] = M31.fromCanonical(st.sha.pend[j]);
    return ST.vecDigest(&limbs);
}

/// The facts of a set child's public part, checked as the circuit checks them.
const SetFacts = struct { count: u32, digest: [8]u32, hash: [32]u8, sum: QM31, max_height: u32, amount: u128, sha: [8]u32 };

fn setFacts(s: *const SetIn) !SetFacts {
    const n = std.mem.readInt(u32, &s.count, .little);
    if (n >= 1 << 30) return error.CountTooLarge;
    if (s.final.i != n) return error.CountMismatch;
    if (s.final.last == null) return error.EmptySet;
    if (s.final.b2.plen > 64 or s.final.sha.plen > 64) return error.BadState;
    if (s.final.b2.nb >= 1 << 30) return error.BadState;
    const fin = SS.finish(s.final);
    return .{ .count = n, .digest = ER.digestWords(fin.digest), .hash = fin.hash, .sum = s.final.sum, .max_height = s.final.max_h, .amount = s.final.amount, .sha = shaDigest(s.final) };
}

/// The native view of the seal: every check the circuit makes, on the same values, and the output.
/// `join` is the chain's replayed last join (its key, start, end, range, `acc`), `jh` its circuit hash;
/// `shashes` the set roots' circuit hashes.
pub fn expected(join: *const EJ.JoinOpen, jh: [8]u32, epochs: []const EpochIn, sets: []const SetIn, shashes: []const [8]u32) !Open {
    const n = epochs.len;
    if (n < 2) return error.NeedTwoEpochs;
    const gen = epochs[0].open.ep.prev == null;
    if (sets.len != nSets(n, gen) or shashes.len != sets.len) return error.WrongSets;
    // The epochs: `rest` from its preimage, the outputs, `acc`, the links, the join's opening.
    var acc: [8]u32 = undefined;
    for (epochs, 0..) |e, i| {
        if ((e.open.ep.prev == null) != !hasStart(gen, i)) return error.PrevSetRequired;
        if (!std.mem.eql(u32, &ER.restOf(&e.pubs), &e.open.rest)) return error.RestMismatch;
        const out = ER.outOf(e.open.key, e.open.ep, e.open.rest);
        if (i == 0) {
            acc = out;
        } else {
            acc = hash2(acc, out);
            const p = epochs[i - 1].open.ep;
            if (p.to + 1 != e.open.ep.from) return error.HeightsDoNotLink;
            if (!std.mem.eql(u8, &p.fin, &e.open.ep.prev.?)) return error.SetsDoNotLink;
        }
    }
    if (!std.mem.eql(u32, &acc, &join.acc)) return error.AccMismatch;
    if (join.a != epochs[0].open.ep.from or join.b != epochs[n - 1].open.ep.to) return error.RangeMismatch;
    const start: [8]u32 = if (epochs[0].open.ep.prev) |p| ER.digestWords(p) else @splat(0);
    if (!std.mem.eql(u32, &start, &join.start) or !std.mem.eql(u32, &ER.digestWords(epochs[n - 1].open.ep.fin), &join.end)) return error.SetsMismatch;
    // The sets: each pass's facts; per epoch the digests, the balance, the ranges.
    var last: SetFacts = undefined;
    var first_sha: [8]u32 = @splat(0);
    for (epochs, 0..) |e, i| {
        const E = try setFacts(&sets[endIdx(gen, i)]);
        if (!std.mem.eql(u32, &E.digest, &ER.digestWords(e.open.ep.fin))) return error.EndDigestMismatch;
        var sum = QM31.fromM31Array(e.pubs.s);
        var count: u64 = e.pubs.nin.toU32() + E.count;
        if (hasStart(gen, i)) {
            const B = try setFacts(&sets[startIdx(gen, i)]);
            if (!std.mem.eql(u32, &B.digest, &ER.digestWords(e.open.ep.prev.?))) return error.StartDigestMismatch;
            if (B.max_height >= e.open.ep.from) return error.PrevSetTooNew;
            sum = sum.add(B.sum);
            count += B.count;
            if (i == 0) first_sha = B.sha;
        }
        if (count >= 1 << 30) return error.EpochTooLarge;
        if (!sum.eql(E.sum)) return error.EpochUnbalanced;
        last = E;
    }
    // The key over every child.
    var hashes: [65][8]u32 = undefined;
    var keys: [65]Key = undefined;
    if (sets.len + 1 > hashes.len) return error.WrongSets;
    hashes[0] = jh;
    keys[0] = join.key;
    for (sets, shashes, 0..) |s, h, j| {
        hashes[1 + j] = h;
        keys[1 + j] = s.key;
    }
    return .{
        .key = wk.key(hashes[0 .. sets.len + 1], keys[0 .. sets.len + 1]),
        .a = join.a,
        .b = join.b,
        .start = start,
        .end = join.end,
        .acc = acc,
        .count = last.count,
        .amount = last.amount,
        .max_height = last.max_height,
        .mroot = ST.rootOf(&sets[sets.len - 1].sum),
        .sha_end = last.sha,
        .sha_start = first_sha,
    };
}

fn hash2(x: [8]u32, y: [8]u32) [8]u32 {
    var h = std.crypto.hash.blake2.Blake2s256.init(.{});
    for (x ++ y) |w| putWord(&h, w);
    var d: [32]u8 = undefined;
    h.final(&d);
    return ER.digestWords(d);
}

// ---------------------------------------------------------------------------------------------
// The circuit

/// A child's verifier configuration from its proof's request (the pinned seal identity fixes it: a
/// child of another shape changes the seal's circuit).
pub fn sharedOf(gpa: std.mem.Allocator, cp: *const leaf.CircuitProof) !multiverifier.SharedConfig {
    var layout: preprocessed.ColumnLayout = undefined;
    if (cp.request.preprocessed_column_log_sizes.len != layout.entries.len) return error.BadLayout;
    for (&layout.entries, cp.request.preprocessed_column_log_sizes) |*e, c| e.* = .{ .id = c.id, .log_size = c.log_size };
    return multiverifier.sharedConfig(gpa, layout, cp.request.pcs_config);
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

fn putState(comptime V: type, ext: []V, at: usize, st: SS.State, count: [4]u8) void {
    if (V != QM31) return;
    putM31(V, ext, at, st.i);
    const last = st.last orelse @as([36]u8, @splat(0));
    for (0..36) |j| putM31(V, ext, at + 1 + j, last[j]);
    putM31(V, ext, at + 37, st.max_h);
    for (st.sum.toM31Array(), 0..) |x, j| ext[at + 38 + j] = QM31.fromBase(x);
    for (0..12) |j| putM31(V, ext, at + 42 + j, @as(u8, @truncate(st.amount >> @intCast(8 * j))));
    for ([_]SS.HashSt{ st.b2, st.sha }, 0..) |hs, q| {
        const b = at + 54 + 82 * q;
        for (0..8) |w| {
            putM31(V, ext, b + 2 * w, hs.h[w] & 0xffff);
            putM31(V, ext, b + 2 * w + 1, hs.h[w] >> 16);
        }
        putM31(V, ext, b + 16, hs.nb);
        putM31(V, ext, b + 17, hs.plen);
        for (0..64) |j| putM31(V, ext, b + 18 + j, hs.pend[j]);
    }
    for (0..4) |j| putM31(V, ext, at + 218 + j, count[j]);
}

/// The seal circuit (finalized, unpadded) over the join child, the set children (proof values,
/// preprocessed roots, configurations, openings) and the epochs' openings.
pub fn buildCircuit(comptime V: type, gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, ms: []const u32, gen: bool, join: EJ.ChildIn(V), set_proofs: []const *const stark_proof.Proof(V), set_shareds: []const *const multiverifier.SharedConfig, set_roots: []const [8]u32, sets: []const SetIn, epochs: []const EpochIn) !Context(V) {
    const n = ms.len;
    const S = nSets(n, gen);
    if (set_proofs.len != S or set_shareds.len != S or set_roots.len != S) return error.WrongSets;
    var ctx = try Context(V).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const prog = try glue.parse(ctx.scratch(), try programJson(ms, gen));
    const n_ext = eState(ms, gen, S);
    const ext = try ctx.scratch().alloc(V, n_ext);
    if (V != QM31) @memset(ext, .{});
    // The join's opening (as `EJ.buildCircuit`'s join child).
    const j = join.open.join;
    putWords(V, ext, 0, j.key);
    putWords(V, ext, 8, j.start);
    putWords(V, ext, 16, j.end);
    putM31(V, ext, 24, j.a);
    putM31(V, ext, 25, j.b);
    putWords(V, ext, 26, j.acc);
    putWords(V, ext, 34, join.preprocessed_root);
    // The set roots: summary, key, preprocessed root.
    if (V == QM31) for (0..S) |k| {
        const e = JEXT + SEXT * k;
        for (sets[k].sum, 0..) |x, q| ext[e + q] = QM31.fromBase(x);
        putWords(V, ext, e + 48, sets[k].key);
        putWords(V, ext, e + 56, set_roots[k]);
    };
    // The epochs: root opening, then `rest`'s preimage.
    if (V == QM31) for (0..n) |i| {
        const e = eRoot(ms, gen, i);
        const o = epochs[i].open;
        if (epochs[i].pubs.hash_roots.len != ms[i]) return error.WrongChildren;
        putWords(V, ext, e, o.key);
        putWords(V, ext, e + 8, ER.digestWords(o.ep.fin));
        putWords(V, ext, e + 16, if (o.ep.prev) |p| ER.digestWords(p) else @splat(0));
        putM31(V, ext, e + 24, o.ep.from);
        putM31(V, ext, e + 25, o.ep.to);
        putWords(V, ext, e + 26, o.rest);
        const p = epochs[i].pubs;
        for (p.s, 0..) |x, q| ext[e + 34 + q] = QM31.fromBase(x);
        ext[e + 38] = QM31.fromBase(p.nin);
        for (p.challenge, 0..) |x, q| ext[e + 39 + q] = QM31.fromBase(x);
        for (p.hash_roots, 0..) |r, c| for (r, 0..) |x, q| {
            ext[e + 51 + 16 * c + q] = QM31.fromBase(x);
        };
    };
    // The sets' final states and count bytes.
    for (0..S) |k| putState(V, ext, eState(ms, gen, k), sets[k].final, sets[k].count);
    const proofs = try ctx.scratch().alloc(*const stark_proof.Proof(V), S + 1);
    const shareds = try ctx.scratch().alloc(*const multiverifier.SharedConfig, S + 1);
    proofs[0] = join.proof;
    shareds[0] = join.shared;
    for (set_proofs, set_shareds, 1..) |p, sh, k| {
        proofs[k] = p;
        shareds[k] = sh;
    }
    try glue.runOutputs(V, &ctx, &prog, ext, EJ.Hook(V){ .ctx = &ctx, .table = table, .proofs = proofs, .shareds = shareds });
    return ctx;
}

/// The seal's topology (no values) over children of the given configurations: its identity.
pub fn topology(gpa: std.mem.Allocator, table: *const circuit.air_eval.component_table.Table, ms: []const u32, gen: bool, join_shared: *const multiverifier.SharedConfig, set_shared: *const multiverifier.SharedConfig) !Context(NoValue) {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const S = nSets(ms.len, gen);
    const ej = try stark_proof.emptyProof(a, join_shared.proof_config);
    const es = try stark_proof.emptyProof(a, set_shared.proof_config);
    const zero: [8]u32 = @splat(0);
    const jo: EJ.Open = .{ .join = .{ .key = zero, .start = zero, .end = zero, .a = 0, .b = 0, .acc = zero } };
    const proofs = try a.alloc(*const stark_proof.Proof(NoValue), S);
    @memset(proofs, &es);
    const shareds = try a.alloc(*const multiverifier.SharedConfig, S);
    @memset(shareds, set_shared);
    const roots = try a.alloc([8]u32, S);
    @memset(roots, zero);
    const sets = try a.alloc(SetIn, S);
    const blank: SS.State = .{ .b2 = .{ .h = @splat(0) }, .sha = .{ .h = @splat(0) } };
    @memset(sets, .{ .proof = undefined, .key = zero, .sum = @splat(M31.zero()), .count = @splat(0), .final = blank });
    const epochs = try a.alloc(EpochIn, ms.len);
    for (epochs, ms, 0..) |*e, m, i| {
        const roots_i = try a.alloc([16]M31, m);
        @memset(roots_i, @splat(M31.zero()));
        e.* = .{
            .open = .{ .key = zero, .ep = .{ .from = 0, .to = 0, .prev = if (hasStart(gen, i)) @splat(0) else null, .fin = @splat(0) }, .rest = zero },
            .pubs = .{ .s = @splat(M31.zero()), .nin = M31.zero(), .challenge = @splat(M31.zero()), .hash_roots = roots_i },
        };
    }
    return buildCircuit(NoValue, gpa, table, ms, gen, .{ .proof = &ej, .preprocessed_root = zero, .shared = join_shared, .open = jo }, proofs, shareds, roots, sets, epochs);
}

pub const VK_MAGIC = "SBSEALVK";
pub const FILE_MAGIC = "SBSEAL01";

/// **The seal's verifying key**: the configuration, the program's parameters, the seal's identity
/// at its natural size (nothing verifies a seal in-circuit).
pub const Vk = struct {
    fri: FriConfigV2,
    ms: []const u32,
    gen: bool,
    trace_log: u32,
    id: BF.Id,

    pub fn encode(self: *const Vk, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, VK_MAGIC);
        try e.int(u32, store.VERSION);
        try e.fri(self.fri);
        try e.int(u32, @intCast(self.ms.len));
        for (self.ms) |m| try e.int(u32, m);
        try e.int(u8, @intFromBool(self.gen));
        try e.int(u32, self.trace_log);
        try e.words(&self.id.root);
        try e.words(&self.id.hash);
        return store.seal(&e);
    }

    pub fn decode(a: std.mem.Allocator, bytes: []const u8) !Vk {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(VK_MAGIC);
        var vk: Vk = undefined;
        vk.fri = try d.fri();
        const n = try d.int(u32);
        if (n < 2 or n > 64) return error.BadVk;
        const ms = try a.alloc(u32, n);
        for (ms) |*m| m.* = try d.int(u32);
        vk.ms = ms;
        vk.gen = switch (try d.int(u8)) {
            0 => false,
            1 => true,
            else => return error.BadVk,
        };
        vk.trace_log = try d.int(u32);
        vk.id = .{ .root = try d.words(8), .hash = try d.words(8) };
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return vk;
    }
};

/// The seal's identity over children of the given configurations.
pub fn setupVk(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, ms: []const u32, gen: bool, join_shared: *const multiverifier.SharedConfig, set_shared: *const multiverifier.SharedConfig, fri: FriConfigV2) !Vk {
    var topo = try topology(gpa, &tables.table, ms, gen, join_shared, set_shared);
    defer topo.deinit();
    const natural = finalize.computePaddedSizes(.fromBuilder(&topo.circuit));
    const id = try BF.identityOf(gpa, NoValue, &topo, natural, fri.log_blowup_factor);
    return .{ .fri = fri, .ms = try a.dupe(u32, ms), .gen = gen, .trace_log = id.trace_log, .id = id.id };
}

/// A set child's public part in the seal file: its segment count (its key follows), the file's count
/// bytes, the final state, the pass's Merkle root.
pub const SetPublic = struct { k: u32, count: [4]u8, final: SS.State, mroot: [8]u32 };

/// **A seal file**: every epoch root's public part (as the chain file), the set VK the passes were
/// proved under (the verifier accepts only a pinned one), each set child's public part, the seal proof.
pub const File = struct {
    heads: []ER.Head,
    setvk: []const u8,
    sets: []SetPublic,
    proof: leaf.CircuitProof,

    pub fn encode(self: *const File, a: std.mem.Allocator) ![]u8 {
        var e: store.Enc = .{ .a = a };
        try e.buf.appendSlice(a, FILE_MAGIC);
        try e.int(u32, store.VERSION);
        try e.int(u32, @intCast(self.heads.len));
        for (self.heads) |*h| try h.encode(&e);
        try e.blob(self.setvk);
        try e.int(u32, @intCast(self.sets.len));
        for (self.sets) |*s| {
            try e.int(u32, s.k);
            try e.buf.appendSlice(a, &s.count);
            try ST.encodeState(&e, s.final);
            try e.words(&s.mroot);
        }
        try store.encodeCircuit(&e, &self.proof, leaf.zero_key, &.{});
        return store.seal(&e);
    }

    pub fn decode(gpa: std.mem.Allocator, a: std.mem.Allocator, bytes: []const u8) !File {
        var d: store.Dec = .{ .bytes = try store.unseal(bytes) };
        try d.magic(FILE_MAGIC);
        const n = try d.int(u32);
        if (n < 2 or n > 64) return error.BadFile;
        const heads = try a.alloc(ER.Head, n);
        for (heads) |*h| h.* = try ER.Head.decode(a, &d);
        const setvk = try a.dupe(u8, try d.blob());
        const ns = try d.int(u32);
        if (ns < 3 or ns > 128) return error.BadFile;
        const sets = try a.alloc(SetPublic, ns);
        for (sets) |*s| {
            s.k = try d.int(u32);
            s.count = (try d.take(4))[0..4].*;
            s.final = try ST.decodeState(&d);
            s.mroot = try d.words(8);
        }
        var none: [0]M31 = .{};
        const c = try store.decodeCircuit(gpa, a, &d, &none);
        if (d.pos != d.bytes.len) return error.TrailingBytes;
        return .{ .heads = heads, .setvk = setvk, .sets = sets, .proof = c.proof };
    }
};

/// A proved set root as the seal takes it: its verifier values and configuration from its own proof.
pub const SetChild = struct {
    values: stark_proof.Proof(QM31),
    shared: multiverifier.SharedConfig,
    root: [8]u32,
    in: SetIn,
};

pub fn setChildOf(gpa: std.mem.Allocator, a: std.mem.Allocator, p: *const ST.Pass) !SetChild {
    return .{
        .values = try circuit_cpu.verifier_proof.circuitVerifierValues(a, &p.root.proof.prepared.proof, p.root.proof.prepared.config),
        .shared = try sharedOf(gpa, &p.root.proof),
        .root = p.root.proof.request.preprocessed_root,
        .in = .{ .proof = &p.root.proof, .key = p.root.key, .sum = p.root.sum, .count = p.count, .final = p.final },
    };
}

pub const Proved = struct { open: Open, n_vars: usize, trace_log: u32, proof: leaf.CircuitProof };

/// Builds the seal over the chain's last join (`join`, its proof `jp`), the set roots (`children`,
/// in set-child order) and the epochs (in chain order), checks it is satisfied with the native output,
/// and proves it at its natural size (CPU).
pub fn prove(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, ms: []const u32, join: *const EJ.JoinOpen, jp: *const leaf.CircuitProof, children: []const SetChild, epochs: []const EpochIn, fri: FriConfigV2) !Proved {
    const gen = epochs[0].open.ep.prev == null;
    const S = nSets(ms.len, gen);
    if (children.len != S) return error.WrongSets;
    var jshared = try sharedOf(gpa, jp);
    defer jshared.deinit(gpa);
    const jchild = try EJ.childOf(a, jp, &jshared, .{ .join = join.* });
    const proofs = try a.alloc(*const stark_proof.Proof(QM31), S);
    const shareds = try a.alloc(*const multiverifier.SharedConfig, S);
    const roots = try a.alloc([8]u32, S);
    const sets = try a.alloc(SetIn, S);
    const hashes = try a.alloc([8]u32, S);
    for (children, 0..) |*c, k| {
        proofs[k] = &c.values;
        shareds[k] = &c.shared;
        roots[k] = c.root;
        sets[k] = c.in;
        hashes[k] = c.in.proof.circuit_hash;
    }
    const want = try expected(join, jp.circuit_hash, epochs, sets, hashes);
    var ctx = try buildCircuit(QM31, gpa, &tables.table, ms, gen, jchild, proofs, shareds, roots, sets, epochs);
    defer ctx.deinit();
    if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
    const out = wk.outputDigest(&ctx);
    if (!std.mem.eql(u32, &out, &sealOut(&want))) return error.SealDigestMismatch;
    const n_vars = ctx.circuit.n_vars;
    var cp = try leaf.proveCircuit(gpa, a, &ctx, null, fri);
    errdefer cp.deinit();
    const got = try leaf.verifyCircuit(gpa, tables, &cp);
    if (!std.mem.eql(u32, &got, &sealOut(&want))) return error.SealDigestMismatch;
    return .{ .open = want, .n_vars = n_vars, .trace_log = cp.request.pcs_config.trace_lifting_log_size - fri.log_blowup_factor, .proof = cp };
}

/// What the verifier knows of a set child: its pinned VK (its circuit hash and key from `k`) and the
/// epoch it belongs to.
pub const Verified = struct { open: Open, hash: [32]u8, start_hash: ?[32]u8 };

/// **The seal verifier.** The heads opened and the joins replayed as `verify-chain` does (block-hash
/// roots against the chain's `T`, keys from the pinned identities), every set child's facts from its
/// public part (its key from the pinned set VK and its segment count), the native view of the seal
/// (`expected`: every check the circuit makes, on the public values), then the one proof against the
/// pinned seal identity with that output digest. Returns the output and Core's `hash_serialized` of
/// the end set (and of the start set, for the anchor).
pub fn verify(gpa: std.mem.Allocator, a: std.mem.Allocator, tables: *const leaf.Tables, vk: *const Vk, jvk: *const EJ.Vk, svk: *const ST.Vk, f: *const File, epochs: []const EJ.EpochIn, n_headers: usize, t: HT.Words) !Verified {
    if (f.heads.len != epochs.len or epochs.len != vk.ms.len) return error.WrongEpochs;
    // Each layer under its production configuration: the seal and the join (`BT.circuitFri`), the set
    // tree (`BF.circuitFri`, fold 1); the set roots verify in-circuit under their own.
    if (!std.meta.eql(vk.fri, BT.circuitFri()) or !std.meta.eql(jvk.fri, BT.circuitFri()) or !std.meta.eql(svk.fri, BF.circuitFri())) return error.ConfigNotPinned;
    const gen = epochs[0].ep.prev == null;
    if (gen != vk.gen or f.sets.len != nSets(epochs.len, gen)) return error.WrongSets;
    const r = try EJ.replay(a, jvk, f.heads, epochs, n_headers, t);
    const eps = try a.alloc(EpochIn, epochs.len);
    for (eps, r.opens, f.heads, 0..) |*e, o, *h, i| {
        if (h.children.len != vk.ms[i]) return error.WrongChildren;
        const roots = try a.alloc([16]M31, h.children.len);
        for (roots, h.children) |*x, c| x.* = c.hash_root;
        e.* = .{ .open = o, .pubs = .{ .s = h.s, .nin = h.nin, .challenge = h.challenge, .hash_roots = roots } };
    }
    const sets = try a.alloc(SetIn, f.sets.len);
    const hashes = try a.alloc([8]u32, f.sets.len);
    for (sets, hashes, f.sets) |*s, *hh, p| {
        const ex = ST.expected(svk, p.k);
        var sum: ST.Summary = @splat(M31.zero());
        for (0..8) |w| {
            sum[32 + 2 * w] = M31.fromCanonical(p.mroot[w] & 0xffff);
            sum[33 + 2 * w] = M31.fromCanonical(p.mroot[w] >> 16);
        }
        s.* = .{ .proof = undefined, .key = ex.key, .sum = sum, .count = p.count, .final = p.final };
        hh.* = ex.hash;
    }
    const want = try expected(&r.join, r.jh, eps, sets, hashes);
    const p = &f.proof;
    if (!std.mem.eql(u32, &p.request.preprocessed_root, &vk.id.root)) return error.WrongCircuit;
    if (!std.mem.eql(u32, &p.circuit_hash, &vk.id.hash)) return error.WrongCircuit;
    if (!std.meta.eql(p.request.pcs_config, PcsConfigV2.fromFriAndTraceSize(vk.fri, vk.trace_log))) return error.ConfigNotPinned;
    const got = try leaf.verifyCircuit(gpa, tables, p);
    if (!std.mem.eql(u32, &got, &sealOut(&want))) return error.WrongDigest;
    const end = SS.finish(f.sets[f.sets.len - 1].final);
    return .{ .open = want, .hash = end.hash, .start_hash = if (gen) null else SS.finish(f.sets[0].final).hash };
}

test "seal programs parse: one hook per child, eight results" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    for ([_]struct { ms: []const u32, gen: bool }{ .{ .ms = &.{ 1, 2, 3 }, .gen = true }, .{ .ms = &.{ 16, 16 }, .gen = false } }) |c| {
        const prog = try glue.parse(arena.allocator(), try programJson(c.ms, c.gen));
        var hooks: usize = 0;
        for (prog.ops) |op| if (op == .hook) {
            hooks += 1;
        };
        try std.testing.expectEqual(nSets(c.ms.len, c.gen) + 1, hooks);
        try std.testing.expectEqual(@as(usize, 8), prog.results.len);
    }
}
