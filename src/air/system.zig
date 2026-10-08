//! A system of IR components proven together in one STARK under the `proving_5a7c5ed` profile
//! (roadmap IR-LOGUP; Lean semantics in lean/StarkedAir/Lookup.lean). Components share the
//! preprocessed, main and interaction trees; their lookups are tied together by LogUp.
//!
//! Transcript: config → preprocessed commitment → statement (per component: log size, AIR
//! digest, public inputs) → main commitment → lookup elements `(z, α)` → claimed sums →
//! interaction commitment → STARK. The verifier pins the preprocessed root and checks that the
//! claimed sums add to zero (the relations balance; `LogUp.logup_sum` in Lean).
//!
//! v0: every component has the same log size (no lifting).

const std = @import("std");
const core = @import("stwo_core");
const ir = @import("ir.zig");
const base = @import("prove.zig");
const rec = @import("prove_rec.zig");
const interp = @import("interp.zig");
const component_mod = @import("component.zig");
const prover_component = @import("stwo_prover_engine").air.component_prover;
const logup_columns = @import("stwo_prover_engine").air.logup_columns;
const prover_pcs = @import("stwo_prover_engine").pcs;
const lookup_transcript = core.channel.lookup_transcript;
const utils = core.utils;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const Revision = core.protocol_revision.Revision;

/// One component of a system: its AIR, trace size and public inputs.
pub const Part = struct {
    air: *const ir.Air,
    log_size: u32,
    pubs: []const M31 = &.{},
};

/// A lookup entry the verifier contributes (e.g. a public root consumed with multiplicity −1).
pub const PubEntry = struct {
    rel: u32,
    vals: []const M31,
    mult: M31,
};

pub const Proof = struct {
    stark: rec.Proof,
    /// Claimed LogUp sums of the components with lookups, in component order.
    claimed_sums: []QM31,
};

fn hasLookups(parts: []const Part) bool {
    for (parts) |p| if (p.air.lookups.len != 0) return true;
    return false;
}

fn checkSizes(parts: []const Part) !u32 {
    if (parts.len == 0) return error.EmptySystem;
    for (parts) |p| if (p.log_size != parts[0].log_size) return error.LiftingUnsupported;
    return parts[0].log_size;
}

fn mixStatements(channel: anytype, allocator: std.mem.Allocator, parts: []const Part) !void {
    channel.mixU32s(&.{@intCast(parts.len)});
    for (parts) |p| base.mixStatement(channel, p.log_size, try p.air.digest(allocator), p.pubs);
}

/// Components wired into the shared trees.
fn components(allocator: std.mem.Allocator, parts: []const Part) ![]component_mod.Component {
    const out = try allocator.alloc(component_mod.Component, parts.len);
    var pre: usize = 0;
    var main: usize = 0;
    var inter: usize = 0;
    const trees: usize = if (hasLookups(parts)) 3 else 2;
    for (parts, out) |p, *c| {
        c.* = try component_mod.Component.init(allocator, p.air.*, p.log_size, p.pubs);
        c.pre_offset = pre;
        c.main_offset = main;
        c.inter_offset = inter;
        c.n_trees = trees;
        pre += p.air.n_preprocessed;
        main += p.air.n_main;
        inter += 4 * component_mod.nBatches(p.air.*);
    }
    return out;
}

fn preprocessedStorage(allocator: std.mem.Allocator, parts: []const Part) ![]prover_pcs.ColumnEvaluation {
    var cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    for (parts) |p| {
        const pre = try p.air.genPreprocessed(allocator, p.log_size);
        defer {
            for (pre) |c| allocator.free(c);
            allocator.free(pre);
        }
        const st = try base.toStorage(allocator, p.log_size, @ptrCast(pre));
        defer allocator.free(st);
        try cols.appendSlice(allocator, st);
    }
    return cols.toOwnedSlice(allocator);
}

/// Root of the preprocessed tree of `parts`, as the honest prover commits it.
pub fn preprocessedRoot(allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part) !rec.Hasher.Hash {
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var scheme = try E.initRevision(allocator, cfg);
    defer E.deinit(&scheme, allocator);
    var channel = rec.Channel{};
    try E.commit(&scheme, allocator, try preprocessedStorage(allocator, parts), null, &channel);
    try E.flushPendingCommit(&scheme, allocator, &channel);
    var roots = try scheme.roots(allocator);
    defer roots.deinit(allocator);
    return roots.items[0];
}

/// Per-row paired fractions of one component, in natural row order.
const Fractions = struct {
    /// `rows × batches`, natural row order.
    values: []logup_columns.Fraction,
    batches: usize,
    /// Storage (bit-reversed circle-domain) index → natural row.
    natural: []const usize,

    fn fill(self: *const Fractions, storage_row: usize, out: []logup_columns.Fraction) anyerror!void {
        @memcpy(out, self.values[self.natural[storage_row] * self.batches ..][0..self.batches]);
    }
};

fn fractions(allocator: std.mem.Allocator, part: Part, main: []const []const M31, el: lookup_transcript.LookupElements) !Fractions {
    const air = part.air.*;
    const n = @as(usize, 1) << @intCast(part.log_size);
    const B = component_mod.nBatches(air);
    const pre = try air.genPreprocessed(allocator, part.log_size);
    var trace = interp.RowTrace{ .log_size = part.log_size, .pubs = part.pubs, .preprocessed = @ptrCast(pre), .main = main };
    const scratch = try allocator.alloc(M31, air.exprs.len);
    const out = try allocator.alloc(M31, air.constraints.len);
    const values = try allocator.alloc(logup_columns.Fraction, n * B);
    var vals: [component_mod.MAX_LOOKUP_VALS]QM31 = undefined;
    for (0..n) |r| {
        trace.row = r;
        interp.evalConstraints(M31, air, part.pubs, scratch, &trace, out);
        for (0..B) |b| {
            var fr: [2]logup_columns.Fraction = undefined;
            const k: usize = if (2 * b + 1 < air.lookups.len) 2 else 1;
            for (0..k) |t| {
                const l = air.lookups[2 * b + t];
                for (l.vals, 0..) |v, i| vals[i] = QM31.fromBase(scratch[v]);
                fr[t] = .{ .numerator = QM31.fromBase(scratch[l.mult]), .denominator = component_mod.denominator(l.rel, vals[0..l.vals.len], el.z, el.alpha) };
            }
            values[r * B + b] = if (k == 2) .{
                .numerator = fr[0].numerator.mul(fr[1].denominator).add(fr[1].numerator.mul(fr[0].denominator)),
                .denominator = fr[0].denominator.mul(fr[1].denominator),
            } else fr[0];
        }
    }
    const natural = try allocator.alloc(usize, n);
    for (0..n) |i| natural[utils.bitReverseIndex(utils.cosetIndexToCircleDomainIndex(i, part.log_size), part.log_size)] = i;
    return .{ .values = values, .batches = B, .natural = natural };
}

/// Proves the system. `mains[i]` are part `i`'s main columns in natural row order.
/// `a` should be an arena (intermediate buffers are not freed individually).
pub fn prove(comptime E: type, caller_allocator: std.mem.Allocator, cfg: rec.Config, parts: []const Part, mains: []const []const []const M31) !Proof {
    // With several components the prover evaluates them on concurrent threads, and each
    // evaluator allocates from this allocator: callers may pass an arena, so serialize it.
    var thread_safe = std.heap.ThreadSafeAllocator{ .child_allocator = caller_allocator };
    const a = thread_safe.allocator();
    _ = try checkSizes(parts);
    var channel = rec.Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try E.initRevision(a, cfg);
    var scheme_owned = true;
    errdefer if (scheme_owned) E.deinit(&scheme, a);

    try E.commit(&scheme, a, try preprocessedStorage(a, parts), null, &channel);
    try E.flushPendingCommit(&scheme, a, &channel);
    try mixStatements(&channel, a, parts);
    var main_cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
    for (parts, mains) |p, m| {
        if (m.len != p.air.n_main) return error.InvalidPreparedGeometry;
        try main_cols.appendSlice(a, try base.toStorage(a, p.log_size, m));
    }
    try E.commit(&scheme, a, try main_cols.toOwnedSlice(a), null, &channel);
    try E.flushPendingCommit(&scheme, a, &channel);

    const comps = try components(a, parts);
    var sums = std.ArrayList(QM31).empty;
    if (hasLookups(parts)) {
        const el = try lookup_transcript.drawLookupElements(a, &channel);
        var inter_cols = std.ArrayList(prover_pcs.ColumnEvaluation).empty;
        for (parts, mains, comps) |p, m, *c| {
            if (p.air.lookups.len == 0) continue;
            const fr = try fractions(a, p, m, el);
            const built = try logup_columns.build(a, p.log_size, fr.batches, &fr, struct {
                fn f(ctx: *const Fractions, row: usize, out: []logup_columns.Fraction) anyerror!void {
                    return ctx.fill(row, out);
                }
            }.f);
            try inter_cols.appendSlice(a, built.columns);
            try sums.append(a, built.claimed_sum);
            c.logup = .{ .z = el.z, .alpha = el.alpha, .claimed_sum = built.claimed_sum };
        }
        lookup_transcript.mixInteractionClaim(&channel, sums.items);
        try E.commit(&scheme, a, try inter_cols.toOwnedSlice(a), null, &channel);
    }
    const provers = try a.alloc(prover_component.ComponentProver, comps.len);
    for (comps, provers) |*c, *p| p.* = c.asProverComponent();
    scheme_owned = false;
    var extended = try E.prove(a, provers, &channel, scheme, .{});
    extended.aux.deinit(a);
    return .{ .stark = extended.proof, .claimed_sums = try sums.toOwnedSlice(a) };
}

/// Verifies a system proof. `a` should be an arena.
pub fn verify(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, proof: Proof) !void {
    return verifyImpl(a, cfg, parts, &.{}, proof, null);
}

/// `verify` with public lookup entries: the relations balance with them included.
pub fn verifyExt(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof) !void {
    return verifyImpl(a, cfg, parts, ext, proof, null);
}

/// `verify`, also capturing what the in-circuit verifier needs (`plain_verifier.fromCapture`).
pub fn verifyCapture(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof, capture: *core.verifier.ProofCapture(rec.Hasher)) !void {
    return verifyImpl(a, cfg, parts, ext, proof, capture);
}

/// `Σ mult / (Σ eᵢ αⁱ − z)` over public entries.
pub fn extSum(ext: []const PubEntry, el: lookup_transcript.LookupElements) !QM31 {
    var sum = QM31.zero();
    var vals: [component_mod.MAX_LOOKUP_VALS]QM31 = undefined;
    for (ext) |e| {
        if (e.vals.len > vals.len) return error.LookupTooWide;
        for (e.vals, 0..) |v, i| vals[i] = QM31.fromBase(v);
        const d = component_mod.denominator(e.rel, vals[0..e.vals.len], el.z, el.alpha);
        sum = sum.add(QM31.fromBase(e.mult).mul(try d.inv()));
    }
    return sum;
}

fn verifyImpl(a: std.mem.Allocator, cfg: rec.Config, parts: []const Part, ext: []const PubEntry, proof: Proof, capture: ?*core.verifier.ProofCapture(rec.Hasher)) !void {
    _ = try checkSizes(parts);
    const lookups = hasLookups(parts);
    const n_trees: usize = if (lookups) 3 else 2;
    if (proof.stark.commitment_scheme_proof.commitments.items.len != n_trees + 1) return error.InvalidProofShape;
    var channel = rec.Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(rec.Hasher, rec.MerkleChannel).init(a, cfg);
    defer scheme.deinit(a);

    var pre_logs = std.ArrayList(u32).empty;
    var main_logs = std.ArrayList(u32).empty;
    var inter_logs = std.ArrayList(u32).empty;
    for (parts) |p| {
        try pre_logs.appendNTimes(a, p.log_size, p.air.n_preprocessed);
        try main_logs.appendNTimes(a, p.log_size, p.air.n_main);
        try inter_logs.appendNTimes(a, p.log_size, 4 * component_mod.nBatches(p.air.*));
    }
    const roots = proof.stark.commitment_scheme_proof.commitments.items;
    const expected_pre = try preprocessedRoot(a, cfg, parts);
    if (!std.mem.eql(u8, std.mem.asBytes(&expected_pre), std.mem.asBytes(&roots[0]))) return error.PreprocessedRootMismatch;
    try scheme.commit(a, roots[0], pre_logs.items, &channel);
    try mixStatements(&channel, a, parts);
    try scheme.commit(a, roots[1], main_logs.items, &channel);

    const comps = try components(a, parts);
    if (lookups) {
        const el = try lookup_transcript.drawLookupElements(a, &channel);
        var n_with: usize = 0;
        for (parts) |p| {
            if (p.air.lookups.len != 0) n_with += 1;
        }
        if (proof.claimed_sums.len != n_with) return error.InvalidProofShape;
        // The relations balance: the claimed sums and the public entries add to zero.
        var total = try extSum(ext, el);
        for (proof.claimed_sums) |s| total = total.add(s);
        if (!total.isZero()) return error.LookupsUnbalanced;
        var k: usize = 0;
        for (parts, comps) |p, *c| {
            if (p.air.lookups.len == 0) continue;
            c.logup = .{ .z = el.z, .alpha = el.alpha, .claimed_sum = proof.claimed_sums[k] };
            k += 1;
        }
        lookup_transcript.mixInteractionClaim(&channel, proof.claimed_sums);
        try scheme.commit(a, roots[2], inter_logs.items, &channel);
    }
    const verifiers = try a.alloc(core.air.components.Component, comps.len);
    for (comps, verifiers) |*c, *v| v.* = c.asVerifierComponent();
    if (capture) |c|
        try core.verifier.verifyWithProofCapture(rec.Hasher, rec.MerkleChannel, a, verifiers, &channel, &scheme, proof.stark, c)
    else
        try core.verifier.verify(rec.Hasher, rec.MerkleChannel, a, verifiers, &channel, &scheme, proof.stark);
}

// ---------------------------------------------------------------- tests

/// Toy system from Lean (`Testing/ByteLookup.lean`, theorem `user_bytes`): a byte table
/// (preprocessed 0..255, main multiplicity column) and a user whose main column is looked up with
/// multiplicity −1.
pub fn byteSystem(a: std.mem.Allocator) ![2]ir.Air {
    return .{
        (try ir.Air.parseJson(a, @embedFile("air:byte_table"))).value,
        (try ir.Air.parseJson(a, @embedFile("air:byte_user"))).value,
    };
}

test "LogUp system: a byte range check proves and verifies; out-of-range values are rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try byteSystem(a);
    const log_size: u32 = 8;
    const n = 256;
    const parts = [_]Part{ .{ .air = &airs[0], .log_size = log_size }, .{ .air = &airs[1], .log_size = log_size } };
    const cfg = rec.Config.fromFriAndTraceSize(try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);

    var prng = std.Random.DefaultPrng.init(7);
    const x = try a.alloc(M31, n);
    const mult = try a.alloc(M31, n);
    @memset(mult, M31.zero());
    for (x) |*v| {
        const b = prng.random().int(u8);
        v.* = M31.fromCanonical(b);
        mult[b] = mult[b].add(M31.one());
    }
    const mains = [_][]const []const M31{ &.{mult}, &.{x} };
    try verify(a, cfg, &parts, try prove(E, a, cfg, &parts, &mains));

    // A value outside the table cannot balance (whatever the multiplicities).
    const bad = try a.dupe(M31, x);
    bad[3] = M31.fromCanonical(300);
    const bad_mains = [_][]const []const M31{ &.{mult}, &.{bad} };
    try std.testing.expectError(error.LookupsUnbalanced, verify(a, cfg, &parts, try prove(E, a, cfg, &parts, &bad_mains)));

    // Forged claimed sums that add to zero do not match the committed interaction columns.
    var forged = try prove(E, a, cfg, &parts, &bad_mains);
    forged.claimed_sums[1] = forged.claimed_sums[0].neg();
    try std.testing.expect(std.meta.isError(verify(a, cfg, &parts, forged)));
}
