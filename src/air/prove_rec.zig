//! Prove and verify an `ir.Air` under the `proving_5a7c5ed` protocol revision: the
//! Blake2sM31 channel, the unprefixed Blake2s Merkle hasher and `PcsConfigV2` (PoW inside FRI,
//! two-felt config mix, explicit lifting heights). This is the profile stwo-zig's circuit
//! recursion verifies (roadmap REC-PROFILE; docs/design/recursion.md).
//!
//! Staging module: stwo-zig's generic `transaction.provePreparedEx` only implements the legacy
//! revision, so this mirrors its (non-interaction) steps with `initRevision` and
//! `Revision.mixConfig`. A candidate for upstreaming to stwo-zig (decision D-008).
//! Transcript: config → preprocessed commitment → statement (`prove.mixStatement`) → main
//! commitment → STARK. The verifier pins the preprocessed root, as in `prove.zig`.

const std = @import("std");
const core = @import("stwo_core");
const ir = @import("ir.zig");
const base = @import("prove.zig");
const component_mod = @import("component.zig");
const prover_engine = @import("stwo_prover_engine").engine;
const prover_component = @import("stwo_prover_engine").air.component_prover;
const M31 = core.fields.m31.M31;

pub const MerkleChannel = core.vcs_lifted.channel_profile.proving_5a7c5ed.Blake2sM31MerkleChannel;
pub const Hasher = MerkleChannel.MerkleHasher;
pub const Channel = MerkleChannel.Channel;
pub const Proof = core.proof.StarkProof(Hasher);
pub const Config = core.pcs.config_v2.PcsConfigV2;
const Revision = core.protocol_revision.Revision;

comptime {
    std.debug.assert(Revision.of(MerkleChannel) == .proving_5a7c5ed);
}

pub fn Engine(comptime Backend: type) type {
    return prover_engine.ProverEngine(Backend, Hasher, MerkleChannel, Channel);
}

/// The production FRI parameters (70 queries, 26-bit PoW, blowup 1, fold step 1), with every
/// tree lifted to the trace's extended domain.
pub fn config(log_size: u32) !Config {
    const fri = try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1);
    return Config.fromFriAndTraceSize(fri, log_size);
}

pub fn prove(
    comptime E: type,
    allocator: std.mem.Allocator,
    cfg: Config,
    statement: base.AirStatement,
    main: []const []const M31,
) !Proof {
    var prepared = try base.prepare(allocator, statement, main);
    defer prepared.deinit(allocator);
    var channel = Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try E.initRevision(allocator, cfg);
    var scheme_owned = true;
    errdefer if (scheme_owned) E.deinit(&scheme, allocator);
    {
        const owned = prepared.trace.preprocessed.takeWithBacking();
        try E.commitPreparedWithBacking(&scheme, allocator, owned.columns, owned.backing_buffers, owned.source, null, &channel);
    }
    try E.flushPendingCommit(&scheme, allocator, &channel);
    base.mixStatement(&channel, statement.log_size, statement.digest, statement.pubs);
    {
        const owned = prepared.trace.main.takeWithBacking();
        try E.commitPreparedWithBacking(&scheme, allocator, owned.columns, owned.backing_buffers, owned.source, null, &channel);
    }
    var component = try component_mod.Component.init(allocator, statement.air.*, statement.log_size, statement.pubs);
    defer component.deinit();
    const components = [_]prover_component.ComponentProver{component.asProverComponent()};
    scheme_owned = false;
    var extended = try E.prove(allocator, components[0..], &channel, scheme, .{});
    extended.aux.deinit(allocator);
    return extended.proof;
}

/// Root of the preprocessed tree as the honest prover commits it under this revision.
pub fn preprocessedRoot(allocator: std.mem.Allocator, cfg: Config, air: ir.Air, log_size: u32) !Hasher.Hash {
    const pre = try air.genPreprocessed(allocator, log_size);
    defer {
        for (pre) |c| allocator.free(c);
        allocator.free(pre);
    }
    const E = Engine(@import("stwo_cpu_backend").CpuBackend);
    var scheme = try E.initRevision(allocator, cfg);
    defer E.deinit(&scheme, allocator);
    var channel = Channel{};
    try E.commit(&scheme, allocator, try base.toStorage(allocator, log_size, @ptrCast(pre)), null, &channel);
    try E.flushPendingCommit(&scheme, allocator, &channel);
    var roots = try scheme.roots(allocator);
    defer roots.deinit(allocator);
    return roots.items[0];
}

pub fn verify(
    allocator: std.mem.Allocator,
    cfg: Config,
    air: ir.Air,
    log_size: u32,
    pubs: []const M31,
    proof_in: Proof,
) !void {
    var proof = proof_in;
    var moved = false;
    defer if (!moved) proof.deinit(allocator);
    if (proof.commitment_scheme_proof.commitments.items.len != 3) return error.InvalidProofShape;

    var channel = Channel{};
    Revision.proving_5a7c5ed.mixConfig(cfg, &channel);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(Hasher, MerkleChannel).init(allocator, cfg);
    defer scheme.deinit(allocator);

    const pre_logs = try allocator.alloc(u32, air.n_preprocessed);
    defer allocator.free(pre_logs);
    @memset(pre_logs, log_size);
    const main_logs = try allocator.alloc(u32, air.n_main);
    defer allocator.free(main_logs);
    @memset(main_logs, log_size);

    const expected_pre = try preprocessedRoot(allocator, cfg, air, log_size);
    if (!std.mem.eql(u8, std.mem.asBytes(&expected_pre), std.mem.asBytes(&proof.commitment_scheme_proof.commitments.items[0])))
        return error.PreprocessedRootMismatch;
    try scheme.commit(allocator, proof.commitment_scheme_proof.commitments.items[0], pre_logs, &channel);
    base.mixStatement(&channel, log_size, try air.digest(allocator), pubs);
    try scheme.commit(allocator, proof.commitment_scheme_proof.commitments.items[1], main_logs, &channel);

    var component = try component_mod.Component.init(allocator, air, log_size, pubs);
    defer component.deinit();
    const components = [_]core.air.components.Component{component.asVerifierComponent()};
    moved = true;
    try core.verifier.verify(Hasher, MerkleChannel, allocator, components[0..], &channel, &scheme, proof);
}

test "header chain segment proves and verifies under the recursion profile" {
    const H = @import("../btc/header_chain.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, H.lean_json)).value;
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const wit = try H.generate(a, 12, headers);
    const cfg = try config(12);
    const statement = base.AirStatement{ .log_size = 12, .digest = try air.digest(a), .pubs = &wit.pubs, .air = &air, .allocator = a };
    const E = Engine(@import("stwo_cpu_backend").CpuBackend);
    try verify(a, cfg, air, 12, &wit.pubs, try prove(E, a, cfg, statement, @ptrCast(wit.main)));
    // The same proof against a different claimed tip must fail.
    var other = wit.pubs;
    other[16] = other[16].add(M31.one());
    try std.testing.expect(std.meta.isError(verify(a, cfg, air, 12, &other, try prove(E, a, cfg, statement, @ptrCast(wit.main)))));
}
