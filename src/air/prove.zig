//! Prove and verify any `ir.Air` (main + preprocessed trees, no interaction yet)
//! with stwo-zig's generic prover engine on any backend (CPU, Metal, ...).
//!
//! Transcript: pcs config → preprocessed commitment → statement
//! (`log_size`, the AIR digest and the public inputs) → main commitment → STARK.
//! The AIR digest binds the exact constraint program into Fiat–Shamir.

const std = @import("std");
const ir = @import("ir.zig");
const component_mod = @import("component.zig");
const core_air_components = @import("stwo_core").air.components;
const channel_blake2s = @import("stwo_core").channel.blake2s;
const pcs_core = @import("stwo_core").pcs;
const pcs_verifier = @import("stwo_core").pcs.verifier;
const core_proof = @import("stwo_core").proof;
const core_verifier = @import("stwo_core").verifier;
const blake2_merkle = @import("stwo_core").vcs_lifted.blake2_merkle;
const utils = @import("stwo_core").utils;
const M31 = @import("stwo_core").fields.m31.M31;
const prover_component = @import("stwo_prover_engine").air.component_prover;
const prover_engine = @import("stwo_prover_engine").engine;
const prover_transaction = @import("stwo_prover_engine").transaction;
const prover_pcs = @import("stwo_prover_engine").pcs;

pub const Hasher = blake2_merkle.Blake2sPrefixedMerkleHasher;
pub const MerkleChannel = blake2_merkle.Blake2sPrefixedMerkleChannel;
pub const Channel = channel_blake2s.Blake2sChannel;
pub const Proof = core_proof.StarkProof(Hasher);

pub fn Engine(comptime Backend: type) type {
    return prover_engine.ProverEngine(Backend, Hasher, MerkleChannel, Channel);
}

pub const AirStatement = struct {
    log_size: u32,
    digest: [32]u8,
    /// Public inputs (canonical M31 values).
    pubs: []const M31 = &.{},
    /// Not part of the public statement; carried so the spec can build the component.
    air: *const ir.Air,
    allocator: std.mem.Allocator,
};

/// Statement transcript: `log_size`, the AIR digest and the public inputs. Shared with
/// `prove_rec.zig`, so both protocol revisions bind the same statement.
pub fn mixStatement(channel: anytype, log_size: u32, digest: [32]u8, pubs: []const M31) void {
    var words: [10]u32 = undefined;
    words[0] = log_size;
    for (0..8) |i| words[1 + i] = std.mem.readInt(u32, digest[4 * i ..][0..4], .little);
    words[9] = @intCast(pubs.len);
    channel.mixU32s(&words);
    for (pubs) |p| channel.mixU32s(&.{p.toU32()});
}

pub const Prepared = prover_transaction.PreparedInput(AirStatement);

/// `main` columns in natural row order (row i = i-th point of the canonic
/// coset). Preprocessed columns are generated from the AIR definition.
pub fn prepare(
    allocator: std.mem.Allocator,
    statement: AirStatement,
    main: []const []const M31,
) !Prepared {
    const pre = try statement.air.genPreprocessed(allocator, statement.log_size);
    defer {
        for (pre) |c| allocator.free(c);
        allocator.free(pre);
    }
    return .{
        .request = statement,
        .trace = try prover_transaction.PreparedTrace.initOwned(
            allocator,
            try toStorage(allocator, statement.log_size, @ptrCast(pre)),
            try toStorage(allocator, statement.log_size, main),
        ),
    };
}

/// Root of the preprocessed tree as the honest prover commits it, recomputed
/// from the AIR definition with the CPU commitment scheme.
pub fn preprocessedRoot(
    allocator: std.mem.Allocator,
    pcs_config: pcs_core.PcsConfig,
    air: ir.Air,
    log_size: u32,
) !Hasher.Hash {
    const pre = try air.genPreprocessed(allocator, log_size);
    defer {
        for (pre) |c| allocator.free(c);
        allocator.free(pre);
    }
    const E = Engine(@import("stwo_cpu_backend").CpuBackend);
    var scheme = try E.init(allocator, pcs_config);
    defer E.deinit(&scheme, allocator);
    var channel = Channel{};
    try E.commit(&scheme, allocator, try toStorage(allocator, log_size, @ptrCast(pre)), null, &channel);
    var roots = try scheme.roots(allocator);
    defer roots.deinit(allocator);
    return roots.items[0];
}

pub fn toStorage(allocator: std.mem.Allocator, log_size: u32, columns: []const []const M31) ![]prover_pcs.ColumnEvaluation {
    const n = @as(usize, 1) << @intCast(log_size);
    const out = try allocator.alloc(prover_pcs.ColumnEvaluation, columns.len);
    var done: usize = 0;
    errdefer {
        for (out[0..done]) |o| allocator.free(o.values);
        allocator.free(out);
    }
    for (columns, out) |col, *o| {
        if (col.len != n) return error.InvalidPreparedGeometry;
        o.* = .{ .log_size = log_size, .values = try allocator.alloc(M31, n) };
        done += 1;
    }
    // The storage position of every natural row, computed once for all the columns, which are then
    // permuted on all cores.
    const position = try allocator.alloc(u32, n);
    defer allocator.free(position);
    for (position, 0..) |*p, i| p.* = @intCast(utils.bitReverseIndex(utils.cosetIndexToCircleDomainIndex(i, log_size), log_size));
    const Job = struct {
        fn run(next: *std.atomic.Value(usize), pos: []const u32, src: []const []const M31, dst: []const prover_pcs.ColumnEvaluation) void {
            while (true) {
                const c = next.fetchAdd(1, .monotonic);
                if (c >= src.len) return;
                const values = @constCast(dst[c].values); // allocated above, not shared yet
                for (src[c], pos) |v, p| values[p] = v;
            }
        }
    };
    var next = std.atomic.Value(usize).init(0);
    const n_threads = @min(std.Thread.getCpuCount() catch 1, 64, columns.len) -| 1;
    var threads: [64]?std.Thread = @splat(null);
    for (threads[0..n_threads]) |*t| t.* = std.Thread.spawn(.{}, Job.run, .{ &next, position, columns, out }) catch null;
    Job.run(&next, position, columns, out);
    for (threads[0..n_threads]) |t| if (t) |th| th.join();
    return out;
}

const Spec = struct {
    pub const Statement = AirStatement;
    pub const PreparedInput = Prepared;
    pub const max_components: usize = 1;

    pub const ProverContext = struct {
        statement_value: AirStatement,
        component: component_mod.Component,
    };

    pub fn validateRequest(request: AirStatement) !void {
        if (!std.mem.eql(u8, &request.digest, &(try request.air.digest(request.allocator))))
            return error.DigestMismatch;
    }

    pub fn validatePrepared(prepared: *const Prepared) !void {
        const pre = prepared.trace.preprocessed.columns orelse return error.PreparedInputConsumed;
        const main = prepared.trace.main.columns orelse return error.PreparedInputConsumed;
        if (pre.len != prepared.request.air.n_preprocessed or main.len != prepared.request.air.n_main)
            return error.InvalidPreparedGeometry;
    }

    pub fn compositionLog(request: AirStatement) !u32 {
        return request.log_size + 1;
    }

    pub fn beforeMainCommit(channel: *Channel, request: AirStatement) !void {
        mixStatement(channel, request.log_size, request.digest, request.pubs);
    }

    pub fn initProverContext(out: *ProverContext, _: *Channel, request: AirStatement) !void {
        out.* = .{
            .statement_value = request,
            .component = try component_mod.Component.init(request.allocator, request.air.*, request.log_size, request.pubs),
        };
    }

    pub fn statement(context: *const ProverContext) AirStatement {
        return context.statement_value;
    }

    pub fn proverComponents(
        context: *const ProverContext,
        out: []prover_component.ComponentProver,
    ) ![]const prover_component.ComponentProver {
        out[0] = context.component.asProverComponent();
        return out[0..1];
    }
};

pub fn prove(
    comptime E: type,
    allocator: std.mem.Allocator,
    pcs_config: pcs_core.PcsConfig,
    prepared: Prepared,
) !Proof {
    var output = try prover_transaction.provePreparedEx(
        E,
        Spec,
        false,
        {},
        allocator,
        pcs_config,
        prepared,
        .{},
    );
    output.proof.aux.deinit(allocator);
    return output.proof.proof;
}

/// Verifies `proof` for the AIR and statement. The verifier recomputes the AIR
/// digest itself; it never trusts a digest supplied with the proof.
pub fn verify(
    allocator: std.mem.Allocator,
    pcs_config: pcs_core.PcsConfig,
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
    pcs_config.mixInto(&channel);
    var scheme = try pcs_verifier.CommitmentSchemeVerifier(Hasher, MerkleChannel).init(allocator, pcs_config);
    defer scheme.deinit(allocator);

    const pre_logs = try allocator.alloc(u32, air.n_preprocessed);
    defer allocator.free(pre_logs);
    @memset(pre_logs, log_size);
    const main_logs = try allocator.alloc(u32, air.n_main);
    defer allocator.free(main_logs);
    @memset(main_logs, log_size);

    const expected_pre = try preprocessedRoot(allocator, pcs_config, air, log_size);
    if (!std.mem.eql(u8, std.mem.asBytes(&expected_pre), std.mem.asBytes(&proof.commitment_scheme_proof.commitments.items[0])))
        return error.PreprocessedRootMismatch;
    try scheme.commit(allocator, proof.commitment_scheme_proof.commitments.items[0], pre_logs, &channel);
    mixStatement(&channel, log_size, try air.digest(allocator), pubs);
    try scheme.commit(allocator, proof.commitment_scheme_proof.commitments.items[1], main_logs, &channel);

    var component = try component_mod.Component.init(allocator, air, log_size, pubs);
    defer component.deinit();
    const components = [_]core_air_components.Component{component.asVerifierComponent()};
    moved = true;
    try core_verifier.verify(Hasher, MerkleChannel, allocator, components[0..], &channel, &scheme, proof);
}
