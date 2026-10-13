//! The one-read terminal proof of a resident block-system proof: stwo-zig's SWPC envelope
//! (`native_cuda/common/proof_bundle.zig`) with our cardinalities, adapted from
//! `circuit_cuda/resident_terminal_bundle.zig`, `resident_terminal_decode.zig` and
//! `resident_terminal_capture.zig`.
//!
//! Differences from the circuit: the claims are ours (one per component with lookups, as
//! `system.Proof.claimed_sums`), and there is no interaction grind, so the first nonce pair of the
//! proof-of-work section stays zero. The STARK part decodes with stwo-zig's generic decoder over
//! our `masks.ProofLayout`; the result is `system.Proof`.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const cc = @import("stwo_circuit_cuda_integration");
const canonical = @import("stwo_cairo_frontend").witness.proof_bundle;
const native = @import("stwo_native_cuda_integration").common;
const shared = native.proof_bundle;
const masks = @import("masks.zig");
const common = cuda.runtime.stages.common;
const QM31 = core.fields.qm31.QM31;
const Plain = core.vcs_lifted.blake2_merkle.Blake2sPlainMerkleHasher;

pub const Layout = struct {
    claims: usize,
    sampled_values: usize,
    fri_roots: usize,
    final_coefficients: usize,
    query_count: u32,
    query_pow_bits: u32,
    blowup: u32,
    fold_step: u32,
    max_log_degree_bound: u32,

    pub fn init(geometry: *const cc.geometry.Geometry, oods: *const masks.OodsPlan, claims: usize, config: core.pcs.config_v2.PcsConfigV2) !Layout {
        if (geometry.fri_layers.len == 0 or geometry.fri_layers.len > 64 or oods.offsets.len == 0 or
            config.fri_config.n_queries == 0 or config.fri_config.fold_step == 0 or claims == 0)
            return error.InvalidTerminalGeometry;
        return .{
            .claims = claims,
            .sampled_values = oods.offsets.len,
            .fri_roots = geometry.fri_layers.len,
            .final_coefficients = try shared.pow2(config.fri_config.log_last_layer_degree_bound),
            .query_count = config.fri_config.n_queries,
            .query_pow_bits = config.fri_config.pow_bits,
            .blowup = config.fri_config.log_blowup_factor,
            .fold_step = config.fri_config.fold_step,
            .max_log_degree_bound = geometry.composition_evaluation_log,
        };
    }
};

pub const Decommit = struct { capacity_words: usize };

const Descriptor = struct {
    pub fn sectionLengths(logical: Layout, decommit: Decommit) ![shared.section_count]usize {
        if (logical.sampled_values == 0 or logical.fri_roots == 0 or logical.final_coefficients == 0 or decommit.capacity_words == 0)
            return error.InvalidTerminalGeometry;
        return .{
            try shared.add(4 * 8, try shared.mul(logical.claims, 4)),
            try shared.mul(logical.sampled_values, 4),
            try shared.mul(logical.fri_roots, 8),
            try shared.mul(logical.final_coefficients, 4),
            4, // (no interaction grind: zero) then the query-grind nonce
            decommit.capacity_words,
        };
    }

    pub fn fixedHeader(logical: Layout, _: Decommit, total_words: usize) ![shared.fixed_header_words]u32 {
        return .{
            shared.magic,
            shared.version,
            try shared.u32Count(total_words),
            shared.section_count,
            4,
            try shared.u32Count(logical.claims),
            try shared.u32Count(try shared.mul(logical.sampled_values, 4)),
            try shared.u32Count(logical.fri_roots),
            try shared.u32Count(logical.final_coefficients),
            logical.query_count,
            logical.query_pow_bits,
            0, // interaction grind bits
            logical.max_log_degree_bound,
            logical.blowup,
            logical.fold_step,
            std.math.maxInt(u32), // final-layer degree verdict, device-written
        };
    }
};

pub const Bundle = shared.BundleFor(Layout, Decommit, Descriptor);

// ------------------------------------------------------------------ capture (device side)

/// Our claimed sums into the trace-commitment section, after the four roots.
pub fn captureClaims(session: anytype, proof: native.resident_views.Proof, claims: common.SecureFields) !void {
    if (proof.trace_commitments.len != 4 * 8 + claims.len * 4) return error.InvalidTerminalBinding;
    try session.context.copyDeviceSlice(u32, try proof.trace_commitments.sub(4 * 8, claims.len * 4), try claims.cast(u32));
}

pub const captureQueryNonce = cc.resident_terminal_capture.captureQueryNonce;
pub const sealVerdict = cc.resident_terminal_capture.sealVerdict;

// ------------------------------------------------------------------ decode (host side)

pub const MeasuredRead = cc.resident_terminal_decode.MeasuredRead;

pub const Proof = struct {
    words: []u32,
    decoded: canonical.ProofBundle,
    read: MeasuredRead,

    pub fn deinit(self: *Proof, allocator: std.mem.Allocator) void {
        self.decoded.deinit(allocator);
        allocator.free(self.words);
        self.* = undefined;
    }

    pub fn decode(allocator: std.mem.Allocator, layout: Layout, decommit: Decommit, transport: []const u32, read: MeasuredRead) !Proof {
        var descriptor = try Bundle.init(allocator, layout, decommit);
        defer descriptor.deinit(allocator);
        try descriptor.validate(decommit.capacity_words);
        try read.validate(descriptor.total_words);
        try validateEnvelope(descriptor, transport);
        const wire_layout = try canonical.Layout.initRuntime(
            4,
            try shared.mul(layout.claims, 4),
            try shared.mul(layout.sampled_values, 4),
            layout.fri_roots,
            try shared.mul(layout.final_coefficients, 4),
            decommit.capacity_words,
        );
        const words = try allocator.alloc(u32, wire_layout.total_words);
        errdefer allocator.free(words);
        try reorder(descriptor, transport, wire_layout, words);
        var decoded = try canonical.ProofBundle.decode(allocator, words, wire_layout);
        errdefer decoded.deinit(allocator);
        if (decoded.decommitment.raw_queries.len != layout.query_count or decoded.decommitment.trees.len != 4 + layout.fri_roots)
            return error.InvalidTerminalDecommitment;
        const capacity = words[wire_layout.decommitment.start..wire_layout.decommitment.end];
        for (capacity[decoded.decommitment.words.len..]) |word| if (word != 0) return error.NonzeroTerminalDecommitmentTail;
        return .{ .words = words, .decoded = decoded, .read = read };
    }

    /// The claimed sums, as `system.Proof.claimed_sums`.
    pub fn claimedSums(self: *const Proof, allocator: std.mem.Allocator) ![]QM31 {
        const w = self.words[self.decoded.layout.interaction_claim.start..self.decoded.layout.interaction_claim.end];
        const out = try allocator.alloc(QM31, w.len / 4);
        for (out, 0..) |*s, i| s.* = QM31.fromU32Unchecked(w[4 * i], w[4 * i + 1], w[4 * i + 2], w[4 * i + 3]);
        return out;
    }

    /// The STARK proof under the plain Blake2s Merkle profile (`rec.Proof`).
    pub fn decodeStarkProof(self: *const Proof, allocator: std.mem.Allocator, logical: *const masks.ProofLayout, config: core.pcs.config_v2.PcsConfigV2) !core.proof.StarkProof(Plain) {
        try logical.validate();
        const decommit_words = self.words[self.decoded.layout.decommitment.start..self.decoded.layout.decommitment.end];
        var nested = try cuda.runtime.proof_assembly.decommit_bundle.Bundle.decodeBorrowed(allocator, decommit_words);
        defer nested.deinit(allocator);
        const view = StarkView{
            .proof = self,
            .decommitment = nested,
            .protocol = .{
                .log_n_rows = logical.fri_trees[0].evaluation_log_size,
                .sequence_len = 0,
                .pow_bits = config.fri_config.pow_bits,
                .log_blowup_factor = config.fri_config.log_blowup_factor,
                .log_last_layer_degree_bound = config.fri_config.log_last_layer_degree_bound,
                .n_queries = config.fri_config.n_queries,
                .fold_step = config.fri_config.fold_step,
                .lifting_log_size = config.trace_lifting_log_size,
                .commitment_root_count = 4,
                .fri_root_count = @intCast(logical.fri_trees.len),
                .decommit_tree_count = @intCast(4 + logical.fri_trees.len),
            },
        };
        const Decoder = native.proof_decode.DecoderFor(masks.ProofLayout, struct {});
        return Decoder.decodeProofWithLayoutFor(Plain, allocator, view, logical);
    }

    /// `system.Proof` (the caller verifies it with `system.verifyExt`).
    pub fn toSystemProof(self: *const Proof, allocator: std.mem.Allocator, logical: *const masks.ProofLayout, config: core.pcs.config_v2.PcsConfigV2) !sb.air.system.Proof {
        var stark = try self.decodeStarkProof(allocator, logical, config);
        errdefer stark.deinit(allocator);
        // stwo-zig's decoder records the lifting height in the legacy `PcsConfig` view; the CPU
        // prover under `proving_5a7c5ed` leaves it empty (the height lives in `PcsConfigV2`). The
        // postcard encoding includes it, so match the CPU's bytes.
        stark.commitment_scheme_proof.config.lifting_log_size = null;
        return .{ .stark = stark, .claimed_sums = try self.claimedSums(allocator) };
    }
};

const StarkView = struct {
    proof: *const Proof,
    decommitment: cuda.runtime.proof_assembly.decommit_bundle.Bundle,
    protocol: cuda.runtime.proof_assembly.stark_bundle.Protocol,

    fn words(self: StarkView, range: canonical.Range) []const u32 {
        return self.proof.words[range.start..range.end];
    }
    pub fn commitmentRoots(self: StarkView) []const u32 {
        return self.words(self.proof.decoded.layout.commitments);
    }
    pub fn sampledValues(self: StarkView) []const u32 {
        return self.words(self.proof.decoded.layout.sampled_values);
    }
    pub fn friRoots(self: StarkView) []const u32 {
        return self.words(self.proof.decoded.layout.fri_commitments);
    }
    pub fn lastLayerPolynomial(self: StarkView) []const u32 {
        return self.words(self.proof.decoded.layout.final_line_poly);
    }
    pub fn powNonce(self: StarkView) u64 {
        const nonce = self.words(self.proof.decoded.layout.query_pow);
        return @as(u64, nonce[0]) | (@as(u64, nonce[1]) << 32);
    }
};

fn validateEnvelope(descriptor: Bundle, transport: []const u32) !void {
    if (transport.len != descriptor.total_words or transport.len < shared.header_words) return error.InvalidTerminalHeader;
    for (descriptor.static_header, 0..) |expected, index| {
        const finalized = if (index == 15) @as(u32, 0) else expected;
        if (transport[index] != finalized) return if (index == 15) error.InvalidFriDegree else error.InvalidTerminalHeader;
    }
}

fn reorder(descriptor: Bundle, transport: []const u32, layout: canonical.Layout, output: []u32) !void {
    if (output.len != layout.total_words) return error.InvalidTerminalLength;
    const roots_and_claims = section(descriptor, transport, .trace_commitments);
    const commitments = layout.commitments.end - layout.commitments.start;
    const claims = layout.interaction_claim.end - layout.interaction_claim.start;
    if (roots_and_claims.len != commitments + claims) return error.InvalidTerminalHeader;
    @memcpy(output[layout.commitments.start..layout.commitments.end], roots_and_claims[0..commitments]);
    @memcpy(output[layout.interaction_claim.start..layout.interaction_claim.end], roots_and_claims[commitments..]);
    const pow = section(descriptor, transport, .proof_of_work);
    if (pow.len != 4) return error.InvalidTerminalHeader;
    @memcpy(output[layout.interaction_pow.start..layout.interaction_pow.end], pow[0..2]);
    @memcpy(output[layout.query_pow.start..layout.query_pow.end], pow[2..4]);
    @memcpy(output[layout.sampled_values.start..layout.sampled_values.end], section(descriptor, transport, .sampled_values));
    @memcpy(output[layout.fri_commitments.start..layout.fri_commitments.end], section(descriptor, transport, .fri_commitments));
    @memcpy(output[layout.final_line_poly.start..layout.final_line_poly.end], section(descriptor, transport, .fri_last_layer));
    @memcpy(output[layout.decommitment.start..layout.decommitment.end], section(descriptor, transport, .decommitment));
}

fn section(descriptor: Bundle, words: []const u32, kind: shared.SectionKind) []const u32 {
    const part = descriptor.section(kind);
    return words[part.offset_words .. part.offset_words + part.words];
}

test "terminal: a poisoned or unmeasured envelope is rejected" {
    const allocator = std.testing.allocator;
    const layout = Layout{ .claims = 15, .sampled_values = 1, .fri_roots = 1, .final_coefficients = 1, .query_count = 1, .query_pow_bits = 1, .blowup = 1, .fold_step = 1, .max_log_degree_bound = 3 };
    const decommit = Decommit{ .capacity_words = 64 };
    var descriptor = try Bundle.init(allocator, layout, decommit);
    defer descriptor.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 4 * 8 + 15 * 4), descriptor.section(.trace_commitments).words);
    const words = try allocator.dupe(u32, descriptor.static_header);
    defer allocator.free(words);
    const unread = MeasuredRead{ .operations = 0, .bytes = words.len * 4, .runtime_compile_attempts = 0, .cpu_fallback_attempts = 0 };
    try std.testing.expectError(error.InvalidTerminalRead, Proof.decode(allocator, layout, decommit, words, unread));
    const measured = MeasuredRead{ .operations = 1, .bytes = descriptor.total_words * 4, .runtime_compile_attempts = 0, .cpu_fallback_attempts = 0 };
    try std.testing.expectError(error.InvalidTerminalHeader, Proof.decode(allocator, layout, decommit, words, measured));
}
