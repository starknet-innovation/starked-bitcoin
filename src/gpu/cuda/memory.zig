//! The one device arena of a resident block-system proof: slot inventory with stage lifetimes
//! (adapted from `circuit_cuda/resident_memory_plan.zig`) and typed views of every stage's buffers
//! (adapted from `resident_memory_binding.zig`).
//!
//! Differences from the circuit:
//! - No circuit witness (`values`), interaction producers or circuit hash. Trace columns are
//!   uploaded at ingress into a staging slot per tree and moved (trees 0–1: reordered natural →
//!   storage, `reorder.zig`) into each tree's coefficient buffer in `.trace_generation`, where the
//!   commitment interpolates them in place (`resident_commit.loadEvaluations` skips the copy when
//!   source and target coincide). The staging slots die there.
//! - New ingress slots: the statement words, the claimed sums (as mixed, and per component for
//!   the composition), the lookup `z` and the powers `α⁰…α^w`.
//! - Device witness (`witness.zig`): `witness_inputs` (ingress → `.trace_generation`) and the SHA
//!   word trace `witness_scratch` (`.trace_generation`); the generators write the staging slots.
//! - Slot ids are `kind · 2¹⁶ + ordinal` (the circuit's `· 256` cannot hold our column counts).

const std = @import("std");
const cuda = @import("stwo_cuda_backend");
const cc = @import("stwo_circuit_cuda_integration");
const cairo = @import("stwo_cairo_cuda_integration");
const shared = @import("stwo_native_cuda_integration").common;
const transcript = @import("transcript.zig");
const controller = @import("composition_controller.zig");
const terminal = @import("terminal.zig");
const masks = @import("masks.zig");
const arena = cuda.runtime.arena;
const Stage = cuda.runtime.telemetry.Stage;
const field = cuda.abi.field;
const common = cuda.runtime.stages.common;
const commit = cc.resident_commit;
const fri = @import("fri.zig");
const decommit = cc.resident_decommit;
const Quotient = cairo.executor.quotient.controller.QuotientBindings;
const logup = @import("logup.zig");

pub const Kind = enum(u8) {
    trace_staging,
    commit_coefficients,
    commit_evaluations,
    commit_logs,
    commit_hashes,
    commit_layers,
    twiddles_forward,
    twiddles_inverse,
    transcript_state,
    transcript_boundary,
    transcript_config,
    transcript_lookup,
    pow_prefix,
    pow_best,
    pow_completed,
    pow_nonce,
    statement,
    claims_mixed,
    claims_component,
    relation_z,
    relation_alpha_powers,
    error_flag,
    composition_constants,
    composition_arguments,
    composition_trace_offsets,
    composition_interaction_offsets,
    composition_lde_descriptors,
    composition_ext_descriptors,
    composition_ext_values,
    composition_denominators,
    composition_lde_tile,
    composition_accumulators,
    composition_powers,
    composition_alpha,
    oods_parameter,
    oods_offsets,
    oods_folds,
    oods_indices,
    oods_sample_points,
    oods_evaluation_points,
    oods_factors,
    oods_reduce_a,
    oods_reduce_b,
    oods_values,
    quotient_challenge,
    quotient_terms,
    quotient_group_offsets,
    quotient_group_term_indices,
    quotient_batch_terms,
    quotient_sources,
    quotient_group_logs,
    quotient_partial_logs,
    quotient_partial_offsets,
    quotient_term_points,
    quotient_lines,
    quotient_group_points,
    quotient_first_terms,
    quotient_partial_coordinates,
    quotient_result,
    quotient_subdomain,
    quotient_inverse_twiddles,
    quotient_coefficient_logs,
    fri_alpha,
    fri_coordinates,
    fri_hashes,
    fri_layers,
    fri_last_evaluation,
    fri_last_coefficients,
    fri_degree_error,
    fri_last_transcript,
    decommit_raw,
    decommit_unique,
    decommit_mapped,
    decommit_walk,
    decommit_walk_scratch,
    decommit_leaf_indices,
    decommit_expanded,
    decommit_sparse_indices,
    decommit_sparse_hashes,
    decommit_counts,
    decommit_level_offsets,
    decommit_level_counts,
    decommit_column_logs,
    terminal_bundle,
    logup_sources,
    logup_tables,
    logup_geometry,
    logup_partials,
    logup_scan,
    witness_inputs,
    witness_scratch,
};

pub const Slot = struct {
    kind: Kind,
    ordinal: u16,
    requirement: arena.Requirement,
};

pub const Input = struct {
    twiddle_words: usize,
    statement_words: usize,
    /// Claimed sums as mixed (components with lookups) and per component.
    claims_mixed: usize,
    claims_component: usize,
    /// `w + 1` for the widest lookup tuple `w`.
    alpha_powers: usize,
    commitments: *const [4]commit.Plan,
    composition: *const cc.resident_composition.Plan,
    oods: *const masks.OodsPlan,
    quotient: *const masks.Topology,
    fri: *const fri.Plan,
    decommit: *const decommit.Plan,
    terminal: *const terminal.Bundle,
    /// Device LogUp (`logup.zig`); null: the interaction tree is built on the host and uploaded.
    logup: ?*const logup.Plan = null,
    /// Device witness (`witness.zig`): its inputs slot and the SHA word scratch; null: the host
    /// uploads every trace column.
    witness: ?WitnessSizes = null,
};

pub const WitnessSizes = struct { input_words: usize, scratch_words: usize };

pub const Plan = struct {
    allocator: std.mem.Allocator,
    slots: []Slot,
    requirements: []arena.Requirement,
    placement: arena.Plan,

    pub fn init(allocator: std.mem.Allocator, input: Input) !Plan {
        var builder = Builder{ .allocator = allocator };
        defer builder.slots.deinit(allocator);
        try builder.build(input);
        const slots = try builder.slots.toOwnedSlice(allocator);
        errdefer allocator.free(slots);
        const requirements = try allocator.alloc(arena.Requirement, slots.len);
        errdefer allocator.free(requirements);
        for (slots, requirements) |entry, *r| r.* = entry.requirement;
        const placement = try arena.Plan.init(allocator, requirements);
        return .{ .allocator = allocator, .slots = slots, .requirements = requirements, .placement = placement };
    }

    pub fn deinit(self: *Plan) void {
        self.placement.deinit(self.allocator);
        self.allocator.free(self.requirements);
        self.allocator.free(self.slots);
        self.* = undefined;
    }

    pub fn slot(self: *const Plan, kind: Kind, ordinal: u16) !Slot {
        for (self.slots) |entry| if (entry.kind == kind and entry.ordinal == ordinal) return entry;
        return error.MissingResidentSlot;
    }

    pub fn bytes(self: *const Plan) !usize {
        return mul(self.placement.total_words, 4);
    }

    /// Bytes of the slots of `kind` (all ordinals), for the size report.
    pub fn kindBytes(self: *const Plan, kind: Kind) usize {
        var words: usize = 0;
        for (self.slots) |s| if (s.kind == kind) {
            words += s.requirement.words;
        };
        return words * 4;
    }

    pub fn cacheKey(self: *const Plan) [32]u8 {
        var hash = std.crypto.hash.sha2.Sha256.init(.{});
        hash.update("starked-bitcoin/cuda-arena/v1\x00");
        hashInt(u64, &hash, @intCast(self.placement.total_words));
        for (self.placement.placements) |p| {
            const r = p.requirement;
            hashInt(u32, &hash, r.id);
            hashInt(u64, &hash, @intCast(r.words));
            hashInt(u64, &hash, @intCast(r.alignment_words));
            hashInt(u8, &hash, @intFromEnum(r.live_from));
            hashInt(u8, &hash, @intFromEnum(r.live_through));
            hashInt(u64, &hash, @intCast(p.offset_words));
        }
        return hash.finalResult();
    }
};

fn hashInt(comptime T: type, hash: *std.crypto.hash.sha2.Sha256, value: T) void {
    var b: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &b, value, .little);
    hash.update(&b);
}

const Builder = struct {
    allocator: std.mem.Allocator,
    slots: std.ArrayList(Slot) = .empty,

    fn add(self: *Builder, kind: Kind, ordinal: usize, words: usize, alignment: usize, from: Stage, through: Stage) !void {
        if (words == 0 or ordinal >= 1 << 16) return error.InvalidResidentSlot;
        const id = (@as(u32, @intFromEnum(kind)) << 16) | @as(u32, @intCast(ordinal));
        try self.slots.append(self.allocator, .{
            .kind = kind,
            .ordinal = @intCast(ordinal),
            .requirement = .{ .id = id, .words = words, .alignment_words = alignment, .live_from = from, .live_through = through },
        });
    }

    fn build(self: *Builder, input: Input) !void {
        if (input.twiddle_words == 0 or input.fri.layers.len == 0 or input.statement_words == 0 or
            input.claims_mixed == 0 or input.claims_component == 0 or input.alpha_powers == 0)
            return error.InvalidResidentGeometry;
        for (input.commitments, 0..) |plan, tree| {
            const r = plan.requirements;
            // Trees 0–2: evaluations are uploaded to a staging slot at ingress and moved into the
            // coefficient buffer in `.trace_generation` (`pipeline.assembleTrace`: trees 0–1
            // reordered natural → storage, a host-LogUp tree 2 copied); the staging slot dies
            // there, so the arena reuses it. The composition tree is written by the evaluator;
            // with device LogUp, tree 2 is written in `.trace_commit` (no staging).
            if (tree < 2 or (tree == 2 and input.logup == null)) try self.add(.trace_staging, tree, r.coefficient_words, 64, .ingress, .trace_generation);
            const start: Stage = if (tree == 3) .constraint_evaluation else .trace_generation;
            try self.add(.commit_coefficients, tree, r.coefficient_words, 64, start, .oods);
            try self.add(.commit_evaluations, tree, r.evaluation_words, 64, if (tree == 3) .constraint_evaluation else .trace_commit, .decommit);
            try self.add(.commit_logs, tree, r.column_log_words, 1, .ingress, if (tree == 3) .constraint_evaluation else .trace_commit);
            try self.add(.commit_hashes, tree, try mul(r.merkle_hashes, 8), 64, if (tree == 3) .constraint_evaluation else .trace_commit, .decommit);
            try self.add(.commit_layers, tree, try mul(r.merkle_layers, @sizeOf(field.MerkleLayerDescriptor) / 4), 2, .ingress, .decommit);
        }
        try self.add(.twiddles_forward, 0, input.twiddle_words, 64, .ingress, .quotient);
        try self.add(.twiddles_inverse, 0, input.twiddle_words, 64, .ingress, .fri_commit);
        try self.add(.transcript_state, 0, 16, 4, .trace_commit, .decommit);
        try self.add(.transcript_boundary, 0, 16, 4, .trace_commit, .decommit);
        try self.add(.transcript_config, 0, 8, 4, .ingress, .trace_commit);
        try self.add(.transcript_lookup, 0, 8, 4, .trace_commit, .constraint_evaluation);
        try self.add(.pow_prefix, 0, 8, 8, .trace_commit, .pow);
        try self.add(.pow_best, 0, 2, 2, .trace_commit, .pow);
        try self.add(.pow_completed, 0, 1, 1, .trace_commit, .pow);
        try self.add(.pow_nonce, 0, 2, 2, .trace_commit, .pow);
        try self.add(.statement, 0, input.statement_words, 4, .ingress, .trace_commit);
        try self.add(.claims_mixed, 0, try mul(input.claims_mixed, 4), 4, .ingress, .trace_commit);
        try self.add(.claims_component, 0, try mul(input.claims_component, 4), 4, .ingress, .constraint_evaluation);
        // Expanded on the device from the drawn (z, α) (`logup.expandChallenges`).
        try self.add(.relation_z, 0, 4, 4, .trace_commit, .constraint_evaluation);
        try self.add(.relation_alpha_powers, 0, try mul(input.alpha_powers, 4), 4, .trace_commit, .constraint_evaluation);
        if (input.logup) |plan| {
            if (plan.alpha_powers > input.alpha_powers or plan.instances.len != input.claims_mixed) return error.InvalidResidentGeometry;
            // The lookups' columns, copied out of the staging slots before trees 0–1 are
            // interpolated in place; the denominator slab borrows tree 2's evaluation buffer.
            try self.add(.logup_sources, 0, plan.source_words, 64, .trace_generation, .trace_commit);
            try self.add(.logup_tables, 0, plan.tableWords(), 2, .ingress, .trace_commit);
            try self.add(.logup_geometry, 0, try mul(plan.instances.len, @sizeOf(cuda.abi.stages.relation.Geometry) / 4), 1, .ingress, .trace_commit);
            const scratch = try plan.scratchWords();
            try self.add(.logup_partials, 0, scratch, 64, .trace_commit, .trace_commit);
            try self.add(.logup_scan, 0, scratch, 64, .trace_commit, .trace_commit);
            if (plan.slab_words > input.commitments[2].requirements.evaluation_words) return error.InvalidResidentGeometry;
        }
        if (input.witness) |w| {
            // Small inputs and pointer tables (ingress), the SHA word trace (`.trace_generation`).
            try self.add(.witness_inputs, 0, w.input_words, 64, .ingress, .trace_generation);
            try self.add(.witness_scratch, 0, w.scratch_words, 64, .trace_generation, .trace_generation);
        }
        try self.add(.error_flag, 0, 1, 1, .ingress, .fri_commit);
        try self.addComposition(input.composition);
        try self.addOods(input.oods);
        try self.addQuotient(input.quotient, input.fri.layers[0].evaluation_log);
        try self.addFri(input.fri);
        try self.addDecommit(input.decommit);
        try self.add(.terminal_bundle, 0, input.terminal.total_words, 64, .ingress, .proof_assembly);
    }

    fn addComposition(self: *Builder, plan: *const cc.resident_composition.Plan) !void {
        const summary = plan.topology.summary;
        try self.add(.composition_constants, 0, plan.constants.len, 4, .ingress, .constraint_evaluation);
        try self.add(.composition_arguments, 0, try mul(plan.placements.len, @sizeOf(cuda.abi.stages.cairo_eval.Args) / 4), 2, .ingress, .constraint_evaluation);
        try self.add(.composition_trace_offsets, 0, @intCast(summary.trace_offset_words), 2, .ingress, .constraint_evaluation);
        try self.add(.composition_interaction_offsets, 0, @intCast(summary.interaction_offset_words), 2, .ingress, .constraint_evaluation);
        try self.add(.composition_lde_descriptors, 0, try mul(plan.topology.sources.len, @sizeOf(cuda.runtime.stages.transform.AddressedLdeDescriptor) / 4), 2, .ingress, .constraint_evaluation);
        try self.add(.composition_ext_descriptors, 0, try mul(plan.topology.extended_parameter_descriptors.len, @sizeOf(cuda.runtime.stages.cairo_eval.ExtSourceDescriptor) / 4), 4, .ingress, .constraint_evaluation);
        try self.add(.composition_ext_values, 0, @intCast(summary.extended_parameter_words), 4, .trace_commit, .constraint_evaluation);
        try self.add(.composition_denominators, 0, plan.denominator_inverses.len, 4, .ingress, .constraint_evaluation);
        try self.add(.composition_lde_tile, 0, @intCast(summary.lde_tile_words), 64, .constraint_evaluation, .constraint_evaluation);
        try self.add(.composition_accumulators, 0, @intCast(summary.accumulator_words), 64, .constraint_evaluation, .constraint_evaluation);
        try self.add(.composition_powers, 0, try mul(summary.constraint_count, 4), 4, .constraint_evaluation, .constraint_evaluation);
        try self.add(.composition_alpha, 0, 4, 4, .constraint_evaluation, .constraint_evaluation);
    }

    fn addOods(self: *Builder, plan: *const masks.OodsPlan) !void {
        const samples = plan.offsets.len;
        try self.add(.oods_parameter, 0, 4, 4, .oods, .quotient);
        try self.add(.oods_offsets, 0, try mul(samples, @sizeOf(field.CirclePointBaseField) / 4), 2, .ingress, .oods);
        try self.add(.oods_folds, 0, samples, 1, .ingress, .oods);
        try self.add(.oods_indices, 0, samples, 1, .ingress, .oods);
        inline for (.{ Kind.oods_sample_points, Kind.oods_evaluation_points }) |kind|
            try self.add(kind, 0, try mul(samples, @sizeOf(field.SecureCirclePoint) / 4), 4, .oods, .quotient);
        try self.add(.oods_factors, 0, try mul(plan.factor_count, 4), 4, .oods, .oods);
        inline for (.{ Kind.oods_reduce_a, Kind.oods_reduce_b }) |kind|
            try self.add(kind, 0, try mul(plan.scratch_count, 4), 4, .oods, .oods);
        try self.add(.oods_values, 0, try mul(samples, 4), 4, .oods, .quotient);
    }

    fn addQuotient(self: *Builder, plan: *const masks.Topology, fri_log: u32) !void {
        const terms = plan.prepared_terms.len;
        const groups = plan.group_log_sizes.len;
        try self.add(.quotient_challenge, 0, 4, 4, .oods, .quotient);
        try self.add(.quotient_terms, 0, try mul(terms, 5), 4, .ingress, .quotient);
        try self.add(.quotient_group_offsets, 0, groups + 1, 1, .ingress, .quotient);
        try self.add(.quotient_group_term_indices, 0, terms, 1, .ingress, .quotient);
        try self.add(.quotient_batch_terms, 0, try mul(terms, 3), 1, .ingress, .quotient);
        try self.add(.quotient_sources, 0, try mul(plan.sources.len, 4), 2, .ingress, .quotient);
        try self.add(.quotient_group_logs, 0, groups, 1, .ingress, .quotient);
        try self.add(.quotient_partial_logs, 0, groups, 1, .ingress, .quotient);
        try self.add(.quotient_partial_offsets, 0, try mul(groups + 1, 2), 2, .ingress, .quotient);
        try self.add(.quotient_term_points, 0, try mul(terms, 8), 8, .quotient, .quotient);
        try self.add(.quotient_lines, 0, try mul(terms, 12), 4, .quotient, .quotient);
        try self.add(.quotient_group_points, 0, try mul(groups, 8), 8, .quotient, .quotient);
        try self.add(.quotient_first_terms, 0, try mul(groups, 4), 4, .quotient, .quotient);
        try self.add(.quotient_partial_coordinates, 0, try mul(@as(usize, @intCast(plan.partial_offsets[groups])), 4), 64, .quotient, .quotient);
        const rows = try pow2(fri_log);
        try self.add(.quotient_result, 0, try mul(rows, 4), 64, .quotient, .decommit);
        try self.add(.quotient_subdomain, 0, try mul(rows / 2, 4), 64, .quotient, .quotient);
        try self.add(.quotient_inverse_twiddles, 0, rows / 4, 64, .ingress, .quotient);
        try self.add(.quotient_coefficient_logs, 0, 4, 1, .ingress, .quotient);
    }

    fn addFri(self: *Builder, plan: *const fri.Plan) !void {
        try self.add(.fri_alpha, 0, 4, 4, .fri_commit, .fri_commit);
        for (plan.layers, 0..) |layer, ordinal| {
            if (ordinal != 0) try self.add(.fri_coordinates, ordinal, try mul(layer.evaluation_size, 4), 64, .fri_commit, .decommit);
            try self.add(.fri_hashes, ordinal, try mul(try mul(layer.evaluation_size >> @intCast(layer.leaf_log), 2) - 1, 8), 64, .fri_commit, .decommit);
            try self.add(.fri_layers, ordinal, try mul(layer.merkle_count, @sizeOf(field.MerkleLayerDescriptor) / 4), 2, .ingress, .decommit);
        }
        const rows = try pow2(plan.final_log);
        try self.add(.fri_last_evaluation, 0, try mul(rows, 4), 4, .fri_commit, .fri_commit);
        try self.add(.fri_last_coefficients, 0, try mul(rows, 4), 4, .fri_commit, .fri_commit);
        try self.add(.fri_degree_error, 0, 1, 1, .fri_commit, .fri_commit);
        try self.add(.fri_last_transcript, 0, try mul(try pow2(plan.final_degree_log), 4), 4, .fri_commit, .fri_commit);
    }

    fn addDecommit(self: *Builder, plan: *const decommit.Plan) !void {
        const topo = &plan.topology;
        const queries = topo.query_count;
        var max_expanded = queries;
        var max_log: usize = 0;
        for (topo.trace_openings) |o| max_log = @max(max_log, o.tree_log_size);
        for (topo.fri_openings) |o| {
            max_expanded = @max(max_expanded, try mul(queries, try pow2(o.fold_step)));
            max_log = @max(max_log, o.evaluation_log_size);
        }
        inline for (.{ Kind.decommit_raw, Kind.decommit_unique, Kind.decommit_mapped }) |kind|
            try self.add(kind, 0, queries, 1, .decommit, .decommit);
        inline for (.{ Kind.decommit_walk, Kind.decommit_walk_scratch, Kind.decommit_expanded }) |kind|
            try self.add(kind, 0, max_expanded, 1, .decommit, .decommit);
        try self.add(.decommit_leaf_indices, 0, 1, 1, .decommit, .decommit);
        try self.add(.decommit_sparse_indices, 0, 1, 1, .decommit, .decommit);
        try self.add(.decommit_sparse_hashes, 0, 8, 8, .decommit, .decommit);
        try self.add(.decommit_counts, 0, 5, 1, .decommit, .decommit);
        try self.add(.decommit_level_offsets, 0, max_log + 1, 1, .decommit, .decommit);
        try self.add(.decommit_level_counts, 0, max_log + 1, 1, .decommit, .decommit);
        var columns: usize = 0;
        for (topo.trace_openings, 0..) |o, ordinal| {
            try self.add(.decommit_column_logs, ordinal, o.column_count, 1, .ingress, .decommit);
            columns += o.column_count;
        }
        if (columns != topo.column_log_sizes.len) return error.InvalidResidentGeometry;
    }
};

// ------------------------------------------------------------------ views

pub const Views = struct {
    allocator: std.mem.Allocator,
    /// Each trace column's ingress destination (inside its tree's staging slot, in the commit's
    /// cohort layout). Empty for tree 2 with device LogUp.
    columns: [3][]common.Words,
    /// Trees 0–2's staging slots (tree 2: none with device LogUp).
    staging: [3]?common.Words,
    /// Device LogUp's buffers (null on the host-LogUp path).
    logup: ?Logup,
    /// Device witness buffers (null: every trace column is uploaded).
    witness: ?Witness,
    coefficient_columns: [3][]common.Words,
    evaluation_columns: [3][]common.Words,
    commits: [4]commit.Buffers,
    twiddles_forward: common.Words,
    twiddles_inverse: common.Words,
    transcript: transcript.Bindings,
    statement: common.Words,
    claims_mixed: common.SecureFields,
    claims_component: common.SecureFields,
    relation_z: common.SecureFields,
    relation_alpha_powers: common.SecureFields,
    error_flag: common.Words,
    composition: controller.Buffers,
    oods: shared.resident_views.Oods,
    quotient: Quotient,
    fri: shared.resident_views.Fri,
    decommit: shared.resident_views.Decommit,
    proof: shared.resident_views.Proof,

    pub fn deinit(self: *Views) void {
        for (self.columns) |c| self.allocator.free(c);
        for (self.coefficient_columns) |c| self.allocator.free(c);
        for (self.evaluation_columns) |c| self.allocator.free(c);
        self.* = undefined;
    }
};

pub const Logup = struct {
    sources: common.Words,
    tables: common.Words,
    geometry: cuda.runtime.stages.relation_completion.Geometries,
    partials: common.Words,
    scan: common.Words,
    /// The denominator slab: the head of tree 2's evaluation buffer.
    denominators: common.Words,
};

pub const Witness = struct {
    inputs: common.Words,
    scratch: common.Words,
};

pub const BindInput = struct {
    plans: *const Plan,
    commitments: *const [4]commit.Plan,
    fri: *const fri.Plan,
    terminal: *const terminal.Bundle,
    /// `logup.Plan.slab_words` (device LogUp only).
    logup_slab_words: usize = 0,
};

/// Typed views of `transaction`'s arena (a `ResidentProofTransaction`, or a test fake with
/// `slot(id)` and `residentArenaWords()`).
pub fn bind(allocator: std.mem.Allocator, transaction: anytype, input: BindInput) !Views {
    const binder = Binder(@TypeOf(transaction)){ .tx = transaction, .plan = input.plans };
    const arena_words = try transaction.residentArenaWords();
    const twiddles_forward = try binder.words(.twiddles_forward, 0);
    const twiddles_inverse = try binder.words(.twiddles_inverse, 0);

    var coefficient_columns: [3][]common.Words = undefined;
    var evaluation_columns: [3][]common.Words = undefined;
    var made: usize = 0;
    errdefer for (coefficient_columns[0..made], evaluation_columns[0..made]) |c, e| {
        allocator.free(c);
        allocator.free(e);
    };
    var staging: [3]?common.Words = undefined;
    var columns: [3][]common.Words = undefined;
    var staged: usize = 0;
    errdefer for (columns[0..staged]) |c| allocator.free(c);
    const device_logup = input.plans.slot(.logup_sources, 0) catch null;
    for (&staging, &columns, input.commitments[0..3], 0..) |*st, *cols, plan, tree| {
        if (tree == 2 and device_logup != null) {
            st.* = null;
            cols.* = &.{};
            staged += 1;
            continue;
        }
        const view = try binder.words(.trace_staging, tree);
        st.* = view;
        cols.* = try allocator.alloc(common.Words, plan.column_logs.len);
        staged += 1;
        for (plan.cohorts) |cohort| {
            const rows = try pow2(cohort.trace_log);
            for (0..cohort.count) |local| cols.*[cohort.first_column + local] = try view.sub(cohort.coefficient_offset + local * rows, rows);
        }
    }
    var commits: [4]commit.Buffers = undefined;
    for (input.commitments, &commits, 0..) |plan, *out, tree| {
        out.* = .{
            .coefficients = try binder.words(.commit_coefficients, tree),
            .evaluations = try binder.words(.commit_evaluations, tree),
            .column_logs = try binder.words(.commit_logs, tree),
            .merkle_hashes = try binder.as(field.Blake2sHash, .commit_hashes, tree),
            .merkle_layers = try binder.as(field.MerkleLayerDescriptor, .commit_layers, tree),
            .forward_twiddles = twiddles_forward,
            .inverse_twiddles = twiddles_inverse,
        };
        try out.validate(&plan);
        if (tree < 3) {
            const coeff = try allocator.alloc(common.Words, plan.column_logs.len);
            errdefer allocator.free(coeff);
            const eval = try allocator.alloc(common.Words, plan.column_logs.len);
            coefficient_columns[tree] = coeff;
            evaluation_columns[tree] = eval;
            made += 1;
            for (plan.cohorts) |cohort| {
                const coeff_rows = try pow2(cohort.trace_log);
                const eval_rows = try pow2(cohort.evaluation_log);
                for (0..cohort.count) |local| {
                    const index = cohort.first_column + local;
                    coeff[index] = try out.coefficients.sub(cohort.coefficient_offset + local * coeff_rows, coeff_rows);
                    eval[index] = try out.evaluations.sub(cohort.evaluation_offset + local * eval_rows, eval_rows);
                }
            }
        }
    }
    const transcript_view = transcript.Bindings{
        .state = try binder.words(.transcript_state, 0),
        .boundary_snapshot = try binder.words(.transcript_boundary, 0),
        .fri_config = try binder.words(.transcript_config, 0),
        .lookup = try binder.as(field.SecureField, .transcript_lookup, 0),
        .pow_prefix = try binder.words(.pow_prefix, 0),
        .pow_best_nonce = try binder.as(u64, .pow_best, 0),
        .pow_completed_blocks = try binder.words(.pow_completed, 0),
        .pow_nonce_words = try binder.words(.pow_nonce, 0),
    };
    try transcript_view.validate();
    const claims_component = try binder.as(field.SecureField, .claims_component, 0);
    const relation_z = try binder.as(field.SecureField, .relation_z, 0);
    const relation_alpha_powers = try binder.as(field.SecureField, .relation_alpha_powers, 0);
    const composition_view = controller.Buffers{
        .arena = arena_words,
        .sources = .{ .coefficients = coefficient_columns, .evaluations = evaluation_columns },
        .base_parameters = try binder.words(.composition_constants, 0),
        .arguments = try binder.as(cuda.runtime.stages.cairo_eval.Args, .composition_arguments, 0),
        .trace_offsets = try binder.words(.composition_trace_offsets, 0),
        .interaction_offsets = try binder.words(.composition_interaction_offsets, 0),
        .lde_descriptors = try binder.as(cuda.runtime.stages.transform.AddressedLdeDescriptor, .composition_lde_descriptors, 0),
        .extended_descriptors = try binder.as(cuda.runtime.stages.cairo_eval.ExtSourceDescriptor, .composition_ext_descriptors, 0),
        .extended_parameters = try binder.words(.composition_ext_values, 0),
        .denominator_inverses = try binder.words(.composition_denominators, 0),
        .lde_tile = try binder.words(.composition_lde_tile, 0),
        .accumulators = try binder.words(.composition_accumulators, 0),
        .random_powers = try binder.as(field.SecureField, .composition_powers, 0),
        .alpha = try binder.as(field.SecureField, .composition_alpha, 0),
        .relation_z = relation_z,
        .relation_alpha_powers = relation_alpha_powers,
        .claimed_sums = claims_component,
        .composition_coefficients = commits[3].coefficients,
        .forward_twiddles = twiddles_forward,
        .inverse_twiddles = twiddles_inverse,
    };
    const oods_view = shared.resident_views.Oods{
        .parameter = try binder.as(field.SecureField, .oods_parameter, 0),
        .offset_points = try binder.as(field.CirclePointBaseField, .oods_offsets, 0),
        .fold_counts = try binder.words(.oods_folds, 0),
        .output_indices = try binder.words(.oods_indices, 0),
        .sample_points = try binder.as(field.SecureCirclePoint, .oods_sample_points, 0),
        .evaluation_points = try binder.as(field.SecureCirclePoint, .oods_evaluation_points, 0),
        .folding_factors = try binder.as(field.SecureField, .oods_factors, 0),
        .reduce_a = try binder.as(field.SecureField, .oods_reduce_a, 0),
        .reduce_b = try binder.as(field.SecureField, .oods_reduce_b, 0),
        .sampled_values = try binder.as(field.SecureField, .oods_values, 0),
    };
    const logup_view: ?Logup = if (device_logup) |_| .{
        .sources = try binder.words(.logup_sources, 0),
        .tables = try binder.words(.logup_tables, 0),
        .geometry = try binder.as(cuda.abi.stages.relation.Geometry, .logup_geometry, 0),
        .partials = try binder.words(.logup_partials, 0),
        .scan = try binder.words(.logup_scan, 0),
        .denominators = try commits[2].evaluations.sub(0, input.logup_slab_words),
    } else null;
    const witness_view: ?Witness = if (input.plans.slot(.witness_inputs, 0)) |_| .{
        .inputs = try binder.words(.witness_inputs, 0),
        .scratch = try binder.words(.witness_scratch, 0),
    } else |_| null;
    const proof_view = try shared.resident_proof_binding.bindAt(shared.proof_bundle, transaction, (try input.plans.slot(.terminal_bundle, 0)).requirement.id, 0, .{ .proof = input.terminal.* });
    return .{
        .allocator = allocator,
        .columns = columns,
        .staging = staging,
        .logup = logup_view,
        .witness = witness_view,
        .coefficient_columns = coefficient_columns,
        .evaluation_columns = evaluation_columns,
        .commits = commits,
        .twiddles_forward = twiddles_forward,
        .twiddles_inverse = twiddles_inverse,
        .transcript = transcript_view,
        .statement = try binder.words(.statement, 0),
        .claims_mixed = try binder.as(field.SecureField, .claims_mixed, 0),
        .claims_component = claims_component,
        .relation_z = relation_z,
        .relation_alpha_powers = relation_alpha_powers,
        .error_flag = try binder.words(.error_flag, 0),
        .composition = composition_view,
        .oods = oods_view,
        .quotient = try bindQuotient(&binder, input.fri.layers[0].evaluation_log),
        .fri = try bindFri(&binder, input.fri),
        .decommit = try bindDecommit(&binder),
        .proof = proof_view,
    };
}

fn Binder(comptime Provider: type) type {
    return struct {
        tx: Provider,
        plan: *const Plan,

        fn words(self: *const @This(), kind: Kind, index: usize) !common.Words {
            const descriptor = try self.plan.slot(kind, @intCast(index));
            const value = try self.tx.slot(descriptor.requirement.id);
            if (value.len != descriptor.requirement.words) return error.InvalidResidentSlot;
            return value;
        }
        fn as(self: *const @This(), comptime F: type, kind: Kind, index: usize) !cuda.runtime.column.DeviceSlice(F) {
            return (try self.words(kind, index)).cast(F);
        }
    };
}

fn bindQuotient(binder: anytype, fri_log: u32) !Quotient {
    const partial = try binder.words(.quotient_partial_coordinates, 0);
    if (partial.len % 4 != 0) return error.InvalidResidentQuotient;
    const partial_rows = partial.len / 4;
    var partial_coordinates: [4]common.Words = undefined;
    for (&partial_coordinates, 0..) |*out, index| out.* = try partial.sub(index * partial_rows, partial_rows);
    const result = try binder.words(.quotient_result, 0);
    const rows = try pow2(fri_log);
    if (result.len != rows * 4) return error.InvalidResidentQuotient;
    return .{
        .subdomain_coordinates = try binder.words(.quotient_subdomain, 0),
        .subdomain_inverse_twiddles = try binder.words(.quotient_inverse_twiddles, 0),
        .coefficient_logs = try binder.words(.quotient_coefficient_logs, 0),
        .challenge = try binder.as(field.SecureField, .quotient_challenge, 0),
        .prepared_terms = try binder.as(cuda.abi.stages.quotient.PreparedTermDescriptor, .quotient_terms, 0),
        .group_offsets = try binder.words(.quotient_group_offsets, 0),
        .group_term_indices = try binder.words(.quotient_group_term_indices, 0),
        .batch_terms = try binder.as(cuda.abi.stages.quotient.BatchTermDescriptor, .quotient_batch_terms, 0),
        .source_descriptors = try binder.as(cuda.abi.stages.quotient.AddressedSourceDescriptor, .quotient_sources, 0),
        .group_log_sizes = try binder.words(.quotient_group_logs, 0),
        .partial_log_sizes = try binder.words(.quotient_partial_logs, 0),
        .partial_offsets = try binder.as(u64, .quotient_partial_offsets, 0),
        .term_points = try binder.as(field.SecureCirclePoint, .quotient_term_points, 0),
        .line_coefficients = try binder.as(field.SecureField, .quotient_lines, 0),
        .group_points = try binder.as(field.SecureCirclePoint, .quotient_group_points, 0),
        .first_linear_terms = try binder.as(field.SecureField, .quotient_first_terms, 0),
        .partial_coordinates = partial_coordinates,
        .result_coordinates = .{
            .c0 = try result.sub(0, rows),
            .c1 = try result.sub(rows, rows),
            .c2 = try result.sub(2 * rows, rows),
            .c3 = try result.sub(3 * rows, rows),
        },
    };
}

fn bindFri(binder: anytype, plan: *const fri.Plan) !shared.resident_views.Fri {
    var layers: [shared.resident_views.max_fri_layers]shared.resident_views.FriLayer = undefined;
    if (plan.layers.len > layers.len) return error.TooManyFriLayers;
    for (plan.layers, 0..) |layer, index| {
        const coordinates = if (index == 0) try binder.words(.quotient_result, 0) else try binder.words(.fri_coordinates, index);
        layers[index] = .{
            .coordinates = .{ .storage = coordinates, .column_stride_words = layer.evaluation_size },
            .merkle_hashes = try binder.as(field.Blake2sHash, .fri_hashes, index),
            .merkle_layers = try binder.as(field.MerkleLayerDescriptor, .fri_layers, index),
        };
    }
    return .{
        .alpha = try binder.as(field.SecureField, .fri_alpha, 0),
        .layers = layers,
        .layer_count = plan.layers.len,
        .last_evaluation = try binder.as(field.SecureField, .fri_last_evaluation, 0),
        .last_coefficients = try binder.as(field.SecureField, .fri_last_coefficients, 0),
        .last_degree_error = try binder.words(.fri_degree_error, 0),
        .last_transcript = try binder.as(field.SecureField, .fri_last_transcript, 0),
    };
}

fn bindDecommit(binder: anytype) !shared.resident_views.Decommit {
    const counts = try binder.words(.decommit_counts, 0);
    return .{
        .raw_queries = try binder.words(.decommit_raw, 0),
        .unique_queries = try binder.words(.decommit_unique, 0),
        .mapped_queries = try binder.words(.decommit_mapped, 0),
        .walk_queries = try binder.words(.decommit_walk, 0),
        .walk_scratch = try binder.words(.decommit_walk_scratch, 0),
        .leaf_indices = try binder.words(.decommit_leaf_indices, 0),
        .expanded_positions = try binder.words(.decommit_expanded, 0),
        .sparse_indices = try binder.words(.decommit_sparse_indices, 0),
        .sparse_hashes = try binder.as(field.Blake2sHash, .decommit_sparse_hashes, 0),
        .counts = .{
            .unique = try counts.sub(0, 1),
            .mapped_or_tree = try counts.sub(1, 1),
            .walk = try counts.sub(2, 1),
            .expanded = try counts.sub(3, 1),
            .leaf_or_sparse = try counts.sub(4, 1),
        },
        .sparse_level_offsets = try binder.words(.decommit_level_offsets, 0),
        .sparse_level_counts = try binder.words(.decommit_level_counts, 0),
        .preprocessed_column_log_sizes = try binder.words(.decommit_column_logs, 0),
        .main_column_log_sizes = try binder.words(.decommit_column_logs, 1),
        .interaction_column_log_sizes = try binder.words(.decommit_column_logs, 2),
        .composition_column_log_sizes = try binder.words(.decommit_column_logs, 3),
    };
}

fn pow2(log: u32) !usize {
    if (log >= @bitSizeOf(usize)) return error.ResidentSizeOverflow;
    return @as(usize, 1) << @intCast(log);
}
fn mul(a: anytype, b: anytype) !usize {
    return std.math.mul(usize, @intCast(a), @intCast(b)) catch error.ResidentSizeOverflow;
}

/// A host stand-in for the transaction's arena (tests): every slot at its planned offset.
pub const FakeArena = struct {
    placement: *const arena.Plan,
    pub const base: usize = 0x1000_0000_000;

    pub fn slot(self: *FakeArena, id: u32) !common.Words {
        const placed = try self.placement.placement(id);
        return .{ .address = base + placed.offset_words * 4, .len = placed.requirement.words, .owner = 1, .generation = 1 };
    }
    pub fn residentArenaWords(self: *FakeArena) !common.Words {
        return .{ .address = base, .len = self.placement.total_words, .owner = 1, .generation = 1 };
    }
};
