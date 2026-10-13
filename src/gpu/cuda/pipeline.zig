//! One proof-owned CUDA schedule for the block system, adapted from
//! `circuit_cuda/resident_pipeline.zig`: our transcript prefix, our device witness (the largest
//! columns generated in `.trace_generation`, `witness.zig`; the rest arrives at ingress), device LogUp in `.trace_commit` as the circuit's (`logup.zig`; or the
//! host's interaction tree from ingress), and our claim capture. The tail (composition, OODS,
//! quotient, FRI, query grind, openings) is stwo-zig's, in its order. Only the terminal bundle
//! leaves the GPU.

const std = @import("std");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const cc = @import("stwo_circuit_cuda_integration");
const shared = @import("stwo_native_cuda_integration").common;
const transcript = @import("transcript.zig");
const controller = @import("composition_controller.zig");
const terminal = @import("terminal.zig");
const logup = @import("logup.zig");
const reorder = @import("reorder.zig");
const witness = @import("witness.zig");
const common = cuda.runtime.stages.common;
const quotient_module = @import("stwo_cairo_cuda_integration").executor.quotient.controller;

pub fn Bound(comptime Transaction: type, comptime Sink: type) type {
    return struct {
        transaction: *Transaction,
        sink: *Sink,
        statement: *const transcript.Statement,
        statement_words: common.Words,
        claims_mixed: common.SecureFields,
        composition: *controller.Bound,
        oods: *const cc.resident_oods.Bound,
        quotient: *const quotient_module.Prepared,
        fri_plan: *const @import("fri.zig").Plan,
        decommit_plan: *const cc.resident_decommit.Plan,
        commitments: *[4]cc.resident_commit.Bound,
        columns: [3][]const common.Words,
        staging: [3]?common.Words,
        /// Device LogUp; null: tree 2 and the claims were uploaded at ingress.
        logup: ?*const logup.Bound,
        relation_z: common.SecureFields,
        relation_alpha_powers: common.SecureFields,
        error_flag: common.Words,
        oods_view: shared.resident_views.Oods,
        quotient_challenge: common.SecureFields,
        fri_view: shared.resident_views.Fri,
        decommit_view: shared.resident_views.Decommit,
        proof: shared.resident_views.Proof,
        twiddles_inverse: common.Words,
        reorder: *const reorder.Kernel,
        /// Device witness generation (null: every trace column arrived at ingress).
        witness: ?*const witness.Bound = null,

        const Self = @This();

        pub fn validate(self: *const Self) !void {
            if (self.statement_words.len != self.statement.words.len or self.claims_mixed.len == 0 or
                self.error_flag.len != 1 or self.quotient_challenge.len != 1 or
                self.proof.trace_commitments.len != 4 * 8 + self.claims_mixed.len * 4 or
                self.composition.buffers.composition_coefficients.address != self.commitments[3].buffers.coefficients.address)
                return error.InvalidResidentPipeline;
            for (self.columns, self.staging, 0..) |cols, staging, tree| {
                const device_tree = tree == 2 and self.logup != null;
                if (device_tree != (staging == null)) return error.InvalidResidentPipeline;
                if (cols.len != if (device_tree) 0 else self.commitments[tree].plan.column_logs.len) return error.InvalidResidentPipeline;
            }
            if (self.logup) |l| if (l.buffers.claims_mixed.address != self.claims_mixed.address or
                l.buffers.z.address != self.relation_z.address or l.buffers.powers.address != self.relation_alpha_powers.address)
                return error.InvalidResidentPipeline;
            const first = self.fri_view.layers[0].coordinates;
            const quotient = self.quotient.views.result_coordinates;
            const row_words = first.column_stride_words;
            if (first.storage.len != 4 * row_words or quotient.c0.address != first.storage.address or
                quotient.c1.address != first.storage.address + row_words * 4 or
                quotient.c2.address != first.storage.address + row_words * 8 or
                quotient.c3.address != first.storage.address + row_words * 12)
                return error.InvalidResidentPipeline;
        }

        /// Every plan, host constant and AOT handle was primed during ingress. No host
        /// synchronisation or read happens here.
        pub fn execute(self: *Self, config: core.pcs.config_v2.PcsConfigV2) !void {
            try self.validate();
            const tx = self.transaction;
            const session = tx.proofSession();
            const sink = self.sink;
            var prefix = transcript.Prefix(Sink){ .sink = sink };
            const proof_root = struct {
                fn capture(s: anytype, proof: shared.resident_views.Proof, tree: usize, root: common.Words) !void {
                    try shared.proof_assembly.captureStaticTraceRoot(s, .{ .proof = proof }, tree, root);
                }
            };

            // Trace assembly (`assembleTrace`): the device-generated columns are written into the
            // staging slots, then trees 0–1 (natural row order) are reordered into storage order by
            // our kernel; the host-LogUp interaction tree is a copy.
            try tx.beginStage(.trace_generation);
            var plans: [3]*const cc.resident_commit.Plan = undefined;
            var coefficients: [3]common.Words = undefined;
            for (self.commitments[0..3], &plans, &coefficients) |*c, *p, *k| {
                p.* = c.plan;
                k.* = c.buffers.coefficients;
            }
            try assembleTrace(session, self.reorder, plans, coefficients, self.staging, self.logup, self.witness);
            try tx.endStage(.trace_generation);

            try tx.beginStage(.trace_commit);
            try sink.initialize();
            try prefix.mixConfig(config);
            try self.commitments[0].execute(session);
            const preprocessed_root = try self.commitments[0].root();
            try proof_root.capture(session, self.proof, 0, preprocessed_root);
            try prefix.commitPreprocessed(preprocessed_root);
            try prefix.mixStatement(self.statement.*, self.statement_words);
            try self.commitments[1].execute(session);
            const main_root = try self.commitments[1].root();
            try proof_root.capture(session, self.proof, 1, main_root);
            try prefix.commitMain(main_root);
            // The device draws (z, α) itself. Device LogUp builds tree 2 (in place in its
            // coefficient buffer) and the claims here; on the host path they were uploaded at
            // ingress, built for the same draw from the host's roots (prover.zig).
            const drawn = try prefix.drawLookupElements();
            if (self.logup) |l| {
                try l.execute(session);
            } else try logup.expandChallenges(session, drawn, self.relation_z, self.relation_alpha_powers);
            try prefix.mixInteractionClaim(try self.claims_mixed.cast(u32));
            try terminal.captureClaims(session, self.proof, self.claims_mixed);
            try self.commitments[2].execute(session);
            const interaction_root = try self.commitments[2].root();
            try proof_root.capture(session, self.proof, 2, interaction_root);
            try prefix.commitInteraction(interaction_root);
            try prefix.admitComposition();
            sink.readyForComposition();
            try tx.endStage(.trace_commit);

            try tx.beginStage(.constraint_evaluation);
            try sink.drawCompositionAlpha(self.composition.buffers.alpha);
            try self.composition.execute(session);
            try self.commitments[3].execute(session);
            const composition_root = try self.commitments[3].root();
            try proof_root.capture(session, self.proof, 3, composition_root);
            try sink.mixCompositionRoot(composition_root);
            try tx.endStage(.constraint_evaluation);

            try tx.beginStage(.oods);
            try sink.drawOodsParameter(self.oods_view.parameter);
            try self.oods.execute(session, self.oods_view);
            try shared.proof_assembly.captureSampledValues(session, .{ .proof = self.proof, .oods = self.oods_view });
            try sink.mixSampledValues(self.oods_view.sampled_values);
            try sink.drawQuotientAlpha(self.quotient_challenge);
            try tx.endStage(.oods);

            try tx.beginStage(.quotient);
            try self.quotient.execute(session);
            try tx.endStage(.quotient);

            try tx.beginStage(.fri_commit);
            try self.fri_plan.execute(session, sink, self.fri_view, self.twiddles_inverse, self.proof);
            try terminal.sealVerdict(session, self.proof, self.fri_view.last_degree_error, self.error_flag);
            try tx.endStage(.fri_commit);

            try tx.beginStage(.pow);
            try sink.absorbQueryPow();
            try terminal.captureQueryNonce(session, self.proof, sink.bindings.pow_nonce_words);
            try tx.endStage(.pow);

            try tx.beginStage(.decommit);
            var buffers: [4]cc.resident_commit.Buffers = undefined;
            for (self.commitments, &buffers) |c, *b| b.* = c.buffers;
            try self.decommit_plan.execute(session, sink, buffers, self.fri_view, self.decommit_view, self.proof.decommitment, self.proof);
            try tx.endStage(.decommit);
        }
    };
}

/// `.trace_generation`: first the device witness (`witness.zig`) writes its columns into the
/// staging slots in natural row order (where ingress puts the host's). Then each staged tree's
/// cohorts go into its commitment's coefficient buffer, in storage order. Trees 0–1 (uploaded or
/// generated in natural row order, `prover.HostTrees`) go through
/// the reorder kernel (one launch per cohort); a staged tree 2 (host LogUp: `system.interactionTrace`
/// columns, already in storage order) is a device copy per cohort. Then
/// device LogUp copies the columns its lookups read out of the reordered buffers (the commitment
/// interpolates them in place in `.trace_commit`).
pub fn assembleTrace(
    session: anytype,
    kernel: *const reorder.Kernel,
    plans: [3]*const cc.resident_commit.Plan,
    coefficients: [3]common.Words,
    staging: [3]?common.Words,
    device_logup: ?*const logup.Bound,
    device_witness: ?*const witness.Bound,
) !void {
    if (device_witness) |w| {
        if (staging[0] == null or staging[1] == null) return error.InvalidResidentPipeline;
        try w.generate(session);
    }
    for (plans, coefficients, staging, 0..) |plan, coeff, maybe_staging, tree| {
        const st = maybe_staging orelse continue;
        for (plan.cohorts) |cohort| {
            const words = cohort.count << @intCast(cohort.trace_log);
            const src = try st.sub(cohort.coefficient_offset, words);
            const dst = try coeff.sub(cohort.coefficient_offset, words);
            if (tree < 2) {
                try kernel.launch(session, src, dst, cohort.trace_log, cohort.count);
            } else try session.context.copyDeviceSlice(u32, dst, src);
        }
    }
    if (device_logup) |l| try l.gather(session);
}

pub const Native = Bound(cuda.runtime.proof_transaction.ResidentProofTransaction, transcript.NativeSink);
