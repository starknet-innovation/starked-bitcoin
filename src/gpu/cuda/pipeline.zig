//! One proof-owned CUDA schedule for the block system, adapted from
//! `circuit_cuda/resident_pipeline.zig`: our transcript prefix, no device witness or interaction
//! stage (their columns arrive at ingress), and our claim capture. The tail (composition, OODS,
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
        staging: [3]common.Words,
        error_flag: common.Words,
        oods_view: shared.resident_views.Oods,
        quotient_challenge: common.SecureFields,
        fri_view: shared.resident_views.Fri,
        decommit_view: shared.resident_views.Decommit,
        proof: shared.resident_views.Proof,
        twiddles_inverse: common.Words,

        const Self = @This();

        pub fn validate(self: *const Self) !void {
            if (self.statement_words.len != self.statement.words.len or self.claims_mixed.len == 0 or
                self.error_flag.len != 1 or self.quotient_challenge.len != 1 or
                self.proof.trace_commitments.len != 4 * 8 + self.claims_mixed.len * 4 or
                self.composition.buffers.composition_coefficients.address != self.commitments[3].buffers.coefficients.address)
                return error.InvalidResidentPipeline;
            for (self.columns, 0..) |cols, tree| if (cols.len != self.commitments[tree].plan.column_logs.len) return error.InvalidResidentPipeline;
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

            // Trace assembly: gather each cohort of trees 0–2 from its ingress staging slot into
            // the commitment's input buffer (stwo-zig's contiguous witness gather; a plain column
            // copy here). The trace itself is built on the host for now, so this is the stage's
            // only device work; device witness generation would replace it.
            try tx.beginStage(.trace_generation);
            for (self.commitments[0..3], self.staging) |*c, staging| {
                for (c.plan.cohorts) |cohort| {
                    const rows: u32 = @as(u32, 1) << @intCast(cohort.trace_log);
                    const words = cohort.count * rows;
                    try cuda.runtime.stages.cairo_witness.Native.gatherEdge(session, .{
                        .producer_rows = rows,
                        .word_base = 0,
                        .words_per_instance = @intCast(cohort.count),
                        .instance_count = 1,
                        .consumer_rows = rows,
                        .include_enabler = false,
                        .include_iota = false,
                    }, try staging.sub(cohort.coefficient_offset, words), .{
                        .storage = try c.buffers.coefficients.sub(cohort.coefficient_offset, words),
                        .column_stride_words = rows,
                    });
                }
            }
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
            // The device draws (z, α) itself; the interaction columns uploaded at ingress were
            // built for the same draw from the host's roots (prover.zig).
            _ = try prefix.drawLookupElements();
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

pub const Native = Bound(cuda.runtime.proof_transaction.ResidentProofTransaction, transcript.NativeSink);
