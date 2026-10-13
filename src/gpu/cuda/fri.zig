//! stwo-zig's resident FRI (`circuit_cuda/resident_fri.zig`), copied with one change: the Merkle
//! leaf packing follows the CPU prover. stwo packs four FRI rows per leaf only when the layer folds
//! more than once (`core/fri.zig`, `pack_leaves = … and fold_step > 1`); the circuit pipeline
//! always packs (it runs fold step 4). Our profile folds once per layer, so its leaves hold one row.
//! Minimal upstream change: derive the leaf size from the layer's fold step.
const std = @import("std");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const field = cuda.abi.field;
const common = cuda.runtime.stages.common;
const stages = cuda.runtime.stages;
const shared = @import("stwo_native_cuda_integration").common;
const geometry_module = @import("stwo_circuit_cuda_integration").geometry;

pub const Layer = struct {
    evaluation_log: u32,
    fold_step: u32,
    evaluation_size: u32,
    merkle_first: usize,
    merkle_count: usize,
    twiddle_offsets: [4]u32,
    /// log2 of the rows per Merkle leaf: 2 when the layer folds more than once, else 0.
    leaf_log: u32,
};

pub fn leafLog(fold_step: u32, evaluation_log: u32) u32 {
    return if (fold_step > 1 and evaluation_log >= core.fri.LOG_PACKED_LEAF_SIZE) core.fri.LOG_PACKED_LEAF_SIZE else 0;
}

pub const Plan = struct {
    allocator: std.mem.Allocator,
    layers: []Layer,
    descriptors: []field.MerkleLayerDescriptor,
    final_log: u32,
    final_degree_log: u32,
    twiddle_words: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        geometry: *const geometry_module.Geometry,
        config: core.pcs.config_v2.PcsConfigV2,
        twiddle_words: usize,
    ) !Plan {
        const fri = config.fri_config;
        if (geometry.fri_layers.len == 0 or geometry.fri_layers.len > shared.resident_views.max_fri_layers or
            geometry.fri_input_log != geometry.fri_layers[0].evaluation_log or
            fri.fold_step == 0 or fri.fold_step > 4)
            return error.InvalidCircuitFriGeometry;
        var descriptor_count: usize = 0;
        for (geometry.fri_layers) |source| descriptor_count = try add(descriptor_count, source.evaluation_log - leafLog(source.fold_step, source.evaluation_log) + 1);
        const layers = try allocator.alloc(Layer, geometry.fri_layers.len);
        errdefer allocator.free(layers);
        const descriptors = try allocator.alloc(field.MerkleLayerDescriptor, descriptor_count);
        errdefer allocator.free(descriptors);
        var cursor: usize = 0;
        var cumulative: u32 = 0;
        for (geometry.fri_layers, layers, 0..) |source, *layer, ordinal| {
            if (source.evaluation_log != geometry.fri_input_log - cumulative or
                source.cumulative_fold != cumulative or source.fold_step == 0 or
                source.fold_step > 4 or source.fold_step > source.evaluation_log or
                (ordinal + 1 < layers.len and source.fold_step != fri.fold_step))
                return error.InvalidCircuitFriGeometry;
            const rows = try pow2u32(source.evaluation_log);
            const leaf_log = leafLog(source.fold_step, source.evaluation_log);
            const count = source.evaluation_log - leaf_log + 1;
            try fillDescriptors(descriptors[cursor..][0..count], rows >> @intCast(leaf_log));
            var offsets = [_]u32{0} ** 4;
            for (0..source.fold_step) |fold| {
                const log = source.evaluation_log - @as(u32, @intCast(fold));
                offsets[fold] = try twiddleOffset(twiddle_words, log, ordinal == 0 and fold == 0);
            }
            layer.* = .{
                .evaluation_log = source.evaluation_log,
                .fold_step = source.fold_step,
                .evaluation_size = rows,
                .merkle_first = cursor,
                .merkle_count = count,
                .twiddle_offsets = offsets,
                .leaf_log = leaf_log,
            };
            cursor = try add(cursor, count);
            cumulative = try addU32(cumulative, source.fold_step);
        }
        const last = layers[layers.len - 1];
        const final_log = last.evaluation_log - last.fold_step;
        if (final_log != fri.log_last_layer_degree_bound + fri.log_blowup_factor or cursor != descriptors.len)
            return error.InvalidCircuitFriGeometry;
        return .{
            .allocator = allocator,
            .layers = layers,
            .descriptors = descriptors,
            .final_log = final_log,
            .final_degree_log = fri.log_last_layer_degree_bound,
            .twiddle_words = twiddle_words,
        };
    }

    pub fn deinit(self: *Plan) void {
        self.allocator.free(self.layers);
        self.allocator.free(self.descriptors);
        self.* = undefined;
    }

    pub fn validate(self: *const Plan, view: shared.resident_views.Fri, inverse_twiddles: common.Words) !void {
        if (view.layer_count != self.layers.len or inverse_twiddles.len != self.twiddle_words or
            view.alpha.len != 1 or view.last_degree_error.len != 1)
            return error.InvalidCircuitFriBuffers;
        for (self.layers, view.activeLayers()) |layer, resident| {
            const rows: usize = layer.evaluation_size;
            if (resident.coordinates.column_stride_words != rows or resident.coordinates.storage.len != try mul(rows, 4) or
                resident.merkle_hashes.len != try fullTreeHashes(rows >> @intCast(layer.leaf_log)) or resident.merkle_layers.len != layer.merkle_count)
                return error.InvalidCircuitFriBuffers;
        }
        const final_rows = try pow2(self.final_log);
        if (view.last_evaluation.len != final_rows or view.last_coefficients.len != final_rows or
            view.last_transcript.len != try pow2(self.final_degree_log))
            return error.InvalidCircuitFriBuffers;
    }

    pub fn upload(self: *const Plan, session: anytype, view: shared.resident_views.Fri, inverse_twiddles: common.Words) !void {
        try self.validate(view, inverse_twiddles);
        for (self.layers, view.activeLayers()) |layer, resident|
            try session.context.uploadSlice(field.MerkleLayerDescriptor, resident.merkle_layers, self.descriptors[layer.merkle_first..][0..layer.merkle_count]);
    }

    /// All arithmetic, Merkle commitments, challenge draws and terminal
    /// interpolation remain on the device. `sink` owns the exact transcript.
    pub fn execute(self: *const Plan, session: anytype, sink: anytype, view: shared.resident_views.Fri, inverse_twiddles: common.Words, proof: shared.resident_views.Proof) !void {
        try self.validate(view, inverse_twiddles);
        if (proof.fri_commitments.len != self.layers.len * 8 or
            proof.fri_last_layer.len != view.last_transcript.len * 4)
            return error.InvalidCircuitFriBuffers;
        try sink.setFriLayers(@intCast(self.layers.len));
        const Builder = shared.commit_tree.BuilderFor(stages.commitment.PlainNative);
        for (self.layers, 0..) |layer, ordinal| {
            const resident = view.layers[ordinal];
            const root = try Builder.fri(
                session,
                layer.evaluation_size,
                layer.leaf_log,
                resident.coordinates,
                resident.merkle_hashes,
                self.descriptors[layer.merkle_first..][0..layer.merkle_count],
            );
            try shared.proof_assembly.captureFriRoot(session, .{ .proof = proof }, ordinal, root);
            try sink.mixFriRoot(try root.cast(u32));
            try sink.drawFriAlpha(view.alpha);
            const destination = if (ordinal + 1 < self.layers.len)
                view.layers[ordinal + 1].coordinates
            else
                common.WordMatrix{
                    .storage = try view.last_evaluation.cast(u32),
                    .column_stride_words = try pow2(self.final_log),
                };
            switch (layer.fold_step) {
                1 => {
                    if (ordinal == 0) try session.zeroResidentSlice(u32, .fri_commit, destination.storage);
                    try stages.fri.Native.fold(session, ordinal == 0, inverse_twiddles, layer.twiddle_offsets[0], layer.evaluation_size, resident.coordinates, view.alpha, 0, destination);
                },
                2 => try stages.fri.Native.foldTwo(session, inverse_twiddles, layer.twiddle_offsets[0..2].*, layer.evaluation_size, ordinal == 0, resident.coordinates, view.alpha, destination),
                3 => try stages.fri.Native.foldThree(session, inverse_twiddles, layer.twiddle_offsets[0..3].*, layer.evaluation_size, ordinal == 0, resident.coordinates, view.alpha, destination),
                4 => try stages.fri.Native.foldFour(session, inverse_twiddles, layer.twiddle_offsets, layer.evaluation_size, ordinal == 0, resident.coordinates, view.alpha, destination),
                else => return error.InvalidCircuitFriGeometry,
            }
        }
        const final_rows = try pow2u32(self.final_log);
        try stages.fri.Native.lastLayer(
            session,
            try view.last_evaluation.cast(u32),
            final_rows,
            self.final_log,
            inverse_twiddles,
            self.final_degree_log,
            try view.last_coefficients.cast(u32),
            view.last_degree_error,
            try view.last_transcript.cast(u32),
        );
        try shared.proof_assembly.captureLastLayer(session, .{ .proof = proof, .fri = view });
        try sink.mixLastLayer(view.last_transcript);
    }
};

fn fillDescriptors(output: []field.MerkleLayerDescriptor, leaves: u32) !void {
    var count: usize = leaves;
    var offset: usize = 0;
    for (output) |*layer| {
        layer.* = .{ .offset_hashes = offset, .hash_count = @intCast(count) };
        offset = try add(offset, count);
        count = @max(count / 2, 1);
    }
}

fn twiddleOffset(words: usize, log: u32, circle: bool) !u32 {
    const rows = try pow2(log);
    const consumed = if (circle) rows / 2 else rows;
    if (consumed > words) return error.InvalidCircuitFriGeometry;
    return std.math.cast(u32, words - consumed) orelse error.CircuitFriSizeOverflow;
}

fn fullTreeHashes(rows: usize) !usize {
    return try std.math.mul(usize, rows, 2) - 1;
}
fn pow2(log: u32) !usize {
    if (log >= @bitSizeOf(usize)) return error.CircuitFriSizeOverflow;
    return @as(usize, 1) << @intCast(log);
}
fn pow2u32(log: u32) !u32 {
    if (log >= 31) return error.CircuitFriSizeOverflow;
    return @as(u32, 1) << @intCast(log);
}
fn add(a: usize, b: usize) !usize {
    return std.math.add(usize, a, b) catch error.CircuitFriSizeOverflow;
}
fn addU32(a: u32, b: u32) !u32 {
    return std.math.add(u32, a, b) catch error.CircuitFriSizeOverflow;
}
fn mul(a: usize, b: usize) !usize {
    return std.math.mul(usize, a, b) catch error.CircuitFriSizeOverflow;
}
