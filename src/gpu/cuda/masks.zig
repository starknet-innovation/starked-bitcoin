//! The OODS samples, DEEP-quotient topology and proof-decoder layout of our system: stwo-zig's
//! circuit versions (`circuit_cuda/resident_oods.zig`, `resident_quotient.zig`,
//! `resident_proof_layout.zig`), copied with one change: a column may have any number of mask
//! offsets. The circuit's AIR reads at most two rows per column and those files reject more; our
//! AIRs read up to 23 (`block_sha`, `block_anc`). The CPU PCS treats more than two samples
//! uniformly (only exactly two get the periodic sample, which is kept). The OODS plan and quotient
//! topology are stwo-zig's own types, so the resident OODS/quotient stages consume them unchanged.
//! Minimal upstream change: drop the `> 2` checks (three places) and use a wider count check in
//! the proof layout; then this file can go.

const std = @import("std");
const core = @import("stwo_core");
const cairo = @import("stwo_cairo_frontend");
const cuda = @import("stwo_cuda_backend");
const cc = @import("stwo_circuit_cuda_integration");
const proof_ir = @import("stwo_backend_contracts").proof_program;
const composition = cairo.witness.composition_bundle;
const quotient_abi = cuda.abi.stages.quotient;
const field = cuda.abi.field;
const circle = core.circle;
const canonic = core.poly.circle.canonic;
const masks_module = cairo.witness.quotient_geometry;
const quotient_geometry = cairo.witness.quotient_geometry;
const types = @import("stwo_cairo_cuda_integration").executor.quotient.types;
const buckets = @import("stwo_cairo_cuda_integration").executor.quotient.buckets;
const controller = @import("stwo_cairo_cuda_integration").executor.quotient.controller;
const geometry_module = cc.geometry;
const commit_module = cc.resident_commit;
const oods_module = cc.resident_oods;
const shared = @import("stwo_native_cuda_integration").common;
const uniform = shared.uniform_layout;
const common = cuda.runtime.stages.common;

pub const OodsPlan = cc.resident_oods.Plan;
const Plan = OodsPlan;
const Cohort = cc.resident_oods.Cohort;
pub const Topology = types.Topology;

// ------------------------------------------------------------------ OODS

pub fn oodsPlan(
    allocator: std.mem.Allocator,
    bound: *const composition.Bundle,
    geometry: *const geometry_module.Geometry,
    blowup: u32,
) !OodsPlan {
    if (blowup == 0 or blowup > 4) return error.InvalidCircuitOodsGeometry;
    const trees = geometry.trees;
    var masks = try quotient_geometry.deriveMasks(
        allocator,
        bound.*,
        trees[0].column_logs.len,
        trees[1].column_logs.len,
        trees[2].column_logs.len,
    );
    defer masks.deinit();
    var samples: std.ArrayList(Sample) = .empty;
    defer samples.deinit(allocator);
    var first_source: [4]usize = undefined;
    var column_offsets: [4][]usize = undefined;
    var total_sources: usize = 0;
    var initialized: usize = 0;
    defer for (column_offsets[0..initialized]) |offsets| allocator.free(offsets);
    for (trees, 0..) |tree, i| {
        first_source[i] = total_sources;
        total_sources = try oodsAdd(total_sources, tree.column_logs.len);
        const offsets = try allocator.alloc(usize, tree.column_logs.len);
        column_offsets[i] = offsets;
        initialized += 1;
        var cursor: usize = 0;
        for (tree.column_logs, offsets) |log, *item| {
            item.* = cursor;
            cursor = try oodsAdd(cursor, try oodsPow2(log));
        }
    }
    for (trees[0].column_logs, 0..) |_, column|
        try samples.append(allocator, try sample(trees[0], 0, column, column_offsets[0][column], 0, blowup));
    for (masks.base_offsets, 0..) |offsets, column| {
        // Changed from stwo-zig: any number of mask offsets per column (ours read up to 23 rows).
        if (offsets.items.len == 0) return error.InvalidCircuitOodsGeometry;
        for (offsets.items) |offset|
            try samples.append(allocator, try sample(trees[1], 1, column, column_offsets[1][column], offset, blowup));
    }
    for (masks.interaction_offsets, 0..) |offsets, column| {
        if (offsets.items.len == 0) return error.InvalidCircuitOodsGeometry;
        for (offsets.items) |offset|
            try samples.append(allocator, try sample(trees[2], 2, column, column_offsets[2][column], offset, blowup));
    }
    for (trees[3].column_logs, 0..) |_, column|
        try samples.append(allocator, try sample(trees[3], 3, column, column_offsets[3][column], 0, blowup));
    if (samples.items.len == 0) return error.InvalidCircuitOodsGeometry;

    const offsets = try allocator.alloc(field.CirclePointBaseField, samples.items.len);
    errdefer allocator.free(offsets);
    const folds = try allocator.alloc(u32, samples.items.len);
    errdefer allocator.free(folds);
    const indices = try allocator.alloc(u32, samples.items.len);
    errdefer allocator.free(indices);
    const sources = try allocator.alloc(u32, samples.items.len);
    errdefer allocator.free(sources);
    var cohorts: std.ArrayList(Cohort) = .empty;
    errdefer cohorts.deinit(allocator);
    var factors: usize = 0;
    var scratch: usize = 0;
    for (samples.items, 0..) |entry, i| {
        offsets[i] = entry.offset;
        folds[i] = entry.fold;
        indices[i] = std.math.cast(u32, i) orelse return error.CircuitOodsSizeOverflow;
        sources[i] = std.math.cast(u32, first_source[entry.tree] + entry.column) orelse return error.CircuitOodsSizeOverflow;
        const rows = try oodsPow2(entry.log);
        const blocks = std.math.divCeil(usize, rows, cuda.runtime.stages.oods.first_coefficients_per_block) catch return error.CircuitOodsSizeOverflow;
        var merged = false;
        if (cohorts.items.len != 0) {
            const previous = &cohorts.items[cohorts.items.len - 1];
            if (previous.tree == entry.tree and previous.coefficient_log == entry.log and
                previous.first_column + previous.sample_count == entry.column and
                previous.first_sample + previous.sample_count == i)
            {
                previous.sample_count += 1;
                merged = true;
            }
        }
        if (!merged) try cohorts.append(allocator, .{
            .tree = entry.tree,
            .first_column = @intCast(entry.column),
            .first_sample = @intCast(i),
            .sample_count = 1,
            .coefficient_log = entry.log,
            .coefficient_offset = entry.coefficient_offset,
            .factor_first = factors,
            .scratch_first = scratch,
        });
        factors = try oodsAdd(factors, entry.log);
        scratch = try oodsAdd(scratch, blocks);
    }
    return .{
        .allocator = allocator,
        .offsets = offsets,
        .folds = folds,
        .indices = indices,
        .sources = sources,
        .cohorts = try cohorts.toOwnedSlice(allocator),
        .factor_count = factors,
        .scratch_count = scratch,
    };
}


const Sample = struct {
    tree: u8,
    column: usize,
    log: u32,
    coefficient_offset: usize,
    offset: field.CirclePointBaseField,
    fold: u32,
};

fn sample(tree: geometry_module.Tree, tree_index: u8, column: usize, coefficient_offset: usize, offset: i32, blowup: u32) !Sample {
    if (column >= tree.column_logs.len or tree.lifted_log <= blowup) return error.InvalidCircuitOodsGeometry;
    const log = tree.column_logs[column];
    if (log == 0 or log > tree.lifted_log - blowup) return error.InvalidCircuitOodsGeometry;
    const step = canonic.CanonicCoset.new(tree.lifted_log - 1).step().mulSigned(offset);
    return .{
        .tree = tree_index,
        .column = column,
        .log = log,
        .coefficient_offset = coefficient_offset,
        .offset = .{ .x = step.x.v, .y = step.y.v },
        .fold = tree.lifted_log - blowup - log,
    };
}

fn oodsPow2(log: u32) !usize {
    if (log >= @bitSizeOf(usize)) return error.CircuitOodsSizeOverflow;
    return @as(usize, 1) << @intCast(log);
}

fn oodsAdd(a: usize, b: usize) !usize { return std.math.add(usize, a, b) catch error.CircuitOodsSizeOverflow; }
fn oodsMul(a: usize, b: usize) !usize { return std.math.mul(usize, a, b) catch error.CircuitOodsSizeOverflow; }

// ------------------------------------------------------------------ DEEP quotient

const Term = struct {
    descriptor: quotient_abi.PreparedTermDescriptor,
    source_index: u32,
    source_log: u32,
    shift: circle.CirclePointM31,
};

const Group = struct {
    shift: circle.CirclePointM31,
    log: u32,
    terms: std.ArrayList(u32) = .empty,

    fn deinit(self: *Group, allocator: std.mem.Allocator) void {
        self.terms.deinit(allocator);
    }
};

const Builder = struct {
    allocator: std.mem.Allocator,
    geometry: *const geometry_module.Geometry,
    blowup: u32,
    trace_step: circle.CirclePointM31,
    lifting_generator: circle.CirclePointM31,
    terms: std.ArrayList(Term) = .empty,
    groups: std.ArrayList(Group) = .empty,
    samples: std.ArrayList(u32) = .empty,

    fn deinit(self: *Builder) void {
        for (self.groups.items) |*group| group.deinit(self.allocator);
        self.groups.deinit(self.allocator);
        self.terms.deinit(self.allocator);
        self.samples.deinit(self.allocator);
    }

    fn appendColumn(self: *Builder, tree_index: usize, column: usize, offsets: []const i32) !void {
        const tree = self.geometry.trees[tree_index];
        // Changed from stwo-zig: any number of mask offsets (the CPU PCS adds the periodic
        // sample only for exactly two, `quotients/samples.zig`).
        if (column >= tree.column_logs.len or offsets.len == 0)
            return error.InvalidCircuitQuotientGeometry;
        const log = tree.column_logs[column];
        if (log == 0 or log >= self.geometry.fri_input_log)
            return error.InvalidCircuitQuotientGeometry;
        var source_index: usize = column;
        for (self.geometry.trees[0..tree_index]) |previous| source_index = try add(source_index, previous.column_logs.len);
        const source = std.math.cast(u32, source_index) orelse return error.CircuitQuotientSizeOverflow;
        const first_sample = self.samples.items.len;
        if (offsets.len == 2) {
            const period = self.lifting_generator.repeatedDouble(log + 1);
            try self.appendTerm(source, log, try u32Count(first_sample + 1), self.trace_step.mulSigned(offsets[1]).add(period), period);
        }
        for (offsets, 0..) |offset, ordinal| {
            try self.appendTerm(source, log, try u32Count(first_sample + ordinal), self.trace_step.mulSigned(offset), null);
            try self.samples.append(self.allocator, source);
        }
    }

    fn appendTerm(self: *Builder, source: u32, log: u32, sample_index: u32, shift: circle.CirclePointM31, period: ?circle.CirclePointM31) !void {
        const index = try u32Count(self.terms.items.len);
        try self.terms.append(self.allocator, .{
            .descriptor = .{
                .sample_index = sample_index,
                .exponent = index,
                .periodic = @intFromBool(period != null),
                .period_x = if (period) |point| point.x.v else 0,
                .period_y = if (period) |point| point.y.v else 0,
            },
            .source_index = source,
            .source_log = log,
            .shift = shift,
        });
        var group_index: usize = self.groups.items.len;
        for (self.groups.items, 0..) |group, i| {
            if (group.shift.eql(shift)) {
                group_index = i;
                break;
            }
        }
        if (group_index == self.groups.items.len)
            try self.groups.append(self.allocator, .{ .shift = shift, .log = 0 });
        const group = &self.groups.items[group_index];
        group.log = @max(group.log, log);
        try group.terms.append(self.allocator, index);
    }
};

pub fn quotientTopology(
    allocator: std.mem.Allocator,
    bound: *const composition.Bundle,
    geometry: *const geometry_module.Geometry,
    oods: *const oods_module.Plan,
    blowup: u32,
) !Topology {
    if (blowup == 0 or blowup > 4 or geometry.fri_input_log <= blowup)
        return error.InvalidCircuitQuotientGeometry;
    var masks = try masks_module.deriveMasks(
        allocator,
        bound.*,
        geometry.trees[0].column_logs.len,
        geometry.trees[1].column_logs.len,
        geometry.trees[2].column_logs.len,
    );
    defer masks.deinit();
    var builder = Builder{
        .allocator = allocator,
        .geometry = geometry,
        .blowup = blowup,
        .trace_step = canonic.CanonicCoset.new(geometry.fri_input_log - 1).step(),
        .lifting_generator = canonic.CanonicCoset.new(geometry.fri_input_log).step(),
    };
    defer builder.deinit();
    for (geometry.trees[0].column_logs, 0..) |_, column| try builder.appendColumn(0, column, &.{0});
    for (masks.base_offsets, 0..) |offsets, column| try builder.appendColumn(1, column, offsets.items);
    for (masks.interaction_offsets, 0..) |offsets, column| try builder.appendColumn(2, column, offsets.items);
    for (geometry.trees[3].column_logs, 0..) |_, column| try builder.appendColumn(3, column, &.{0});
    if (builder.samples.items.len != oods.sources.len or builder.groups.items.len == 0)
        return error.InvalidCircuitQuotientGeometry;
    for (builder.samples.items, oods.sources) |expected, actual|
        if (expected != actual) return error.InvalidCircuitQuotientGeometry;

    const sources = try compileSources(allocator, geometry, blowup);
    errdefer allocator.free(sources.columns);
    errdefer allocator.free(sources.trees);
    const terms = try allocator.alloc(quotient_abi.PreparedTermDescriptor, builder.terms.items.len);
    errdefer allocator.free(terms);
    const group_offsets = try allocator.alloc(u32, builder.groups.items.len + 1);
    errdefer allocator.free(group_offsets);
    const group_term_indices = try allocator.alloc(u32, builder.terms.items.len);
    errdefer allocator.free(group_term_indices);
    const batch_terms = try allocator.alloc(quotient_abi.BatchTermDescriptor, builder.terms.items.len);
    errdefer allocator.free(batch_terms);
    const group_logs = try allocator.alloc(u32, builder.groups.items.len);
    errdefer allocator.free(group_logs);
    const partial_logs = try allocator.alloc(u32, builder.groups.items.len);
    errdefer allocator.free(partial_logs);
    const partial_offsets = try allocator.alloc(u64, builder.groups.items.len + 1);
    errdefer allocator.free(partial_offsets);
    for (builder.terms.items, terms) |term, *descriptor| descriptor.* = term.descriptor;
    group_offsets[0] = 0;
    partial_offsets[0] = 0;
    var cursor: usize = 0;
    var maximum_log: u32 = 0;
    for (builder.groups.items, 0..) |group, i| {
        if (group.log == 0 or group.terms.items.len == 0 or group.log >= 31)
            return error.InvalidCircuitQuotientGeometry;
        group_logs[i] = group.log;
        partial_logs[i] = group.log;
        maximum_log = @max(maximum_log, group.log);
        partial_offsets[i + 1] = std.math.add(u64, partial_offsets[i], @as(u64, 1) << @intCast(group.log)) catch
            return error.CircuitQuotientSizeOverflow;
        for (group.terms.items) |term_index| {
            const term = builder.terms.items[term_index];
            group_term_indices[cursor] = term_index;
            batch_terms[cursor] = .{
                .source_index = term.source_index,
                .term_index = term_index,
                .source_log_size = term.source_log,
            };
            cursor += 1;
        }
        group_offsets[i + 1] = try u32Count(cursor);
    }
    if (cursor != terms.len) return error.InvalidCircuitQuotientGeometry;
    var hash = std.crypto.hash.sha2.Sha256.init(.{});
    hash.update("starked-bitcoin/cuda/quotient-topology/v1\x00");
    hash.update(&geometry.identity);
    hash.update(std.mem.sliceAsBytes(terms));
    hash.update(std.mem.sliceAsBytes(group_offsets));
    hash.update(std.mem.sliceAsBytes(group_term_indices));
    hash.update(std.mem.sliceAsBytes(batch_terms));
    hash.update(std.mem.sliceAsBytes(group_logs));
    hash.update(std.mem.sliceAsBytes(partial_offsets));
    return .{
        .allocator = allocator,
        .prepared_terms = terms,
        .group_offsets = group_offsets,
        .group_term_indices = group_term_indices,
        .batch_terms = batch_terms,
        .sources = sources.columns,
        .source_trees = sources.trees,
        .group_log_sizes = group_logs,
        .partial_log_sizes = partial_logs,
        .partial_offsets = partial_offsets,
        .sampled_value_count = try u32Count(builder.samples.items.len),
        .source_evaluation_word_count = sources.words,
        .maximum_partial_rows = try pow2u32(maximum_log),
        .identity = hash.finalResult(),
    };
}

/// Admit and execute the circuit's DEEP quotient with the shared Cairo CUDA
/// addressed-kernel controller. Every source remains in its committed tree.
pub fn prepareQuotient(
    allocator: std.mem.Allocator,
    session: anytype,
    bound: *const composition.Bundle,
    geometry: *const geometry_module.Geometry,
    oods_plan: *const oods_module.Plan,
    blowup: u32,
    commits: [4]commit_module.Buffers,
    oods_view: shared.resident_views.Oods,
    quotient: controller.QuotientBindings,
    twiddles_forward: common.Words,
    twiddles_inverse: common.Words,
) !controller.Prepared {
    var topology = try quotientTopology(allocator, bound, geometry, oods_plan, blowup);
    var owns_topology = true;
    errdefer if (owns_topology) topology.deinit();
    var evaluations: [4]common.Words = undefined;
    for (commits, topology.source_trees, &evaluations) |tree, span, *output| {
        if (tree.evaluations.len != span.evaluation_words or
            tree.coefficients.len != span.evaluation_words >> @intCast(blowup))
            return error.InvalidCircuitQuotientBuffers;
        output.* = tree.evaluations;
    }
    var prepared = try controller.prepareFromTopology(
        allocator,
        session,
        &topology,
        &evaluations,
        oods_view.sample_points,
        oods_view.sampled_values,
        quotient,
        twiddles_forward,
        geometry.fri_input_log,
        geometry.identity,
    );
    owns_topology = false;
    errdefer prepared.deinit();
    try prepared.initializeTransform(session, twiddles_inverse);
    return prepared;
}

const SourceSet = struct {
    columns: []types.SourceDescriptor,
    trees: []types.TreeSpan,
    words: u64,
};

fn compileSources(allocator: std.mem.Allocator, geometry: *const geometry_module.Geometry, blowup: u32) !SourceSet {
    var count: usize = 0;
    for (geometry.trees) |tree| count = try add(count, tree.column_logs.len);
    const columns = try allocator.alloc(types.SourceDescriptor, count);
    errdefer allocator.free(columns);
    const trees = try allocator.alloc(types.TreeSpan, 4);
    errdefer allocator.free(trees);
    var source_index: usize = 0;
    var all_words: u64 = 0;
    for (geometry.trees, trees, 0..) |tree, *span, ordinal| {
        var offset: u64 = 0;
        const first = source_index;
        for (tree.column_logs, 0..) |log, local| {
            const physical_log = try addU32(log, blowup);
            const stride = try pow2u32(physical_log);
            columns[source_index] = .{
                .tree_ordinal = @intCast(ordinal),
                .local_column = @intCast(local),
                .global_column = @intCast(source_index),
                .compact = .{
                    .offset_words = offset,
                    .stride_words = stride,
                    .log_size = log,
                },
            };
            source_index += 1;
            offset = std.math.add(u64, offset, stride) catch return error.CircuitQuotientSizeOverflow;
        }
        span.* = .{
            .tree_ordinal = @intCast(ordinal),
            .role = @enumFromInt(ordinal),
            .first_source = @intCast(first),
            .source_count = @intCast(tree.column_logs.len),
            .evaluation_words = offset,
        };
        all_words = std.math.add(u64, all_words, offset) catch return error.CircuitQuotientSizeOverflow;
    }
    return .{ .columns = columns, .trees = trees, .words = all_words };
}

fn pow2u32(log: u32) !u32 {
    if (log >= 31) return error.CircuitQuotientSizeOverflow;
    return @as(u32, 1) << @intCast(log);
}
fn u32Count(value: usize) !u32 { return std.math.cast(u32, value) orelse error.CircuitQuotientSizeOverflow; }
fn add(a: usize, b: usize) !usize { return std.math.add(usize, a, b) catch error.CircuitQuotientSizeOverflow; }
fn addU32(a: u32, b: u32) !u32 { return std.math.add(u32, a, b) catch error.CircuitQuotientSizeOverflow; }

// ------------------------------------------------------------------ proof layout

pub const ProofLayout = struct {
    allocator: std.mem.Allocator,
    trace_trees: [4]uniform.TraceTree,
    fri_trees: []uniform.FriTree,
    sample_counts: [4][]u8,
    sample_total: usize,

    pub fn init(
        allocator: std.mem.Allocator,
        geometry: *const geometry_module.Geometry,
        oods: *const OodsPlan,
        config: core.pcs.config_v2.PcsConfigV2,
    ) !ProofLayout {
        if (geometry.fri_layers.len == 0 or oods.sources.len != oods.offsets.len or
            config.fri_config.fold_step == 0)
            return error.InvalidCircuitProofLayout;
        var trees: [4]uniform.TraceTree = undefined;
        var counts: [4][]u8 = undefined;
        var initialized: usize = 0;
        errdefer for (counts[0..initialized]) |owned| allocator.free(owned);
        var source_first: usize = 0;
        for (geometry.trees, &trees, &counts, 0..) |tree, *target, *count_slice, index| {
            if (tree.column_logs.len == 0) return error.InvalidCircuitProofLayout;
            const max_log = std.mem.max(u32, tree.column_logs);
            if (max_log + config.fri_config.log_blowup_factor > tree.lifted_log)
                return error.InvalidCircuitProofLayout;
            target.* = .{
                .role = switch (index) {
                    0 => .preprocessed,
                    1 => .main,
                    2 => .interaction,
                    3 => .composition,
                    else => unreachable,
                },
                .column_count = tree.column_logs.len,
                .column_log_size = max_log,
                .commitment_log_size = tree.lifted_log,
                .sampled = true,
                .decommitted = true,
            };
            const owned = try allocator.alloc(u8, tree.column_logs.len);
            @memset(owned, 0);
            count_slice.* = owned;
            initialized += 1;
            const source_end = try std.math.add(usize, source_first, tree.column_logs.len);
            for (oods.sources) |source| {
                if (source >= source_first and source < source_end) {
                    const count = &owned[source - source_first];
                    if (count.* == std.math.maxInt(u8)) return error.InvalidCircuitProofLayout;
                    count.* += 1;
                }
            }
            for (owned) |count| if (count == 0) return error.InvalidCircuitProofLayout;
            source_first = source_end;
        }
        const fri = try allocator.alloc(uniform.FriTree, geometry.fri_layers.len);
        errdefer allocator.free(fri);
        for (geometry.fri_layers, fri, 0..) |layer, *target, index| target.* = .{
            .tree_index = 4 + index,
            .evaluation_log_size = layer.evaluation_log,
            .cumulative_fold = layer.cumulative_fold,
            .fold_step = layer.fold_step,
            .log_rows_per_leaf = 2,
        };
        const result = ProofLayout{
            .allocator = allocator,
            .trace_trees = trees,
            .fri_trees = fri,
            .sample_counts = counts,
            .sample_total = oods.sources.len,
        };
        try result.validate();
        return result;
    }

    pub fn deinit(self: *ProofLayout, _: std.mem.Allocator) void {
        for (self.sample_counts) |owned| self.allocator.free(owned);
        self.allocator.free(self.fri_trees);
        self.* = undefined;
    }

    pub fn validate(self: ProofLayout) !void {
        if (self.fri_trees.len == 0) return error.InvalidCircuitProofLayout;
        var samples: usize = 0;
        for (self.trace_trees, self.sample_counts, 0..) |tree, counts, index| {
            const expected_role: uniform.TraceRole = switch (index) {
                0 => .preprocessed,
                1 => .main,
                2 => .interaction,
                3 => .composition,
                else => unreachable,
            };
            if (tree.role != expected_role or !tree.sampled or !tree.decommitted or
                counts.len != tree.column_count or tree.column_log_size > tree.commitment_log_size)
                return error.InvalidCircuitProofLayout;
            for (counts) |count| {
                if (count == 0) return error.InvalidCircuitProofLayout;
                samples += count;
            }
        }
        if (samples != self.sample_total) return error.InvalidCircuitProofLayout;
        for (self.fri_trees, 0..) |tree, index| {
            if (tree.tree_index != 4 + index or tree.fold_step == 0 or
                tree.fold_step > 4 or tree.log_rows_per_leaf != 2)
                return error.InvalidCircuitProofLayout;
        }
    }

    pub fn sampleCount(self: *const ProofLayout, tree_index: usize, column_index: usize) !usize {
        if (tree_index >= 4 or column_index >= self.sample_counts[tree_index].len)
            return error.InvalidCircuitProofLayout;
        return self.sample_counts[tree_index][column_index];
    }
};
