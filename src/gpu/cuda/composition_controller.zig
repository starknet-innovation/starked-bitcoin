//! stwo-zig's resident composition controller (`circuit_cuda/resident_composition_controller.zig`),
//! copied with one change: the number of lookup-α powers is the system's (α⁰…α^w; our widest
//! tuple has w = 17), not the circuit's fixed 6. Minimal upstream change: take the count from the
//! plan (or accept any non-zero count); then this file can go.
const std = @import("std");
const cuda = @import("stwo_cuda_backend");
const common = cuda.runtime.stages.common;
const stages = cuda.runtime.stages;
const eval_stage = stages.cairo_eval;
const transform = stages.transform;
const topology_module = @import("stwo_cairo_cuda_integration").executor.eval.topology;
const plan_module = @import("stwo_circuit_cuda_integration").resident_composition;

const native = struct {
    const Powers = stages.constraint_power.Native;
    const Transform = transform.Native;
    const Lift = stages.composition_lift.Native;
    const Split = stages.composition_split.Native;
};

pub const SourceColumns = struct {
    coefficients: [3][]const common.Words,
    evaluations: [3][]const common.Words,
};

pub const Buffers = struct {
    arena: common.Words,
    sources: SourceColumns,
    base_parameters: common.Words,
    arguments: cuda.runtime.column.DeviceSlice(eval_stage.Args),
    trace_offsets: common.Words,
    interaction_offsets: common.Words,
    lde_descriptors: transform.AddressedLdeDescriptors,
    extended_descriptors: cuda.runtime.column.DeviceSlice(eval_stage.ExtSourceDescriptor),
    extended_parameters: common.Words,
    denominator_inverses: common.Words,
    lde_tile: common.Words,
    accumulators: common.Words,
    random_powers: common.SecureFields,
    alpha: common.SecureFields,
    relation_z: common.SecureFields,
    relation_alpha_powers: common.SecureFields,
    claimed_sums: common.SecureFields,
    composition_coefficients: common.Words,
    forward_twiddles: common.Words,
    inverse_twiddles: common.Words,
};

pub const Bound = struct {
    allocator: std.mem.Allocator,
    plan: *const plan_module.Plan,
    buffers: Buffers,
    arguments: []eval_stage.Args,
    trace_offsets: []u32,
    interaction_offsets: []u32,
    lde_descriptors: []transform.AddressedLdeDescriptor,
    launches: []eval_stage.PreparedLaunch,
    primed: bool = false,
    executed: bool = false,

    pub fn init(allocator: std.mem.Allocator, plan: *const plan_module.Plan, buffers: Buffers) !Bound {
        try validateBuffers(plan, buffers);
        const topology = plan.topology;
        const arguments = try allocator.alloc(eval_stage.Args, topology.placements.len);
        errdefer allocator.free(arguments);
        const trace_offsets = try allocator.alloc(u32, topology.summary.trace_offset_words);
        errdefer allocator.free(trace_offsets);
        const interaction_offsets = try allocator.alloc(u32, topology.summary.interaction_offset_words);
        errdefer allocator.free(interaction_offsets);
        const descriptors = try allocator.alloc(transform.AddressedLdeDescriptor, topology.sources.len);
        errdefer allocator.free(descriptors);
        @memset(std.mem.sliceAsBytes(descriptors), 0);
        const launches = try allocator.alloc(eval_stage.PreparedLaunch, topology.placements.len);
        errdefer allocator.free(launches);
        const base_parameter_offset = try arenaOffset(buffers.arena, buffers.base_parameters);
        const argument_offset = try arenaOffset(buffers.arena, buffers.arguments);
        _ = argument_offset;
        const trace_offset = try arenaOffset(buffers.arena, buffers.trace_offsets);
        const interaction_offset = try arenaOffset(buffers.arena, buffers.interaction_offsets);
        const extended_offset = try arenaOffset(buffers.arena, buffers.extended_parameters);
        const power_offset = try arenaOffset(buffers.arena, buffers.random_powers);
        const denominator_offset = try arenaOffset(buffers.arena, buffers.denominator_inverses);
        const accumulator_offset = try arenaOffset(buffers.arena, buffers.accumulators);
        const lde_tile_offset = try arenaOffset(buffers.arena, buffers.lde_tile);
        for (topology.components) |component| {
            for (topology.sources[component.first_source..][0..component.source_count], 0..) |source, local| {
                const tree = sourceTree(source.role);
                const index = source.column;
                const address = if (source.reuse_committed_lde) blk: {
                    if (index >= buffers.sources.evaluations[tree].len)
                        return error.InvalidCircuitCompositionBuffers;
                    const view = buffers.sources.evaluations[tree][index];
                    if (view.len != try pow2(component.evaluation_log_size))
                        return error.InvalidCircuitCompositionBuffers;
                    break :blk try arenaOffset(buffers.arena, view);
                } else blk: {
                    if (index >= buffers.sources.coefficients[tree].len)
                        return error.InvalidCircuitCompositionBuffers;
                    const view = buffers.sources.coefficients[tree][index];
                    if (view.len != try pow2(source.log_rows))
                        return error.InvalidCircuitCompositionBuffers;
                    descriptors[component.first_source + local] = transform.AddressedLdeDescriptor.init(
                        try arenaOffset(buffers.arena, view),
                        try checkedAdd(lde_tile_offset, source.tile_offset),
                        source.log_rows,
                    );
                    break :blk try checkedAdd(lde_tile_offset, source.tile_offset);
                };
                const at = component.first_trace_offset + 2 * local;
                trace_offsets[at] = @truncate(address);
                trace_offsets[at + 1] = @intCast(address >> 32);
            }
            if (component.recompute_source_count != 0) try transform.validateAddressedPlan(
                descriptors[component.first_source..][0..component.recompute_source_count],
                buffers.arena.len,
                @intCast(lde_tile_offset),
                component.evaluation_log_size,
            );
            const at = component.first_interaction_offset;
            interaction_offsets[at] = 0;
            interaction_offsets[at + 1] = component.preprocessed_count;
            interaction_offsets[at + 2] = component.preprocessed_count + component.main_count;
        }
        for (topology.placements, plan.placements, arguments) |placement, admitted, *out| {
            const component = topology.components[placement.component_index];
            const captured_part = plan.placements[component.first_placement + placement.part_index];
            if (admitted.component_index != placement.component_index or
                admitted.part_index != placement.part_index or
                captured_part.cache_key != admitted.cache_key)
                return error.CircuitCompositionPlacementMismatch;
            const rows = try pow2(component.evaluation_log_size);
            const coordinate = try checkedAdd(accumulator_offset, component.accumulator_offset);
            out.* = .{
                .trace_offsets = try checkedAdd(trace_offset, component.first_trace_offset),
                .interaction_offsets = try checkedAdd(interaction_offset, component.first_interaction_offset),
                .base_params = try checkedAdd(base_parameter_offset, admitted.constant_offset),
                .ext_params = try checkedAdd(extended_offset, component.first_extended_parameter),
                .random_coeffs = power_offset,
                .denom_inv = try checkedAdd(denominator_offset, component.first_denominator),
                .coord_0 = coordinate,
                .coord_1 = try checkedAdd(coordinate, rows),
                .coord_2 = try checkedAdd(coordinate, 2 * rows),
                .coord_3 = try checkedAdd(coordinate, 3 * rows),
                .row_count = @intCast(rows),
                .trace_log_size = component.trace_log_size,
                .domain_log_size = placement.domain_log_size,
                .rc_base = placement.global_rc_base,
            };
            try out.validate(.{
                .arena_words = buffers.arena.len,
                .trace_offset_count = component.source_count * 2,
                .base_param_count = admitted.constant_count,
                .ext_param_count = component.extended_parameter_count,
                .random_constraint_count = topology.summary.constraint_count,
                .denominator_count = component.denominator_count,
                .rc_count = placement.rc_count,
            });
        }
        return .{
            .allocator = allocator,
            .plan = plan,
            .buffers = buffers,
            .arguments = arguments,
            .trace_offsets = trace_offsets,
            .interaction_offsets = interaction_offsets,
            .lde_descriptors = descriptors,
            .launches = launches,
        };
    }

    pub fn deinit(self: *Bound) void {
        self.allocator.free(self.launches);
        self.allocator.free(self.lde_descriptors);
        self.allocator.free(self.interaction_offsets);
        self.allocator.free(self.trace_offsets);
        self.allocator.free(self.arguments);
        self.* = undefined;
    }

    /// All host-derived tables and strict-AOT launch receipts are fixed at
    /// ingress. Execution after this point reads only resident proof data.
    pub fn prime(self: *Bound, session: anytype) !void {
        if (self.primed) return error.CircuitCompositionAlreadyPrimed;
        const buffers = self.buffers;
        try session.context.uploadSlice(u32, buffers.base_parameters, self.plan.constants);
        try session.context.uploadSlice(eval_stage.Args, buffers.arguments, self.arguments);
        try session.context.uploadSlice(u32, buffers.trace_offsets, self.trace_offsets);
        try session.context.uploadSlice(u32, buffers.interaction_offsets, self.interaction_offsets);
        try session.context.uploadSlice(transform.AddressedLdeDescriptor, buffers.lde_descriptors, self.lde_descriptors);
        try session.context.uploadSlice(eval_stage.ExtSourceDescriptor, buffers.extended_descriptors, self.plan.topology.extended_parameter_descriptors);
        try session.context.uploadSlice(u32, buffers.denominator_inverses, self.plan.denominator_inverses);
        for (self.plan.topology.placements, self.plan.placements, self.arguments, self.launches, 0..) |placement, admitted, args, *launch, index| {
            const component = self.plan.topology.components[placement.component_index];
            launch.* = try eval_stage.prepare(session, .{
                .cache_key = admitted.cache_key,
                .kernel_name = admitted.kernel_name,
                .args = args,
                .bounds = .{
                    .arena_words = buffers.arena.len,
                    .trace_offset_count = component.source_count * 2,
                    .base_param_count = admitted.constant_count,
                    .ext_param_count = component.extended_parameter_count,
                    .random_constraint_count = self.plan.topology.summary.constraint_count,
                    .denominator_count = component.denominator_count,
                    .rc_count = placement.rc_count,
                },
            }, buffers.arena, try buffers.arguments.sub(index, 1));
        }
        self.primed = true;
    }

    pub fn execute(self: *Bound, session: anytype) !void {
        if (!self.primed or self.executed) return error.InvalidCircuitCompositionState;
        const buffers = self.buffers;
        try session.zeroResidentSlice(u32, .constraint_evaluation, buffers.accumulators);
        try native.Powers.expandReversed(session, buffers.alpha, buffers.random_powers);
        try eval_stage.materializeParameters(session, buffers.arena, .{
            .descriptors = try arenaOffset(buffers.arena, buffers.extended_descriptors),
            .descriptor_count = @intCast(self.plan.topology.extended_parameter_descriptors.len),
            .z = try arenaOffset(buffers.arena, buffers.relation_z),
            .alpha_powers = try arenaOffset(buffers.arena, buffers.relation_alpha_powers),
            .alpha_power_count = @intCast(buffers.relation_alpha_powers.len),
            .claimed_sums = try arenaOffset(buffers.arena, buffers.claimed_sums),
            .claimed_sum_count = @intCast(buffers.claimed_sums.len),
            .output = try arenaOffset(buffers.arena, buffers.extended_parameters),
            .output_words = buffers.extended_parameters.len,
        });
        const tile_offset = try arenaOffset(buffers.arena, buffers.lde_tile);
        for (self.plan.topology.components) |component| {
            if (component.recompute_source_count != 0) try native.Transform.extendAddressed(
                session,
                .constraint_evaluation,
                buffers.arena,
                try buffers.lde_descriptors.sub(component.first_source, component.recompute_source_count),
                @intCast(tile_offset),
                component.evaluation_log_size,
                buffers.forward_twiddles,
                false,
            );
            for (self.launches[component.first_placement..][0..component.placement_count]) |*launch|
                try launch.launch(session);
        }
        const accumulators = self.plan.topology.accumulators;
        if (accumulators.len == 0) return error.InvalidCircuitCompositionState;
        const maximum = accumulators[accumulators.len - 1];
        const current = try accumulatorMatrix(buffers.accumulators, maximum);
        for (accumulators[0 .. accumulators.len - 1]) |source| try native.Lift.accumulate(
            session,
            try accumulatorMatrix(buffers.accumulators, source),
            source.evaluation_log_size,
            current,
            maximum.evaluation_log_size,
        );
        const domain = try pow2(maximum.evaluation_log_size - 1);
        try native.Split.interpolateAndSplit(session, current, .{
            .storage = buffers.composition_coefficients,
            .column_stride_words = domain,
        }, maximum.evaluation_log_size, buffers.inverse_twiddles);
        self.executed = true;
    }
};

fn validateBuffers(plan: *const plan_module.Plan, buffers: Buffers) !void {
    const summary = plan.topology.summary;
    if (!plan.topology.wide_trace_offsets or buffers.arena.len == 0 or
        buffers.base_parameters.len != plan.constants.len or
        buffers.arguments.len != plan.placements.len or
        buffers.trace_offsets.len != summary.trace_offset_words or
        buffers.interaction_offsets.len != summary.interaction_offset_words or
        buffers.lde_descriptors.len != plan.topology.sources.len or
        buffers.extended_descriptors.len != plan.topology.extended_parameter_descriptors.len or
        buffers.extended_parameters.len != summary.extended_parameter_words or
        buffers.denominator_inverses.len != plan.denominator_inverses.len or
        buffers.lde_tile.len < summary.lde_tile_words or
        buffers.accumulators.len != summary.accumulator_words or
        buffers.random_powers.len != summary.constraint_count or
        buffers.alpha.len != 1 or buffers.relation_z.len != 1 or
        buffers.claimed_sums.len != summary.component_count or
        buffers.relation_alpha_powers.len == 0 or
        buffers.forward_twiddles.len < try pow2(plan.topology.accumulators[plan.topology.accumulators.len - 1].evaluation_log_size - 1) or
        buffers.inverse_twiddles.len < try pow2(plan.topology.accumulators[plan.topology.accumulators.len - 1].evaluation_log_size - 1) or
        buffers.composition_coefficients.len != 8 * (try pow2(plan.topology.accumulators[plan.topology.accumulators.len - 1].evaluation_log_size - 1)))
        return error.InvalidCircuitCompositionBuffers;
    inline for (.{ buffers.base_parameters, buffers.arguments, buffers.trace_offsets, buffers.interaction_offsets, buffers.lde_descriptors, buffers.extended_descriptors, buffers.extended_parameters, buffers.denominator_inverses, buffers.lde_tile, buffers.accumulators, buffers.random_powers, buffers.alpha, buffers.relation_z, buffers.relation_alpha_powers, buffers.claimed_sums, buffers.composition_coefficients, buffers.forward_twiddles, buffers.inverse_twiddles }) |view|
        _ = try arenaOffset(buffers.arena, view);
}

fn sourceTree(role: topology_module.SourceRole) usize {
    return switch (role) {
        .preprocessed => 0,
        .main => 1,
        .interaction => 2,
    };
}

fn arenaOffset(arena: common.Words, view: anytype) !u64 {
    if (view.owner != arena.owner or view.generation != arena.generation or
        view.address < arena.address or view.address % @sizeOf(u32) != 0)
        return error.InvalidCircuitCompositionBuffers;
    const delta = view.address - arena.address;
    if (delta % @sizeOf(u32) != 0) return error.InvalidCircuitCompositionBuffers;
    const words_view = try view.cast(u32);
    const words = try checkedAdd(delta / @sizeOf(u32), words_view.len);
    if (words > arena.len) return error.InvalidCircuitCompositionBuffers;
    return delta / @sizeOf(u32);
}

fn accumulatorMatrix(storage: common.Words, descriptor: topology_module.Accumulator) !common.WordMatrix {
    return .{
        .storage = try storage.sub(@intCast(descriptor.offset_words), @intCast(descriptor.words)),
        .column_stride_words = try pow2(descriptor.evaluation_log_size),
    };
}

fn pow2(log: u32) !usize {
    if (log >= @bitSizeOf(usize)) return error.CircuitCompositionSizeOverflow;
    return @as(usize, 1) << @intCast(log);
}

fn checkedAdd(a: anytype, b: anytype) !u64 {
    return std.math.add(u64, @intCast(a), @intCast(b)) catch error.CircuitCompositionSizeOverflow;
}

fn checkedMul(a: usize, b: usize) !usize {
    return std.math.mul(usize, a, b) catch error.CircuitCompositionSizeOverflow;
}
