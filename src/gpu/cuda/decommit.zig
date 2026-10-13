//! The decommit plan of `circuit_cuda/resident_decommit.zig` (its `Plan` type, execution unchanged),
//! built with the FRI leaf size of `fri.leafLog` instead of the circuit's fixed four rows per leaf.

const std = @import("std");
const core = @import("stwo_core");
const cc = @import("stwo_circuit_cuda_integration");
const decommit = @import("stwo_cairo_cuda_integration").executor.pcs_decommit_topology;
const geometry_module = cc.geometry;
const fri = @import("fri.zig");

pub const Plan = cc.resident_decommit.Plan;

pub fn decommitPlan(
    allocator: std.mem.Allocator,
    geometry: *const geometry_module.Geometry,
    config: core.pcs.config_v2.PcsConfigV2,
) !Plan {
    const queries = config.fri_config.n_queries;
    if (queries == 0 or geometry.fri_layers.len == 0) return error.InvalidCircuitDecommitGeometry;
    var trees: [4]decommit.GenericTree = undefined;
    for (geometry.trees, &trees) |tree, *target| target.* = .{
        .column_logs = tree.column_logs,
        .lifted_log = tree.lifted_log,
    };
    const fri_layers = try allocator.alloc(decommit.GenericFriLayer, geometry.fri_layers.len);
    defer allocator.free(fri_layers);
    for (geometry.fri_layers, fri_layers) |layer, *target| target.* = .{
        .evaluation_log = layer.evaluation_log,
        .cumulative_fold = layer.cumulative_fold,
        .fold_step = layer.fold_step,
        .log_rows_per_leaf = fri.leafLog(layer.fold_step, layer.evaluation_log),
    };
    const capacity = try capacityWords(geometry, queries);
    return .{ .topology = try decommit.deriveGeneric(
        allocator,
        trees,
        fri_layers,
        config.fri_config.log_blowup_factor,
        geometry.fri_input_log,
        queries,
        capacity,
        geometry.identity,
    ) };
}


fn capacityWords(geometry: *const geometry_module.Geometry, queries: usize) !usize {
    var words = try add(1024, try mul(queries, 2));
    for (geometry.trees) |tree| {
        words = try add(words, try mul(queries, try add(tree.column_logs.len, 1)));
        // The device Merkle walk temporarily reserves one hash (8 words)
        // and two auxiliary nodes (10 words each) per query and level.
        // Earlier 8-word accounting covered only the hash staging area.
        words = try add(words, try mul(try mul(queries, tree.lifted_log), 28));
    }
    for (geometry.fri_layers) |layer| {
        const expanded = try mul(queries, try pow2(layer.fold_step));
        words = try add(words, try mul(expanded, 9));
        // Four rows share each FRI Merkle leaf. Its 28 staging words per
        // leaf and level fit under seven words per expanded row; eight
        // leaves margin for each fixed-capacity record.
        words = try add(words, try mul(try mul(expanded, layer.evaluation_log), 8));
    }
    return try add(words, 1024);
}

fn pow2(log: u32) !usize {
    if (log >= @bitSizeOf(usize)) return error.CircuitDecommitSizeOverflow;
    return @as(usize, 1) << @intCast(log);
}
fn add(a: usize, b: usize) !usize {
    return std.math.add(usize, a, b) catch error.CircuitDecommitSizeOverflow;
}
fn mul(a: usize, b: usize) !usize {
    return std.math.mul(usize, a, b) catch error.CircuitDecommitSizeOverflow;
}
