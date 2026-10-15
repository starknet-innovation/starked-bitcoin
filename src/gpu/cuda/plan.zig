//! Host plans of one resident block-system proof: the lowered bundle, the PCS geometry and every
//! stage plan stwo-zig's resident circuit pipeline needs, built for our components.
//!
//! What is ours: the bundle (our AIRs lowered with public inputs as slots, `catalog.zig`), the
//! geometry (`circuit_cuda/geometry.Geometry` is a plain struct; its `init` is bound to the 11
//! recursion components, so `geometry` below fills it from our parts), and the composition plan
//! (`circuit_cuda/resident_composition.Plan`, filled from our catalog instead of the pinned circuit
//! catalog). The FRI and decommit plans are stwo-zig's, unchanged; the OODS, quotient and
//! proof-layout plans are stwo-zig's with the two-sample cap lifted (`masks.zig`).
//! The memory plan is `memory_plan.zig`.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cc = @import("stwo_circuit_cuda_integration");
const cairo_cuda = @import("stwo_cairo_cuda_integration");
const catalog_mod = @import("catalog.zig");
const ir = sb.air.ir;
const stwzeva = sb.air.stwzeva;
const system = sb.air.system;
const component_mod = sb.air.component;
const composition = stwzeva.composition;
const parametric = cairo_cuda.parametric_eval;
const topology_fork = @import("topology.zig");
const masks = @import("masks.zig");
const fri_mod = @import("fri.zig");
const decommit_mod = @import("decommit.zig");

pub const Geometry = cc.geometry.Geometry;
pub const Tree = cc.geometry.Tree;
pub const PcsConfig = core.pcs.config_v2.PcsConfigV2;

/// Where each component's columns start in the three trace trees (as `system.components`).
pub const Offsets = struct { pre: u32, main: u32, inter: u32 };

pub fn offsets(allocator: std.mem.Allocator, parts: []const system.Part) ![]Offsets {
    const out = try allocator.alloc(Offsets, parts.len);
    var o = Offsets{ .pre = 0, .main = 0, .inter = 0 };
    for (parts, out) |p, *x| {
        x.* = o;
        o.pre += p.air.n_preprocessed;
        o.main += p.air.n_main;
        o.inter += @intCast(4 * component_mod.nBatches(p.air.*));
    }
    return out;
}

/// The system's composition bundle: each AIR lowered with its public inputs as slots, at its own
/// log size and tree offsets, constraint offsets accumulated in component order.
pub fn bundle(allocator: std.mem.Allocator, parts: []const system.Part) !composition.Bundle {
    const offs = try offsets(allocator, parts);
    defer allocator.free(offs);
    const components = try allocator.alloc(composition.Component, parts.len);
    var made: usize = 0;
    errdefer {
        for (components[0..made]) |*c| composition.deinitComponent(allocator, c);
        allocator.free(components);
    }
    var rc: u32 = 0;
    var total: u64 = 0;
    var max_eval: u32 = 0;
    for (parts, offs, components) |p, o, *c| {
        c.* = try stwzeva.lowerComponentMode(allocator, p.air.*, .{ .slots = p.pubs }, .{
            .log_size = p.log_size,
            .pre_offset = o.pre,
            .main_offset = o.main,
            .inter_offset = o.inter,
            .rc_offset = rc,
        });
        made += 1;
        rc += c.n_constraints;
        total += c.n_constraints;
        max_eval = @max(max_eval, c.evaluation_log_size);
    }
    return .{
        .allocator = allocator,
        .max_kernel_instructions = 1_000_000,
        .total_constraints = total,
        .max_evaluation_log_size = max_eval,
        .plan_hash = composition.scheduleHash(components),
        .components = components,
    };
}

/// Column log sizes of the preprocessed, main and interaction trees, in commitment order.
pub fn treeLogs(allocator: std.mem.Allocator, parts: []const system.Part) ![3][]u32 {
    var lists: [3]std.ArrayList(u32) = .{ .empty, .empty, .empty };
    errdefer for (&lists) |*l| l.deinit(allocator);
    for (parts) |p| {
        try lists[0].appendNTimes(allocator, p.log_size, p.air.n_preprocessed);
        try lists[1].appendNTimes(allocator, p.log_size, p.air.n_main);
        try lists[2].appendNTimes(allocator, p.log_size, 4 * component_mod.nBatches(p.air.*));
    }
    var out: [3][]u32 = undefined;
    for (&out, &lists) |*o, *l| o.* = try l.toOwnedSlice(allocator);
    return out;
}

fn treeFor(allocator: std.mem.Allocator, role: cc.geometry.TreeRole, logs: []u32, config: PcsConfig) !Tree {
    errdefer allocator.free(logs);
    const blowup = config.fri_config.log_blowup_factor;
    const extended = try allocator.alloc(u32, logs.len);
    defer allocator.free(extended);
    for (logs, extended) |log, *e| e.* = log + blowup;
    return .{ .role = role, .column_logs = logs, .lifted_log = try config.treeHeight(@intFromEnum(role), extended) };
}

/// The four lifted trees and the FRI layers of our system under `config` (the logic of
/// `circuit_cuda/geometry.Geometry.init`, with our trees). `identity` hashes everything the
/// resident schedule depends on, including the catalog's kernel identities.
pub fn geometry(allocator: std.mem.Allocator, parts: []const system.Part, b: *const composition.Bundle, cat: *const catalog_mod.Catalog, config: PcsConfig) !Geometry {
    const logs = try treeLogs(allocator, parts);
    var trees: [4]Tree = undefined;
    var owned: usize = 0;
    errdefer for (trees[0..owned]) |t| allocator.free(t.column_logs);
    errdefer for (logs[owned..]) |l| allocator.free(l);
    inline for (.{ .preprocessed, .main, .interaction }, 0..) |role, i| {
        if (logs[i].len == 0) return error.EmptyResidentTree;
        trees[i] = try treeFor(allocator, role, logs[i], config);
        owned += 1;
    }
    // The prover interpolates the unsplit composition evaluation domain (one above the largest
    // trace) and commits its 2 × 4 coordinate halves.
    const composition_log = b.max_evaluation_log_size;
    const split = core.verifier_types.COMPOSITION_LOG_SPLIT;
    if (composition_log <= split) return error.InvalidResidentGeometry;
    const composition_logs = try allocator.alloc(u32, 4 << @intCast(split));
    @memset(composition_logs, composition_log - split);
    trees[3] = try treeFor(allocator, .composition, composition_logs, config);
    owned += 1;

    const blowup = config.fri_config.log_blowup_factor;
    const fri_input_log = try config.finalLiftingLogSize(trees[0].lifted_log, true, composition_log - split);
    const final_log = config.fri_config.log_last_layer_degree_bound + blowup;
    if (final_log >= fri_input_log) return error.InvalidResidentGeometry;
    const fold_step = config.fri_config.fold_step;
    const rounds = std.math.divCeil(u32, fri_input_log - final_log, fold_step) catch return error.InvalidResidentGeometry;
    const fri = core.fri.geometry.FriGeometry.initRuntime(fri_input_log, .{
        .round_count = rounds,
        .fold_step = fold_step,
        .final_log = final_log,
        .packed_log = core.fri.LOG_PACKED_LEAF_SIZE,
    }) catch return error.InvalidResidentGeometry;
    const layers = try allocator.alloc(cc.geometry.FriLayer, fri.roundCount());
    errdefer allocator.free(layers);
    for (layers, 0..) |*layer, i| {
        const evaluation_log = try fri.evaluationLog(i);
        const leaf_log = try fri.leafLog(i);
        layer.* = .{
            .evaluation_log = evaluation_log,
            .fold_step = try fri.roundFold(i),
            .cumulative_fold = try fri.cumulativeFold(i),
            .rows_per_leaf_log = evaluation_log - leaf_log,
            .leaf_log = leaf_log,
        };
    }
    return .{
        .allocator = allocator,
        .trees = trees,
        .fri_layers = layers,
        .composition_evaluation_log = composition_log,
        .fri_input_log = fri_input_log,
        .identity = identity(parts, cat, trees, layers, config),
    };
}

fn identity(parts: []const system.Part, cat: *const catalog_mod.Catalog, trees: [4]Tree, layers: []const cc.geometry.FriLayer, pcs: PcsConfig) [32]u8 {
    var h = std.crypto.hash.sha2.Sha256.init(.{});
    h.update("starked-bitcoin/cuda/resident-geometry/v1\x00");
    for (parts, cat.bodies) |p, b| {
        h.update(&b.normalized_program_identity);
        hashInt(&h, p.log_size);
    }
    for (trees) |t| {
        hashInt(&h, @intFromEnum(t.role));
        hashInt(&h, t.lifted_log);
        for (t.column_logs) |l| hashInt(&h, l);
    }
    for (layers) |l| inline for (.{ l.evaluation_log, l.fold_step, l.cumulative_fold, l.leaf_log }) |v| hashInt(&h, v);
    const f = pcs.fri_config;
    inline for (.{ f.pow_bits, f.log_blowup_factor, f.log_last_layer_degree_bound, f.n_queries, f.fold_step, pcs.trace_lifting_log_size, pcs.preprocessed_lifting_log_size }) |v| hashInt(&h, v);
    return h.finalResult();
}

fn hashInt(h: *std.crypto.hash.sha2.Sha256, v: u32) void {
    var b: [4]u8 = undefined;
    std.mem.writeInt(u32, &b, v, .little);
    h.update(&b);
}

/// `circuit_cuda/resident_composition.Plan` for our bundle: stwo-zig's heterogeneous-domain
/// topology (`deriveCanonical`, forked in `topology.zig` for components without lookups), every placement admitted against our catalog, the live constants
/// (AIR literals and the statement's public inputs) in catalog order.
pub fn compositionPlan(allocator: std.mem.Allocator, b: *const composition.Bundle, cat: *const catalog_mod.Catalog, preprocessed_logs: []const u32) !cc.resident_composition.Plan {
    const pre = try allocator.dupe(u32, preprocessed_logs);
    errdefer allocator.free(pre);
    var topology = try topology_fork.deriveCanonical(allocator, b.*, pre);
    errdefer topology.deinit();
    if (topology.components.len != cat.bodies.len or topology.placements.len != b.components.len)
        return error.ResidentCompositionPlacementMismatch;
    var constant_count: usize = 0;
    var denominator_count: usize = 0;
    for (b.components) |c| {
        if (c.parts.len != 1) return error.ResidentCompositionPlacementMismatch;
        denominator_count += c.denominator_inverses.len;
        constant_count += try parametric.constantWordCount(c.parts[0].program);
    }
    if (denominator_count != topology.summary.denominator_words) return error.ResidentCompositionPlacementMismatch;
    const constants = try allocator.alloc(u32, constant_count);
    errdefer allocator.free(constants);
    const denominators = try allocator.alloc(u32, denominator_count);
    errdefer allocator.free(denominators);
    const placements = try allocator.alloc(cc.resident_composition.Placement, b.components.len);
    var made: usize = 0;
    errdefer {
        for (placements[0..made]) |p| allocator.free(p.kernel_name);
        allocator.free(placements);
    }
    var cc_cursor: usize = 0;
    var dd_cursor: usize = 0;
    for (b.components, topology.placements, placements, 0..) |c, tp, *out, i| {
        if (tp.component_index != i or tp.part_index != 0) return error.ResidentCompositionPlacementMismatch;
        @memcpy(denominators[dd_cursor..][0..c.denominator_inverses.len], c.denominator_inverses);
        dd_cursor += c.denominator_inverses.len;
        const body = try cat.admit(i, c.parts[0].program);
        const n = body.constant_count;
        try parametric.writeConstants(c.parts[0].program, constants[cc_cursor..][0..n]);
        out.* = .{
            .component_index = @intCast(i),
            .part_index = 0,
            .cache_key = body.cache_key,
            .kernel_name = try allocator.dupeZ(u8, body.kernel_name),
            .constant_offset = @intCast(cc_cursor),
            .constant_count = n,
        };
        made += 1;
        cc_cursor += n;
    }
    return .{
        .allocator = allocator,
        .topology = topology,
        .placements = placements,
        .constants = constants,
        .denominator_inverses = denominators,
        .preprocessed_logs = pre,
    };
}

/// The largest lookup tuple width (the number of `α` powers the composition reads).
pub fn lookupWidth(parts: []const system.Part) usize {
    var w: usize = 0;
    for (parts) |p| for (p.air.lookups) |l| {
        w = @max(w, l.vals.len);
    };
    return w;
}

/// Every host plan of one proof.
pub const Plans = struct {
    allocator: std.mem.Allocator,
    config: PcsConfig,
    bundle: composition.Bundle,
    geometry: Geometry,
    composition: cc.resident_composition.Plan,
    commits: [4]cc.resident_commit.Plan,
    oods: cc.resident_oods.Plan,
    quotient: cc.resident_quotient.Topology,
    fri: fri_mod.Plan,
    decommit: decommit_mod.Plan,
    proof_layout: masks.ProofLayout,
    twiddle_words: usize,

    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part, cat: *const catalog_mod.Catalog, config: PcsConfig) !Plans {
        if (parts.len != cat.bodies.len) return error.ResidentCatalogMismatch;
        const blowup = config.fri_config.log_blowup_factor;
        var b = try bundle(allocator, parts);
        errdefer b.deinit();
        var geo = try geometry(allocator, parts, &b, cat, config);
        errdefer geo.deinit();
        var comp = try compositionPlan(allocator, &b, cat, geo.trees[0].column_logs);
        errdefer comp.deinit();
        var commits: [4]cc.resident_commit.Plan = undefined;
        var n_commits: usize = 0;
        errdefer for (commits[0..n_commits]) |*c| c.deinit();
        for (geo.trees, &commits) |t, *c| {
            c.* = try cc.resident_commit.Plan.init(allocator, t, blowup);
            n_commits += 1;
        }
        var oods = try masks.oodsPlan(allocator, &b, &geo, blowup);
        errdefer oods.deinit();
        var quotient = try masks.quotientTopology(allocator, &b, &geo, &oods, blowup);
        errdefer quotient.deinit();
        const twiddle_words = @as(usize, 1) << @intCast(geo.fri_input_log - 1);
        var fri = try fri_mod.Plan.init(allocator, &geo, config, twiddle_words);
        errdefer fri.deinit();
        var decommit = try decommit_mod.decommitPlan(allocator, &geo, config);
        errdefer decommit.deinit();
        const layout = try masks.ProofLayout.init(allocator, &geo, &oods, config);
        return .{
            .allocator = allocator,
            .config = config,
            .bundle = b,
            .geometry = geo,
            .composition = comp,
            .commits = commits,
            .oods = oods,
            .quotient = quotient,
            .fri = fri,
            .decommit = decommit,
            .proof_layout = layout,
            .twiddle_words = twiddle_words,
        };
    }

    pub fn deinit(self: *Plans) void {
        self.proof_layout.deinit(self.allocator);
        self.decommit.deinit();
        self.fri.deinit();
        self.quotient.deinit();
        self.oods.deinit();
        for (&self.commits) |*c| c.deinit();
        self.composition.deinit();
        self.geometry.deinit();
        self.bundle.deinit();
        self.* = undefined;
    }
};
