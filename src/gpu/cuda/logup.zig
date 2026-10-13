//! Device LogUp for the resident block-system prover (docs/design/gpu-cuda.md § Device LogUp).
//!
//! After the device draws `(z, α)` inside `.trace_commit`, the interaction tree (tree 2) and the
//! claimed sums are produced on the GPU, as stwo-zig's circuit pipeline does
//! (`circuit_cuda/resident_pipeline.zig`, `resident_interaction.zig`):
//! 1. `stwo_relation_expand_challenges_on` turns the drawn `(z, α)` into `z` and `α⁰…α^w`
//!    (w = our widest lookup tuple; the circuit wrapper fixes 6, so we call the ABI directly).
//! 2. One generated kernel per AIR with lookups (this file, `generate`) computes, per storage row,
//!    the paired numerator `N = m₀·d₁ + m₁·d₀` and denominator `D = d₀·d₁` of every batch exactly as
//!    `system.Fractions.fill` does, with `d = rel + Σ vᵢ·αⁱ⁺¹ − z`. Numerators go straight into the
//!    batch's four tree-2 columns; denominators into a slab.
//! 3. stwo-zig's generic `relation_completion` (batch inverse, per-row running sum across batches,
//!    claimed sums, the `claimed_sum / 2^log` shift and the coset-order prefix scan of the last
//!    column: `logup_columns.build`'s semantics) finishes tree 2 in place and writes the claims.
//!
//! Row order. Device trace columns are storage-order evaluations (bit-reversed circle domain).
//! Storage row `s` is natural (coset-order) row `i` with `s = bitrev(circle(i))`, the `natural`
//! map of `system.fractions`. A lookup read at offset `o` reads storage row
//! `bitrev(circle((i + o) mod n))`.
//!
//! Sources. The lookups read 551 of the 1,435 preprocessed and main columns. They are copied into
//! one compact slot (`logup_sources`) in `.trace_generation`, per component in kernel order
//! (`sources`), from the trees' coefficient buffers right after the natural → storage reorder
//! (`reorder.zig`), because the commitment interpolates trees 0–1 in place before the draw. The denominator slab (tree-2 sized) lives in tree 2's evaluation buffer, which
//! is unused until tree 2 is committed right after the completion.
//!
//! The kernels are AOT products (`gpu/cuda_aot/witness_starked_logup_*.cu`): stwo-zig's
//! native-authenticated identity (`sha256-source-and-contract-v1`) under the ABI tag
//! `native_blake_exact_interaction_v1` (the only paired-LogUp-fraction schema the build admits; the
//! argument contract is ours and is pinned by the semantic contract string).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const ir = sb.air.ir;
const system = sb.air.system;
const component_mod = sb.air.component;
const common = cuda.runtime.stages.common;
const completion = cuda.runtime.stages.relation_completion;
const relation_abi = cuda.abi.stages.relation;
const resident_layout = cuda.runtime.stages.resident_layout;
const field = cuda.abi.field;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

pub const version: u32 = 1;
pub const abi_schema_name = "native_blake_exact_interaction_v1";
pub const abi_schema = cuda.abi.schema.KernelSchema.native_blake_exact_interaction_v1;
pub const identity_scheme = "sha256-source-and-contract-v1";
/// `sources, outputs, pubs, powers, z, denominators, error, log_size`.
pub const argument_count: u32 = 8;
pub const threads: u32 = 256;
const pointer_words: usize = @sizeOf(usize) / @sizeOf(u32);

// ------------------------------------------------------------------ kernels

/// A column a component's lookups read.
pub const Source = struct { tree: ir.Tree, index: u32 };

/// The columns `air`'s lookups read, in kernel order: preprocessed by index, then main by index.
pub fn sources(allocator: std.mem.Allocator, air: ir.Air) ![]Source {
    const reads = try system.LookupReads.init(allocator, air);
    defer reads.deinit(allocator);
    var pre = try allocator.alloc(bool, air.n_preprocessed);
    defer allocator.free(pre);
    @memset(pre, false);
    for (air.exprs, reads.exprs) |e, live| if (live) switch (e) {
        .col => |c| if (c.tree == .preprocessed) {
            pre[c.index] = true;
        },
        else => {},
    };
    var out = std.ArrayList(Source).empty;
    errdefer out.deinit(allocator);
    for (pre, 0..) |r, i| if (r) try out.append(allocator, .{ .tree = .preprocessed, .index = @intCast(i) });
    for (reads.main, 0..) |r, i| if (r) try out.append(allocator, .{ .tree = .main, .index = @intCast(i) });
    return out.toOwnedSlice(allocator);
}

/// The widest tuple of `air`'s lookups (values, without the relation id).
pub fn width(air: ir.Air) u32 {
    var w: usize = 0;
    for (air.lookups) |l| w = @max(w, l.vals.len);
    return @intCast(w);
}

/// One AIR's fraction kernel and its AOT identity.
pub const Kernel = struct {
    air: []const u8,
    air_digest: [32]u8,
    semantic_contract: []u8,
    semantic_hash: u64,
    kernel_name: [:0]u8,
    source: []u8,
    /// sha256 of `source` (the manifest's `program_identity`).
    program_identity: [32]u8,
    cache_key: u64,
    sources: []Source,
    batches: u32,
    width: u32,

    pub fn deinit(self: *Kernel, allocator: std.mem.Allocator) void {
        allocator.free(self.semantic_contract);
        allocator.free(self.kernel_name);
        allocator.free(self.source);
        allocator.free(self.sources);
        self.* = undefined;
    }

    /// The manifest label (`[a-z0-9_]+`).
    pub fn label(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "starked_logup_{x:0>16}", .{self.semantic_hash});
    }

    /// `witness_<label>_<cache key>.cu`, as stwo-zig's build requires.
    pub fn fileName(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "witness_starked_logup_{x:0>16}_{x:0>16}.cu", .{ self.semantic_hash, self.cache_key });
    }
};

fn sha256(bytes: []const u8) [32]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return d;
}

/// The fraction kernel of `air` (which must have lookups).
pub fn kernel(allocator: std.mem.Allocator, air: ir.Air) !Kernel {
    if (air.lookups.len == 0) return error.NoLookups;
    const digest = try air.digest(allocator);
    const contract = try std.fmt.allocPrint(allocator, "starked-bitcoin/logup-fractions/v{d};air={s};digest={x};args=sources,outputs,pubs,powers,z,denominators,error,log_size;rows=storage;threads={d}", .{ version, air.name, &digest, threads });
    errdefer allocator.free(contract);
    const semantic_hash = std.mem.readInt(u64, sha256(contract)[0..8], .big);
    const name = try std.fmt.allocPrintSentinel(allocator, "starked_logup_v{d}_{x:0>16}", .{ version, semantic_hash }, 0);
    errdefer allocator.free(name);
    const srcs = try sources(allocator, air);
    errdefer allocator.free(srcs);
    const source = try generate(allocator, air, srcs, name, &digest);
    errdefer allocator.free(source);
    const program_identity = sha256(source);
    // stwo-zig `aot_identity.validate_native_aot_identity`: the cache key is the first 64 bits of
    // the sha256 of the canonical JSON {abi_schema, kernel_name, program_identity, semantic_hash}.
    const payload = try std.fmt.allocPrint(allocator, "{{\"abi_schema\":\"{s}\",\"kernel_name\":\"{s}\",\"program_identity\":\"{x}\",\"semantic_hash\":\"{x:0>16}\"}}", .{ abi_schema_name, name, &program_identity, semantic_hash });
    defer allocator.free(payload);
    return .{
        .air = air.name,
        .air_digest = digest,
        .semantic_contract = contract,
        .semantic_hash = semantic_hash,
        .kernel_name = name,
        .source = source,
        .program_identity = program_identity,
        .cache_key = std.mem.readInt(u64, sha256(payload)[0..8], .big),
        .sources = srcs,
        .batches = @intCast(component_mod.nBatches(air)),
        .width = width(air),
    };
}

const prelude =
    \\typedef unsigned long long u64;
    \\#define STARKED_P 2147483647u
    \\struct StarkedQm31 { unsigned a, b, c, d; };
    \\__device__ __forceinline__ unsigned starked_add(unsigned x, unsigned y) {
    \\    const unsigned s = x + y;
    \\    return s < STARKED_P ? s : s - STARKED_P;
    \\}
    \\__device__ __forceinline__ unsigned starked_sub(unsigned x, unsigned y) {
    \\    return x >= y ? x - y : x + STARKED_P - y;
    \\}
    \\__device__ __forceinline__ unsigned starked_mul(unsigned x, unsigned y) {
    \\    const u64 p = (u64)x * y;
    \\    const unsigned f = (unsigned)(p & STARKED_P) + (unsigned)(p >> 31u);
    \\    return f < STARKED_P ? f : f - STARKED_P;
    \\}
    \\__device__ __forceinline__ unsigned starked_neg(unsigned x) {
    \\    return x == 0u ? 0u : STARKED_P - x;
    \\}
    \\__device__ __forceinline__ StarkedQm31 starked_q_add(StarkedQm31 x, StarkedQm31 y) {
    \\    return {starked_add(x.a, y.a), starked_add(x.b, y.b), starked_add(x.c, y.c), starked_add(x.d, y.d)};
    \\}
    \\__device__ __forceinline__ StarkedQm31 starked_q_mul_base(StarkedQm31 x, unsigned s) {
    \\    return {starked_mul(x.a, s), starked_mul(x.b, s), starked_mul(x.c, s), starked_mul(x.d, s)};
    \\}
    \\// (a + b·u)(c + d·u) with u² = 2 + i over CM31 = M31[i]/(i² + 1), as stwo.
    \\__device__ __forceinline__ StarkedQm31 starked_q_mul(StarkedQm31 l, StarkedQm31 r) {
    \\    const unsigned x0 = starked_sub(starked_mul(l.a, r.a), starked_mul(l.b, r.b));
    \\    const unsigned x1 = starked_add(starked_mul(l.a, r.b), starked_mul(l.b, r.a));
    \\    const unsigned y0 = starked_sub(starked_mul(l.c, r.c), starked_mul(l.d, r.d));
    \\    const unsigned y1 = starked_add(starked_mul(l.c, r.d), starked_mul(l.d, r.c));
    \\    const unsigned c0 = starked_sub(starked_mul(l.a, r.c), starked_mul(l.b, r.d));
    \\    const unsigned c1 = starked_add(starked_mul(l.a, r.d), starked_mul(l.b, r.c));
    \\    const unsigned c2 = starked_sub(starked_mul(l.c, r.a), starked_mul(l.d, r.b));
    \\    const unsigned c3 = starked_add(starked_mul(l.c, r.b), starked_mul(l.d, r.a));
    \\    return {starked_add(x0, starked_sub(starked_add(y0, y0), y1)),
    \\            starked_add(x1, starked_add(y0, starked_add(y1, y1))),
    \\            starked_add(c0, c2), starked_add(c1, c3)};
    \\}
    \\__device__ __forceinline__ StarkedQm31 starked_q_load(const unsigned *p) {
    \\    return {p[0], p[1], p[2], p[3]};
    \\}
    \\__device__ __forceinline__ unsigned starked_brev(unsigned v, unsigned bits) {
    \\    return bits == 0u ? 0u : __brev(v) >> (32u - bits);
    \\}
    \\// Storage (bit-reversed circle-domain) index of natural (coset-order) row i.
    \\__device__ __forceinline__ unsigned starked_storage_row(unsigned i, unsigned log_size) {
    \\    const unsigned n = 1u << log_size;
    \\    const unsigned circle = (i & 1u) == 0u ? i >> 1u : n - 1u - (i >> 1u);
    \\    return starked_brev(circle, log_size);
    \\}
    \\// Natural (coset-order) row of storage index s.
    \\__device__ __forceinline__ unsigned starked_natural_row(unsigned s, unsigned log_size) {
    \\    const unsigned n = 1u << log_size;
    \\    const unsigned c = starked_brev(s, log_size);
    \\    return c < (n >> 1u) ? c << 1u : ((n - c) << 1u) - 1u;
    \\}
    \\
;

/// The CUDA source of `air`'s fraction kernel. One thread per storage row; every live lookup
/// expression once, then every batch: numerator coordinates to `outputs[4b..4b+3][row]`,
/// denominator to `denominators[b·rows + row]` (QM31, four words).
pub fn generate(allocator: std.mem.Allocator, air: ir.Air, srcs: []const Source, name: []const u8, digest: *const [32]u8) ![]u8 {
    const reads = try system.LookupReads.init(allocator, air);
    defer reads.deinit(allocator);
    var out: std.Io.Writer.Allocating = .init(allocator);
    errdefer out.deinit();
    const w = &out.writer;
    try w.print(
        \\// starked-bitcoin LogUp fraction kernel v{d} (src/gpu/cuda/logup.zig): AIR {s}, digest {x}.
        \\// {d} lookups in {d} batches, {d} source columns, tuples up to {d} values.
        \\
    , .{ version, air.name, digest, air.lookups.len, component_mod.nBatches(air), srcs.len, width(air) });
    try w.writeAll(prelude);
    try w.print(
        \\extern "C" __global__ void __launch_bounds__({d}) {s}(
        \\    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
        \\    const unsigned *powers, const unsigned *z, unsigned *denominators,
        \\    unsigned *error, unsigned log_size) {{
        \\    const unsigned rows = 1u << log_size;
        \\    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
        \\    if (row >= rows) return;
        \\    const unsigned natural = starked_natural_row(row, log_size);
        \\    (void)natural; (void)pubs;
        \\
    , .{ threads, name });
    // Row index of every offset the lookups read.
    var offsets = std.ArrayList(i32).empty;
    defer offsets.deinit(allocator);
    for (air.exprs, reads.exprs) |e, live| if (live) switch (e) {
        .col => |c| if (std.mem.indexOfScalar(i32, offsets.items, c.offset) == null) try offsets.append(allocator, c.offset),
        else => {},
    };
    std.mem.sort(i32, offsets.items, {}, std.sort.asc(i32));
    for (offsets.items) |o| {
        if (o == 0) {
            try w.writeAll("    const u64 r_0 = row;\n");
        } else {
            // (natural + o) mod rows: 2³² is a multiple of rows, so the u32 wrap is exact.
            try w.print("    const u64 r_{s}{d} = starked_storage_row((natural + {d}u) & (rows - 1u), log_size);\n", .{ if (o < 0) "m" else "p", @abs(o), @as(u32, @bitCast(o)) });
        }
    }
    for (air.exprs, reads.exprs, 0..) |e, live, id| {
        if (!live) continue;
        switch (e) {
            .col => |c| {
                var k: usize = 0;
                while (k < srcs.len and !(srcs[k].tree == c.tree and srcs[k].index == c.index)) k += 1;
                if (k == srcs.len) return error.LogupSourceMissing;
                try w.print("    const unsigned v{d} = sources[(u64){d}u * rows + r_{s}{d}];\n", .{ id, k, if (c.offset < 0) "m" else if (c.offset > 0) "p" else "", @abs(c.offset) });
            },
            .constant => |v| try w.print("    const unsigned v{d} = {d}u;\n", .{ id, v % ((1 << 31) - 1) }),
            .add => |x| try w.print("    const unsigned v{d} = starked_add(v{d}, v{d});\n", .{ id, x[0], x[1] }),
            .sub => |x| try w.print("    const unsigned v{d} = starked_sub(v{d}, v{d});\n", .{ id, x[0], x[1] }),
            .mul => |x| try w.print("    const unsigned v{d} = starked_mul(v{d}, v{d});\n", .{ id, x[0], x[1] }),
            .neg => |x| try w.print("    const unsigned v{d} = starked_neg(v{d});\n", .{ id, x }),
            .@"pub" => |i| {
                if (i >= air.n_pub) return error.LogupPubOutOfRange;
                try w.print("    const unsigned v{d} = pubs[{d}];\n", .{ id, i });
            },
        }
    }
    try w.writeAll("    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};\n");
    for (1..width(air) + 1) |i| try w.print("    const StarkedQm31 alpha{d} = starked_q_load(powers + {d});\n", .{ i, 4 * i });
    for (air.lookups, 0..) |l, j| {
        // d = rel + Σ vᵢ·αⁱ⁺¹ − z (`component.denominator`).
        try w.print("    StarkedQm31 d{d} = minus_z;\n    d{d}.a = starked_add(d{d}.a, {d}u);\n", .{ j, j, j, l.rel % ((1 << 31) - 1) });
        for (l.vals, 0..) |v, i| try w.print("    d{d} = starked_q_add(d{d}, starked_q_mul_base(alpha{d}, v{d}));\n", .{ j, j, i + 1, v });
    }
    const batches = component_mod.nBatches(air);
    for (0..batches) |b| {
        const j = 2 * b;
        try w.print("    {{\n", .{});
        if (j + 1 < air.lookups.len) {
            try w.print(
                \\        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d{d}, v{d}), starked_q_mul_base(d{d}, v{d}));
                \\        const StarkedQm31 d = starked_q_mul(d{d}, d{d});
                \\
            , .{ j + 1, air.lookups[j].mult, j, air.lookups[j + 1].mult, j, j + 1 });
        } else {
            try w.print(
                \\        const StarkedQm31 n = {{v{d}, 0u, 0u, 0u}};
                \\        const StarkedQm31 d = d{d};
                \\
            , .{ air.lookups[j].mult, j });
        }
        try w.print(
            \\        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
            \\        outputs[{d}][row] = n.a;
            \\        outputs[{d}][row] = n.b;
            \\        outputs[{d}][row] = n.c;
            \\        outputs[{d}][row] = n.d;
            \\        unsigned *slot = denominators + ((u64){d}u * rows + row) * 4u;
            \\        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
            \\    }}
            \\
        , .{ 4 * b, 4 * b + 1, 4 * b + 2, 4 * b + 3, b });
    }
    try w.writeAll("}\n");
    return out.toOwnedSlice();
}

// ------------------------------------------------------------------ plan

/// One component with lookups: its kernel, sizes and where its data lives.
pub const Instance = struct {
    component: u32,
    kernel: *const Kernel,
    log_size: u32,
    rows: u32,
    batches: u32,
    /// Offset (words) of its source block in `logup_sources`: column k at `source_offset + k·rows`.
    source_offset: usize,
    /// Each source as a (tree, global column) of trees 0–1.
    columns: []Column,
    /// First tree-2 column (its 4·batches columns follow).
    output_first: u32,
    /// Offset (words) of its denominators in the slab.
    slab_offset: usize,
    /// Its public inputs inside the statement words.
    pub_offset: u32,
    n_pub: u32,
};

pub const Column = struct { tree: u1, column: u32 };

/// The device LogUp of one system.
pub const Plan = struct {
    allocator: std.mem.Allocator,
    instances: []Instance,
    geometry: []relation_abi.Geometry,
    total_pair_blocks: u32,
    total_inverse_blocks: u32,
    total_row_blocks: u32,
    source_words: usize,
    slab_words: usize,
    output_columns: usize,
    alpha_powers: usize,

    /// `kernels[i]` is component i's kernel (null without lookups).
    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part, kernels: []const ?Kernel) !Plan {
        if (kernels.len != parts.len) return error.InvalidLogupPlan;
        var instances = std.ArrayList(Instance).empty;
        errdefer {
            for (instances.items) |x| allocator.free(x.columns);
            instances.deinit(allocator);
        }
        var geometry = std.ArrayList(relation_abi.Geometry).empty;
        errdefer geometry.deinit(allocator);
        var pre: u32 = 0;
        var main: u32 = 0;
        var inter: u32 = 0;
        var statement: u32 = 1;
        var source_words: usize = 0;
        var slab_words: usize = 0;
        var pairs: u32 = 0;
        var inverses: u32 = 0;
        var row_blocks_total: u32 = 0;
        var w: usize = 0;
        for (parts, kernels, 0..) |p, k, ci| {
            const air = p.air.*;
            const pub_offset = statement + 10;
            statement += 10 + @as(u32, @intCast(p.pubs.len));
            defer {
                pre += air.n_preprocessed;
                main += air.n_main;
                inter += @intCast(4 * component_mod.nBatches(air));
            }
            if (air.lookups.len == 0) {
                if (k != null) return error.InvalidLogupPlan;
                continue;
            }
            if (k == null) return error.InvalidLogupPlan;
            const kern: *const Kernel = &(kernels[ci].?);
            if (kern.batches != component_mod.nBatches(air) or p.pubs.len != air.n_pub) return error.InvalidLogupPlan;
            if (p.log_size < 4 or p.log_size >= 31) return error.InvalidLogupPlan;
            w = @max(w, kern.width);
            const rows: u32 = @as(u32, 1) << @intCast(p.log_size);
            const columns = try allocator.alloc(Column, kern.sources.len);
            errdefer allocator.free(columns);
            for (kern.sources, columns) |s, *c| c.* = switch (s.tree) {
                .preprocessed => .{ .tree = 0, .column = pre + s.index },
                .main => .{ .tree = 1, .column = main + s.index },
            };
            try instances.append(allocator, .{
                .component = @intCast(ci),
                .kernel = kern,
                .log_size = p.log_size,
                .rows = rows,
                .batches = kern.batches,
                .source_offset = source_words,
                .columns = columns,
                .output_first = inter,
                .slab_offset = slab_words,
                .pub_offset = pub_offset,
                .n_pub = @intCast(p.pubs.len),
            });
            source_words += kern.sources.len * rows;
            slab_words += 4 * @as(usize, rows) * kern.batches;
            // As `circuit_cuda/resident_interaction.Plan.init`.
            const row_blocks = ceilDiv(rows, relation_abi.launch_block);
            const pair_blocks = try mul(row_blocks, kern.batches);
            const inverse_blocks = ceilDiv(try mul(rows, kern.batches), relation_abi.inverse_block_values);
            try geometry.append(allocator, .{
                .pair_first = pairs,
                .pair_blocks = pair_blocks,
                .inverse_first = inverses,
                .inverse_blocks = inverse_blocks,
                .row_first = row_blocks_total,
                .row_blocks = row_blocks,
                .rows = rows,
                .columns = kern.batches,
                .real_rows = rows,
                .source_offset_rows = 0,
                .inverse_rows = @as(u32, 1) << @intCast(31 - p.log_size),
            });
            pairs = try add(pairs, pair_blocks);
            inverses = try add(inverses, inverse_blocks);
            row_blocks_total = try add(row_blocks_total, row_blocks);
        }
        if (instances.items.len == 0) return error.ResidentNeedsLookups;
        var plan = Plan{
            .allocator = allocator,
            .instances = try instances.toOwnedSlice(allocator),
            .geometry = undefined,
            .total_pair_blocks = pairs,
            .total_inverse_blocks = inverses,
            .total_row_blocks = row_blocks_total,
            .source_words = @max(source_words, 1),
            .slab_words = slab_words,
            .output_columns = 0,
            .alpha_powers = w + 1,
        };
        plan.geometry = geometry.toOwnedSlice(allocator) catch |e| {
            for (plan.instances) |x| allocator.free(x.columns);
            allocator.free(plan.instances);
            return e;
        };
        for (plan.instances) |x| plan.output_columns += 4 * x.batches;
        errdefer plan.deinit();
        try plan.topology().validate();
        return plan;
    }

    pub fn deinit(self: *Plan) void {
        for (self.instances) |x| self.allocator.free(x.columns);
        self.allocator.free(self.instances);
        self.allocator.free(self.geometry);
        self.* = undefined;
    }

    pub fn topology(self: *const Plan) completion.Topology {
        return .{
            .geometry = self.geometry,
            .max_alpha_powers = @intCast(self.alpha_powers),
            .total_pair_blocks = self.total_pair_blocks,
            .total_inverse_blocks = self.total_inverse_blocks,
            .total_chain_blocks = self.total_row_blocks,
            .total_row_blocks = self.total_row_blocks,
        };
    }

    pub fn scratchWords(self: *const Plan) !usize {
        return @intCast(try self.topology().scratchWords());
    }

    /// Words of the pointer-table slot: the output pointer table (one pointer per tree-2
    /// column), then the per-instance output, denominator and claimed-sum tables.
    pub fn tableWords(self: *const Plan) usize {
        return (self.output_columns + 3 * self.instances.len) * pointer_words;
    }
};

// ------------------------------------------------------------------ device

pub const Buffers = struct {
    /// `logup_sources` (compact lookup sources).
    sources: common.Words,
    /// Trees 0–1: each column's coefficient view (`memory.Views.coefficient_columns`), which
    /// holds the storage-order evaluations after the reorder of `.trace_generation`.
    trace: [2][]const common.Words,
    /// Tree 2: each column's coefficient view (the commitment interpolates them in place).
    outputs: []const common.Words,
    /// The denominator slab (inside tree 2's evaluation buffer).
    denominators: common.Words,
    tables: common.Words,
    geometry: completion.Geometries,
    partials: common.Words,
    scan: common.Words,
    statement: common.Words,
    /// The drawn `(z, α)`.
    lookup: common.SecureFields,
    z: common.SecureFields,
    powers: common.SecureFields,
    claims_mixed: common.SecureFields,
    claims_component: common.SecureFields,
    error_flag: common.Words,

    pub fn validate(self: Buffers, plan: *const Plan) !void {
        const scratch = try plan.scratchWords();
        if (self.sources.len != plan.source_words or self.denominators.len != plan.slab_words or
            self.outputs.len != plan.output_columns or self.tables.len != plan.tableWords() or
            self.geometry.len != plan.instances.len or self.partials.len != scratch or self.scan.len != scratch or
            self.lookup.len != 2 or self.z.len != 1 or self.powers.len < plan.alpha_powers or
            self.claims_mixed.len != plan.instances.len or self.error_flag.len != 1 or
            self.tables.address % @alignOf(usize) != 0)
            return error.InvalidLogupBuffers;
        for (plan.instances) |x| {
            for (x.columns) |c| if (c.column >= self.trace[c.tree].len or self.trace[c.tree][c.column].len != x.rows) return error.InvalidLogupBuffers;
            for (self.outputs[x.output_first..][0 .. 4 * x.batches]) |o| if (o.len != x.rows) return error.InvalidLogupBuffers;
            if (x.component >= self.claims_component.len or x.pub_offset + x.n_pub > self.statement.len) return error.InvalidLogupBuffers;
        }
    }

    fn outputTable(self: Buffers, plan: *const Plan, instance: usize) !common.Words {
        const x = plan.instances[instance];
        return self.tables.sub(x.output_first * pointer_words, 4 * x.batches * pointer_words);
    }
    fn table(self: Buffers, plan: *const Plan, which: usize) !common.Words {
        const n = plan.instances.len;
        return self.tables.sub((plan.output_columns + which * n) * pointer_words, n * pointer_words);
    }
    fn slab(self: Buffers, plan: *const Plan, instance: usize) !common.SecureFields {
        const x = plan.instances[instance];
        return (try self.denominators.sub(x.slab_offset, 4 * @as(usize, x.rows) * x.batches)).cast(field.SecureField);
    }
};

pub const Bound = struct {
    allocator: std.mem.Allocator,
    plan: *const Plan,
    buffers: Buffers,
    prepared: ?*completion.PreparedPlan = null,
    /// Per instance, the output column views (owned; `completion.prepare` copies them too).
    coordinates: [][]common.Words = &.{},

    pub fn init(allocator: std.mem.Allocator, plan: *const Plan, buffers: Buffers) !Bound {
        try buffers.validate(plan);
        return .{ .allocator = allocator, .plan = plan, .buffers = buffers };
    }

    pub fn deinit(self: *Bound) void {
        if (self.prepared) |p| completion.deinit(self.allocator, p);
        for (self.coordinates) |c| self.allocator.free(c);
        self.allocator.free(self.coordinates);
        self.* = undefined;
    }

    /// Ingress: the pointer tables and the completion geometry. (The caller zeroes
    /// `claims_component`: components without lookups keep a zero claim.)
    pub fn prime(self: *Bound, session: anytype) !void {
        const plan = self.plan;
        const b = self.buffers;
        const words = try self.allocator.alloc(u32, plan.tableWords());
        defer self.allocator.free(words);
        const put = struct {
            fn f(dst: []u32, at: usize, address: usize) void {
                dst[at * pointer_words] = @truncate(address);
                dst[at * pointer_words + 1] = @truncate(address >> 32);
            }
        }.f;
        for (b.outputs, 0..) |o, i| put(words, i, o.address);
        const n = plan.instances.len;
        for (plan.instances, 0..) |_, i| {
            put(words, plan.output_columns + i, (try b.outputTable(plan, i)).address);
            put(words, plan.output_columns + n + i, (try b.slab(plan, i)).address);
            put(words, plan.output_columns + 2 * n + i, (try b.claims_mixed.sub(i, 1)).address);
        }
        try session.context.uploadSlice(u32, b.tables, words);
        try session.context.uploadSlice(relation_abi.Geometry, b.geometry, plan.geometry);
        try self.prepareCompletion();
    }

    /// stwo-zig's checked completion plan over our views (no device work; host-testable).
    pub fn prepareCompletion(self: *Bound) !void {
        const plan = self.plan;
        const b = self.buffers;
        const n = plan.instances.len;
        if (self.prepared != null) return error.LogupAlreadyPrimed;
        self.coordinates = try self.allocator.alloc([]common.Words, n);
        @memset(self.coordinates, &.{});
        const instances = try self.allocator.alloc(completion.InstanceBinding, n);
        defer self.allocator.free(instances);
        for (plan.instances, instances, self.coordinates, 0..) |x, *inst, *coords, i| {
            coords.* = try self.allocator.dupe(common.Words, b.outputs[x.output_first..][0 .. 4 * x.batches]);
            inst.* = .{
                .output_pointer_table = try b.outputTable(plan, i),
                .output_coordinates = coords.*,
                .denominator_slab = try b.slab(plan, i),
                .claimed_sum = try b.claims_mixed.sub(i, 1),
            };
        }
        self.prepared = try completion.prepare(self.allocator, .{
            .topology = plan.topology(),
            .buffers = .{
                .output_tables = try b.table(plan, 0),
                .denominator_slabs = try b.table(plan, 1),
                .geometry = b.geometry,
                .claimed_sums = try b.table(plan, 2),
                .reduction_partials = b.partials,
                .scan_block_sums = b.scan,
            },
            .instances = instances,
        });
    }

    /// `.trace_generation`, after the reorder (`pipeline.assembleTrace`): the lookups' columns,
    /// from the trees' coefficient buffers into `logup_sources` (runs of adjacent columns in one
    /// copy).
    pub fn gather(self: *const Bound, session: anytype) !void {
        const b = self.buffers;
        for (self.plan.instances) |x| {
            var k: usize = 0;
            while (k < x.columns.len) {
                const first = b.trace[x.columns[k].tree][x.columns[k].column];
                var run: usize = 1;
                while (k + run < x.columns.len) : (run += 1) {
                    const c = x.columns[k + run];
                    const next = b.trace[c.tree][c.column];
                    if (next.address != first.address + run * x.rows * 4) break;
                }
                const src = common.Words{ .address = first.address, .len = run * x.rows, .owner = first.owner, .generation = first.generation };
                try session.context.copyDeviceSlice(u32, try b.sources.sub(x.source_offset + k * x.rows, run * x.rows), src);
                k += run;
            }
        }
    }

    /// `.trace_commit`, after the draw: fractions, completion, claims.
    pub fn execute(self: *const Bound, session: anytype) !void {
        const plan = self.plan;
        const b = self.buffers;
        try expandChallenges(session, b.lookup, b.z, b.powers);
        const powers = try session.context.deviceSlicePointer(u32, try b.powers.cast(u32), 4 * plan.alpha_powers);
        const z = try session.context.deviceSlicePointer(u32, try b.z.cast(u32), 4);
        const err = try session.context.deviceSlicePointer(u32, b.error_flag, 1);
        for (plan.instances, 0..) |x, i| {
            const n_sources = x.columns.len * x.rows;
            const source_view = if (n_sources == 0) b.sources else try b.sources.sub(x.source_offset, n_sources);
            const pub_view = if (x.n_pub == 0) b.statement else try b.statement.sub(x.pub_offset, x.n_pub);
            var args = Arguments{
                .sources = try session.context.deviceSlicePointer(u32, source_view, 1),
                .outputs = try session.context.deviceSlicePointer(u32, try b.outputTable(plan, i), 4 * x.batches * pointer_words),
                .pubs = try session.context.deviceSlicePointer(u32, pub_view, 1),
                .powers = powers,
                .z = z,
                .denominators = try session.context.deviceSlicePointer(u32, try (try b.slab(plan, i)).cast(u32), 4 * @as(usize, x.rows) * x.batches),
                .error_flag = err,
                .log_size = x.log_size,
            };
            var pointers = args.pointers();
            try session.launchKernel(.{
                .stage = .trace_commit,
                .abi_schema = abi_schema,
                .cache_key = x.kernel.cache_key,
                .name = x.kernel.kernel_name,
                .grid = .{ ceilDiv(x.rows, threads), 1, 1 },
                .block = .{ threads, 1, 1 },
                .argument_count = argument_count,
            }, &pointers);
        }
        try completion.TraceCommitNative.execute(session, self.prepared orelse return error.LogupNotPrimed);
        // Per-component claims for the composition (zero where a component has no lookups).
        var i: usize = 0;
        while (i < plan.instances.len) {
            var run: usize = 1;
            while (i + run < plan.instances.len and plan.instances[i + run].component == plan.instances[i].component + run) run += 1;
            try session.context.copyDeviceSlice(u32, try (try b.claims_component.sub(plan.instances[i].component, run)).cast(u32), try (try b.claims_mixed.sub(i, run)).cast(u32));
            i += run;
        }
    }
};

/// The kernel arguments (by value, as `cuLaunchKernel` takes them).
const Arguments = struct {
    sources: [*]u32,
    outputs: [*]u32,
    pubs: [*]u32,
    powers: [*]u32,
    z: [*]u32,
    denominators: [*]u32,
    error_flag: [*]u32,
    log_size: u32,

    fn pointers(self: *Arguments) [argument_count]?*anyopaque {
        return .{
            @ptrCast(&self.sources),     @ptrCast(&self.outputs), @ptrCast(&self.pubs),         @ptrCast(&self.powers),
            @ptrCast(&self.z),           @ptrCast(&self.denominators), @ptrCast(&self.error_flag), @ptrCast(&self.log_size),
        };
    }
};

/// `z` and `α⁰…α^(n−1)` from the drawn `(z, α)` (`stwo_relation_expand_challenges_on`; the circuit
/// wrapper `circuit_interaction.expandChallenges` fixes n = 6).
pub fn expandChallenges(session: anytype, drawn: common.SecureFields, z: common.SecureFields, powers: common.SecureFields) !void {
    try common.requireStage(session, .trace_commit);
    if (drawn.len != 2 or z.len != 1 or powers.len == 0) return error.InvalidKernelDescriptor;
    const d = try resident_layout.resident(session, field.SecureField, drawn, 2);
    const p = try resident_layout.resident(session, field.SecureField, powers, powers.len);
    const x = try resident_layout.resident(session, field.SecureField, z, 1);
    try resident_layout.requireDisjoint(&.{ p.range, x.range }, &.{d.range});
    try common.record(session, .trace_commit, relation_abi.stwo_relation_expand_challenges_on(d.pointer, p.pointer, @intCast(powers.len), @ptrCast(x.pointer), session.context.stream));
}

fn ceilDiv(value: u32, divisor: u32) u32 {
    return value / divisor + @intFromBool(value % divisor != 0);
}
fn add(a: u32, b: u32) !u32 {
    return std.math.add(u32, a, b) catch error.InvalidLogupPlan;
}
fn mul(a: u32, b: u32) !u32 {
    return std.math.mul(u32, a, b) catch error.InvalidLogupPlan;
}

// ------------------------------------------------------------------ host model

/// A host model of `relation_completion` (stwo-zig `native/relation/graph.cu`) for one instance:
/// `outputs` hold the paired numerators, `slab` the denominators (`slab[b·rows + row]`). Inverts,
/// accumulates each row across batches, sums the last column, subtracts `claimed_sum · inverse_rows`
/// and prefix-sums the last column in coset order (`relation_coset_scan_row`). Returns the claim.
pub fn hostComplete(geometry: relation_abi.Geometry, outputs: []const []M31, slab: []const QM31) !QM31 {
    const rows = geometry.rows;
    const columns = geometry.columns;
    if (outputs.len != 4 * columns or slab.len != @as(usize, rows) * columns) return error.InvalidLogupBuffers;
    var claim = QM31.zero();
    for (0..rows) |row| {
        var acc = QM31.zero();
        for (0..columns) |c| {
            const n = QM31.fromM31(outputs[4 * c][row], outputs[4 * c + 1][row], outputs[4 * c + 2][row], outputs[4 * c + 3][row]);
            const d = slab[c * rows + row];
            if (d.isZero()) return error.DegenerateDenominator;
            acc = acc.add(n.mul(try d.inv()));
            const xs = acc.toM31Array();
            for (0..4) |k| outputs[4 * c + k][row] = xs[k];
        }
        claim = claim.add(acc);
    }
    const sum = claim.toM31Array();
    const inv_rows = M31.fromCanonical(geometry.inverse_rows);
    const bits = std.math.log2_int(u32, rows);
    for (0..4) |k| {
        const col = outputs[4 * (columns - 1) + k];
        const shift = inv_rows.mul(sum[k]);
        var running = M31.zero();
        for (0..rows) |scan| {
            const circle: u32 = if (scan & 1 == 0) @intCast(scan / 2) else rows - 1 - @as(u32, @intCast(scan / 2));
            const row: usize = if (bits == 0) 0 else @bitReverse(circle) >> @intCast(32 - @as(u32, bits));
            running = running.add(col[row].sub(shift));
            col[row] = running;
        }
    }
    return claim;
}
