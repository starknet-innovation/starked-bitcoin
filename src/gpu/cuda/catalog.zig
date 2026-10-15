//! The AOT kernel catalog of the block system: one CUDA constraint kernel per AIR.
//!
//! Each AIR is lowered with its public inputs as dedicated base constants
//! (`stwzeva.PubMode.slots`), normalised by stwo-zig's parametric CUDA path
//! (`cairo_cuda/parametric_eval.normalize`: every base literal becomes a session constant, the
//! domain size is erased) and generated with every constant dynamic, as `circuit_cuda/air_aot`
//! does for the recursion circuit. The kernel therefore depends on the AIR only: not on its log
//! size, nor on the statement. Its cache key binds the program and source identities (see
//! `identity_scheme`), so an AIR change selects new code and an unchanged AIR keeps its kernel.
//!
//! Each AIR with lookups also has a LogUp fraction kernel (`logup.zig`), a `witness` entry under
//! stwo-zig's native-authenticated identity, the system one natural → storage reorder kernel
//! (`reorder.zig`) and the seven device witness generators (`witness.zig`, the last `witness`
//! entries).
//!
//! `gpu/cuda_aot/` holds the generated sources, an `aot_manifest.json` that stwo-zig's CUDA build
//! admits (the `circuit_eval` set of our local AOT root, see build.zig `cuda-archive`) and
//! `catalog.json` (kernels → AIR). The drift test regenerates them and compares byte for byte;
//! `STARKED_CUDA_AOT_WRITE=1` rewrites them.

const std = @import("std");
const sb = @import("starked_bitcoin");
const cairo_cuda = @import("stwo_cairo_cuda_integration");
const codegen = cairo_cuda.eval_codegen;
const parametric = cairo_cuda.parametric_eval;
const ir = sb.air.ir;
const stwzeva = sb.air.stwzeva;
const M31 = @import("stwo_core").fields.m31.M31;
const logup = @import("logup.zig");
const reorder = @import("reorder.zig");
const witness = @import("witness.zig");

/// Where the generated catalog lives, relative to the repository root.
pub const directory = "gpu/cuda_aot";
/// stwo-zig's CUDA build (`scripts/cuda_build_lib/aot_identity.py`, `_validate_parametric_cairo_eval`)
/// admits parametric `cairo_eval_part_v1` kernels under two schemes only, each with a pinned
/// authority in the cache key. We use the Cairo one (the circuit one caps component indices at 11):
/// cache key = `parametric.cacheKey(program, source, parametric.source_authority)`. Which AIR a
/// kernel belongs to is recorded in `catalog.json` beside the manifest.
pub const identity_scheme = "sha256-cairo-eval-parametric-source-v6";

pub const Body = struct {
    /// The AIR's name (`ir.Air.name`).
    air: []const u8,
    /// `ir.Air.digest`: the canonical-JSON SHA-256 the statement mixes into the transcript.
    air_digest: [32]u8,
    semantic_hash: u64,
    normalized_program_identity: [32]u8,
    source_identity: [32]u8,
    cache_key: u64,
    kernel_name: []u8,
    source: []u8,
    /// Base constants the kernel reads from `args->base_params`: the AIR's literals and its
    /// public inputs, in instruction order (`parametric.writeConstants`).
    constant_count: u32,

    pub fn deinit(self: *Body, allocator: std.mem.Allocator) void {
        allocator.free(self.kernel_name);
        allocator.free(self.source);
        self.* = undefined;
    }

    /// `constraint_starked_eval_<semantic>_<cache key>.cu`
    pub fn fileName(self: Body, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "constraint_starked_eval_{x:0>16}_{x:0>16}.cu", .{ self.semantic_hash, self.cache_key });
    }
};

/// The normalised program of `air` (its public inputs as slots; values and log size are erased).
pub fn normalized(allocator: std.mem.Allocator, air: ir.Air, pubs: []const M31, log_size: u32) !@import("stwo_cairo_frontend").witness.eval_program.Program {
    var lowered = try stwzeva.lowerComponentMode(allocator, air, .{ .slots = pubs }, .{ .log_size = log_size });
    defer stwzeva.composition.deinitComponent(allocator, &lowered);
    return parametric.normalize(allocator, lowered.parts[0].program);
}

/// The kernel body of one AIR.
pub fn body(allocator: std.mem.Allocator, air: ir.Air) !Body {
    const zeros = try allocator.alloc(M31, air.n_pub);
    defer allocator.free(zeros);
    @memset(zeros, M31.zero());
    var program = try normalized(allocator, air, zeros, 4);
    defer program.deinit();
    const constant_count = try parametric.constantWordCount(program);
    const dynamic = try allocator.alloc(bool, constant_count);
    defer allocator.free(dynamic);
    @memset(dynamic, true);
    const source = try codegen.generateParametric(allocator, program, dynamic);
    errdefer allocator.free(source);
    const kernel_name = try std.fmt.allocPrint(allocator, "stwo_cairo_cuda_eval_v{}_{x:0>16}", .{ codegen.parametric_version, program.header.semantic_hash });
    errdefer allocator.free(kernel_name);
    const digest = try air.digest(allocator);
    const program_identity = codegen.programIdentity(program);
    const source_identity = codegen.sourceIdentity(source);
    return .{
        .air = air.name,
        .air_digest = digest,
        .semantic_hash = program.header.semantic_hash,
        .normalized_program_identity = program_identity,
        .source_identity = source_identity,
        .cache_key = parametric.cacheKey(program_identity, source_identity, parametric.source_authority),
        .kernel_name = kernel_name,
        .source = source,
        .constant_count = constant_count,
    };
}

/// One body per component of a system, in component order, and its LogUp kernel (null without
/// lookups).
pub const Catalog = struct {
    allocator: std.mem.Allocator,
    bodies: []Body,
    logup: []?logup.Kernel = &.{},
    /// The trace reorder (null only in tests that build a catalog by hand).
    reorder: ?reorder.Kernel = null,
    /// The device witness generators (null only in tests that build a catalog by hand).
    witness: ?witness.Kernels = null,

    pub fn init(allocator: std.mem.Allocator, airs: []const ir.Air) !Catalog {
        const bodies = try allocator.alloc(Body, airs.len);
        var made: usize = 0;
        errdefer {
            for (bodies[0..made]) |*b| b.deinit(allocator);
            allocator.free(bodies);
        }
        for (airs, bodies) |air, *out| {
            out.* = try body(allocator, air);
            made += 1;
        }
        const kernels = try allocator.alloc(?logup.Kernel, airs.len);
        @memset(kernels, null);
        errdefer {
            for (kernels) |*k| if (k.*) |*x| x.deinit(allocator);
            allocator.free(kernels);
        }
        for (airs, kernels) |air, *out| {
            if (air.lookups.len != 0) out.* = try logup.kernel(allocator, air);
        }
        for (bodies, 0..) |a, i| for (bodies[i + 1 ..]) |b| {
            if (a.cache_key == b.cache_key or std.mem.eql(u8, a.kernel_name, b.kernel_name)) return error.CudaCatalogCollision;
        };
        for (kernels, 0..) |ka, i| if (ka) |a| {
            for (bodies) |b| if (a.cache_key == b.cache_key) return error.CudaCatalogCollision;
            for (kernels[i + 1 ..]) |kb| if (kb) |b| {
                if (a.cache_key == b.cache_key or std.mem.eql(u8, a.kernel_name, b.kernel_name)) return error.CudaCatalogCollision;
            };
        };
        var permute = try reorder.kernel(allocator);
        errdefer permute.deinit(allocator);
        for (bodies) |b| if (b.cache_key == permute.cache_key) return error.CudaCatalogCollision;
        for (kernels) |k| if (k) |x| if (x.cache_key == permute.cache_key) return error.CudaCatalogCollision;
        var generators = try witness.kernels(allocator);
        errdefer generators.deinit(allocator);
        for (generators.all(), 0..) |g, i| {
            for (bodies) |b| if (b.cache_key == g.cache_key) return error.CudaCatalogCollision;
            for (kernels) |k| if (k) |x| if (x.cache_key == g.cache_key) return error.CudaCatalogCollision;
            if (permute.cache_key == g.cache_key) return error.CudaCatalogCollision;
            for (generators.all()[i + 1 ..]) |h| if (h.cache_key == g.cache_key) return error.CudaCatalogCollision;
        }
        return .{ .allocator = allocator, .bodies = bodies, .logup = kernels, .reorder = permute, .witness = generators };
    }

    pub fn deinit(self: *Catalog) void {
        for (self.bodies) |*b| b.deinit(self.allocator);
        self.allocator.free(self.bodies);
        for (self.logup) |*k| if (k.*) |*x| x.deinit(self.allocator);
        self.allocator.free(self.logup);
        if (self.reorder) |*r| r.deinit(self.allocator);
        if (self.witness) |*w| w.deinit(self.allocator);
        self.* = undefined;
    }

    /// Admits component `index` of a live system: its program must normalise to the catalog
    /// body (same code, same constant count). Returns the body.
    pub fn admit(self: *const Catalog, index: usize, program: @import("stwo_cairo_frontend").witness.eval_program.Program) !*const Body {
        if (index >= self.bodies.len) return error.CudaCatalogPlacementMismatch;
        var norm = try parametric.normalize(self.allocator, program);
        defer norm.deinit();
        const b = &self.bodies[index];
        if (!std.mem.eql(u8, &b.normalized_program_identity, &codegen.programIdentity(norm)) or
            b.constant_count != try parametric.constantWordCount(program))
            return error.CudaCatalogBodyMismatch;
        return b;
    }

    /// `aot_manifest.json` in stwo-zig's AOT product-set format (`backends/cuda/aot/native/*`): the
    /// exact field set and (kind, label, cache key) order its build validates.
    pub fn manifest(self: *const Catalog, allocator: std.mem.Allocator) ![]u8 {
        const order = try allocator.alloc(usize, self.bodies.len);
        defer allocator.free(order);
        for (order, 0..) |*o, i| o.* = i;
        std.mem.sort(usize, order, self, struct {
            fn lt(c: *const Catalog, l: usize, r: usize) bool {
                return c.bodies[l].semantic_hash < c.bodies[r].semantic_hash;
            }
        }.lt);
        var out: std.Io.Writer.Allocating = .init(allocator);
        errdefer out.deinit();
        const w = &out.writer;
        try w.writeAll("[\n");
        for (order, 0..) |i, n| {
            const b = self.bodies[i];
            const file = try b.fileName(allocator);
            defer allocator.free(file);
            var source_sha: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(b.source, &source_sha, .{});
            try w.print(
                \\  {{
                \\    "kind": "constraint",
                \\    "label": "starked_eval_{x:0>16}",
                \\    "abi_schema": "cairo_eval_part_v1",
                \\    "kernel_name": "{s}",
                \\    "cache_key": "{x:0>16}",
                \\    "semantic_hash": "{x:0>16}",
                \\    "program_identity": "{x}",
                \\    "file": "{s}",
                \\    "module_globals": "none",
                \\    "catalog_identity": "{s}",
                \\    "codegen_version": {d},
                \\    "identity_scheme": "{s}",
                \\    "occurrences": [
                \\      {{
                \\        "component_index": {d},
                \\        "part_index": 0
                \\      }}
                \\    ],
                \\    "source_sha256": "{x}"
                \\  }}{s}
                \\
            , .{
                b.semantic_hash,
                b.kernel_name,
                b.cache_key,
                b.semantic_hash,
                &b.normalized_program_identity,
                file,
                parametric.authority_hex,
                codegen.parametric_version,
                identity_scheme,
                i,
                &source_sha,
                if (n + 1 == self.bodies.len and self.logupCount() == 0 and self.reorder == null and self.witness == null) "" else ",",
            });
        }
        // LogUp fraction kernels (`kind: witness` sorts after every constraint): stwo-zig's
        // native-authenticated identity (`aot_identity.validate_native_aot_identity`).
        const lorder = try allocator.alloc(usize, self.logupCount());
        defer allocator.free(lorder);
        {
            var k: usize = 0;
            for (self.logup, 0..) |x, i| if (x != null) {
                lorder[k] = i;
                k += 1;
            };
        }
        std.mem.sort(usize, lorder, self, struct {
            fn lt(c: *const Catalog, l: usize, r: usize) bool {
                return c.logup[l].?.semantic_hash < c.logup[r].?.semantic_hash;
            }
        }.lt);
        for (lorder, 0..) |i, n| {
            const k = self.logup[i].?;
            const file = try k.fileName(allocator);
            defer allocator.free(file);
            const label = try k.label(allocator);
            defer allocator.free(label);
            try w.print(
                \\  {{
                \\    "kind": "witness",
                \\    "label": "{s}",
                \\    "abi_schema": "{s}",
                \\    "kernel_name": "{s}",
                \\    "cache_key": "{x:0>16}",
                \\    "semantic_hash": "{x:0>16}",
                \\    "program_identity": "{x}",
                \\    "file": "{s}",
                \\    "module_globals": "none",
                \\    "identity_scheme": "{s}",
                \\    "semantic_contract": "{s}"
                \\  }}{s}
                \\
            , .{
                label,
                logup.abi_schema_name,
                k.kernel_name,
                k.cache_key,
                k.semantic_hash,
                &k.program_identity,
                file,
                logup.identity_scheme,
                k.semantic_contract,
                if (n + 1 == lorder.len and self.reorder == null and self.witness == null) "" else ",",
            });
        }
        // The reorder kernel: label `starked_reorder_*` sorts after every `starked_logup_*`.
        if (self.reorder) |r| {
            const file = try r.fileName(allocator);
            defer allocator.free(file);
            const label = try r.label(allocator);
            defer allocator.free(label);
            try w.print(
                \\  {{
                \\    "kind": "witness",
                \\    "label": "{s}",
                \\    "abi_schema": "{s}",
                \\    "kernel_name": "{s}",
                \\    "cache_key": "{x:0>16}",
                \\    "semantic_hash": "{x:0>16}",
                \\    "program_identity": "{x}",
                \\    "file": "{s}",
                \\    "module_globals": "none",
                \\    "identity_scheme": "{s}",
                \\    "semantic_contract": "{s}"
                \\  }}{s}
                \\
            , .{ label, reorder.abi_schema_name, r.kernel_name, r.cache_key, r.semantic_hash, &r.program_identity, file, reorder.identity_scheme, reorder.semantic_contract, if (self.witness == null) "" else "," });
        }
        // The device witness generators: labels `starked_witness_{b2s,bytes,msg,pre,sha_columns,sha_words,walk}_*`
        // sort after `starked_reorder_*`, in this order.
        if (self.witness) |*ws| for (ws.all(), 0..) |g, n| {
            const file = try g.fileName(allocator);
            defer allocator.free(file);
            const label = try g.label(allocator);
            defer allocator.free(label);
            try w.print(
                \\  {{
                \\    "kind": "witness",
                \\    "label": "{s}",
                \\    "abi_schema": "{s}",
                \\    "kernel_name": "{s}",
                \\    "cache_key": "{x:0>16}",
                \\    "semantic_hash": "{x:0>16}",
                \\    "program_identity": "{x}",
                \\    "file": "{s}",
                \\    "module_globals": "none",
                \\    "identity_scheme": "{s}",
                \\    "semantic_contract": "{s}"
                \\  }}{s}
                \\
            , .{ label, witness.abi_schema_name, g.kernel_name, g.cache_key, g.semantic_hash, &g.program_identity, file, witness.identity_scheme, g.semantic_contract, if (n + 1 == ws.all().len) "" else "," });
        };
        try w.writeAll("]\n");
        return out.toOwnedSlice();
    }

    pub fn logupCount(self: *const Catalog) usize {
        var n: usize = 0;
        for (self.logup) |k| n += @intFromBool(k != null);
        return n;
    }

    /// `catalog.json`: which AIR (name, digest, component index) each kernel is, in component order.
    pub fn sidecar(self: *const Catalog, allocator: std.mem.Allocator) ![]u8 {
        var out: std.Io.Writer.Allocating = .init(allocator);
        errdefer out.deinit();
        const w = &out.writer;
        try w.writeAll("[\n");
        for (self.bodies, 0..) |b, i| {
            try w.print("  {{ \"component_index\": {d}, \"air\": \"{s}\", \"air_digest\": \"{x}\", \"kernel_name\": \"{s}\", \"cache_key\": \"{x:0>16}\", \"constant_count\": {d}", .{
                i, b.air, &b.air_digest, b.kernel_name, b.cache_key, b.constant_count,
            });
            if (i < self.logup.len) if (self.logup[i]) |k| try w.print(", \"logup_kernel\": \"{s}\", \"logup_cache_key\": \"{x:0>16}\", \"logup_batches\": {d}, \"logup_sources\": {d}", .{ k.kernel_name, k.cache_key, k.batches, k.sources.len });
            try w.print(" }}{s}\n", .{if (i + 1 == self.bodies.len) "" else ","});
        }
        try w.writeAll("]\n");
        return out.toOwnedSlice();
    }
};

// ------------------------------------------------------------------ tests

const block = sb.block.system;

fn blockAirs(a: std.mem.Allocator) ![block.N_COMP]ir.Air {
    return block.parseAirs(a);
}

test "cuda catalog: one kernel per AIR, independent of log size and public inputs" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try blockAirs(a);
    var prng = std.Random.DefaultPrng.init(7);
    const r = prng.random();
    for (airs) |air| {
        // Statements whose public inputs collide with each other and with AIR literals (all zero,
        // all one) and random ones, at three log sizes: one normal form.
        var identity: ?[32]u8 = null;
        var count: ?u32 = null;
        for ([_]u32{ 8, 12, 22 }) |log| for (0..3) |variant| {
            const pubs = try a.alloc(M31, air.n_pub);
            for (pubs) |*p| p.* = switch (variant) {
                0 => M31.zero(),
                1 => M31.one(),
                else => M31.fromCanonical(r.uintLessThan(u32, (1 << 31) - 1)),
            };
            var lowered = try stwzeva.lowerComponentMode(a, air, .{ .slots = pubs }, .{ .log_size = log });
            const program = lowered.parts[0].program;
            const norm = try parametric.normalize(a, program);
            const id = codegen.programIdentity(norm);
            const n = try parametric.constantWordCount(program);
            if (identity) |want| try std.testing.expectEqualSlices(u8, &want, &id) else identity = id;
            if (count) |want| try std.testing.expectEqual(want, n) else count = n;
            stwzeva.composition.deinitComponent(a, &lowered);
        };
    }
}

test "cuda catalog: generated sources and manifest match gpu/cuda_aot (drift check)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try blockAirs(a);
    var catalog = try Catalog.init(a, &airs);
    const manifest = try catalog.manifest(a);
    var total: usize = 0;
    for (catalog.bodies) |b| total += b.source.len;
    const write = std.process.hasEnvVarConstant("STARKED_CUDA_AOT_WRITE");
    if (write) {
        try std.fs.cwd().deleteTree(directory);
        try std.fs.cwd().makePath(directory);
        var dir = try std.fs.cwd().openDir(directory, .{});
        defer dir.close();
        for (catalog.bodies) |b| try dir.writeFile(.{ .sub_path = try b.fileName(a), .data = b.source });
        for (catalog.logup) |k| if (k) |x| try dir.writeFile(.{ .sub_path = try x.fileName(a), .data = x.source });
        if (catalog.reorder) |r| try dir.writeFile(.{ .sub_path = try r.fileName(a), .data = r.source });
        if (catalog.witness) |*ws| for (ws.all()) |g| try dir.writeFile(.{ .sub_path = try g.fileName(a), .data = g.source });
        try dir.writeFile(.{ .sub_path = "aot_manifest.json", .data = manifest });
        try dir.writeFile(.{ .sub_path = "catalog.json", .data = try catalog.sidecar(a) });
        std.debug.print("cuda catalog: wrote {d} constraint, {d} LogUp, {d} reorder and {d} witness kernels to {s}\n", .{ catalog.bodies.len, catalog.logupCount(), @intFromBool(catalog.reorder != null), if (catalog.witness) |*ws| ws.all().len else 0, directory });
        return;
    }
    var dir = std.fs.cwd().openDir(directory, .{ .iterate = true }) catch |e| {
        std.debug.print("cuda catalog: {s} missing; run with STARKED_CUDA_AOT_WRITE=1\n", .{directory});
        return e;
    };
    defer dir.close();
    const pinned = try dir.readFileAlloc(a, "aot_manifest.json", 1 << 20);
    try std.testing.expectEqualStrings(pinned, manifest);
    try std.testing.expectEqualStrings(try dir.readFileAlloc(a, "catalog.json", 1 << 20), try catalog.sidecar(a));
    var expected = std.StringHashMap(void).init(a);
    for (catalog.bodies) |b| {
        const name = try b.fileName(a);
        try expected.put(name, {});
        const on_disk = try dir.readFileAlloc(a, name, 64 << 20);
        try std.testing.expect(std.mem.eql(u8, on_disk, b.source));
    }
    for (catalog.logup) |k| if (k) |x| {
        const name = try x.fileName(a);
        try expected.put(name, {});
        const on_disk = try dir.readFileAlloc(a, name, 64 << 20);
        try std.testing.expect(std.mem.eql(u8, on_disk, x.source));
        total += x.source.len;
    };
    if (catalog.reorder) |r| {
        const name = try r.fileName(a);
        try expected.put(name, {});
        try std.testing.expect(std.mem.eql(u8, try dir.readFileAlloc(a, name, 1 << 20), r.source));
    }
    if (catalog.witness) |*ws| for (ws.all()) |g| {
        const name = try g.fileName(a);
        try expected.put(name, {});
        try std.testing.expect(std.mem.eql(u8, try dir.readFileAlloc(a, name, 1 << 20), g.source));
    };
    // No stale kernels.
    var it = dir.iterate();
    while (try it.next()) |entry| {
        if (std.mem.eql(u8, entry.name, "aot_manifest.json") or std.mem.eql(u8, entry.name, "catalog.json")) continue;
        if (!expected.contains(entry.name)) {
            std.debug.print("cuda catalog: stale file {s}/{s}\n", .{ directory, entry.name });
            return error.CudaCatalogDrift;
        }
    }
    std.debug.print("cuda catalog: {d} constraint, {d} LogUp, {d} reorder and {d} witness kernels ({d} KiB of CUDA) match {s}\n", .{ catalog.bodies.len, catalog.logupCount(), @intFromBool(catalog.reorder != null), if (catalog.witness) |*ws| ws.all().len else 0, total / 1024, directory });
}

// The catalog's own kernels (parametric, wide trace offsets, constants from the live program)
// built as host C++ and run row by row: their composition must equal our interpreter's, with the
// statement bound only through `args->base_params` (as `resident_composition_controller` binds
// it). This checks the exact sources a GPU build compiles; NVIDIA codegen comes with a GPU.
const shim =
    \\#include <cstdint>
    \\#define __global__
    \\#define __device__ static
    \\#define __forceinline__ inline
    \\#define __noinline__ __attribute__((noinline))
    \\#define __launch_bounds__(x)
    \\struct StwoHostDim3 { unsigned x, y, z; };
    \\static thread_local StwoHostDim3 blockIdx, blockDim, threadIdx;
    \\static inline unsigned __brev(unsigned v) {
    \\    v = ((v >> 1u) & 0x55555555u) | ((v & 0x55555555u) << 1u);
    \\    v = ((v >> 2u) & 0x33333333u) | ((v & 0x33333333u) << 2u);
    \\    v = ((v >> 4u) & 0x0f0f0f0fu) | ((v & 0x0f0f0f0fu) << 4u);
    \\    v = ((v >> 8u) & 0x00ff00ffu) | ((v & 0x00ff00ffu) << 8u);
    \\    return (v >> 16u) | (v << 16u);
    \\}
    \\static inline int __clz(unsigned v) { return v == 0u ? 32 : __builtin_clz(v); }
    \\
;

/// Mirrors the generated `StwoCairoEvalArgs`.
const Args = extern struct {
    trace_offsets: u64,
    interaction_offsets: u64,
    base_params: u64,
    ext_params: u64,
    random_coeffs: u64,
    denom_inv: u64,
    coord: [4]u64,
    row_count: u32,
    trace_log_size: u32,
    domain_log_size: u32,
    rc_base: u32,
};
const Drive = *const fn ([*]u32, u64, *const Args) callconv(.c) void;

fn hostParity(lib: *std.DynLib, a: std.mem.Allocator, air: ir.Air, b: *const Body, log_size: u32, seed: u64) !void {
    const core = @import("stwo_core");
    const component_mod = sb.air.component;
    const prover_component = @import("stwo_prover_engine").air.component_prover;
    const DomainAccumulator = @import("stwo_prover_engine").air.accumulation.DomainEvaluationAccumulator;
    const generateSecurePowers = @import("stwo_prover_engine").air.accumulation.generateSecurePowers;
    const QM31 = core.fields.qm31.QM31;
    const P = core.fields.m31.Modulus;
    var prng = std.Random.DefaultPrng.init(seed);
    const r = prng.random();
    const rand = struct {
        fn m(rr: std.Random) M31 {
            return M31.fromCanonical(rr.uintLessThan(u32, P));
        }
        fn q(rr: std.Random) QM31 {
            return QM31.fromM31(m(rr), m(rr), m(rr), m(rr));
        }
    };
    const pubs = try a.alloc(M31, air.n_pub);
    for (pubs) |*p| p.* = rand.m(r);
    var reference = try component_mod.Component.init(a, air, log_size, pubs);
    const n_batches = component_mod.nBatches(air);
    reference.n_trees = if (n_batches != 0) 3 else 2;
    if (n_batches != 0) reference.logup = .{ .z = rand.q(r), .alpha = rand.q(r), .claimed_sum = rand.q(r) };
    var live = try stwzeva.lowerComponentMode(a, air, .{ .slots = pubs }, .{ .log_size = log_size });
    _ = try (Catalog{ .allocator = a, .bodies = @constCast(b)[0..1] }).admit(0, live.parts[0].program);
    const pre_logs = try a.alloc(u32, air.n_preprocessed);
    @memset(pre_logs, log_size);
    const wrapped = try stwzeva.Component.init(a, &reference, &live, pre_logs, log_size);
    const n: usize = live.n_constraints;
    const eval_log = log_size + 1;
    const rows: usize = @as(usize, 1) << @intCast(eval_log);
    const counts = [3]usize{ air.n_preprocessed, air.n_main, 4 * n_batches };
    var tree_polys: [3][]prover_component.Poly = undefined;
    for (&tree_polys, counts) |*t, k| {
        t.* = try a.alloc(prover_component.Poly, k);
        for (t.*) |*poly| {
            const values = try a.alloc(M31, rows);
            for (values) |*v| v.* = rand.m(r);
            poly.* = .{ .log_size = eval_log, .values = values };
        }
    }
    var items: [3][]const prover_component.Poly = .{ tree_polys[0], tree_polys[1], tree_polys[2] };
    const trace = prover_component.Trace{ .polys = .{ .items = items[0..reference.n_trees] } };
    const alpha = rand.q(r);
    var acc = try DomainAccumulator.init(a, alpha, eval_log, n);
    try reference.evaluateConstraintQuotientsOnDomain(&trace, &acc);
    const want = try acc.finalize();

    const n_cols = counts[0] + counts[1] + counts[2];
    const params = try wrapped.prover.runtime.extensionParameters();
    var next: usize = 1;
    const column_base = next;
    next += n_cols * rows;
    const trace_offsets = next;
    next += 2 * n_cols;
    const interaction_offsets = next;
    next += 3;
    const base_params = next;
    next += b.constant_count;
    const ext_params = next;
    next += 4 * params.len;
    const random_coeffs = next;
    next += 4 * n;
    const denom_inv = next;
    next += live.denominator_inverses.len;
    var coordinates: [4]u64 = undefined;
    for (&coordinates) |*k| {
        k.* = next;
        next += rows;
    }
    const words = try a.alloc(u32, next);
    @memset(words, 0);
    var global: usize = 0;
    for (tree_polys, 0..) |t, tree| {
        words[interaction_offsets + tree] = @intCast(global);
        for (t) |poly| {
            const at = column_base + global * rows;
            for (poly.values, 0..) |v, i| words[at + i] = v.toU32();
            words[trace_offsets + 2 * global] = @truncate(at);
            words[trace_offsets + 2 * global + 1] = @intCast(at >> 32);
            global += 1;
        }
    }
    try parametric.writeConstants(live.parts[0].program, words[base_params..][0..b.constant_count]);
    for (params, 0..) |p, i| for (p.toM31Array(), 0..) |x, k| {
        words[ext_params + 4 * i + k] = x.toU32();
    };
    const powers = try generateSecurePowers(a, alpha, n);
    for (0..n) |i| for (powers[n - 1 - i].toM31Array(), 0..) |x, k| {
        words[random_coeffs + 4 * i + k] = x.toU32();
    };
    for (live.denominator_inverses, 0..) |d, i| words[denom_inv + i] = d;
    const args = Args{
        .trace_offsets = trace_offsets,
        .interaction_offsets = interaction_offsets,
        .base_params = base_params,
        .ext_params = ext_params,
        .random_coeffs = random_coeffs,
        .denom_inv = denom_inv,
        .coord = coordinates,
        .row_count = @intCast(rows),
        .trace_log_size = log_size,
        .domain_log_size = log_size,
        .rc_base = 0,
    };
    const sym = try std.fmt.allocPrintSentinel(a, "drive_{s}", .{b.kernel_name}, 0);
    const drive = lib.lookup(Drive, sym) orelse return error.MissingKernel;
    drive(words.ptr, words.len, &args);
    for (want.columns, coordinates) |column, at| {
        for (column, 0..) |v, row| try std.testing.expectEqual(v.toU32(), words[at + row]);
    }
}

test "cuda catalog: AOT kernels (host C++ build) equal the interpreter, statement in base_params" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try blockAirs(a);
    const catalog = try Catalog.init(a, &airs);
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const dir = try tmp.dir.realpathAlloc(a, ".");
    var argv = std.ArrayList([]const u8).empty;
    try argv.appendSlice(a, &.{ "zig", "c++", "-shared", "-O1", "-std=c++17", "-w", "-o", try std.fs.path.join(a, &.{ dir, "kernels.so" }) });
    for (catalog.bodies, 0..) |b, i| {
        const tu = try std.fmt.allocPrint(a,
            \\{s}{s}
            \\extern "C" void drive_{s}(unsigned *arena, u64 words, const StwoCairoEvalArgs *args) {{
            \\    blockDim = {{256u, 1u, 1u}};
            \\    for (unsigned row = 0; row < args->row_count; ++row) {{
            \\        blockIdx = {{row / 256u, 0u, 0u}};
            \\        threadIdx = {{row % 256u, 0u, 0u}};
            \\        {s}(arena, words, args);
            \\    }}
            \\}}
            \\
        , .{ shim, b.source, b.kernel_name, b.kernel_name });
        const path = try std.fmt.allocPrint(a, "k{d}.cpp", .{i});
        try tmp.dir.writeFile(.{ .sub_path = path, .data = tu });
        try argv.append(a, try std.fs.path.join(a, &.{ dir, path }));
    }
    var timer = try std.time.Timer.start();
    const res = try std.process.Child.run(.{ .allocator = a, .argv = argv.items, .max_output_bytes = 1 << 20 });
    if (res.term != .Exited or res.term.Exited != 0) {
        std.debug.print("zig c++ failed:\n{s}\n", .{res.stderr});
        return error.CompileFailed;
    }
    std.debug.print("cuda catalog: host C++ build of {d} AOT kernels {d} ms\n", .{ catalog.bodies.len, timer.read() / std.time.ns_per_ms });
    var lib = try std.DynLib.open(try std.fs.path.join(a, &.{ dir, "kernels.so" }));
    defer lib.close();
    for (airs, catalog.bodies, 0..) |air, *b, i| {
        // Two statements and two sizes through the same kernel.
        for ([_]u32{ 6, 9 }) |log| try hostParity(&lib, a, air, b, log, 1000 + i * 7 + log);
        std.debug.print("cuda catalog: {s}: AOT kernel = interpreter (logs 6, 9; {d} constants)\n", .{ b.air, b.constant_count });
    }
}
