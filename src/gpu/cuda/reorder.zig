//! Device natural → storage reorder of trees 0–1 (docs/design/gpu-cuda.md § Natural upload).
//!
//! Ingress uploads the preprocessed and main columns in natural (coset) row order, straight from
//! the host's own column slices (the witness generators' output; no host permutation). In
//! `.trace_generation` this kernel moves each cohort from its staging slot into the commitment's
//! coefficient buffer in storage order (bit-reversed circle domain), the order the in-place
//! commitment, the LogUp sources and every later stage read:
//!
//!   storage[c·2^log + s] = natural[c·2^log + natural_row(s)],
//!   natural_row = the inverse of `bitReverseIndex(cosetIndexToCircleDomainIndex(i, log), log)`
//!
//! (`air/prove.zig toStorage`). One thread per destination row (coalesced writes, gathered
//! reads), `grid = (⌈2^log / 256⌉, columns)`, one launch per cohort (≤ 65,535 columns each).
//!
//! The kernel is one fixed AOT product (`gpu/cuda_aot/witness_starked_reorder_*.cu`) under
//! stwo-zig's native-authenticated identity (`sha256-source-and-contract-v1`), ABI tag
//! `native_m31_permutation_trace_v3` (a row permutation of M31 columns; the argument contract is
//! ours and pinned by the semantic contract string).

const std = @import("std");
const cuda = @import("stwo_cuda_backend");
const common = cuda.runtime.stages.common;

pub const version: u32 = 1;
pub const abi_schema_name = "native_m31_permutation_trace_v3";
pub const abi_schema = cuda.abi.schema.KernelSchema.native_m31_permutation_trace_v3;
pub const identity_scheme = "sha256-source-and-contract-v1";
/// `natural, storage, log_size, columns`.
pub const argument_count: u32 = 4;
pub const threads: u32 = 256;
/// CUDA's grid y limit: larger cohorts are split.
pub const max_columns_per_launch: u32 = 65_535;

pub const semantic_contract = std.fmt.comptimePrint("starked-bitcoin/natural-to-storage/v{d};args=natural,storage,log_size,columns;storage[c<<log|s]=natural[c<<log|natural_row(s,log)];grid=rows/{d},columns;threads={d}", .{ version, threads, threads });

pub const Kernel = struct {
    semantic_hash: u64,
    kernel_name: [:0]u8,
    source: []u8,
    /// sha256 of `source` (the manifest's `program_identity`).
    program_identity: [32]u8,
    cache_key: u64,

    pub fn deinit(self: *Kernel, allocator: std.mem.Allocator) void {
        allocator.free(self.kernel_name);
        allocator.free(self.source);
        self.* = undefined;
    }

    pub fn label(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "starked_reorder_{x:0>16}", .{self.semantic_hash});
    }

    /// `witness_<label>_<cache key>.cu`, as stwo-zig's build requires.
    pub fn fileName(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "witness_starked_reorder_{x:0>16}_{x:0>16}.cu", .{ self.semantic_hash, self.cache_key });
    }

    /// `.trace_generation`: `count` columns of `2^log` rows, natural (`src`) → storage (`dst`);
    /// the two ranges must not overlap.
    pub fn launch(self: *const Kernel, session: anytype, src: common.Words, dst: common.Words, log_size: u32, count: usize) !void {
        if (log_size >= 31) return error.InvalidReorder;
        const rows = @as(usize, 1) << @intCast(log_size);
        if (src.len != count * rows or dst.len != count * rows) return error.InvalidReorder;
        if (count == 0) return;
        var first: usize = 0;
        while (first < count) {
            const n: u32 = @intCast(@min(count - first, max_columns_per_launch));
            const words = n * rows;
            var args = Arguments{
                .natural = try session.context.deviceSlicePointer(u32, try src.sub(first * rows, words), words),
                .storage = try session.context.deviceSlicePointer(u32, try dst.sub(first * rows, words), words),
                .log_size = log_size,
                .columns = n,
            };
            var pointers = args.pointers();
            try session.launchKernel(.{
                .stage = .trace_generation,
                .abi_schema = abi_schema,
                .cache_key = self.cache_key,
                .name = self.kernel_name,
                .grid = .{ @intCast((rows + threads - 1) / threads), n, 1 },
                .block = .{ threads, 1, 1 },
                .argument_count = argument_count,
            }, &pointers);
            first += n;
        }
    }
};

const Arguments = struct {
    natural: [*]u32,
    storage: [*]u32,
    log_size: u32,
    columns: u32,

    fn pointers(self: *Arguments) [argument_count]?*anyopaque {
        return .{ @ptrCast(&self.natural), @ptrCast(&self.storage), @ptrCast(&self.log_size), @ptrCast(&self.columns) };
    }
};

fn sha256(bytes: []const u8) [32]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return d;
}

/// The kernel and its AOT identity.
pub fn kernel(allocator: std.mem.Allocator) !Kernel {
    const semantic_hash = std.mem.readInt(u64, sha256(semantic_contract)[0..8], .big);
    const name = try std.fmt.allocPrintSentinel(allocator, "starked_reorder_v{d}_{x:0>16}", .{ version, semantic_hash }, 0);
    errdefer allocator.free(name);
    const source = try std.fmt.allocPrint(allocator,
        \\// starked-bitcoin natural -> storage reorder v{d} (src/gpu/cuda/reorder.zig).
        \\// storage[c * 2^log + s] = natural[c * 2^log + natural_row(s)]: storage row s is the
        \\// bit-reversed circle-domain index of natural (coset-order) row natural_row(s).
        \\typedef unsigned long long u64;
        \\extern "C" __global__ void __launch_bounds__({d}) {s}(
        \\    const unsigned *natural, unsigned *storage, unsigned log_size, unsigned columns) {{
        \\    const unsigned rows = 1u << log_size;
        \\    const unsigned s = blockIdx.x * blockDim.x + threadIdx.x;
        \\    const unsigned c = blockIdx.y;
        \\    if (s >= rows || c >= columns) return;
        \\    // One row (log 0) is its own image; else circle c < n/2 is natural 2c, c >= n/2 is 2(n - c) - 1.
        \\    const unsigned circle = log_size == 0u ? 0u : __brev(s) >> (32u - log_size);
        \\    const unsigned i = log_size == 0u ? 0u : circle < (rows >> 1u) ? circle << 1u : ((rows - circle) << 1u) - 1u;
        \\    const u64 base = (u64)c << log_size;
        \\    storage[base + s] = natural[base + i];
        \\}}
        \\
    , .{ version, threads, name });
    errdefer allocator.free(source);
    const program_identity = sha256(source);
    // stwo-zig `aot_identity.validate_native_aot_identity` (as `logup.kernel`).
    const payload = try std.fmt.allocPrint(allocator, "{{\"abi_schema\":\"{s}\",\"kernel_name\":\"{s}\",\"program_identity\":\"{x}\",\"semantic_hash\":\"{x:0>16}\"}}", .{ abi_schema_name, name, &program_identity, semantic_hash });
    defer allocator.free(payload);
    return .{
        .semantic_hash = semantic_hash,
        .kernel_name = name,
        .source = source,
        .program_identity = program_identity,
        .cache_key = std.mem.readInt(u64, sha256(payload)[0..8], .big),
    };
}
