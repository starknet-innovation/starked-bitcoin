//! Device witness generation (docs/design/gpu-cuda.md § Device witness): in `.trace_generation`,
//! before the natural → storage reorder, four fixed kernels write the largest trace columns into
//! the trees' staging slots in natural row order, exactly where ingress would have put the host's
//! columns. Everything downstream (reorder, LogUp gather, commitments) is unchanged.
//!
//! | kernel | grid | writes | host generator |
//! |---|---|---|---|
//! | `sha_words` | one thread per 72-row period | words `a, e, w` per row (scratch) | `sha256/witness.zig Words.place` |
//! | `sha_columns` | one thread per row | `block_sha`'s 144 columns | `witness.columns` (shaRole), `block/sha.zig Extra` |
//! | `b2s` | one thread per row (recomputes its period's G steps) | `block_b2s`'s 312 columns | `hash/blake2s_air.zig fillPeriod`, `block/commit.zig B2sFill` |
//! | `pre` | one thread per (row, column), one launch per tree-0 cohort | every preprocessed column | `ir.PreCol.at` |
//!
//! Ingress uploads only their small inputs into one slot (`witness_inputs`, `Layout`): the SHA-256
//! round constants and Blake2s σ table, per `block_sha` period its compression (input state, block)
//! and final `Meta`, per `block_b2s` period its compression input (chaining value, block, counter,
//! last flag) plus one dummy, the preprocessed column descriptors and periodic values, and the
//! device address of every generated column (pointer tables). The SHA word trace (3 words per row)
//! lives in `witness_scratch` (`.trace_generation` only).
//!
//! Each kernel is one fixed AOT `witness` product under stwo-zig's native-authenticated identity
//! (`sha256-source-and-contract-v1`), ABI tag `native_indexed_recurrence_trace_v1` (a row-indexed
//! trace; the tag is only an equality key between the manifest and the launch, the five-argument
//! contract is ours and pinned by each kernel's semantic contract).

const std = @import("std");
const sb = @import("starked_bitcoin");
const cuda = @import("stwo_cuda_backend");
const common = cuda.runtime.stages.common;
const ir = sb.air.ir;
const system = sb.air.system;
const shaw = sb.sha256_witness;
const spec = sb.sha256;
const bsha = sb.block.sha;
const commit = sb.block.commit;
const b2 = sb.blake2s_air;
const P = @import("stwo_core").fields.m31.Modulus;

pub const version: u32 = 1;
pub const abi_schema_name = "native_indexed_recurrence_trace_v1";
pub const abi_schema = cuda.abi.schema.KernelSchema.native_indexed_recurrence_trace_v1;
pub const identity_scheme = "sha256-source-and-contract-v1";
pub const argument_count: u32 = 5;
pub const threads: u32 = 256;
pub const period_threads: u32 = 64;
pub const max_columns_per_launch: u32 = 65_535;

pub const SHA_COLUMNS: usize = bsha.N_MAIN;
pub const B2S_COLUMNS: usize = 312;
const SHA_COMP_WORDS = 24;
const SHA_META_WORDS = 6;
const B2S_PERIOD_WORDS = 27;
const PRE_DESC_WORDS = 8;

pub const Which = enum { b2s, pre, sha_columns, sha_words };

/// One fixed kernel and its AOT identity (as `reorder.Kernel`).
pub const Kernel = struct {
    which: Which,
    semantic_contract: []u8,
    semantic_hash: u64,
    kernel_name: [:0]u8,
    source: []u8,
    program_identity: [32]u8,
    cache_key: u64,

    pub fn deinit(self: *Kernel, allocator: std.mem.Allocator) void {
        allocator.free(self.semantic_contract);
        allocator.free(self.kernel_name);
        allocator.free(self.source);
        self.* = undefined;
    }

    pub fn label(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "starked_witness_{s}_{x:0>16}", .{ @tagName(self.which), self.semantic_hash });
    }

    /// `witness_<label>_<cache key>.cu`, as stwo-zig's build requires.
    pub fn fileName(self: Kernel, allocator: std.mem.Allocator) ![]u8 {
        return std.fmt.allocPrint(allocator, "witness_starked_witness_{s}_{x:0>16}_{x:0>16}.cu", .{ @tagName(self.which), self.semantic_hash, self.cache_key });
    }

    fn launch(self: *const Kernel, session: anytype, grid: [3]u32, block: u32, arguments: *[argument_count]?*anyopaque) !void {
        try session.launchKernel(.{
            .stage = .trace_generation,
            .abi_schema = abi_schema,
            .cache_key = self.cache_key,
            .name = self.kernel_name,
            .grid = grid,
            .block = .{ block, 1, 1 },
            .argument_count = argument_count,
        }, arguments);
    }
};

/// The four kernels, in manifest (label) order.
pub const Kernels = struct {
    b2s: Kernel,
    pre: Kernel,
    sha_columns: Kernel,
    sha_words: Kernel,

    pub fn deinit(self: *Kernels, allocator: std.mem.Allocator) void {
        inline for (.{ &self.b2s, &self.pre, &self.sha_columns, &self.sha_words }) |k| k.deinit(allocator);
    }

    pub fn all(self: *const Kernels) [4]*const Kernel {
        return .{ &self.b2s, &self.pre, &self.sha_columns, &self.sha_words };
    }
};

fn sha256(bytes: []const u8) [32]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return d;
}

fn contract(allocator: std.mem.Allocator, which: Which) ![]u8 {
    return switch (which) {
        .sha_words => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-sha-words/v{d};args=ktab(meta region: K[64], then meta),comps,count,words,rows;per 72-row period p: Words.place(comps[p] or zero dummy) -> a,e,w at words[0|rows|2rows + r];grid=periods/{d};threads={d}", .{ version, period_threads, period_threads }),
        .sha_columns => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-sha-columns/v{d};args=words,meta,count,columns,rows;block_sha 144 natural columns: sha256 columns(shaRole, K=meta[0..64]) + Extra(meta[64+6p]: mid,blk,flags,lid,rid,ym);columns=u64 pointers;grid=rows/{d};threads={d}", .{ version, threads, threads }),
        .b2s => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-b2s/v{d};args=sigma,periods,count,columns,rows;block_b2s 312 natural columns: fillPeriod(periods[min(p,count)]: h8,m16,tlo,thi,last) + B2sFill extras;columns=u64 pointers;grid=rows/{d};threads={d}", .{ version, threads, threads }),
        .pre => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-pre/v{d};args=desc,values,first,log_size,columns;out[i]=PreCol.at(i,2^log) natural;desc=kind,k,voff,vlen,ptr_lo,ptr_hi,0,0;grid=rows/{d},columns;threads={d}", .{ version, threads, threads }),
    };
}

fn kernelOf(allocator: std.mem.Allocator, which: Which) !Kernel {
    const sc = try contract(allocator, which);
    errdefer allocator.free(sc);
    const semantic_hash = std.mem.readInt(u64, sha256(sc)[0..8], .big);
    const name = try std.fmt.allocPrintSentinel(allocator, "starked_witness_{s}_v{d}_{x:0>16}", .{ @tagName(which), version, semantic_hash }, 0);
    errdefer allocator.free(name);
    const source = try sourceOf(allocator, which, name);
    errdefer allocator.free(source);
    const program_identity = sha256(source);
    // stwo-zig `aot_identity.validate_native_aot_identity` (as `reorder.kernel`).
    const payload = try std.fmt.allocPrint(allocator, "{{\"abi_schema\":\"{s}\",\"kernel_name\":\"{s}\",\"program_identity\":\"{x}\",\"semantic_hash\":\"{x:0>16}\"}}", .{ abi_schema_name, name, &program_identity, semantic_hash });
    defer allocator.free(payload);
    return .{
        .which = which,
        .semantic_contract = sc,
        .semantic_hash = semantic_hash,
        .kernel_name = name,
        .source = source,
        .program_identity = program_identity,
        .cache_key = std.mem.readInt(u64, sha256(payload)[0..8], .big),
    };
}

pub fn kernels(allocator: std.mem.Allocator) !Kernels {
    var out: Kernels = undefined;
    out.b2s = try kernelOf(allocator, .b2s);
    errdefer out.b2s.deinit(allocator);
    out.pre = try kernelOf(allocator, .pre);
    errdefer out.pre.deinit(allocator);
    out.sha_columns = try kernelOf(allocator, .sha_columns);
    errdefer out.sha_columns.deinit(allocator);
    out.sha_words = try kernelOf(allocator, .sha_words);
    return out;
}

const header =
    \\typedef unsigned long long u64;
    \\__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }
    \\
;

const m31 =
    \\#define STARKED_P 0x7fffffffu
    \\__device__ __forceinline__ unsigned m31_add(unsigned a, unsigned b) { unsigned s = a + b; return s >= STARKED_P ? s - STARKED_P : s; }
    \\__device__ __forceinline__ unsigned m31_sub(unsigned a, unsigned b) { return a >= b ? a - b : a + STARKED_P - b; }
    \\__device__ __forceinline__ unsigned m31_mul(unsigned a, unsigned b) {
    \\    const u64 p = (u64)a * (u64)b;
    \\    const unsigned s = (unsigned)(p & STARKED_P) + (unsigned)(p >> 31);
    \\    return s >= STARKED_P ? s - STARKED_P : s;
    \\}
    \\__device__ __forceinline__ unsigned m31_inv(unsigned x) {
    \\    // x^(P-2), P - 2 = 2^31 - 3 = 0b111...1101 (31 bits).
    \\    unsigned r = 1u, b = x, e = STARKED_P - 2u;
    \\    while (e) { if (e & 1u) r = m31_mul(r, b); b = m31_mul(b, b); e >>= 1u; }
    \\    return r;
    \\}
    \\
;

fn sourceOf(allocator: std.mem.Allocator, which: Which, name: []const u8) ![]u8 {
    return switch (which) {
        .sha_words => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_sha word trace.
            \\// Thread p lays compression p (comps[24p..]: input state, block; a zero dummy for p >= count)
            \\// on rows 72p .. 72p+71 (truncated at rows) as sha256/witness.zig Words.place: init rows
            \\// a = input[3-q], e = input[7-q]; round rows the new a, e and w_t; final rows
            \\// a = a[r-4] + a[r-68], e likewise; w = 0 off the rounds.
            \\{s}
            \\__device__ __forceinline__ unsigned starked_S0(unsigned x) {{ return starked_rotr(x, 2u) ^ starked_rotr(x, 13u) ^ starked_rotr(x, 22u); }}
            \\__device__ __forceinline__ unsigned starked_S1(unsigned x) {{ return starked_rotr(x, 6u) ^ starked_rotr(x, 11u) ^ starked_rotr(x, 25u); }}
            \\__device__ __forceinline__ unsigned starked_s0(unsigned x) {{ return starked_rotr(x, 7u) ^ starked_rotr(x, 18u) ^ (x >> 3u); }}
            \\__device__ __forceinline__ unsigned starked_s1(unsigned x) {{ return starked_rotr(x, 17u) ^ starked_rotr(x, 19u) ^ (x >> 10u); }}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *ktab, const unsigned *comps, unsigned count, unsigned *words, unsigned rows) {{
            \\    const unsigned p = blockIdx.x * blockDim.x + threadIdx.x;
            \\    const unsigned periods = (rows + 71u) / 72u;
            \\    if (p >= periods) return;
            \\    unsigned *wa = words;
            \\    unsigned *we = words + (u64)rows;
            \\    unsigned *ww = words + 2ull * (u64)rows;
            \\    unsigned h[8], blk[16];
            \\    for (unsigned i = 0; i < 8u; ++i) h[i] = p < count ? comps[(u64)p * 24u + i] : 0u;
            \\    for (unsigned i = 0; i < 16u; ++i) blk[i] = p < count ? comps[(u64)p * 24u + 8u + i] : 0u;
            \\    const u64 start = (u64)p * 72u;
            \\    for (unsigned q = 0; q < 4u; ++q) {{
            \\        const u64 r = start + q;
            \\        if (r < rows) {{ wa[r] = h[3u - q]; we[r] = h[7u - q]; ww[r] = 0u; }}
            \\    }}
            \\    unsigned a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
            \\    unsigned w[16];
            \\    for (unsigned t = 0; t < 64u; ++t) {{
            \\        unsigned wt;
            \\        if (t < 16u) wt = blk[t];
            \\        else wt = starked_s1(w[(t - 2u) & 15u]) + w[(t - 7u) & 15u] + starked_s0(w[(t - 15u) & 15u]) + w[(t - 16u) & 15u];
            \\        w[t & 15u] = wt;
            \\        const unsigned t1 = hh + starked_S1(e) + ((e & f) ^ (~e & g)) + ktab[t] + wt;
            \\        const unsigned t2 = starked_S0(a) + ((a & b) ^ (a & c) ^ (b & c));
            \\        hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
            \\        const u64 r = start + 4u + t;
            \\        if (r < rows) {{ wa[r] = a; we[r] = e; ww[r] = wt; }}
            \\    }}
            \\    // a, e of rounds 60..63 are (d, c, b, a) and (hh, g, f, e).
            \\    const unsigned la[4] = {{ d, c, b, a }};
            \\    const unsigned le[4] = {{ hh, g, f, e }};
            \\    for (unsigned j = 0; j < 4u; ++j) {{
            \\        const u64 r = start + 68u + j;
            \\        if (r < rows) {{ wa[r] = la[j] + h[3u - j]; we[r] = le[j] + h[7u - j]; ww[r] = 0u; }}
            \\    }}
            \\}}
            \\
        , .{ version, header, period_threads, name }),
        .sha_columns => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_sha's 144 columns.
            \\// Row r from the word trace (words: a, e, w, `rows` each; cyclic neighbours) as
            \\// sha256/witness.zig `columns` with `shaRole`, then block/sha.zig `Extra`: per period
            \\// meta[64 + 6p..] = mid, blk, flags (fst 1, dbl 2, node 4, npad 8, dup 16), lid, rid, ym for
            \\// (meta[0..64]: the round constants)
            \\// p < count, else NILS; the mutation check (limb differences with row r - 8, inverses)
            \\// and the ALLEQ chain on period rows 12..19. columns[c] is column c's address.
            \\{s}{s}
            \\__device__ __forceinline__ unsigned starked_S0(unsigned x) {{ return starked_rotr(x, 2u) ^ starked_rotr(x, 13u) ^ starked_rotr(x, 22u); }}
            \\__device__ __forceinline__ unsigned starked_S1(unsigned x) {{ return starked_rotr(x, 6u) ^ starked_rotr(x, 11u) ^ starked_rotr(x, 25u); }}
            \\__device__ __forceinline__ unsigned starked_s0(unsigned x) {{ return starked_rotr(x, 7u) ^ starked_rotr(x, 18u) ^ (x >> 3u); }}
            \\__device__ __forceinline__ unsigned starked_s1(unsigned x) {{ return starked_rotr(x, 17u) ^ starked_rotr(x, 19u) ^ (x >> 10u); }}
            \\__device__ __forceinline__ unsigned starked_zz(const unsigned *ww, unsigned r, unsigned rows) {{
            \\    const unsigned x = ww[r], y = ww[(r + rows - 8u) % rows];
            \\    return ((x & 0xffffu) == (y & 0xffffu) && (x >> 16u) == (y >> 16u)) ? 1u : 0u;
            \\}}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *words, const unsigned *meta, unsigned count, const u64 *columns, unsigned rows) {{
            \\    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
            \\    if (r >= rows) return;
            \\    const unsigned *wa = words;
            \\    const unsigned *we = words + (u64)rows;
            \\    const unsigned *ww = words + 2ull * (u64)rows;
            \\#define AT(x, back) x[(r + rows - (back)) % rows]
            \\#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
            \\    const unsigned av = wa[r], ev = we[r], wv = ww[r];
            \\    for (unsigned i = 0; i < 32u; ++i) {{
            \\        PUT(i, (av >> i) & 1u);
            \\        PUT(32u + i, (ev >> i) & 1u);
            \\        PUT(64u + i, (wv >> i) & 1u);
            \\    }}
            \\    const unsigned a1 = AT(wa, 1u), a2 = AT(wa, 2u), a3 = AT(wa, 3u);
            \\    const unsigned e1 = AT(we, 1u), e2 = AT(we, 2u), e3 = AT(we, 3u);
            \\    const unsigned s0v = starked_S0(a1), s1v = starked_S1(e1);
            \\    const unsigned chv = (e1 & e2) ^ (~e1 & e3);
            \\    const unsigned mjv = (a1 & a2) ^ (a1 & a3) ^ (a2 & a3);
            \\    const unsigned ss0 = starked_s0(AT(ww, 15u)), ss1 = starked_s1(AT(ww, 2u));
            \\    const unsigned pairs[6] = {{ s0v, s1v, chv, mjv, ss0, ss1 }};
            \\    for (unsigned k = 0; k < 6u; ++k) {{ PUT(96u + 2u * k, pairs[k] & 0xffffu); PUT(97u + 2u * k, pairs[k] >> 16u); }}
            \\    unsigned ca0 = 0u, ca1 = 0u, ce0 = 0u, ce1 = 0u, cw0 = 0u, cw1 = 0u;
            \\    const unsigned q = r % 72u;
            \\    if (q >= 4u && q < 68u) {{
            \\        const unsigned t = q - 4u;
            \\        const unsigned k = meta[t];
            \\        const unsigned h4 = AT(we, 4u), d4 = AT(wa, 4u);
            \\        const unsigned t1_lo = (h4 & 0xffffu) + (s1v & 0xffffu) + (chv & 0xffffu) + (k & 0xffffu) + (wv & 0xffffu);
            \\        const unsigned t1_hi = (h4 >> 16u) + (s1v >> 16u) + (chv >> 16u) + (k >> 16u) + (wv >> 16u);
            \\        ca0 = (t1_lo + (s0v & 0xffffu) + (mjv & 0xffffu)) >> 16u;
            \\        ca1 = (t1_hi + (s0v >> 16u) + (mjv >> 16u) + ca0) >> 16u;
            \\        ce0 = ((d4 & 0xffffu) + t1_lo) >> 16u;
            \\        ce1 = ((d4 >> 16u) + t1_hi + ce0) >> 16u;
            \\        if (t >= 16u) {{
            \\            const unsigned w7 = AT(ww, 7u), w16 = AT(ww, 16u);
            \\            cw0 = ((ss1 & 0xffffu) + (w7 & 0xffffu) + (ss0 & 0xffffu) + (w16 & 0xffffu)) >> 16u;
            \\            cw1 = ((ss1 >> 16u) + (w7 >> 16u) + (ss0 >> 16u) + (w16 >> 16u) + cw0) >> 16u;
            \\        }}
            \\    }} else if (q >= 68u) {{
            \\        const unsigned x4 = AT(wa, 4u), x68 = AT(wa, 68u), y4 = AT(we, 4u), y68 = AT(we, 68u);
            \\        ca0 = ((x4 & 0xffffu) + (x68 & 0xffffu)) >> 16u;
            \\        ca1 = ((x4 >> 16u) + (x68 >> 16u) + ca0) >> 16u;
            \\        ce0 = ((y4 & 0xffffu) + (y68 & 0xffffu)) >> 16u;
            \\        ce1 = ((y4 >> 16u) + (y68 >> 16u) + ce0) >> 16u;
            \\    }}
            \\    for (unsigned j = 0; j < 3u; ++j) {{
            \\        PUT(108u + j, (ca0 >> j) & 1u); PUT(111u + j, (ca1 >> j) & 1u);
            \\        PUT(114u + j, (ce0 >> j) & 1u); PUT(117u + j, (ce1 >> j) & 1u);
            \\    }}
            \\    for (unsigned j = 0; j < 2u; ++j) {{ PUT(120u + j, (cw0 >> j) & 1u); PUT(122u + j, (cw1 >> j) & 1u); }}
            \\    // block/sha.zig Extra: 124 MID, 125 BLKI, 126 FST, 127 DBL, 128 NILS, 129 USEW, 130 CHN,
            \\    // 131 YM, 132 NODE, 133 NPAD, 134 LID, 135 RID, 136 NDUP, 137 ZL, 138 IL, 139 ZH, 140 IH,
            \\    // 141 ZZ, 142 ALLEQ, 143 NNE.
            \\    const unsigned per = r / 72u;
            \\    unsigned mid = 0u, blk = 0u, flags = 0u, lid = 0u, rid = 0u, ym = 0u, nils = 0u;
            \\    if (per < count) {{
            \\        const unsigned *m = meta + 64u + (u64)per * 6u;
            \\        mid = m[0]; blk = m[1]; flags = m[2]; lid = m[3]; rid = m[4];
            \\        if ((flags & 2u) && q == 71u) ym = m[5];
            \\    }} else nils = 1u;
            \\    const unsigned fst = flags & 1u, dbl = (flags >> 1u) & 1u, node = (flags >> 2u) & 1u, npad = (flags >> 3u) & 1u, dup = (flags >> 4u) & 1u;
            \\    const unsigned kinds = m31_add(node, npad);
            \\    PUT(124u, mid); PUT(125u, blk); PUT(126u, fst); PUT(127u, dbl); PUT(128u, nils);
            \\    PUT(129u, m31_sub(m31_sub(m31_sub(1u, dbl), nils), kinds));
            \\    PUT(130u, m31_sub(m31_sub(m31_sub(m31_sub(1u, fst), dbl), nils), kinds));
            \\    PUT(131u, ym); PUT(132u, node); PUT(133u, npad); PUT(134u, lid); PUT(135u, rid); PUT(136u, dup);
            \\    PUT(143u, m31_mul(node, m31_sub(1u, dup)));
            \\    const unsigned wp = AT(ww, 8u);
            \\    const unsigned dl = m31_sub(wv & 0xffffu, wp & 0xffffu);
            \\    const unsigned dh = m31_sub(wv >> 16u, wp >> 16u);
            \\    const unsigned zl = dl == 0u ? 1u : 0u, zh = dh == 0u ? 1u : 0u;
            \\    PUT(137u, zl); PUT(138u, zl ? 0u : m31_inv(dl));
            \\    PUT(139u, zh); PUT(140u, zh ? 0u : m31_inv(dh));
            \\    const unsigned zz = zl & zh;
            \\    PUT(141u, zz);
            \\    unsigned alleq = 0u;
            \\    if (q >= 12u && q < 20u) {{
            \\        alleq = zz;
            \\        for (unsigned k = 1u; k <= q - 12u; ++k) alleq &= starked_zz(ww, r - k, rows);
            \\    }}
            \\    PUT(142u, alleq);
            \\#undef AT
            \\#undef PUT
            \\}}
            \\
        , .{ version, header, m31, threads, name }),
        .b2s => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_b2s's 312 columns.
            \\// Row r of period p = r / 88 (input periods[27 min(p, count)..]: h[8], m[16], t_lo, t_hi,
            \\// last; entry `count` is the unused-period dummy) as hash/blake2s_air.zig fillPeriod
            \\// (init rows 0-3, G rows 4-83 after recomputing the earlier G steps, final rows 84-87,
            \\// message limbs 256-287) and block/commit.zig B2sFill (300-311). sigma: 10 x 16 words.
            \\{s}
            \\__device__ __forceinline__ void starked_carries(unsigned *out, unsigned x, unsigned y, unsigned z) {{
            \\    const unsigned lo = (x & 0xffffu) + (y & 0xffffu) + (z & 0xffffu);
            \\    const unsigned hi = (x >> 16u) + (y >> 16u) + (z >> 16u);
            \\    out[0] = lo >> 16u;
            \\    out[1] = (hi + out[0]) >> 16u;
            \\}}
            \\__device__ __forceinline__ void starked_gidx(unsigned g, unsigned *ix) {{
            \\    if (g < 4u) {{ ix[0] = g; ix[1] = g + 4u; ix[2] = g + 8u; ix[3] = g + 12u; }}
            \\    else {{ const unsigned k = g - 4u; ix[0] = k; ix[1] = 4u + ((k + 1u) & 3u); ix[2] = 8u + ((k + 2u) & 3u); ix[3] = 12u + ((k + 3u) & 3u); }}
            \\}}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *sigma, const unsigned *periods, unsigned count, const u64 *columns, unsigned rows) {{
            \\    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
            \\    if (r >= rows) return;
            \\#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
            \\    const unsigned p = r / 88u, q = r % 88u;
            \\    const unsigned used = p < count ? 1u : 0u;
            \\    const unsigned *in = periods + (u64)(used ? p : count) * 27u;
            \\    unsigned h[8], m[16], v[16];
            \\    for (unsigned i = 0; i < 8u; ++i) h[i] = in[i];
            \\    for (unsigned i = 0; i < 16u; ++i) m[i] = in[8u + i];
            \\    const unsigned tlo = in[24], thi = in[25], fl = in[26];
            \\    const unsigned iv[8] = {{ 0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au, 0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u }};
            \\    for (unsigned i = 0; i < 8u; ++i) {{ v[i] = h[i]; v[8u + i] = iv[i]; }}
            \\    v[12] ^= tlo; v[13] ^= thi; if (fl) v[14] ^= 0xffffffffu;
            \\    unsigned slot[8] = {{ 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u }};
            \\    unsigned carry[8] = {{ 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u }};
            \\    if (q < 4u) {{
            \\        unsigned ix[4];
            \\        starked_gidx(4u + q, ix);
            \\        // OUT_W = 4, 7, 6, 5 for roles a, b, c, d.
            \\        slot[4] = v[ix[0]]; slot[7] = v[ix[1]]; slot[6] = v[ix[2]]; slot[5] = v[ix[3]];
            \\        if (q == 0u) {{ slot[0] = tlo; slot[1] = thi; slot[2] = fl; }}
            \\    }} else {{
            \\        const unsigned steps = q < 84u ? q - 4u : 80u;
            \\        for (unsigned j = 0; j <= steps && j < 80u; ++j) {{
            \\            unsigned ix[4];
            \\            starked_gidx(j % 8u, ix);
            \\            const unsigned rr = j / 8u, g = j % 8u;
            \\            const unsigned x = m[sigma[rr * 16u + 2u * g]], y = m[sigma[rr * 16u + 2u * g + 1u]];
            \\            const unsigned a = v[ix[0]], b = v[ix[1]], c = v[ix[2]], d = v[ix[3]];
            \\            const unsigned a1 = a + b + x;
            \\            const unsigned d1 = starked_rotr(d ^ a1, 16u);
            \\            const unsigned c1 = c + d1;
            \\            const unsigned b1 = starked_rotr(b ^ c1, 12u);
            \\            const unsigned a2 = a1 + b1 + y;
            \\            const unsigned d2 = starked_rotr(d1 ^ a2, 8u);
            \\            const unsigned c2 = c1 + d2;
            \\            const unsigned b2 = starked_rotr(b1 ^ c2, 7u);
            \\            if (j == steps) {{
            \\                slot[0] = a1; slot[1] = d1; slot[2] = c1; slot[3] = b1;
            \\                slot[4] = a2; slot[5] = d2; slot[6] = c2; slot[7] = b2;
            \\                starked_carries(carry + 0, a, b, x);
            \\                starked_carries(carry + 2, c, d1, 0u);
            \\                starked_carries(carry + 4, a1, b1, y);
            \\                starked_carries(carry + 6, c1, d2, 0u);
            \\            }}
            \\            v[ix[0]] = a2; v[ix[1]] = b2; v[ix[2]] = c2; v[ix[3]] = d2;
            \\        }}
            \\        if (q >= 84u) {{
            \\            const unsigned k = q - 84u;
            \\            unsigned ix[4];
            \\            starked_gidx(4u + k, ix);
            \\            const unsigned bk = ix[1];
            \\            slot[2] = h[k] ^ v[k];
            \\            slot[0] = h[k] ^ v[k] ^ v[k + 8u];
            \\            slot[3] = h[bk] ^ v[bk];
            \\            slot[1] = h[bk] ^ v[bk] ^ v[bk + 8u];
            \\        }}
            \\    }}
            \\    for (unsigned s = 0; s < 8u; ++s)
            \\        for (unsigned i = 0; i < 32u; ++i) PUT(32u * s + i, (slot[s] >> i) & 1u);
            \\    // Carry bits: 288 (2), 290 (2), 292 (1), 293 (1), 294 (2), 296 (2), 298 (1), 299 (1).
            \\    PUT(288u, carry[0] & 1u); PUT(289u, (carry[0] >> 1u) & 1u);
            \\    PUT(290u, carry[1] & 1u); PUT(291u, (carry[1] >> 1u) & 1u);
            \\    PUT(292u, carry[2] & 1u); PUT(293u, carry[3] & 1u);
            \\    PUT(294u, carry[4] & 1u); PUT(295u, (carry[4] >> 1u) & 1u);
            \\    PUT(296u, carry[5] & 1u); PUT(297u, (carry[5] >> 1u) & 1u);
            \\    PUT(298u, carry[6] & 1u); PUT(299u, carry[7] & 1u);
            \\    for (unsigned k = 0; k < 16u; ++k) {{ PUT(256u + 2u * k, m[k] & 0xffffu); PUT(257u + 2u * k, m[k] >> 16u); }}
            \\    // 300 BLKI, 301 FST, 302 NIL, 303 LASTF, 304 T, 305 WLO, 306 WHI, 307 CHN, 308 USEW,
            \\    // 309 YD, 310 MU0, 311 MU1.
            \\    const unsigned last = used & (fl ? 1u : 0u);
            \\    PUT(300u, used ? p : 0u);
            \\    PUT(301u, (used && p == 0u) ? 1u : 0u);
            \\    PUT(302u, used ? 0u : 1u);
            \\    PUT(303u, last);
            \\    PUT(304u, used ? tlo : 0u);
            \\    PUT(305u, q < 16u ? (m[q] & 0xffffu) : 0u);
            \\    PUT(306u, q < 16u ? (m[q] >> 16u) : 0u);
            \\    PUT(307u, (used && p > 0u) ? 1u : 0u);
            \\    PUT(308u, used);
            \\    PUT(309u, last);
            \\    PUT(310u, (used && q < 16u) ? 1u : 0u);
            \\    PUT(311u, (used && q == 0u) ? 1u : 0u);
            \\#undef PUT
            \\}}
            \\
        , .{ version, header, threads, name }),
        .pre => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): preprocessed columns.
            \\// Column first + blockIdx.y (desc[8 c..]: kind, k, values offset, period, address lo, hi),
            \\// row i < 2^log in natural order: ir.PreCol.at(i, 2^log). Kinds: 0 is_first, 1 not_last,
            \\// 2 periodic (values[off + i % period]), 3 row_lt (i < k), 4 row_ge_end (i + k >= n).
            \\{s}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *desc, const unsigned *values, unsigned first, unsigned log_size, unsigned columns) {{
            \\    const unsigned rows = 1u << log_size;
            \\    const unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
            \\    const unsigned c = blockIdx.y;
            \\    if (i >= rows || c >= columns) return;
            \\    const unsigned *d = desc + (u64)(first + c) * 8u;
            \\    const unsigned k = d[1];
            \\    unsigned v = 0u;
            \\    switch (d[0]) {{
            \\    case 0u: v = i == 0u ? 1u : 0u; break;
            \\    case 1u: v = i + 1u < rows ? 1u : 0u; break;
            \\    case 2u: v = values[d[2] + i % d[3]]; break;
            \\    case 3u: v = i < k ? 1u : 0u; break;
            \\    default: v = (u64)i + (u64)k >= (u64)rows ? 1u : 0u; break;
            \\    }}
            \\    ((unsigned *)(((u64)d[5] << 32u) | (u64)d[4]))[i] = v;
            \\}}
            \\
        , .{ version, header, threads, name }),
    };
}

// ------------------------------------------------------------------ host inputs and plan

/// The block's witness inputs (host, small): what the generators read.
pub const Inputs = struct {
    /// Part indices of `block_sha` and `block_b2s`.
    sha_component: usize,
    b2s_component: usize,
    /// `block_sha`: one compression and its final `Meta` per used period.
    compressions: []const shaw.Compression,
    meta: []const bsha.Meta,
    /// `block_b2s`: the undo stream's blocks and the chaining value after each.
    blocks: []const commit.Block,
    chain: []const [8]u32,

    /// From a built block (`block.system.buildFull`, `Built.sha_plan` and `Built.undo`).
    pub fn ofBlock(allocator: std.mem.Allocator, built: anytype) !Inputs {
        const C = sb.block.system.C;
        const bl = try commit.blocks(allocator, built.undo);
        return .{
            .sha_component = C.sha,
            .b2s_component = C.b2s,
            .compressions = built.sha_plan.compressions,
            .meta = built.sha_plan.meta,
            .blocks = bl,
            .chain = try commit.chain(allocator, bl),
        };
    }
};

/// Word offsets inside the `witness_inputs` slot (each region 8-byte aligned).
pub const Layout = struct {
    sigma: usize = 0,
    comps: usize = 0,
    meta: usize = 0,
    periods: usize = 0,
    pre_desc: usize = 0,
    pre_values: usize = 0,
    sha_columns: usize = 0,
    b2s_columns: usize = 0,
    words: usize = 0,
};

pub const Plan = struct {
    inputs: *const Inputs,
    layout: Layout,
    sha_log: u32,
    b2s_log: u32,
    /// First tree-1 column of each generated component.
    sha_first: usize,
    b2s_first: usize,
    /// Tree-1 columns whose values the device writes (the host skips them).
    generated_main: []bool,
    /// Every preprocessed definition in tree-0 order, and its periodic value offset.
    pre_defs: []ir.PreCol,
    pre_logs: []u32,
    pre_offsets: []u32,
    scratch_words: usize,

    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part, inputs: *const Inputs) !Plan {
        if (inputs.sha_component >= parts.len or inputs.b2s_component >= parts.len) return error.InvalidWitnessPlan;
        const sha_part = parts[inputs.sha_component];
        const b2s_part = parts[inputs.b2s_component];
        if (sha_part.air.n_main != SHA_COLUMNS or b2s_part.air.n_main != B2S_COLUMNS) return error.InvalidWitnessPlan;
        const sha_rows = @as(usize, 1) << @intCast(sha_part.log_size);
        const b2s_rows = @as(usize, 1) << @intCast(b2s_part.log_size);
        if (inputs.compressions.len != inputs.meta.len or inputs.compressions.len > shaw.capacity(sha_part.log_size)) return error.InvalidWitnessPlan;
        if (inputs.blocks.len == 0 or inputs.blocks.len != inputs.chain.len or inputs.blocks.len * b2.PERIOD > b2s_rows) return error.InvalidWitnessPlan;
        if (sha_rows >= 1 << 30 or b2s_rows >= 1 << 30) return error.InvalidWitnessPlan;
        var n_main: usize = 0;
        var sha_first: usize = 0;
        var b2s_first: usize = 0;
        var n_pre: usize = 0;
        for (parts, 0..) |p, i| {
            if (i == inputs.sha_component) sha_first = n_main;
            if (i == inputs.b2s_component) b2s_first = n_main;
            n_main += p.air.n_main;
            n_pre += p.air.preprocessed.len;
        }
        const generated = try allocator.alloc(bool, n_main);
        errdefer allocator.free(generated);
        @memset(generated, false);
        @memset(generated[sha_first..][0..SHA_COLUMNS], true);
        @memset(generated[b2s_first..][0..B2S_COLUMNS], true);
        const defs = try allocator.alloc(ir.PreCol, n_pre);
        errdefer allocator.free(defs);
        const logs = try allocator.alloc(u32, n_pre);
        errdefer allocator.free(logs);
        const offsets = try allocator.alloc(u32, n_pre);
        errdefer allocator.free(offsets);
        var k: usize = 0;
        var values: usize = 0;
        for (parts) |p| for (p.air.preprocessed) |d| {
            defs[k] = d;
            logs[k] = p.log_size;
            offsets[k] = @intCast(values);
            if (d == .periodic) {
                if (d.periodic.len == 0) return error.InvalidWitnessPlan;
                values += d.periodic.len;
            }
            k += 1;
        };
        var at: usize = 0;
        var l = Layout{};
        const region = struct {
            fn f(cursor: *usize, words: usize) usize {
                const start = std.mem.alignForward(usize, cursor.*, 2);
                cursor.* = start + words;
                return start;
            }
        }.f;
        l.sigma = region(&at, 160);
        l.comps = region(&at, inputs.compressions.len * SHA_COMP_WORDS);
        l.meta = region(&at, 64 + inputs.meta.len * SHA_META_WORDS);
        l.periods = region(&at, (inputs.blocks.len + 1) * B2S_PERIOD_WORDS);
        l.pre_desc = region(&at, n_pre * PRE_DESC_WORDS);
        l.pre_values = region(&at, @max(values, 1));
        l.sha_columns = region(&at, 2 * SHA_COLUMNS);
        l.b2s_columns = region(&at, 2 * B2S_COLUMNS);
        l.words = at;
        return .{
            .inputs = inputs,
            .layout = l,
            .sha_log = sha_part.log_size,
            .b2s_log = b2s_part.log_size,
            .sha_first = sha_first,
            .b2s_first = b2s_first,
            .generated_main = generated,
            .pre_defs = defs,
            .pre_logs = logs,
            .pre_offsets = offsets,
            .scratch_words = 3 * sha_rows,
        };
    }

    pub fn deinit(self: *Plan, allocator: std.mem.Allocator) void {
        allocator.free(self.generated_main);
        allocator.free(self.pre_defs);
        allocator.free(self.pre_logs);
        allocator.free(self.pre_offsets);
        self.* = undefined;
    }

    pub fn inputBytes(self: *const Plan) usize {
        return self.layout.words * 4;
    }

    /// The `witness_inputs` image: every input word, with `staging[t][j]` (tree `t`'s column `j`
    /// destination) as the column addresses.
    pub fn image(self: *const Plan, allocator: std.mem.Allocator, staging: [2][]const common.Words) ![]u32 {
        const l = self.layout;
        const in = self.inputs;
        if (staging[0].len != self.pre_defs.len or staging[1].len != self.generated_main.len) return error.InvalidWitnessPlan;
        const out = try allocator.alloc(u32, l.words);
        errdefer allocator.free(out);
        @memset(out, 0);
        @memcpy(out[l.meta..][0..64], &spec.K);
        const sigma = sigmaTable();
        @memcpy(out[l.sigma..][0..160], &sigma);
        for (in.compressions, 0..) |c, i| {
            @memcpy(out[l.comps + SHA_COMP_WORDS * i ..][0..8], &c.input);
            @memcpy(out[l.comps + SHA_COMP_WORDS * i + 8 ..][0..16], &c.block);
        }
        for (in.meta, 0..) |m, i| {
            const o = out[l.meta + 64 + SHA_META_WORDS * i ..][0..SHA_META_WORDS];
            for ([_]u32{ m.mid, m.blk, m.lid, m.rid, m.ym }) |x| if (x >= P) return error.InvalidWitnessPlan;
            o.* = .{ m.mid, m.blk, @as(u32, @intFromBool(m.fst)) | @as(u32, @intFromBool(m.dbl)) << 1 | @as(u32, @intFromBool(m.node)) << 2 | @as(u32, @intFromBool(m.npad)) << 3 | @as(u32, @intFromBool(m.dup)) << 4, m.lid, m.rid, m.ym };
        }
        for (0..in.blocks.len + 1) |p| {
            const o = out[l.periods + B2S_PERIOD_WORDS * p ..][0..B2S_PERIOD_WORDS];
            if (p < in.blocks.len) {
                const bl = in.blocks[p];
                if (bl.t >= P) return error.InvalidWitnessPlan;
                @memcpy(o[0..8], if (p == 0) &commit.H0 else &in.chain[p - 1]);
                @memcpy(o[8..24], &bl.m);
                o[24] = @truncate(bl.t);
                o[25] = @truncate(bl.t >> 32);
                o[26] = @intFromBool(bl.last);
            } else {
                // The unused-period dummy (`B2sFill`): H0, zero message, t = 0, not last.
                @memcpy(o[0..8], &commit.H0);
            }
        }
        for (self.pre_defs, self.pre_offsets, staging[0], 0..) |d, off, dst, j| {
            const o = out[l.pre_desc + PRE_DESC_WORDS * j ..][0..PRE_DESC_WORDS];
            o.* = switch (d) {
                .is_first => .{ 0, 0, 0, 1, 0, 0, 0, 0 },
                .not_last => .{ 1, 0, 0, 1, 0, 0, 0, 0 },
                .periodic => |v| .{ 2, 0, off, @intCast(v.len), 0, 0, 0, 0 },
                .row_lt => |k| .{ 3, k, 0, 1, 0, 0, 0, 0 },
                .row_ge_end => |k| .{ 4, k, 0, 1, 0, 0, 0, 0 },
            };
            if (d == .periodic) for (d.periodic, 0..) |x, i| {
                if (x >= P) return error.InvalidWitnessPlan;
                out[l.pre_values + off + i] = x;
            };
            o[4] = @truncate(dst.address);
            o[5] = @truncate(dst.address >> 32);
        }
        const sha_rows = @as(usize, 1) << @intCast(self.sha_log);
        const b2s_rows = @as(usize, 1) << @intCast(self.b2s_log);
        for (staging[1][self.sha_first..][0..SHA_COLUMNS], 0..) |dst, c| {
            if (dst.len != sha_rows) return error.InvalidWitnessPlan;
            out[l.sha_columns + 2 * c] = @truncate(dst.address);
            out[l.sha_columns + 2 * c + 1] = @truncate(dst.address >> 32);
        }
        for (staging[1][self.b2s_first..][0..B2S_COLUMNS], 0..) |dst, c| {
            if (dst.len != b2s_rows) return error.InvalidWitnessPlan;
            out[l.b2s_columns + 2 * c] = @truncate(dst.address);
            out[l.b2s_columns + 2 * c + 1] = @truncate(dst.address >> 32);
        }
        return out;
    }
};

fn sigmaTable() [160]u32 {
    // hash/blake2s_air.zig's SIGMA (RFC 7693).
    const S = [10][16]u8{
        .{ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 },
        .{ 14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3 },
        .{ 11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4 },
        .{ 7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8 },
        .{ 9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13 },
        .{ 2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9 },
        .{ 12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11 },
        .{ 13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10 },
        .{ 6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5 },
        .{ 10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0 },
    };
    var out: [160]u32 = undefined;
    for (S, 0..) |row, r| for (row, 0..) |x, i| {
        out[16 * r + i] = x;
    };
    return out;
}

// ------------------------------------------------------------------ device

pub const Buffers = struct {
    inputs: common.Words,
    scratch: common.Words,
};

pub const Bound = struct {
    plan: *const Plan,
    kernels: *const Kernels,
    buffers: Buffers,
    /// Tree 0's cohorts (runs of equal log size, `resident_commit` order).
    pre_cohorts: []const Cohort,

    pub const Cohort = struct { first: u32, count: u32, log_size: u32 };

    /// Ingress: the inputs image (`Plan.image`) into `witness_inputs`.
    pub fn upload(self: *const Bound, allocator: std.mem.Allocator, session: anytype, staging: [2][]const common.Words) !void {
        if (self.buffers.inputs.len != self.plan.layout.words or self.buffers.scratch.len != self.plan.scratch_words) return error.InvalidWitnessBuffers;
        const words = try self.plan.image(allocator, staging);
        defer allocator.free(words);
        try session.context.uploadSlice(u32, self.buffers.inputs, words);
    }

    /// `.trace_generation`, before the reorder: SHA words, SHA columns, Blake2s columns, the
    /// preprocessed columns (one launch per tree-0 cohort).
    pub fn generate(self: *const Bound, session: anytype) !void {
        const plan = self.plan;
        const l = plan.layout;
        const b = self.buffers;
        const ptr = struct {
            fn f(s: anytype, w: common.Words, offset: usize, n: usize) ![*]u32 {
                return s.context.deviceSlicePointer(u32, try w.sub(offset, @max(n, 1)), @max(n, 1));
            }
        }.f;
        const in = plan.inputs;
        const sha_rows: u32 = @as(u32, 1) << @intCast(plan.sha_log);
        const b2s_rows: u32 = @as(u32, 1) << @intCast(plan.b2s_log);
        const words = try session.context.deviceSlicePointer(u32, b.scratch, b.scratch.len);
        {
            var args = Args{
                .p0 = try ptr(session, b.inputs, l.meta, 64),
                .p1 = try ptr(session, b.inputs, l.comps, in.compressions.len * SHA_COMP_WORDS),
                .n = @intCast(in.compressions.len),
                .p2 = words,
                .rows = sha_rows,
            };
            var pointers = args.pointers();
            const periods = (sha_rows + shaw.PERIOD - 1) / shaw.PERIOD;
            try self.kernels.sha_words.launch(session, .{ @intCast((periods + period_threads - 1) / period_threads), 1, 1 }, period_threads, &pointers);
        }
        {
            var args = Args{
                .p0 = words,
                .p1 = try ptr(session, b.inputs, l.meta, 64 + in.meta.len * SHA_META_WORDS),
                .n = @intCast(in.meta.len),
                .p2 = try ptr(session, b.inputs, l.sha_columns, 2 * SHA_COLUMNS),
                .rows = sha_rows,
            };
            var pointers = args.pointers();
            try self.kernels.sha_columns.launch(session, .{ (sha_rows + threads - 1) / threads, 1, 1 }, threads, &pointers);
        }
        {
            var args = Args{
                .p0 = try ptr(session, b.inputs, l.sigma, 160),
                .p1 = try ptr(session, b.inputs, l.periods, (in.blocks.len + 1) * B2S_PERIOD_WORDS),
                .n = @intCast(in.blocks.len),
                .p2 = try ptr(session, b.inputs, l.b2s_columns, 2 * B2S_COLUMNS),
                .rows = b2s_rows,
            };
            var pointers = args.pointers();
            try self.kernels.b2s.launch(session, .{ (b2s_rows + threads - 1) / threads, 1, 1 }, threads, &pointers);
        }
        const desc = try ptr(session, b.inputs, l.pre_desc, plan.pre_defs.len * PRE_DESC_WORDS);
        const values = try ptr(session, b.inputs, l.pre_values, 1);
        for (self.pre_cohorts) |c| {
            var first = c.first;
            const end = c.first + c.count;
            while (first < end) {
                const n: u32 = @min(end - first, max_columns_per_launch);
                const rows: u32 = @as(u32, 1) << @intCast(c.log_size);
                var args = PreArgs{ .desc = desc, .values = values, .first = first, .log_size = c.log_size, .columns = n };
                var pointers = args.pointers();
                try self.kernels.pre.launch(session, .{ (rows + threads - 1) / threads, n, 1 }, threads, &pointers);
                first += n;
            }
        }
    }
};

/// Tree 0's runs of equal-log columns (one `pre` launch each).
pub fn preCohorts(allocator: std.mem.Allocator, plan: *const Plan) ![]Bound.Cohort {
    var out = std.ArrayList(Bound.Cohort).empty;
    errdefer out.deinit(allocator);
    for (plan.pre_logs, 0..) |log, j| {
        if (out.items.len != 0 and out.items[out.items.len - 1].log_size == log) {
            out.items[out.items.len - 1].count += 1;
        } else try out.append(allocator, .{ .first = @intCast(j), .count = 1, .log_size = log });
    }
    return out.toOwnedSlice(allocator);
}

/// The kernel arguments (by value, as `cuLaunchKernel` takes them): pointer, pointer, count,
/// pointer, rows.
const Args = struct {
    p0: [*]u32,
    p1: [*]u32,
    n: u32,
    p2: [*]u32,
    rows: u32,

    fn pointers(self: *Args) [argument_count]?*anyopaque {
        return .{ @ptrCast(&self.p0), @ptrCast(&self.p1), @ptrCast(&self.n), @ptrCast(&self.p2), @ptrCast(&self.rows) };
    }
};

const PreArgs = struct {
    desc: [*]u32,
    values: [*]u32,
    first: u32,
    log_size: u32,
    columns: u32,

    fn pointers(self: *PreArgs) [argument_count]?*anyopaque {
        return .{ @ptrCast(&self.desc), @ptrCast(&self.values), @ptrCast(&self.first), @ptrCast(&self.log_size), @ptrCast(&self.columns) };
    }
};
