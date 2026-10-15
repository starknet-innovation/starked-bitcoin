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
//! | `bytes` | one thread per row | `block_bytes`' 12 columns | `block/bytes.zig generate` (multiplicities from the host) |
//! | `msg` | one thread per row (binary search for its message) | `block_msg`'s 38 columns | `block/msg.zig generate`, `setUses`, `merkle.addHeaderUses` |
//! | `walk` | one thread per row (its record from the host's sequential pass) | `block_walk`'s 51 columns | `block/walk.zig columns` |
//!
//! Ingress uploads only their small inputs into one slot (`witness_inputs`, `Layout`): the SHA-256
//! round constants and Blake2s σ table, per `block_sha` period its compression (input state, block)
//! and final `Meta`, per `block_b2s` period its compression input (chaining value, block, counter,
//! last flag) plus one dummy, the preprocessed column descriptors and periodic values, the block's
//! bytes, the reads per block position (`bytes.multiplicities`), one descriptor per hash message (`msg.descriptors`), the walker's row records
//! (`walk.Rec`, 16 bytes per walked row), and the device address of every generated column
//! (pointer tables). The SHA word trace (3 words per row)
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
const bmsg = sb.block.msg;
const bwalk = sb.block.walk;
const bbytes = sb.block.bytes;
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
pub const MSG_COLUMNS: usize = bmsg.N_MAIN;
pub const BYTES_COLUMNS: usize = bbytes.N_MAIN;
pub const WALK_COLUMNS: usize = bwalk.N_MAIN;
const WALK_REC_WORDS = 4;
const SHA_COMP_WORDS = 24;
const SHA_META_WORDS = 6;
const B2S_PERIOD_WORDS = 27;
const PRE_DESC_WORDS = 8;

pub const Which = enum { b2s, bytes, msg, pre, sha_columns, sha_words, walk };

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

/// The seven kernels, in manifest (label) order.
pub const Kernels = struct {
    b2s: Kernel,
    bytes: Kernel,
    msg: Kernel,
    pre: Kernel,
    sha_columns: Kernel,
    sha_words: Kernel,
    walk: Kernel,

    pub fn deinit(self: *Kernels, allocator: std.mem.Allocator) void {
        inline for (.{ &self.b2s, &self.bytes, &self.msg, &self.pre, &self.sha_columns, &self.sha_words, &self.walk }) |k| k.deinit(allocator);
    }

    pub fn all(self: *const Kernels) [7]*const Kernel {
        return .{ &self.b2s, &self.bytes, &self.msg, &self.pre, &self.sha_columns, &self.sha_words, &self.walk };
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
        .bytes => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-bytes/v{d};args=raw,mults,len,columns,rows;block_bytes 12 natural columns: bytes.generate (pos, byte, bits, active, mult) from raw (bytes, little-endian words) and mults[r] for r < len;columns=u64 pointers;grid=rows/{d};threads={d}", .{ version, threads, threads }),
        .msg => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-msg/v{d};args=raw,msgs,count,columns,rows;block_msg 38 natural columns: msg.generate + setUses + merkle.addHeaderUses from raw (bytes, little-endian words) and msgs[{d}m]: row,id,flags(hdr,wtx,seg,split),i,a,w,l,dl,prev_dl;columns=u64 pointers;grid=rows/{d};threads={d}", .{ version, bmsg.DESC_WORDS, threads, threads }),
        .walk => std.fmt.allocPrint(allocator, "starked-bitcoin/witness-walk/v{d};args=raw,recs,count,columns,rows;block_walk 51 natural columns: walk.columns from raw and recs[0]=sigops, recs[4+4r..]: w0(pos,kind,li,lk,first),rem,val,sums;columns=u64 pointers;grid=rows/{d};threads={d}", .{ version, threads, threads }),
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
    out.bytes = try kernelOf(allocator, .bytes);
    errdefer out.bytes.deinit(allocator);
    out.msg = try kernelOf(allocator, .msg);
    errdefer out.msg.deinit(allocator);
    out.pre = try kernelOf(allocator, .pre);
    errdefer out.pre.deinit(allocator);
    out.sha_columns = try kernelOf(allocator, .sha_columns);
    errdefer out.sha_columns.deinit(allocator);
    out.sha_words = try kernelOf(allocator, .sha_words);
    errdefer out.sha_words.deinit(allocator);
    out.walk = try kernelOf(allocator, .walk);
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
        .bytes => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_bytes columns.
            \\// Row r: POS = r; for r < len its byte raw[r], the byte's bits, ACTIVE and MULT = mults[r]
            \\// (the reads of position r); zero past the block (block/bytes.zig generate).
            \\{s}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *raw, const unsigned *mults, unsigned len, const u64 *columns, unsigned rows) {{
            \\    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
            \\    if (r >= rows) return;
            \\#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
            \\    const unsigned active = r < len ? 1u : 0u;
            \\    const unsigned b = active ? (raw[r >> 2u] >> (8u * (r & 3u))) & 0xffu : 0u;
            \\    PUT(0u, r);
            \\    PUT(1u, b);
            \\    for (unsigned i = 0; i < 8u; ++i) PUT(2u + i, (b >> i) & 1u);
            \\    PUT(10u, active);
            \\    PUT(11u, active ? mults[r] : 0u);
            \\#undef PUT
            \\}}
            \\
        , .{ version, header, threads, name }),
        .msg => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_msg columns.
            \\// Row r belongs to the last message m with msgs[10m] <= r (row, id, flags hdr|wtx|seg|split,
            \\// i, a, w, l, dl, prev_dl); past the last message's padded length the row is padding (NIL,
            \\// the last message's tuple, IDX counting on). As block/msg.zig generate, setUses and
            \\// merkle.addHeaderUses: data bytes at a + j (split txid: a + j, a + 2 + j, l + j - (dl - 4)),
            \\// 0x80, zeros, the 64-bit bit length; derived EZ, Z, INV, CONT, SW, ENDD; the running DLC.
            \\{s}{s}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *raw, const unsigned *msgs, unsigned count, const u64 *columns, unsigned rows) {{
            \\    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
            \\    if (r >= rows) return;
            \\#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
            \\    unsigned lo = 0u, hi = count - 1u;
            \\    while (lo < hi) {{ const unsigned mid = (lo + hi + 1u) / 2u; if (msgs[(u64)mid * {d}u] <= r) lo = mid; else hi = mid - 1u; }}
            \\    const unsigned *d = msgs + (u64)lo * {d}u;
            \\    const unsigned id = d[1], fl = d[2], ti = d[3], ta = d[4], tw = d[5], tl = d[6], dl = d[7], prev = d[8];
            \\    const unsigned padded = (dl + 9u + 63u) / 64u * 64u;
            \\    const unsigned j = r - d[0];
            \\    const unsigned mt = (fl >> 3u) & 1u;
            \\    unsigned v[38];
            \\    for (unsigned c = 0; c < 38u; ++c) v[c] = 0u;
            \\    v[10] = fl & 1u; v[11] = (fl >> 1u) & 1u; v[12] = (fl >> 2u) & 1u;
            \\    v[13] = ti; v[14] = ta; v[15] = tw; v[16] = tl; v[9] = mt; v[17] = id; v[18] = j;
            \\    const unsigned nil = j < padded ? 0u : 1u;
            \\    if (!nil) {{
            \\        if (j == 0u) v[5] = 1u;
            \\        unsigned byte = 0u;
            \\        if (j < dl) {{
            \\            v[0] = 1u;
            \\            const unsigned piece = !mt ? 0u : (j < 4u ? 0u : (j < dl - 4u ? 1u : 2u));
            \\            const unsigned pos = piece == 0u ? ta + j : (piece == 1u ? ta + 2u + j : tl + j - (dl - 4u));
            \\            v[19] = pos;
            \\            byte = (raw[pos >> 2u] >> (8u * (pos & 3u))) & 0xffu;
            \\            v[6u + piece] = 1u;
            \\        }} else if (j == dl) {{
            \\            v[1] = 1u; byte = 0x80u;
            \\        }} else if (j < padded - 8u) {{
            \\            v[2] = 1u;
            \\        }} else {{
            \\            v[3] = 1u;
            \\            const u64 bits = 8ull * (u64)dl;
            \\            byte = (unsigned)((bits >> (8u * (padded - 1u - j))) & 0xffull);
            \\        }}
            \\        v[20] = byte;
            \\        for (unsigned b = 0; b < 8u; ++b) v[21u + b] = (byte >> b) & 1u;
            \\        v[35] = j >= dl ? dl : prev;
            \\    }} else {{
            \\        v[4] = 1u;
            \\        v[35] = dl;
            \\    }}
            \\    // Derived (msg.zig Derived.rows).
            \\    const unsigned pos = v[19];
            \\    const unsigned tl3 = m31_add(tl, 3u);
            \\    const unsigned ez = m31_add(m31_mul(mt, m31_add(m31_add(m31_mul(v[6], m31_sub(j, 3u)), m31_mul(v[7], m31_add(m31_sub(pos, tw), 1u))), m31_mul(v[8], m31_sub(pos, tl3)))),
            \\                       m31_mul(m31_sub(1u, mt), m31_sub(pos, tl3)));
            \\    const unsigned z = ez == 0u ? 1u : 0u;
            \\    v[29] = ez; v[30] = z; v[31] = ez == 0u ? 0u : m31_inv(ez);
            \\    v[32] = m31_mul(v[0], m31_sub(1u, z));
            \\    v[33] = m31_mul(m31_mul(z, mt), m31_add(v[6], v[7]));
            \\    v[34] = m31_sub(m31_mul(v[0], z), v[33]);
            \\    // Uses (setUses, merkle.addHeaderUses: the header's eight words read twice).
            \\    if (!nil) {{
            \\        v[36] = ((r & 3u) == 3u ? 1u : 0u) + ((r >= 39u && r <= 67u && ((r - 39u) & 3u) == 0u) ? 1u : 0u);
            \\        v[37] = ((r & 63u) == 63u && v[3]) ? 1u : 0u;
            \\    }}
            \\    for (unsigned c = 0; c < 38u; ++c) PUT(c, v[c]);
            \\#undef PUT
            \\}}
            \\
        , .{ version, header, m31, threads, name, bmsg.DESC_WORDS, bmsg.DESC_WORDS }),
        .walk => std.fmt.allocPrint(allocator,
            \\// starked-bitcoin device witness v{d} (src/gpu/cuda/witness.zig): block_walk columns.
            \\// Row r < count expands record recs[4 + 4r] (w0: pos 0-23, kind 24-25 (op, ln, dt, inf),
            \\// li 26-27, lk code 28-29 (0, 1, 2, 4), first 30; rem; val = dr or lacc; sums) with its byte
            \\// raw[pos] as block/walk.zig columns: the row's state, the automaton step, the zero tests and
            \\// their inverses. Rows past count are padding (SUMS = recs[0], ZA = 1, INVD = INVR = 1/(-1)).
            \\{s}{s}
            \\extern "C" __global__ void __launch_bounds__({d}) {s}(
            \\    const unsigned *raw, const unsigned *recs, unsigned count, const u64 *columns, unsigned rows) {{
            \\    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
            \\    if (r >= rows) return;
            \\#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
            \\    unsigned v[51];
            \\    for (unsigned c = 0; c < 51u; ++c) v[c] = 0u;
            \\    const unsigned inv_m1 = m31_inv(STARKED_P - 1u);
            \\    if (r >= count) {{
            \\        v[49] = recs[0]; v[30] = 1u; v[33] = inv_m1; v[35] = inv_m1;
            \\    }} else {{
            \\        const unsigned *rc = recs + 4ull + 4ull * (u64)r;
            \\        const unsigned w0 = rc[0], rem = rc[1], val = rc[2], sums = rc[3];
            \\        const unsigned pos = w0 & 0xffffffu, kind = (w0 >> 24u) & 3u, li = (w0 >> 26u) & 3u;
            \\        const unsigned lkc = (w0 >> 28u) & 3u, first = (w0 >> 30u) & 1u;
            \\        const unsigned lk = lkc == 3u ? 4u : lkc;
            \\        const unsigned b = (raw[pos >> 2u] >> (8u * (pos & 3u))) & 0xffu;
            \\        v[0] = 1u; v[1] = first; v[2] = pos; v[3] = rem; v[4] = b;
            \\        v[34] = rem == 1u ? 1u : 0u;
            \\        v[35] = rem == 1u ? 0u : m31_inv(m31_sub(rem, 1u));
            \\        // The next state (walk.zig step): kind, dr, lk, li, lacc.
            \\        unsigned nk = 0u, ndr = 0u, nlk = 0u, nli = 0u, nlacc = 0u;
            \\        if (kind == 0u) {{
            \\            v[5] = 1u;
            \\            v[9] = b < 0x4cu ? b : 0u;
            \\            v[10] = b == 0x4cu; v[11] = b == 0x4du; v[12] = b == 0x4eu;
            \\            v[13] = (b == 0xacu || b == 0xadu) ? 1u : ((b == 0xaeu || b == 0xafu) ? 20u : 0u);
            \\            v[14] = (b >= 1u && b < 0x4cu) ? 1u : 0u;
            \\            if (b >= 1u && b < 0x4cu) {{ nk = 2u; ndr = b; }}
            \\            else if (b >= 0x4cu && b <= 0x4eu) {{ nk = 1u; nlk = b == 0x4cu ? 1u : (b == 0x4du ? 2u : 4u); }}
            \\        }} else if (kind == 1u) {{
            \\            v[6] = 1u;
            \\            v[15u + li] = 1u;
            \\            if (lk == 1u) v[19] = 1u; else if (lk == 2u) v[20] = 1u; else v[21] = 1u;
            \\            v[22] = val;
            \\            const u64 acc2 = (u64)val + ((u64)b << (8u * li));
            \\            if (li + 1u == lk) {{
            \\                v[25] = 1u; v[26] = 1u;
            \\                if (lk == 4u && b >= 2u) {{ v[28] = 1u; nk = 3u; }}
            \\                else {{
            \\                    v[27] = 1u;
            \\                    if (lk == 4u) v[29] = 1u;
            \\                    if (acc2 == 0ull) nk = 0u; else {{ nk = 2u; ndr = (unsigned)acc2; }}
            \\                }}
            \\            }} else {{ nk = 1u; nlk = lk; nli = li + 1u; nlacc = (unsigned)acc2; }}
            \\            const unsigned a2 = (unsigned)(acc2 % (u64)STARKED_P);
            \\            v[24] = a2; v[30] = a2 == 0u ? 1u : 0u; v[31] = a2 == 0u ? 0u : m31_inv(a2);
            \\        }} else if (kind == 2u) {{
            \\            v[7] = 1u; v[23] = val;
            \\            if (val == 1u) nk = 0u; else {{ nk = 2u; ndr = val - 1u; }}
            \\        }} else {{
            \\            v[8] = 1u; nk = 3u;
            \\        }}
            \\        if (kind != 1u) {{ v[30] = 1u; v[31] = 0u; }}
            \\        v[32] = v[23] == 1u ? 1u : 0u;
            \\        v[33] = v[23] == 1u ? 0u : m31_inv(m31_sub(v[23], 1u));
            \\        v[36] = nk == 0u; v[37] = nk == 1u; v[38] = nk == 2u; v[39] = nk == 3u;
            \\        if (nk == 2u) v[40] = ndr;
            \\        if (nk == 1u) {{
            \\            v[41] = nlacc;
            \\            v[42u + nli] = 1u;
            \\            if (nlk == 1u) v[46] = 1u; else if (nlk == 2u) v[47] = 1u; else v[48] = 1u;
            \\        }}
            \\        v[50] = first ? 0u : 1u;
            \\        v[49] = sums;
            \\    }}
            \\    for (unsigned c = 0; c < 51u; ++c) PUT(c, v[c]);
            \\#undef PUT
            \\}}
            \\
        , .{ version, header, m31, threads, name }),
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
    /// Part indices of `block_sha`, `block_b2s`, `block_msg` and `block_walk`.
    sha_component: usize,
    b2s_component: usize,
    msg_component: usize,
    walk_component: usize,
    bytes_component: usize,
    /// `block_sha`: one compression and its final `Meta` per used period.
    compressions: []const shaw.Compression,
    meta: []const bsha.Meta,
    /// `block_b2s`: the undo stream's blocks and the chaining value after each.
    blocks: []const commit.Block,
    chain: []const [8]u32,
    /// `block_msg` and `block_walk`: the block, the message descriptors (`msg.descriptors`), the
    /// walker's row records (`walk.plan`) and its sigop total.
    raw: []const u8,
    msgs: []const u32,
    walk_recs: []const bwalk.Rec,
    sigops: u32,
    /// `block_bytes`: the reads per block position.
    byte_mults: []const u32,
    /// Size the inputs slot by the components' log sizes (the largest inputs they admit) instead of
    /// this block's: every block of a size class then has the same memory plan, so a batch run
    /// reuses one prepared device arena per class (`cuda-epoch`, `prover.Input.runtime`).
    fixed_capacity: bool = false,

    /// From a built block (`block.system.buildFull`: `sha_plan`, `undo`, `raw`, `msgs`, `walk_recs`).
    pub fn ofBlock(allocator: std.mem.Allocator, built: anytype) !Inputs {
        const C = sb.block.system.C;
        const bl = try commit.blocks(allocator, built.undo);
        return .{
            .sha_component = C.sha,
            .b2s_component = C.b2s,
            .msg_component = C.msg,
            .walk_component = C.walk,
            .bytes_component = C.bytes,
            .compressions = built.sha_plan.compressions,
            .meta = built.sha_plan.meta,
            .blocks = bl,
            .chain = try commit.chain(allocator, bl),
            .raw = built.raw,
            .msgs = try bmsg.descriptors(allocator, built.msgs),
            .walk_recs = built.walk_recs,
            .sigops = built.sigops,
            // A full build (`skip_device_columns` off) keeps only the reads.
            .byte_mults = if (built.byte_mults.len == built.raw.len) built.byte_mults else try bbytes.multiplicities(allocator, built.raw.len, built.reads),
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
    raw: usize = 0,
    msgs: usize = 0,
    walk: usize = 0,
    mults: usize = 0,
    msg_columns: usize = 0,
    walk_columns: usize = 0,
    bytes_columns: usize = 0,
    words: usize = 0,
};

pub const Plan = struct {
    inputs: *const Inputs,
    layout: Layout,
    sha_log: u32,
    b2s_log: u32,
    msg_log: u32,
    walk_log: u32,
    bytes_log: u32,
    /// First tree-1 column of each generated component.
    sha_first: usize,
    b2s_first: usize,
    msg_first: usize,
    walk_first: usize,
    bytes_first: usize,
    /// Tree-1 columns whose values the device writes (the host skips them).
    generated_main: []bool,
    /// Every preprocessed definition in tree-0 order, and its periodic value offset.
    pre_defs: []ir.PreCol,
    pre_logs: []u32,
    pre_offsets: []u32,
    scratch_words: usize,

    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part, inputs: *const Inputs) !Plan {
        for ([_]usize{ inputs.sha_component, inputs.b2s_component, inputs.msg_component, inputs.walk_component, inputs.bytes_component }) |c| if (c >= parts.len) return error.InvalidWitnessPlan;
        const bytes_part = parts[inputs.bytes_component];
        if (bytes_part.air.n_main != BYTES_COLUMNS or bytes_part.log_size >= 30) return error.InvalidWitnessPlan;
        if (inputs.raw.len == 0 or inputs.raw.len > @as(usize, 1) << @intCast(bytes_part.log_size) or inputs.byte_mults.len != inputs.raw.len) return error.InvalidWitnessPlan;
        for (inputs.byte_mults) |m| if (m >= P) return error.InvalidWitnessPlan;
        const sha_part = parts[inputs.sha_component];
        const b2s_part = parts[inputs.b2s_component];
        const msg_part = parts[inputs.msg_component];
        const walk_part = parts[inputs.walk_component];
        if (sha_part.air.n_main != SHA_COLUMNS or b2s_part.air.n_main != B2S_COLUMNS or msg_part.air.n_main != MSG_COLUMNS or walk_part.air.n_main != WALK_COLUMNS) return error.InvalidWitnessPlan;
        const sha_rows = @as(usize, 1) << @intCast(sha_part.log_size);
        const b2s_rows = @as(usize, 1) << @intCast(b2s_part.log_size);
        const msg_rows = @as(usize, 1) << @intCast(msg_part.log_size);
        const walk_rows = @as(usize, 1) << @intCast(walk_part.log_size);
        if (msg_rows >= 1 << 30 or walk_rows >= 1 << 30 or inputs.raw.len >= 1 << 24) return error.InvalidWitnessPlan;
        // Messages: at least the header, in row order, each padded length inside the column.
        const n_msgs = inputs.msgs.len / bmsg.DESC_WORDS;
        if (n_msgs == 0 or inputs.msgs.len != n_msgs * bmsg.DESC_WORDS) return error.InvalidWitnessPlan;
        {
            var end: usize = 0;
            for (0..n_msgs) |m| {
                const d = inputs.msgs[bmsg.DESC_WORDS * m ..][0..bmsg.DESC_WORDS];
                if (d[0] != end) return error.InvalidWitnessPlan;
                end += (@as(usize, d[7]) + 9 + 63) / 64 * 64;
            }
            if (end >= msg_rows) return error.InvalidWitnessPlan;
        }
        if (inputs.walk_recs.len >= walk_rows) return error.InvalidWitnessPlan;
        if (inputs.compressions.len != inputs.meta.len or inputs.compressions.len > shaw.capacity(sha_part.log_size)) return error.InvalidWitnessPlan;
        if (inputs.blocks.len == 0 or inputs.blocks.len != inputs.chain.len or inputs.blocks.len * b2.PERIOD > b2s_rows) return error.InvalidWitnessPlan;
        if (sha_rows >= 1 << 30 or b2s_rows >= 1 << 30) return error.InvalidWitnessPlan;
        var n_main: usize = 0;
        var sha_first: usize = 0;
        var b2s_first: usize = 0;
        var msg_first: usize = 0;
        var walk_first: usize = 0;
        var bytes_first: usize = 0;
        var n_pre: usize = 0;
        for (parts, 0..) |p, i| {
            if (i == inputs.sha_component) sha_first = n_main;
            if (i == inputs.b2s_component) b2s_first = n_main;
            if (i == inputs.msg_component) msg_first = n_main;
            if (i == inputs.walk_component) walk_first = n_main;
            if (i == inputs.bytes_component) bytes_first = n_main;
            n_main += p.air.n_main;
            n_pre += p.air.preprocessed.len;
        }
        const generated = try allocator.alloc(bool, n_main);
        errdefer allocator.free(generated);
        @memset(generated, false);
        @memset(generated[sha_first..][0..SHA_COLUMNS], true);
        @memset(generated[b2s_first..][0..B2S_COLUMNS], true);
        @memset(generated[msg_first..][0..MSG_COLUMNS], true);
        @memset(generated[walk_first..][0..WALK_COLUMNS], true);
        @memset(generated[bytes_first..][0..BYTES_COLUMNS], true);
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
        // The variable regions' sizes: this block's, or the bounds the checks above enforce.
        const fixed = inputs.fixed_capacity;
        const bytes_rows = @as(usize, 1) << @intCast(bytes_part.log_size);
        const n_comps = if (fixed) shaw.capacity(sha_part.log_size) else inputs.compressions.len;
        const n_blocks = if (fixed) b2s_rows / b2.PERIOD else inputs.blocks.len;
        const raw_len = if (fixed) bytes_rows else inputs.raw.len;
        const msg_words = if (fixed) bmsg.DESC_WORDS * (msg_rows / 64) else inputs.msgs.len;
        const n_recs = if (fixed) walk_rows else inputs.walk_recs.len;
        l.sigma = region(&at, 160);
        l.comps = region(&at, n_comps * SHA_COMP_WORDS);
        l.meta = region(&at, 64 + n_comps * SHA_META_WORDS);
        l.periods = region(&at, (n_blocks + 1) * B2S_PERIOD_WORDS);
        l.pre_desc = region(&at, n_pre * PRE_DESC_WORDS);
        l.pre_values = region(&at, @max(values, 1));
        l.sha_columns = region(&at, 2 * SHA_COLUMNS);
        l.b2s_columns = region(&at, 2 * B2S_COLUMNS);
        l.raw = region(&at, @max((raw_len + 3) / 4, 1));
        l.msgs = region(&at, msg_words);
        l.walk = region(&at, WALK_REC_WORDS * (1 + n_recs));
        l.mults = region(&at, raw_len);
        l.msg_columns = region(&at, 2 * MSG_COLUMNS);
        l.walk_columns = region(&at, 2 * WALK_COLUMNS);
        l.bytes_columns = region(&at, 2 * BYTES_COLUMNS);
        l.words = at;
        return .{
            .inputs = inputs,
            .layout = l,
            .sha_log = sha_part.log_size,
            .b2s_log = b2s_part.log_size,
            .msg_log = msg_part.log_size,
            .walk_log = walk_part.log_size,
            .bytes_log = bytes_part.log_size,
            .sha_first = sha_first,
            .b2s_first = b2s_first,
            .msg_first = msg_first,
            .walk_first = walk_first,
            .bytes_first = bytes_first,
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
        // The block's bytes as little-endian words.
        @memcpy(std.mem.sliceAsBytes(out[l.raw..])[0..in.raw.len], in.raw);
        @memcpy(out[l.msgs..][0..in.msgs.len], in.msgs);
        out[l.walk] = in.sigops;
        const recs: [*]const u32 = @ptrCast(in.walk_recs.ptr);
        @memcpy(out[l.walk + WALK_REC_WORDS ..][0 .. WALK_REC_WORDS * in.walk_recs.len], recs[0 .. WALK_REC_WORDS * in.walk_recs.len]);
        @memcpy(out[l.mults..][0..in.byte_mults.len], in.byte_mults);
        const msg_rows = @as(usize, 1) << @intCast(self.msg_log);
        const walk_rows = @as(usize, 1) << @intCast(self.walk_log);
        const bytes_rows = @as(usize, 1) << @intCast(self.bytes_log);
        for (staging[1][self.bytes_first..][0..BYTES_COLUMNS], 0..) |dst, c| {
            if (dst.len != bytes_rows) return error.InvalidWitnessPlan;
            out[l.bytes_columns + 2 * c] = @truncate(dst.address);
            out[l.bytes_columns + 2 * c + 1] = @truncate(dst.address >> 32);
        }
        for (staging[1][self.msg_first..][0..MSG_COLUMNS], 0..) |dst, c| {
            if (dst.len != msg_rows) return error.InvalidWitnessPlan;
            out[l.msg_columns + 2 * c] = @truncate(dst.address);
            out[l.msg_columns + 2 * c + 1] = @truncate(dst.address >> 32);
        }
        for (staging[1][self.walk_first..][0..WALK_COLUMNS], 0..) |dst, c| {
            if (dst.len != walk_rows) return error.InvalidWitnessPlan;
            out[l.walk_columns + 2 * c] = @truncate(dst.address);
            out[l.walk_columns + 2 * c + 1] = @truncate(dst.address >> 32);
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
        {
            const rows: u32 = @as(u32, 1) << @intCast(plan.msg_log);
            var args = Args{
                .p0 = try ptr(session, b.inputs, l.raw, (in.raw.len + 3) / 4),
                .p1 = try ptr(session, b.inputs, l.msgs, in.msgs.len),
                .n = @intCast(in.msgs.len / bmsg.DESC_WORDS),
                .p2 = try ptr(session, b.inputs, l.msg_columns, 2 * MSG_COLUMNS),
                .rows = rows,
            };
            var pointers = args.pointers();
            try self.kernels.msg.launch(session, .{ (rows + threads - 1) / threads, 1, 1 }, threads, &pointers);
        }
        {
            const rows: u32 = @as(u32, 1) << @intCast(plan.walk_log);
            var args = Args{
                .p0 = try ptr(session, b.inputs, l.raw, (in.raw.len + 3) / 4),
                .p1 = try ptr(session, b.inputs, l.walk, WALK_REC_WORDS * (1 + in.walk_recs.len)),
                .n = @intCast(in.walk_recs.len),
                .p2 = try ptr(session, b.inputs, l.walk_columns, 2 * WALK_COLUMNS),
                .rows = rows,
            };
            var pointers = args.pointers();
            try self.kernels.walk.launch(session, .{ (rows + threads - 1) / threads, 1, 1 }, threads, &pointers);
        }
        {
            const rows: u32 = @as(u32, 1) << @intCast(plan.bytes_log);
            var args = Args{
                .p0 = try ptr(session, b.inputs, l.raw, (in.raw.len + 3) / 4),
                .p1 = try ptr(session, b.inputs, l.mults, in.byte_mults.len),
                .n = @intCast(in.raw.len),
                .p2 = try ptr(session, b.inputs, l.bytes_columns, 2 * BYTES_COLUMNS),
                .rows = rows,
            };
            var pointers = args.pointers();
            try self.kernels.bytes.launch(session, .{ (rows + threads - 1) / threads, 1, 1 }, threads, &pointers);
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
