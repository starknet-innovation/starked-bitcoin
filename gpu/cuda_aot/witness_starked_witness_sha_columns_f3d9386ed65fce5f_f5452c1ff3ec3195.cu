// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): block_sha's 144 columns.
// Row r from the word trace (words: a, e, w, `rows` each; cyclic neighbours) as
// sha256/witness.zig `columns` with `shaRole`, then block/sha.zig `Extra`: per period
// meta[64 + 6p..] = mid, blk, flags (fst 1, dbl 2, node 4, npad 8, dup 16), lid, rid, ym for
// (meta[0..64]: the round constants)
// p < count, else NILS; the mutation check (limb differences with row r - 8, inverses)
// and the ALLEQ chain on period rows 12..19. columns[c] is column c's address.
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }
#define STARKED_P 0x7fffffffu
__device__ __forceinline__ unsigned m31_add(unsigned a, unsigned b) { unsigned s = a + b; return s >= STARKED_P ? s - STARKED_P : s; }
__device__ __forceinline__ unsigned m31_sub(unsigned a, unsigned b) { return a >= b ? a - b : a + STARKED_P - b; }
__device__ __forceinline__ unsigned m31_mul(unsigned a, unsigned b) {
    const u64 p = (u64)a * (u64)b;
    const unsigned s = (unsigned)(p & STARKED_P) + (unsigned)(p >> 31);
    return s >= STARKED_P ? s - STARKED_P : s;
}
__device__ __forceinline__ unsigned m31_inv(unsigned x) {
    // x^(P-2), P - 2 = 2^31 - 3 = 0b111...1101 (31 bits).
    unsigned r = 1u, b = x, e = STARKED_P - 2u;
    while (e) { if (e & 1u) r = m31_mul(r, b); b = m31_mul(b, b); e >>= 1u; }
    return r;
}

__device__ __forceinline__ unsigned starked_S0(unsigned x) { return starked_rotr(x, 2u) ^ starked_rotr(x, 13u) ^ starked_rotr(x, 22u); }
__device__ __forceinline__ unsigned starked_S1(unsigned x) { return starked_rotr(x, 6u) ^ starked_rotr(x, 11u) ^ starked_rotr(x, 25u); }
__device__ __forceinline__ unsigned starked_s0(unsigned x) { return starked_rotr(x, 7u) ^ starked_rotr(x, 18u) ^ (x >> 3u); }
__device__ __forceinline__ unsigned starked_s1(unsigned x) { return starked_rotr(x, 17u) ^ starked_rotr(x, 19u) ^ (x >> 10u); }
__device__ __forceinline__ unsigned starked_zz(const unsigned *ww, unsigned r, unsigned rows) {
    const unsigned x = ww[r], y = ww[(r + rows - 8u) % rows];
    return ((x & 0xffffu) == (y & 0xffffu) && (x >> 16u) == (y >> 16u)) ? 1u : 0u;
}
extern "C" __global__ void __launch_bounds__(256) starked_witness_sha_columns_v1_f3d9386ed65fce5f(
    const unsigned *words, const unsigned *meta, unsigned count, const u64 *columns, unsigned rows) {
    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
    const unsigned *wa = words;
    const unsigned *we = words + (u64)rows;
    const unsigned *ww = words + 2ull * (u64)rows;
#define AT(x, back) x[(r + rows - (back)) % rows]
#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
    const unsigned av = wa[r], ev = we[r], wv = ww[r];
    for (unsigned i = 0; i < 32u; ++i) {
        PUT(i, (av >> i) & 1u);
        PUT(32u + i, (ev >> i) & 1u);
        PUT(64u + i, (wv >> i) & 1u);
    }
    const unsigned a1 = AT(wa, 1u), a2 = AT(wa, 2u), a3 = AT(wa, 3u);
    const unsigned e1 = AT(we, 1u), e2 = AT(we, 2u), e3 = AT(we, 3u);
    const unsigned s0v = starked_S0(a1), s1v = starked_S1(e1);
    const unsigned chv = (e1 & e2) ^ (~e1 & e3);
    const unsigned mjv = (a1 & a2) ^ (a1 & a3) ^ (a2 & a3);
    const unsigned ss0 = starked_s0(AT(ww, 15u)), ss1 = starked_s1(AT(ww, 2u));
    const unsigned pairs[6] = { s0v, s1v, chv, mjv, ss0, ss1 };
    for (unsigned k = 0; k < 6u; ++k) { PUT(96u + 2u * k, pairs[k] & 0xffffu); PUT(97u + 2u * k, pairs[k] >> 16u); }
    unsigned ca0 = 0u, ca1 = 0u, ce0 = 0u, ce1 = 0u, cw0 = 0u, cw1 = 0u;
    const unsigned q = r % 72u;
    if (q >= 4u && q < 68u) {
        const unsigned t = q - 4u;
        const unsigned k = meta[t];
        const unsigned h4 = AT(we, 4u), d4 = AT(wa, 4u);
        const unsigned t1_lo = (h4 & 0xffffu) + (s1v & 0xffffu) + (chv & 0xffffu) + (k & 0xffffu) + (wv & 0xffffu);
        const unsigned t1_hi = (h4 >> 16u) + (s1v >> 16u) + (chv >> 16u) + (k >> 16u) + (wv >> 16u);
        ca0 = (t1_lo + (s0v & 0xffffu) + (mjv & 0xffffu)) >> 16u;
        ca1 = (t1_hi + (s0v >> 16u) + (mjv >> 16u) + ca0) >> 16u;
        ce0 = ((d4 & 0xffffu) + t1_lo) >> 16u;
        ce1 = ((d4 >> 16u) + t1_hi + ce0) >> 16u;
        if (t >= 16u) {
            const unsigned w7 = AT(ww, 7u), w16 = AT(ww, 16u);
            cw0 = ((ss1 & 0xffffu) + (w7 & 0xffffu) + (ss0 & 0xffffu) + (w16 & 0xffffu)) >> 16u;
            cw1 = ((ss1 >> 16u) + (w7 >> 16u) + (ss0 >> 16u) + (w16 >> 16u) + cw0) >> 16u;
        }
    } else if (q >= 68u) {
        const unsigned x4 = AT(wa, 4u), x68 = AT(wa, 68u), y4 = AT(we, 4u), y68 = AT(we, 68u);
        ca0 = ((x4 & 0xffffu) + (x68 & 0xffffu)) >> 16u;
        ca1 = ((x4 >> 16u) + (x68 >> 16u) + ca0) >> 16u;
        ce0 = ((y4 & 0xffffu) + (y68 & 0xffffu)) >> 16u;
        ce1 = ((y4 >> 16u) + (y68 >> 16u) + ce0) >> 16u;
    }
    for (unsigned j = 0; j < 3u; ++j) {
        PUT(108u + j, (ca0 >> j) & 1u); PUT(111u + j, (ca1 >> j) & 1u);
        PUT(114u + j, (ce0 >> j) & 1u); PUT(117u + j, (ce1 >> j) & 1u);
    }
    for (unsigned j = 0; j < 2u; ++j) { PUT(120u + j, (cw0 >> j) & 1u); PUT(122u + j, (cw1 >> j) & 1u); }
    // block/sha.zig Extra: 124 MID, 125 BLKI, 126 FST, 127 DBL, 128 NILS, 129 USEW, 130 CHN,
    // 131 YM, 132 NODE, 133 NPAD, 134 LID, 135 RID, 136 NDUP, 137 ZL, 138 IL, 139 ZH, 140 IH,
    // 141 ZZ, 142 ALLEQ, 143 NNE.
    const unsigned per = r / 72u;
    unsigned mid = 0u, blk = 0u, flags = 0u, lid = 0u, rid = 0u, ym = 0u, nils = 0u;
    if (per < count) {
        const unsigned *m = meta + 64u + (u64)per * 6u;
        mid = m[0]; blk = m[1]; flags = m[2]; lid = m[3]; rid = m[4];
        if ((flags & 2u) && q == 71u) ym = m[5];
    } else nils = 1u;
    const unsigned fst = flags & 1u, dbl = (flags >> 1u) & 1u, node = (flags >> 2u) & 1u, npad = (flags >> 3u) & 1u, dup = (flags >> 4u) & 1u;
    const unsigned kinds = m31_add(node, npad);
    PUT(124u, mid); PUT(125u, blk); PUT(126u, fst); PUT(127u, dbl); PUT(128u, nils);
    PUT(129u, m31_sub(m31_sub(m31_sub(1u, dbl), nils), kinds));
    PUT(130u, m31_sub(m31_sub(m31_sub(m31_sub(1u, fst), dbl), nils), kinds));
    PUT(131u, ym); PUT(132u, node); PUT(133u, npad); PUT(134u, lid); PUT(135u, rid); PUT(136u, dup);
    PUT(143u, m31_mul(node, m31_sub(1u, dup)));
    const unsigned wp = AT(ww, 8u);
    const unsigned dl = m31_sub(wv & 0xffffu, wp & 0xffffu);
    const unsigned dh = m31_sub(wv >> 16u, wp >> 16u);
    const unsigned zl = dl == 0u ? 1u : 0u, zh = dh == 0u ? 1u : 0u;
    PUT(137u, zl); PUT(138u, zl ? 0u : m31_inv(dl));
    PUT(139u, zh); PUT(140u, zh ? 0u : m31_inv(dh));
    const unsigned zz = zl & zh;
    PUT(141u, zz);
    unsigned alleq = 0u;
    if (q >= 12u && q < 20u) {
        alleq = zz;
        for (unsigned k = 1u; k <= q - 12u; ++k) alleq &= starked_zz(ww, r - k, rows);
    }
    PUT(142u, alleq);
#undef AT
#undef PUT
}
