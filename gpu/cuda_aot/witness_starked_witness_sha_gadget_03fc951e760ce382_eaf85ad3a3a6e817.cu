// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): the SHA-256 gadget's 124
// columns of any component (the coin-set pass's set_shac). Row r from the word trace (words:
// a, e, w, `rows` each; cyclic neighbours; the `sha_words` kernel) as sha256/witness.zig
// `columns` with `shaRole`; ktab[0..64]: the round constants. count: unused.
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }

__device__ __forceinline__ unsigned starked_S0(unsigned x) { return starked_rotr(x, 2u) ^ starked_rotr(x, 13u) ^ starked_rotr(x, 22u); }
__device__ __forceinline__ unsigned starked_S1(unsigned x) { return starked_rotr(x, 6u) ^ starked_rotr(x, 11u) ^ starked_rotr(x, 25u); }
__device__ __forceinline__ unsigned starked_s0(unsigned x) { return starked_rotr(x, 7u) ^ starked_rotr(x, 18u) ^ (x >> 3u); }
__device__ __forceinline__ unsigned starked_s1(unsigned x) { return starked_rotr(x, 17u) ^ starked_rotr(x, 19u) ^ (x >> 10u); }
extern "C" __global__ void __launch_bounds__(256) starked_witness_sha_gadget_v1_03fc951e760ce382(
    const unsigned *words, const unsigned *ktab, unsigned count, const u64 *columns, unsigned rows) {
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
        const unsigned k = ktab[t];
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
#undef AT
#undef PUT
}
