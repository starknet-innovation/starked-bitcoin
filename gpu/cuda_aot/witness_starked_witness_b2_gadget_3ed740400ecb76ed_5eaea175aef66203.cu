// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): the Blake2s gadget's 300
// columns of any component (the coin-set pass's set_b2c, set_lc, set_mt). Row r of period
// p = r / 88 from its own input periods[27 min(p, count - 1)..]: h[8], m[16], t_lo, t_hi, last
// (the host gives every period's input, used or not) as hash/blake2s_air.zig fillPeriod
// (init rows 0-3, G rows 4-83 after recomputing the earlier G steps, final rows 84-87,
// message limbs 256-287, carries 288-299). sigma: 10 x 16 words.
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }

__device__ __forceinline__ void starked_carries(unsigned *out, unsigned x, unsigned y, unsigned z) {
    const unsigned lo = (x & 0xffffu) + (y & 0xffffu) + (z & 0xffffu);
    const unsigned hi = (x >> 16u) + (y >> 16u) + (z >> 16u);
    out[0] = lo >> 16u;
    out[1] = (hi + out[0]) >> 16u;
}
__device__ __forceinline__ void starked_gidx(unsigned g, unsigned *ix) {
    if (g < 4u) { ix[0] = g; ix[1] = g + 4u; ix[2] = g + 8u; ix[3] = g + 12u; }
    else { const unsigned k = g - 4u; ix[0] = k; ix[1] = 4u + ((k + 1u) & 3u); ix[2] = 8u + ((k + 2u) & 3u); ix[3] = 12u + ((k + 3u) & 3u); }
}
extern "C" __global__ void __launch_bounds__(256) starked_witness_b2_gadget_v1_3ed740400ecb76ed(
    const unsigned *sigma, const unsigned *periods, unsigned count, const u64 *columns, unsigned rows) {
    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
    const unsigned p = r / 88u, q = r % 88u;
    const unsigned *in = periods + (u64)(p < count ? p : count - 1u) * 27u;
    unsigned h[8], m[16], v[16];
    for (unsigned i = 0; i < 8u; ++i) h[i] = in[i];
    for (unsigned i = 0; i < 16u; ++i) m[i] = in[8u + i];
    const unsigned tlo = in[24], thi = in[25], fl = in[26];
    const unsigned iv[8] = { 0x6A09E667u, 0xBB67AE85u, 0x3C6EF372u, 0xA54FF53Au, 0x510E527Fu, 0x9B05688Cu, 0x1F83D9ABu, 0x5BE0CD19u };
    for (unsigned i = 0; i < 8u; ++i) { v[i] = h[i]; v[8u + i] = iv[i]; }
    v[12] ^= tlo; v[13] ^= thi; if (fl) v[14] ^= 0xffffffffu;
    unsigned slot[8] = { 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u };
    unsigned carry[8] = { 0u, 0u, 0u, 0u, 0u, 0u, 0u, 0u };
    if (q < 4u) {
        unsigned ix[4];
        starked_gidx(4u + q, ix);
        // OUT_W = 4, 7, 6, 5 for roles a, b, c, d.
        slot[4] = v[ix[0]]; slot[7] = v[ix[1]]; slot[6] = v[ix[2]]; slot[5] = v[ix[3]];
        if (q == 0u) { slot[0] = tlo; slot[1] = thi; slot[2] = fl; }
    } else {
        const unsigned steps = q < 84u ? q - 4u : 80u;
        for (unsigned j = 0; j <= steps && j < 80u; ++j) {
            unsigned ix[4];
            starked_gidx(j % 8u, ix);
            const unsigned rr = j / 8u, g = j % 8u;
            const unsigned x = m[sigma[rr * 16u + 2u * g]], y = m[sigma[rr * 16u + 2u * g + 1u]];
            const unsigned a = v[ix[0]], b = v[ix[1]], c = v[ix[2]], d = v[ix[3]];
            const unsigned a1 = a + b + x;
            const unsigned d1 = starked_rotr(d ^ a1, 16u);
            const unsigned c1 = c + d1;
            const unsigned b1 = starked_rotr(b ^ c1, 12u);
            const unsigned a2 = a1 + b1 + y;
            const unsigned d2 = starked_rotr(d1 ^ a2, 8u);
            const unsigned c2 = c1 + d2;
            const unsigned b2 = starked_rotr(b1 ^ c2, 7u);
            if (j == steps) {
                slot[0] = a1; slot[1] = d1; slot[2] = c1; slot[3] = b1;
                slot[4] = a2; slot[5] = d2; slot[6] = c2; slot[7] = b2;
                starked_carries(carry + 0, a, b, x);
                starked_carries(carry + 2, c, d1, 0u);
                starked_carries(carry + 4, a1, b1, y);
                starked_carries(carry + 6, c1, d2, 0u);
            }
            v[ix[0]] = a2; v[ix[1]] = b2; v[ix[2]] = c2; v[ix[3]] = d2;
        }
        if (q >= 84u) {
            const unsigned k = q - 84u;
            unsigned ix[4];
            starked_gidx(4u + k, ix);
            const unsigned bk = ix[1];
            slot[2] = h[k] ^ v[k];
            slot[0] = h[k] ^ v[k] ^ v[k + 8u];
            slot[3] = h[bk] ^ v[bk];
            slot[1] = h[bk] ^ v[bk] ^ v[bk + 8u];
        }
    }
    for (unsigned s = 0; s < 8u; ++s)
        for (unsigned i = 0; i < 32u; ++i) PUT(32u * s + i, (slot[s] >> i) & 1u);
    // Carry bits: 288 (2), 290 (2), 292 (1), 293 (1), 294 (2), 296 (2), 298 (1), 299 (1).
    PUT(288u, carry[0] & 1u); PUT(289u, (carry[0] >> 1u) & 1u);
    PUT(290u, carry[1] & 1u); PUT(291u, (carry[1] >> 1u) & 1u);
    PUT(292u, carry[2] & 1u); PUT(293u, carry[3] & 1u);
    PUT(294u, carry[4] & 1u); PUT(295u, (carry[4] >> 1u) & 1u);
    PUT(296u, carry[5] & 1u); PUT(297u, (carry[5] >> 1u) & 1u);
    PUT(298u, carry[6] & 1u); PUT(299u, carry[7] & 1u);
    for (unsigned k = 0; k < 16u; ++k) { PUT(256u + 2u * k, m[k] & 0xffffu); PUT(257u + 2u * k, m[k] >> 16u); }
#undef PUT
}
