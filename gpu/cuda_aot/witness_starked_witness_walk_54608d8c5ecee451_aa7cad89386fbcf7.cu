// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): block_walk columns.
// Row r < count expands record recs[4 + 4r] (w0: pos 0-23, kind 24-25 (op, ln, dt, inf),
// li 26-27, lk code 28-29 (0, 1, 2, 4), first 30; rem; val = dr or lacc; sums) with its byte
// raw[pos] as block/walk.zig columns: the row's state, the automaton step, the zero tests and
// their inverses. Rows past count are padding (SUMS = recs[0], ZA = 1, INVD = INVR = 1/(-1)).
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

extern "C" __global__ void __launch_bounds__(256) starked_witness_walk_v1_54608d8c5ecee451(
    const unsigned *raw, const unsigned *recs, unsigned count, const u64 *columns, unsigned rows) {
    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
    unsigned v[51];
    for (unsigned c = 0; c < 51u; ++c) v[c] = 0u;
    const unsigned inv_m1 = m31_inv(STARKED_P - 1u);
    if (r >= count) {
        v[49] = recs[0]; v[30] = 1u; v[33] = inv_m1; v[35] = inv_m1;
    } else {
        const unsigned *rc = recs + 4ull + 4ull * (u64)r;
        const unsigned w0 = rc[0], rem = rc[1], val = rc[2], sums = rc[3];
        const unsigned pos = w0 & 0xffffffu, kind = (w0 >> 24u) & 3u, li = (w0 >> 26u) & 3u;
        const unsigned lkc = (w0 >> 28u) & 3u, first = (w0 >> 30u) & 1u;
        const unsigned lk = lkc == 3u ? 4u : lkc;
        const unsigned b = (raw[pos >> 2u] >> (8u * (pos & 3u))) & 0xffu;
        v[0] = 1u; v[1] = first; v[2] = pos; v[3] = rem; v[4] = b;
        v[34] = rem == 1u ? 1u : 0u;
        v[35] = rem == 1u ? 0u : m31_inv(m31_sub(rem, 1u));
        // The next state (walk.zig step): kind, dr, lk, li, lacc.
        unsigned nk = 0u, ndr = 0u, nlk = 0u, nli = 0u, nlacc = 0u;
        if (kind == 0u) {
            v[5] = 1u;
            v[9] = b < 0x4cu ? b : 0u;
            v[10] = b == 0x4cu; v[11] = b == 0x4du; v[12] = b == 0x4eu;
            v[13] = (b == 0xacu || b == 0xadu) ? 1u : ((b == 0xaeu || b == 0xafu) ? 20u : 0u);
            v[14] = (b >= 1u && b < 0x4cu) ? 1u : 0u;
            if (b >= 1u && b < 0x4cu) { nk = 2u; ndr = b; }
            else if (b >= 0x4cu && b <= 0x4eu) { nk = 1u; nlk = b == 0x4cu ? 1u : (b == 0x4du ? 2u : 4u); }
        } else if (kind == 1u) {
            v[6] = 1u;
            v[15u + li] = 1u;
            if (lk == 1u) v[19] = 1u; else if (lk == 2u) v[20] = 1u; else v[21] = 1u;
            v[22] = val;
            const u64 acc2 = (u64)val + ((u64)b << (8u * li));
            if (li + 1u == lk) {
                v[25] = 1u; v[26] = 1u;
                if (lk == 4u && b >= 2u) { v[28] = 1u; nk = 3u; }
                else {
                    v[27] = 1u;
                    if (lk == 4u) v[29] = 1u;
                    if (acc2 == 0ull) nk = 0u; else { nk = 2u; ndr = (unsigned)acc2; }
                }
            } else { nk = 1u; nlk = lk; nli = li + 1u; nlacc = (unsigned)acc2; }
            const unsigned a2 = (unsigned)(acc2 % (u64)STARKED_P);
            v[24] = a2; v[30] = a2 == 0u ? 1u : 0u; v[31] = a2 == 0u ? 0u : m31_inv(a2);
        } else if (kind == 2u) {
            v[7] = 1u; v[23] = val;
            if (val == 1u) nk = 0u; else { nk = 2u; ndr = val - 1u; }
        } else {
            v[8] = 1u; nk = 3u;
        }
        if (kind != 1u) { v[30] = 1u; v[31] = 0u; }
        v[32] = v[23] == 1u ? 1u : 0u;
        v[33] = v[23] == 1u ? 0u : m31_inv(m31_sub(v[23], 1u));
        v[36] = nk == 0u; v[37] = nk == 1u; v[38] = nk == 2u; v[39] = nk == 3u;
        if (nk == 2u) v[40] = ndr;
        if (nk == 1u) {
            v[41] = nlacc;
            v[42u + nli] = 1u;
            if (nlk == 1u) v[46] = 1u; else if (nlk == 2u) v[47] = 1u; else v[48] = 1u;
        }
        v[50] = first ? 0u : 1u;
        v[49] = sums;
    }
    for (unsigned c = 0; c < 51u; ++c) PUT(c, v[c]);
#undef PUT
}
