// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): block_msg columns.
// Row r belongs to the last message m with msgs[10m] <= r (row, id, flags hdr|wtx|seg|split,
// i, a, w, l, dl, prev_dl); past the last message's padded length the row is padding (NIL,
// the last message's tuple, IDX counting on). As block/msg.zig generate, setUses and
// merkle.addHeaderUses: data bytes at a + j (split txid: a + j, a + 2 + j, l + j - (dl - 4)),
// 0x80, zeros, the 64-bit bit length; derived EZ, Z, INV, CONT, SW, ENDD; the running DLC.
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

extern "C" __global__ void __launch_bounds__(256) starked_witness_msg_v1_54b8bcb38815ef89(
    const unsigned *raw, const unsigned *msgs, unsigned count, const u64 *columns, unsigned rows) {
    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
    unsigned lo = 0u, hi = count - 1u;
    while (lo < hi) { const unsigned mid = (lo + hi + 1u) / 2u; if (msgs[(u64)mid * 10u] <= r) lo = mid; else hi = mid - 1u; }
    const unsigned *d = msgs + (u64)lo * 10u;
    const unsigned id = d[1], fl = d[2], ti = d[3], ta = d[4], tw = d[5], tl = d[6], dl = d[7], prev = d[8];
    const unsigned padded = (dl + 9u + 63u) / 64u * 64u;
    const unsigned j = r - d[0];
    const unsigned mt = (fl >> 3u) & 1u;
    unsigned v[38];
    for (unsigned c = 0; c < 38u; ++c) v[c] = 0u;
    v[10] = fl & 1u; v[11] = (fl >> 1u) & 1u; v[12] = (fl >> 2u) & 1u;
    v[13] = ti; v[14] = ta; v[15] = tw; v[16] = tl; v[9] = mt; v[17] = id; v[18] = j;
    const unsigned nil = j < padded ? 0u : 1u;
    if (!nil) {
        if (j == 0u) v[5] = 1u;
        unsigned byte = 0u;
        if (j < dl) {
            v[0] = 1u;
            const unsigned piece = !mt ? 0u : (j < 4u ? 0u : (j < dl - 4u ? 1u : 2u));
            const unsigned pos = piece == 0u ? ta + j : (piece == 1u ? ta + 2u + j : tl + j - (dl - 4u));
            v[19] = pos;
            byte = (raw[pos >> 2u] >> (8u * (pos & 3u))) & 0xffu;
            v[6u + piece] = 1u;
        } else if (j == dl) {
            v[1] = 1u; byte = 0x80u;
        } else if (j < padded - 8u) {
            v[2] = 1u;
        } else {
            v[3] = 1u;
            const u64 bits = 8ull * (u64)dl;
            byte = (unsigned)((bits >> (8u * (padded - 1u - j))) & 0xffull);
        }
        v[20] = byte;
        for (unsigned b = 0; b < 8u; ++b) v[21u + b] = (byte >> b) & 1u;
        v[35] = j >= dl ? dl : prev;
    } else {
        v[4] = 1u;
        v[35] = dl;
    }
    // Derived (msg.zig Derived.rows).
    const unsigned pos = v[19];
    const unsigned tl3 = m31_add(tl, 3u);
    const unsigned ez = m31_add(m31_mul(mt, m31_add(m31_add(m31_mul(v[6], m31_sub(j, 3u)), m31_mul(v[7], m31_add(m31_sub(pos, tw), 1u))), m31_mul(v[8], m31_sub(pos, tl3)))),
                       m31_mul(m31_sub(1u, mt), m31_sub(pos, tl3)));
    const unsigned z = ez == 0u ? 1u : 0u;
    v[29] = ez; v[30] = z; v[31] = ez == 0u ? 0u : m31_inv(ez);
    v[32] = m31_mul(v[0], m31_sub(1u, z));
    v[33] = m31_mul(m31_mul(z, mt), m31_add(v[6], v[7]));
    v[34] = m31_sub(m31_mul(v[0], z), v[33]);
    // Uses (setUses, merkle.addHeaderUses: the header's eight words read twice).
    if (!nil) {
        v[36] = ((r & 3u) == 3u ? 1u : 0u) + ((r >= 39u && r <= 67u && ((r - 39u) & 3u) == 0u) ? 1u : 0u);
        v[37] = ((r & 63u) == 63u && v[3]) ? 1u : 0u;
    }
    for (unsigned c = 0; c < 38u; ++c) PUT(c, v[c]);
#undef PUT
}
