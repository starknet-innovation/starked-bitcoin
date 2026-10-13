// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): block_sha word trace.
// Thread p lays compression p (comps[24p..]: input state, block; a zero dummy for p >= count)
// on rows 72p .. 72p+71 (truncated at rows) as sha256/witness.zig Words.place: init rows
// a = input[3-q], e = input[7-q]; round rows the new a, e and w_t; final rows
// a = a[r-4] + a[r-68], e likewise; w = 0 off the rounds.
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }

__device__ __forceinline__ unsigned starked_S0(unsigned x) { return starked_rotr(x, 2u) ^ starked_rotr(x, 13u) ^ starked_rotr(x, 22u); }
__device__ __forceinline__ unsigned starked_S1(unsigned x) { return starked_rotr(x, 6u) ^ starked_rotr(x, 11u) ^ starked_rotr(x, 25u); }
__device__ __forceinline__ unsigned starked_s0(unsigned x) { return starked_rotr(x, 7u) ^ starked_rotr(x, 18u) ^ (x >> 3u); }
__device__ __forceinline__ unsigned starked_s1(unsigned x) { return starked_rotr(x, 17u) ^ starked_rotr(x, 19u) ^ (x >> 10u); }
extern "C" __global__ void __launch_bounds__(64) starked_witness_sha_words_v1_f0c8fc61b9592dfd(
    const unsigned *ktab, const unsigned *comps, unsigned count, unsigned *words, unsigned rows) {
    const unsigned p = blockIdx.x * blockDim.x + threadIdx.x;
    const unsigned periods = (rows + 71u) / 72u;
    if (p >= periods) return;
    unsigned *wa = words;
    unsigned *we = words + (u64)rows;
    unsigned *ww = words + 2ull * (u64)rows;
    unsigned h[8], blk[16];
    for (unsigned i = 0; i < 8u; ++i) h[i] = p < count ? comps[(u64)p * 24u + i] : 0u;
    for (unsigned i = 0; i < 16u; ++i) blk[i] = p < count ? comps[(u64)p * 24u + 8u + i] : 0u;
    const u64 start = (u64)p * 72u;
    for (unsigned q = 0; q < 4u; ++q) {
        const u64 r = start + q;
        if (r < rows) { wa[r] = h[3u - q]; we[r] = h[7u - q]; ww[r] = 0u; }
    }
    unsigned a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
    unsigned w[16];
    for (unsigned t = 0; t < 64u; ++t) {
        unsigned wt;
        if (t < 16u) wt = blk[t];
        else wt = starked_s1(w[(t - 2u) & 15u]) + w[(t - 7u) & 15u] + starked_s0(w[(t - 15u) & 15u]) + w[(t - 16u) & 15u];
        w[t & 15u] = wt;
        const unsigned t1 = hh + starked_S1(e) + ((e & f) ^ (~e & g)) + ktab[t] + wt;
        const unsigned t2 = starked_S0(a) + ((a & b) ^ (a & c) ^ (b & c));
        hh = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
        const u64 r = start + 4u + t;
        if (r < rows) { wa[r] = a; we[r] = e; ww[r] = wt; }
    }
    // a, e of rounds 60..63 are (d, c, b, a) and (hh, g, f, e).
    const unsigned la[4] = { d, c, b, a };
    const unsigned le[4] = { hh, g, f, e };
    for (unsigned j = 0; j < 4u; ++j) {
        const u64 r = start + 68u + j;
        if (r < rows) { wa[r] = la[j] + h[3u - j]; we[r] = le[j] + h[7u - j]; ww[r] = 0u; }
    }
}
