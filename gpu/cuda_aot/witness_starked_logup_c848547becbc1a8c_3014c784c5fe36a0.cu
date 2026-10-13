// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_b2msg, digest 17b86e90878320a24431119691aa8bad3a4a79b9c8fa478a7214fa4435aebdd6.
// 6 lookups in 3 batches, 15 source columns, tuples up to 4 values.
typedef unsigned long long u64;
#define STARKED_P 2147483647u
struct StarkedQm31 { unsigned a, b, c, d; };
__device__ __forceinline__ unsigned starked_add(unsigned x, unsigned y) {
    const unsigned s = x + y;
    return s < STARKED_P ? s : s - STARKED_P;
}
__device__ __forceinline__ unsigned starked_sub(unsigned x, unsigned y) {
    return x >= y ? x - y : x + STARKED_P - y;
}
__device__ __forceinline__ unsigned starked_mul(unsigned x, unsigned y) {
    const u64 p = (u64)x * y;
    const unsigned f = (unsigned)(p & STARKED_P) + (unsigned)(p >> 31u);
    return f < STARKED_P ? f : f - STARKED_P;
}
__device__ __forceinline__ unsigned starked_neg(unsigned x) {
    return x == 0u ? 0u : STARKED_P - x;
}
__device__ __forceinline__ StarkedQm31 starked_q_add(StarkedQm31 x, StarkedQm31 y) {
    return {starked_add(x.a, y.a), starked_add(x.b, y.b), starked_add(x.c, y.c), starked_add(x.d, y.d)};
}
__device__ __forceinline__ StarkedQm31 starked_q_mul_base(StarkedQm31 x, unsigned s) {
    return {starked_mul(x.a, s), starked_mul(x.b, s), starked_mul(x.c, s), starked_mul(x.d, s)};
}
// (a + b·u)(c + d·u) with u² = 2 + i over CM31 = M31[i]/(i² + 1), as stwo.
__device__ __forceinline__ StarkedQm31 starked_q_mul(StarkedQm31 l, StarkedQm31 r) {
    const unsigned x0 = starked_sub(starked_mul(l.a, r.a), starked_mul(l.b, r.b));
    const unsigned x1 = starked_add(starked_mul(l.a, r.b), starked_mul(l.b, r.a));
    const unsigned y0 = starked_sub(starked_mul(l.c, r.c), starked_mul(l.d, r.d));
    const unsigned y1 = starked_add(starked_mul(l.c, r.d), starked_mul(l.d, r.c));
    const unsigned c0 = starked_sub(starked_mul(l.a, r.c), starked_mul(l.b, r.d));
    const unsigned c1 = starked_add(starked_mul(l.a, r.d), starked_mul(l.b, r.c));
    const unsigned c2 = starked_sub(starked_mul(l.c, r.a), starked_mul(l.d, r.b));
    const unsigned c3 = starked_add(starked_mul(l.c, r.b), starked_mul(l.d, r.a));
    return {starked_add(x0, starked_sub(starked_add(y0, y0), y1)),
            starked_add(x1, starked_add(y0, starked_add(y1, y1))),
            starked_add(c0, c2), starked_add(c1, c3)};
}
__device__ __forceinline__ StarkedQm31 starked_q_load(const unsigned *p) {
    return {p[0], p[1], p[2], p[3]};
}
__device__ __forceinline__ unsigned starked_brev(unsigned v, unsigned bits) {
    return bits == 0u ? 0u : __brev(v) >> (32u - bits);
}
// Storage (bit-reversed circle-domain) index of natural (coset-order) row i.
__device__ __forceinline__ unsigned starked_storage_row(unsigned i, unsigned log_size) {
    const unsigned n = 1u << log_size;
    const unsigned circle = (i & 1u) == 0u ? i >> 1u : n - 1u - (i >> 1u);
    return starked_brev(circle, log_size);
}
// Natural (coset-order) row of storage index s.
__device__ __forceinline__ unsigned starked_natural_row(unsigned s, unsigned log_size) {
    const unsigned n = 1u << log_size;
    const unsigned c = starked_brev(s, log_size);
    return c < (n >> 1u) ? c << 1u : ((n - c) << 1u) - 1u;
}
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_c848547becbc1a8c(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v0 = sources[(u64)2u * rows + r_0];
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)13u * rows + r_0];
    const unsigned v7 = sources[(u64)9u * rows + r_0];
    const unsigned v10 = sources[(u64)10u * rows + r_0];
    const unsigned v13 = sources[(u64)11u * rows + r_0];
    const unsigned v16 = sources[(u64)12u * rows + r_0];
    const unsigned v22 = sources[(u64)3u * rows + r_0];
    const unsigned v35 = sources[(u64)1u * rows + r_0];
    const unsigned v44 = sources[(u64)4u * rows + r_0];
    const unsigned v48 = sources[(u64)0u * rows + r_0];
    const unsigned v83 = sources[(u64)14u * rows + r_0];
    const unsigned v90 = sources[(u64)5u * rows + r_0];
    const unsigned v92 = sources[(u64)6u * rows + r_0];
    const unsigned v95 = sources[(u64)7u * rows + r_0];
    const unsigned v98 = sources[(u64)8u * rows + r_0];
    const unsigned v108 = starked_neg(v7);
    const unsigned v109 = 0u;
    const unsigned v110 = starked_add(v44, v109);
    const unsigned v111 = starked_neg(v10);
    const unsigned v112 = starked_add(v44, v1);
    const unsigned v113 = starked_neg(v13);
    const unsigned v114 = 2u;
    const unsigned v115 = starked_add(v44, v114);
    const unsigned v116 = starked_neg(v16);
    const unsigned v117 = 3u;
    const unsigned v118 = starked_add(v44, v117);
    const unsigned v119 = 256u;
    const unsigned v120 = starked_mul(v119, v92);
    const unsigned v121 = starked_add(v90, v120);
    const unsigned v122 = starked_mul(v119, v98);
    const unsigned v123 = starked_add(v95, v122);
    const unsigned v124 = starked_mul(v0, v35);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 17u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v110));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v90));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 17u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v112));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v92));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 17u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v115));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v95));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 17u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v118));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v98));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 18u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v22));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v48));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha3, v121));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha4, v123));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 19u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v22));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v4));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha3, v83));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v108), starked_q_mul_base(d0, v111));
        const StarkedQm31 d = starked_q_mul(d0, d1);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[0][row] = n.a;
        outputs[1][row] = n.b;
        outputs[2][row] = n.c;
        outputs[3][row] = n.d;
        unsigned *slot = denominators + ((u64)0u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v113), starked_q_mul_base(d2, v116));
        const StarkedQm31 d = starked_q_mul(d2, d3);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[4][row] = n.a;
        outputs[5][row] = n.b;
        outputs[6][row] = n.c;
        outputs[7][row] = n.d;
        unsigned *slot = denominators + ((u64)1u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v0), starked_q_mul_base(d4, v124));
        const StarkedQm31 d = starked_q_mul(d4, d5);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[8][row] = n.a;
        outputs[9][row] = n.b;
        outputs[10][row] = n.c;
        outputs[11][row] = n.d;
        unsigned *slot = denominators + ((u64)2u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
