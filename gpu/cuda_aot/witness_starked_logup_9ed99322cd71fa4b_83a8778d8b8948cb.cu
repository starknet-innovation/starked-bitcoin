// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_fpwalk, digest 9f6211bfc3f082efc8c67241016f7a686a686f4a34667b033608b95d8423fe92.
// 4 lookups in 2 batches, 13 source columns, tuples up to 7 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_9ed99322cd71fa4b(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v0 = sources[(u64)0u * rows + r_0];
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)1u * rows + r_0];
    const unsigned v7 = sources[(u64)5u * rows + r_0];
    const unsigned v10 = sources[(u64)6u * rows + r_0];
    const unsigned v28 = sources[(u64)2u * rows + r_0];
    const unsigned v32 = sources[(u64)3u * rows + r_0];
    const unsigned v37 = sources[(u64)7u * rows + r_0];
    const unsigned v42 = sources[(u64)8u * rows + r_0];
    const unsigned v63 = sources[(u64)9u * rows + r_0];
    const unsigned v64 = sources[(u64)4u * rows + r_0];
    const unsigned v67 = sources[(u64)10u * rows + r_0];
    const unsigned v71 = sources[(u64)11u * rows + r_0];
    const unsigned v74 = sources[(u64)12u * rows + r_0];
    const unsigned v132 = starked_sub(v1, v4);
    const unsigned v133 = starked_mul(v0, v132);
    const unsigned v134 = starked_neg(v133);
    const unsigned v135 = starked_mul(v0, v4);
    const unsigned v136 = starked_neg(v135);
    const unsigned v137 = starked_neg(v7);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    const StarkedQm31 alpha5 = starked_q_load(powers + 20);
    const StarkedQm31 alpha6 = starked_q_load(powers + 24);
    const StarkedQm31 alpha7 = starked_q_load(powers + 28);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 3u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v32));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v64));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 17u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v32));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v64));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 21u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v4));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v28));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v32));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v37));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 22u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v4));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v28));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v42));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v63));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha5, v67));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha6, v71));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha7, v74));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v134), starked_q_mul_base(d0, v136));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v137), starked_q_mul_base(d2, v10));
        const StarkedQm31 d = starked_q_mul(d2, d3);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[4][row] = n.a;
        outputs[5][row] = n.b;
        outputs[6][row] = n.c;
        outputs[7][row] = n.d;
        unsigned *slot = denominators + ((u64)1u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
