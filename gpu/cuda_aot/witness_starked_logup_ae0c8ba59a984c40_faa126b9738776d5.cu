// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_tmsg, digest 037f8922078d48ced14ab12dbbc470084a5cfef06c1d44afe05722ae94561d1d.
// 8 lookups in 4 batches, 16 source columns, tuples up to 3 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_ae0c8ba59a984c40(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_m3 = starked_storage_row((natural + 4294967293u) & (rows - 1u), log_size);
    const u64 r_m2 = starked_storage_row((natural + 4294967294u) & (rows - 1u), log_size);
    const u64 r_m1 = starked_storage_row((natural + 4294967295u) & (rows - 1u), log_size);
    const u64 r_0 = row;
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)5u * rows + r_0];
    const unsigned v7 = sources[(u64)6u * rows + r_0];
    const unsigned v10 = sources[(u64)7u * rows + r_0];
    const unsigned v13 = sources[(u64)8u * rows + r_0];
    const unsigned v16 = sources[(u64)9u * rows + r_0];
    const unsigned v22 = sources[(u64)14u * rows + r_0];
    const unsigned v29 = sources[(u64)0u * rows + r_0];
    const unsigned v40 = sources[(u64)3u * rows + r_0];
    const unsigned v71 = sources[(u64)11u * rows + r_0];
    const unsigned v73 = sources[(u64)10u * rows + r_0];
    const unsigned v82 = sources[(u64)12u * rows + r_0];
    const unsigned v86 = sources[(u64)13u * rows + r_0];
    const unsigned v139 = sources[(u64)15u * rows + r_0];
    const unsigned v152 = sources[(u64)2u * rows + r_0];
    const unsigned v157 = pubs[484];
    const unsigned v158 = pubs[402];
    const unsigned v159 = starked_sub(v157, v158);
    const unsigned v170 = starked_neg(v4);
    const unsigned v171 = sources[(u64)4u * rows + r_0];
    const unsigned v172 = starked_neg(v7);
    const unsigned v173 = starked_add(v82, v71);
    const unsigned v174 = starked_neg(v10);
    const unsigned v175 = 36u;
    const unsigned v176 = starked_sub(v71, v175);
    const unsigned v177 = starked_neg(v13);
    const unsigned v178 = 9u;
    const unsigned v179 = starked_add(v173, v178);
    const unsigned v180 = starked_neg(v16);
    const unsigned v181 = starked_neg(v22);
    const unsigned v182 = sources[(u64)1u * rows + r_0];
    const unsigned v183 = starked_mul(v139, v182);
    const unsigned v184 = 3u;
    const unsigned v185 = starked_sub(v40, v184);
    const unsigned v186 = 256u;
    const unsigned v187 = sources[(u64)4u * rows + r_m1];
    const unsigned v188 = starked_mul(v186, v187);
    const unsigned v189 = starked_add(v188, v171);
    const unsigned v190 = sources[(u64)4u * rows + r_m3];
    const unsigned v191 = starked_mul(v186, v190);
    const unsigned v192 = sources[(u64)4u * rows + r_m2];
    const unsigned v193 = starked_add(v191, v192);
    const unsigned v194 = starked_neg(v29);
    const unsigned v195 = starked_sub(v159, v1);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 28u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v40));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v171));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 3u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v173));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v171));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 33u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v73));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v176));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v171));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 3u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v179));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v171));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 32u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v73));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v82));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha3, v86));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 29u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v152));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v171));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 34u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v185));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v189));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha3, v193));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 35u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v195));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v170), starked_q_mul_base(d0, v172));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v174), starked_q_mul_base(d2, v177));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v180), starked_q_mul_base(d4, v181));
        const StarkedQm31 d = starked_q_mul(d4, d5);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[8][row] = n.a;
        outputs[9][row] = n.b;
        outputs[10][row] = n.c;
        outputs[11][row] = n.d;
        unsigned *slot = denominators + ((u64)2u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v183), starked_q_mul_base(d6, v194));
        const StarkedQm31 d = starked_q_mul(d6, d7);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[12][row] = n.a;
        outputs[13][row] = n.b;
        outputs[14][row] = n.c;
        outputs[15][row] = n.d;
        unsigned *slot = denominators + ((u64)3u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
