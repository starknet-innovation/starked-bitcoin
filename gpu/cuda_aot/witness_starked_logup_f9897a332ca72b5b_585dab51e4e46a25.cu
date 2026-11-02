// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_lw, digest 2bb94628a1ca6ed077d33d76852dfae15cedbb3b78b1ddf115747f420c32f1df.
// 8 lookups in 4 batches, 19 source columns, tuples up to 5 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_f9897a332ca72b5b(
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
    const unsigned v7 = sources[(u64)15u * rows + r_0];
    const unsigned v13 = sources[(u64)18u * rows + r_0];
    const unsigned v16 = sources[(u64)9u * rows + r_0];
    const unsigned v19 = sources[(u64)10u * rows + r_0];
    const unsigned v22 = sources[(u64)11u * rows + r_0];
    const unsigned v25 = sources[(u64)12u * rows + r_0];
    const unsigned v41 = sources[(u64)1u * rows + r_0];
    const unsigned v63 = sources[(u64)3u * rows + r_0];
    const unsigned v71 = sources[(u64)16u * rows + r_0];
    const unsigned v75 = sources[(u64)17u * rows + r_0];
    const unsigned v79 = sources[(u64)4u * rows + r_0];
    const unsigned v117 = sources[(u64)14u * rows + r_0];
    const unsigned v120 = 64u;
    const unsigned v121 = starked_mul(v120, v79);
    const unsigned v126 = sources[(u64)5u * rows + r_0];
    const unsigned v128 = sources[(u64)6u * rows + r_0];
    const unsigned v131 = sources[(u64)7u * rows + r_0];
    const unsigned v134 = sources[(u64)8u * rows + r_0];
    const unsigned v144 = starked_neg(v13);
    const unsigned v145 = sources[(u64)0u * rows + r_0];
    const unsigned v146 = 256u;
    const unsigned v147 = starked_mul(v146, v128);
    const unsigned v148 = starked_add(v126, v147);
    const unsigned v149 = starked_mul(v146, v134);
    const unsigned v150 = starked_add(v131, v149);
    const unsigned v151 = starked_neg(v7);
    const unsigned v152 = 85u;
    const unsigned v153 = starked_sub(v75, v152);
    const unsigned v154 = starked_sub(v1, v13);
    const unsigned v155 = starked_mul(v16, v154);
    const unsigned v156 = starked_neg(v155);
    const unsigned v157 = starked_add(v71, v121);
    const unsigned v158 = 4u;
    const unsigned v159 = starked_mul(v158, v145);
    const unsigned v160 = 0u;
    const unsigned v161 = starked_add(v159, v160);
    const unsigned v162 = starked_add(v157, v161);
    const unsigned v163 = 36u;
    const unsigned v164 = starked_sub(v162, v163);
    const unsigned v165 = starked_mul(v19, v154);
    const unsigned v166 = starked_neg(v165);
    const unsigned v167 = starked_add(v159, v1);
    const unsigned v168 = starked_add(v157, v167);
    const unsigned v169 = starked_sub(v168, v163);
    const unsigned v170 = starked_mul(v22, v154);
    const unsigned v171 = starked_neg(v170);
    const unsigned v172 = 2u;
    const unsigned v173 = starked_add(v159, v172);
    const unsigned v174 = starked_add(v157, v173);
    const unsigned v175 = starked_sub(v174, v163);
    const unsigned v176 = starked_mul(v25, v154);
    const unsigned v177 = starked_neg(v176);
    const unsigned v178 = 3u;
    const unsigned v179 = starked_add(v159, v178);
    const unsigned v180 = starked_add(v157, v179);
    const unsigned v181 = starked_sub(v180, v163);
    const unsigned v182 = starked_mul(v0, v41);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    const StarkedQm31 alpha5 = starked_q_load(powers + 20);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 36u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v63));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v145));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha3, v148));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha4, v150));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 32u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v63));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v71));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha3, v153));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 3u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v164));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v126));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 3u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v169));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v128));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 3u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v175));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v131));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 3u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v181));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v134));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 37u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v63));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v79));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha3, v145));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha4, v148));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha5, v150));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 38u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v63));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v79));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v4));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v117));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v144), starked_q_mul_base(d0, v151));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v156), starked_q_mul_base(d2, v166));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v171), starked_q_mul_base(d4, v177));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v0), starked_q_mul_base(d6, v182));
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
