// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_b2w, digest 4f62318d703256eb46579091b96ca5a8e91e287c8a9202ec88935f8e3c3b4107.
// 14 lookups in 7 batches, 18 source columns, tuples up to 4 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_b510828ab6c80d1b(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)16u * rows + r_0];
    const unsigned v7 = sources[(u64)8u * rows + r_0];
    const unsigned v10 = sources[(u64)9u * rows + r_0];
    const unsigned v13 = sources[(u64)10u * rows + r_0];
    const unsigned v16 = sources[(u64)11u * rows + r_0];
    const unsigned v19 = sources[(u64)12u * rows + r_0];
    const unsigned v22 = sources[(u64)13u * rows + r_0];
    const unsigned v25 = sources[(u64)14u * rows + r_0];
    const unsigned v28 = sources[(u64)15u * rows + r_0];
    const unsigned v31 = sources[(u64)0u * rows + r_0];
    const unsigned v34 = sources[(u64)2u * rows + r_0];
    const unsigned v56 = sources[(u64)3u * rows + r_0];
    const unsigned v59 = 4u;
    const unsigned v60 = sources[(u64)1u * rows + r_0];
    const unsigned v61 = starked_mul(v59, v60);
    const unsigned v64 = pubs[320];
    const unsigned v65 = pubs[238];
    const unsigned v66 = starked_sub(v64, v65);
    const unsigned v85 = sources[(u64)17u * rows + r_0];
    const unsigned v108 = pubs[239];
    const unsigned v141 = sources[(u64)4u * rows + r_0];
    const unsigned v143 = sources[(u64)5u * rows + r_0];
    const unsigned v145 = sources[(u64)6u * rows + r_0];
    const unsigned v147 = sources[(u64)7u * rows + r_0];
    const unsigned v166 = starked_neg(v19);
    const unsigned v167 = 0u;
    const unsigned v168 = starked_add(v56, v167);
    const unsigned v169 = starked_neg(v22);
    const unsigned v170 = starked_add(v56, v1);
    const unsigned v171 = starked_neg(v25);
    const unsigned v172 = 2u;
    const unsigned v173 = starked_add(v56, v172);
    const unsigned v174 = starked_neg(v28);
    const unsigned v175 = 3u;
    const unsigned v176 = starked_add(v56, v175);
    const unsigned v177 = starked_sub(v7, v19);
    const unsigned v178 = starked_neg(v177);
    const unsigned v179 = starked_sub(v168, v108);
    const unsigned v180 = starked_sub(v10, v22);
    const unsigned v181 = starked_neg(v180);
    const unsigned v182 = starked_sub(v170, v108);
    const unsigned v183 = starked_sub(v13, v25);
    const unsigned v184 = starked_neg(v183);
    const unsigned v185 = starked_sub(v173, v108);
    const unsigned v186 = starked_sub(v16, v28);
    const unsigned v187 = starked_neg(v186);
    const unsigned v188 = starked_sub(v176, v108);
    const unsigned v189 = starked_mul(v4, v7);
    const unsigned v190 = starked_neg(v189);
    const unsigned v191 = starked_add(v61, v167);
    const unsigned v192 = starked_mul(v4, v10);
    const unsigned v193 = starked_neg(v192);
    const unsigned v194 = starked_add(v61, v1);
    const unsigned v195 = starked_mul(v4, v13);
    const unsigned v196 = starked_neg(v195);
    const unsigned v197 = starked_add(v61, v172);
    const unsigned v198 = starked_mul(v4, v16);
    const unsigned v199 = starked_neg(v198);
    const unsigned v200 = starked_add(v61, v175);
    const unsigned v201 = 256u;
    const unsigned v202 = starked_mul(v201, v143);
    const unsigned v203 = starked_add(v141, v202);
    const unsigned v204 = starked_mul(v201, v147);
    const unsigned v205 = starked_add(v145, v204);
    const unsigned v206 = starked_neg(v31);
    const unsigned v207 = starked_sub(v66, v1);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 26u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v168));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v141));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 26u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v170));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v143));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 26u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v173));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v145));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 26u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v176));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v147));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 3u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v179));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v141));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 3u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v182));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v143));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 3u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v185));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v145));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 3u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v188));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v147));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 27u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v191));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v141));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 27u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v194));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v143));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 27u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v197));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v145));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 27u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v200));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v147));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 30u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v34));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v60));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha3, v203));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha4, v205));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 31u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v207));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v166), starked_q_mul_base(d0, v169));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v171), starked_q_mul_base(d2, v174));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v178), starked_q_mul_base(d4, v181));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v184), starked_q_mul_base(d6, v187));
        const StarkedQm31 d = starked_q_mul(d6, d7);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[12][row] = n.a;
        outputs[13][row] = n.b;
        outputs[14][row] = n.c;
        outputs[15][row] = n.d;
        unsigned *slot = denominators + ((u64)3u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v190), starked_q_mul_base(d8, v193));
        const StarkedQm31 d = starked_q_mul(d8, d9);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[16][row] = n.a;
        outputs[17][row] = n.b;
        outputs[18][row] = n.c;
        outputs[19][row] = n.d;
        unsigned *slot = denominators + ((u64)4u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v196), starked_q_mul_base(d10, v199));
        const StarkedQm31 d = starked_q_mul(d10, d11);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[20][row] = n.a;
        outputs[21][row] = n.b;
        outputs[22][row] = n.c;
        outputs[23][row] = n.d;
        unsigned *slot = denominators + ((u64)5u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v85), starked_q_mul_base(d12, v206));
        const StarkedQm31 d = starked_q_mul(d12, d13);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[24][row] = n.a;
        outputs[25][row] = n.b;
        outputs[26][row] = n.c;
        outputs[27][row] = n.d;
        unsigned *slot = denominators + ((u64)6u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
