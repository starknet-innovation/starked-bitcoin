// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_merkle, digest 06b584f2c7bf0e9948fc5906dcff1ff22988c89f396bf37738c8f24af9b72244.
// 11 lookups in 6 batches, 25 source columns, tuples up to 17 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_01e2084e1dfdb54c(
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
    const unsigned v4 = sources[(u64)1u * rows + r_0];
    const unsigned v71 = sources[(u64)2u * rows + r_0];
    const unsigned v126 = sources[(u64)5u * rows + r_0];
    const unsigned v129 = sources[(u64)3u * rows + r_0];
    const unsigned v135 = 134217728u;
    const unsigned v142 = sources[(u64)4u * rows + r_0];
    const unsigned v148 = sources[(u64)8u * rows + r_0];
    const unsigned v150 = starked_add(v135, v71);
    const unsigned v157 = sources[(u64)6u * rows + r_0];
    const unsigned v158 = starked_mul(v0, v157);
    const unsigned v159 = sources[(u64)7u * rows + r_0];
    const unsigned v160 = starked_mul(v0, v159);
    const unsigned v161 = 128u;
    const unsigned v162 = starked_neg(v4);
    const unsigned v163 = sources[(u64)9u * rows + r_0];
    const unsigned v164 = sources[(u64)10u * rows + r_0];
    const unsigned v165 = sources[(u64)11u * rows + r_0];
    const unsigned v166 = sources[(u64)12u * rows + r_0];
    const unsigned v167 = sources[(u64)13u * rows + r_0];
    const unsigned v168 = sources[(u64)14u * rows + r_0];
    const unsigned v169 = sources[(u64)15u * rows + r_0];
    const unsigned v170 = sources[(u64)16u * rows + r_0];
    const unsigned v171 = sources[(u64)17u * rows + r_0];
    const unsigned v172 = sources[(u64)18u * rows + r_0];
    const unsigned v173 = sources[(u64)19u * rows + r_0];
    const unsigned v174 = sources[(u64)20u * rows + r_0];
    const unsigned v175 = sources[(u64)21u * rows + r_0];
    const unsigned v176 = sources[(u64)22u * rows + r_0];
    const unsigned v177 = sources[(u64)23u * rows + r_0];
    const unsigned v178 = sources[(u64)24u * rows + r_0];
    const unsigned v179 = 0u;
    const unsigned v180 = 36u;
    const unsigned v181 = 40u;
    const unsigned v182 = 44u;
    const unsigned v183 = 48u;
    const unsigned v184 = 52u;
    const unsigned v185 = 56u;
    const unsigned v186 = 60u;
    const unsigned v187 = 64u;
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    const StarkedQm31 alpha5 = starked_q_load(powers + 20);
    const StarkedQm31 alpha6 = starked_q_load(powers + 24);
    const StarkedQm31 alpha7 = starked_q_load(powers + 28);
    const StarkedQm31 alpha8 = starked_q_load(powers + 32);
    const StarkedQm31 alpha9 = starked_q_load(powers + 36);
    const StarkedQm31 alpha10 = starked_q_load(powers + 40);
    const StarkedQm31 alpha11 = starked_q_load(powers + 44);
    const StarkedQm31 alpha12 = starked_q_load(powers + 48);
    const StarkedQm31 alpha13 = starked_q_load(powers + 52);
    const StarkedQm31 alpha14 = starked_q_load(powers + 56);
    const StarkedQm31 alpha15 = starked_q_load(powers + 60);
    const StarkedQm31 alpha16 = starked_q_load(powers + 64);
    const StarkedQm31 alpha17 = starked_q_load(powers + 68);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 8u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v150));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v129));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha3, v142));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha4, v126));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 6u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v150));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v161));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 7u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v148));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v163));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v164));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v165));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha5, v166));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha6, v167));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha7, v168));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha8, v169));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha9, v170));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha10, v171));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha11, v172));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha12, v173));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha13, v174));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha14, v175));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha15, v176));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha16, v177));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha17, v178));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 5u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v179));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v180));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v163));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v164));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 5u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v179));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v181));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha3, v165));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha4, v166));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 5u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v179));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v182));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha3, v167));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha4, v168));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 5u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v179));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v183));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha3, v169));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha4, v170));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 5u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v179));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v184));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v171));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v172));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 5u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v179));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v185));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha3, v173));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha4, v174));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 5u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v179));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v186));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha3, v175));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha4, v176));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 5u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v179));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v187));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha3, v177));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha4, v178));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v158), starked_q_mul_base(d0, v160));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v162), starked_q_mul_base(d2, v162));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v162), starked_q_mul_base(d4, v162));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v162), starked_q_mul_base(d6, v162));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v162), starked_q_mul_base(d8, v162));
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
        const StarkedQm31 n = {v162, 0u, 0u, 0u};
        const StarkedQm31 d = d10;
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[20][row] = n.a;
        outputs[21][row] = n.b;
        outputs[22][row] = n.c;
        outputs[23][row] = n.d;
        unsigned *slot = denominators + ((u64)5u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
