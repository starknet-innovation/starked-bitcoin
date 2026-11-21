// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_urec, digest 8d09e4ef561ecaec82db72dca70dce9de6aa9764fe9125c301af7c6867cd540e.
// 28 lookups in 14 batches, 37 source columns, tuples up to 11 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_fd9d43fbc488fc00(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v0 = sources[(u64)1u * rows + r_0];
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)0u * rows + r_0];
    const unsigned v13 = sources[(u64)2u * rows + r_0];
    const unsigned v20 = sources[(u64)3u * rows + r_0];
    const unsigned v24 = 9u;
    const unsigned v28 = 4u;
    const unsigned v36 = starked_add(v20, v24);
    const unsigned v37 = sources[(u64)4u * rows + r_0];
    const unsigned v38 = starked_add(v36, v37);
    const unsigned v47 = sources[(u64)20u * rows + r_0];
    const unsigned v48 = 256u;
    const unsigned v49 = sources[(u64)21u * rows + r_0];
    const unsigned v54 = sources[(u64)26u * rows + r_0];
    const unsigned v57 = sources[(u64)22u * rows + r_0];
    const unsigned v66 = sources[(u64)27u * rows + r_0];
    const unsigned v77 = sources[(u64)28u * rows + r_0];
    const unsigned v91 = sources[(u64)23u * rows + r_0];
    const unsigned v95 = sources[(u64)24u * rows + r_0];
    const unsigned v111 = sources[(u64)29u * rows + r_0];
    const unsigned v117 = sources[(u64)25u * rows + r_0];
    const unsigned v126 = sources[(u64)30u * rows + r_0];
    const unsigned v129 = sources[(u64)31u * rows + r_0];
    const unsigned v132 = sources[(u64)32u * rows + r_0];
    const unsigned v135 = starked_neg(v4);
    const unsigned v136 = 0u;
    const unsigned v137 = starked_neg(v0);
    const unsigned v138 = starked_add(v20, v136);
    const unsigned v139 = sources[(u64)5u * rows + r_0];
    const unsigned v140 = starked_add(v20, v1);
    const unsigned v141 = sources[(u64)6u * rows + r_0];
    const unsigned v142 = 2u;
    const unsigned v143 = starked_add(v20, v142);
    const unsigned v144 = sources[(u64)7u * rows + r_0];
    const unsigned v145 = 3u;
    const unsigned v146 = starked_add(v20, v145);
    const unsigned v147 = sources[(u64)8u * rows + r_0];
    const unsigned v148 = sources[(u64)9u * rows + r_0];
    const unsigned v149 = 10u;
    const unsigned v150 = starked_add(v20, v149);
    const unsigned v151 = sources[(u64)10u * rows + r_0];
    const unsigned v152 = 11u;
    const unsigned v153 = starked_add(v20, v152);
    const unsigned v154 = sources[(u64)11u * rows + r_0];
    const unsigned v155 = 12u;
    const unsigned v156 = starked_add(v20, v155);
    const unsigned v157 = sources[(u64)12u * rows + r_0];
    const unsigned v158 = 13u;
    const unsigned v159 = starked_add(v20, v158);
    const unsigned v160 = sources[(u64)13u * rows + r_0];
    const unsigned v161 = 14u;
    const unsigned v162 = starked_add(v20, v161);
    const unsigned v163 = sources[(u64)14u * rows + r_0];
    const unsigned v164 = 15u;
    const unsigned v165 = starked_add(v20, v164);
    const unsigned v166 = sources[(u64)15u * rows + r_0];
    const unsigned v167 = 16u;
    const unsigned v168 = starked_add(v20, v167);
    const unsigned v169 = sources[(u64)16u * rows + r_0];
    const unsigned v170 = starked_add(v20, v28);
    const unsigned v171 = sources[(u64)17u * rows + r_0];
    const unsigned v172 = 5u;
    const unsigned v173 = starked_add(v20, v172);
    const unsigned v174 = sources[(u64)18u * rows + r_0];
    const unsigned v175 = 6u;
    const unsigned v176 = starked_add(v20, v175);
    const unsigned v177 = sources[(u64)19u * rows + r_0];
    const unsigned v178 = 7u;
    const unsigned v179 = starked_add(v20, v178);
    const unsigned v180 = 8u;
    const unsigned v181 = starked_add(v20, v180);
    const unsigned v182 = starked_mul(v48, v141);
    const unsigned v183 = starked_add(v139, v182);
    const unsigned v184 = starked_mul(v48, v147);
    const unsigned v185 = starked_add(v144, v184);
    const unsigned v186 = starked_mul(v48, v151);
    const unsigned v187 = starked_add(v148, v186);
    const unsigned v188 = 65536u;
    const unsigned v189 = starked_mul(v188, v154);
    const unsigned v190 = starked_add(v187, v189);
    const unsigned v191 = starked_mul(v48, v160);
    const unsigned v192 = starked_add(v157, v191);
    const unsigned v193 = starked_mul(v188, v163);
    const unsigned v194 = starked_add(v192, v193);
    const unsigned v195 = 16777216u;
    const unsigned v196 = starked_mul(v195, v166);
    const unsigned v197 = starked_add(v194, v196);
    const unsigned v198 = starked_mul(v48, v174);
    const unsigned v199 = starked_add(v171, v198);
    const unsigned v200 = starked_mul(v188, v177);
    const unsigned v201 = starked_add(v199, v200);
    const unsigned v202 = sources[(u64)33u * rows + r_0];
    const unsigned v203 = sources[(u64)34u * rows + r_0];
    const unsigned v204 = starked_mul(v48, v203);
    const unsigned v205 = starked_add(v202, v204);
    const unsigned v206 = sources[(u64)35u * rows + r_0];
    const unsigned v207 = sources[(u64)36u * rows + r_0];
    const unsigned v208 = starked_mul(v48, v207);
    const unsigned v209 = starked_add(v206, v208);
    const unsigned v210 = 17u;
    const unsigned v211 = starked_add(v20, v210);
    const unsigned v212 = starked_add(v66, v77);
    const unsigned v213 = starked_add(v54, v212);
    const unsigned v214 = starked_mul(v0, v213);
    const unsigned v215 = starked_neg(v214);
    const unsigned v216 = 18u;
    const unsigned v217 = starked_add(v20, v216);
    const unsigned v218 = 19u;
    const unsigned v219 = starked_add(v20, v218);
    const unsigned v220 = starked_mul(v0, v111);
    const unsigned v221 = starked_neg(v220);
    const unsigned v222 = 40u;
    const unsigned v223 = starked_add(v20, v222);
    const unsigned v224 = starked_add(v150, v37);
    const unsigned v225 = starked_add(v153, v37);
    const unsigned v226 = starked_add(v156, v37);
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
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 17u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v136));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v1));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 17u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v138));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v139));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 17u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v140));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v141));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 17u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v143));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v144));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 17u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v146));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v147));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 17u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v36));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v148));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 17u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v150));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v151));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 17u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v153));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v154));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 17u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v156));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v157));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 17u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v159));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v160));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 17u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v162));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v163));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 17u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v165));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v166));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 17u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v168));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v169));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 17u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v170));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v171));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 17u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v173));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v174));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 17u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v176));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v177));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 17u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v179));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v47));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 17u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v181));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v49));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 21u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v1));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha2, v13));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha3, v36));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha4, v37));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 23u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v13));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha2, v183));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha3, v185));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha4, v190));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha5, v197));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha6, v201));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha7, v126));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha8, v129));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha9, v132));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha10, v205));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha11, v209));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 17u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v211));
    d20 = starked_q_add(d20, starked_q_mul_base(alpha2, v57));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 17u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v217));
    d21 = starked_q_add(d21, starked_q_mul_base(alpha2, v91));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 17u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v219));
    d22 = starked_q_add(d22, starked_q_mul_base(alpha2, v95));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 17u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v223));
    d23 = starked_q_add(d23, starked_q_mul_base(alpha2, v117));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 17u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v38));
    d24 = starked_q_add(d24, starked_q_mul_base(alpha2, v202));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 17u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v224));
    d25 = starked_q_add(d25, starked_q_mul_base(alpha2, v203));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 17u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v225));
    d26 = starked_q_add(d26, starked_q_mul_base(alpha2, v206));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 17u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v226));
    d27 = starked_q_add(d27, starked_q_mul_base(alpha2, v207));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v135), starked_q_mul_base(d0, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v137), starked_q_mul_base(d2, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v137), starked_q_mul_base(d4, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v137), starked_q_mul_base(d6, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v137), starked_q_mul_base(d8, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v137), starked_q_mul_base(d10, v137));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v137), starked_q_mul_base(d12, v137));
        const StarkedQm31 d = starked_q_mul(d12, d13);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[24][row] = n.a;
        outputs[25][row] = n.b;
        outputs[26][row] = n.c;
        outputs[27][row] = n.d;
        unsigned *slot = denominators + ((u64)6u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v137), starked_q_mul_base(d14, v137));
        const StarkedQm31 d = starked_q_mul(d14, d15);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[28][row] = n.a;
        outputs[29][row] = n.b;
        outputs[30][row] = n.c;
        outputs[31][row] = n.d;
        unsigned *slot = denominators + ((u64)7u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v137), starked_q_mul_base(d16, v137));
        const StarkedQm31 d = starked_q_mul(d16, d17);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[32][row] = n.a;
        outputs[33][row] = n.b;
        outputs[34][row] = n.c;
        outputs[35][row] = n.d;
        unsigned *slot = denominators + ((u64)8u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v0), starked_q_mul_base(d18, v0));
        const StarkedQm31 d = starked_q_mul(d18, d19);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[36][row] = n.a;
        outputs[37][row] = n.b;
        outputs[38][row] = n.c;
        outputs[39][row] = n.d;
        unsigned *slot = denominators + ((u64)9u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v137), starked_q_mul_base(d20, v215));
        const StarkedQm31 d = starked_q_mul(d20, d21);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[40][row] = n.a;
        outputs[41][row] = n.b;
        outputs[42][row] = n.c;
        outputs[43][row] = n.d;
        unsigned *slot = denominators + ((u64)10u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v215), starked_q_mul_base(d22, v221));
        const StarkedQm31 d = starked_q_mul(d22, d23);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[44][row] = n.a;
        outputs[45][row] = n.b;
        outputs[46][row] = n.c;
        outputs[47][row] = n.d;
        unsigned *slot = denominators + ((u64)11u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v137), starked_q_mul_base(d24, v137));
        const StarkedQm31 d = starked_q_mul(d24, d25);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[48][row] = n.a;
        outputs[49][row] = n.b;
        outputs[50][row] = n.c;
        outputs[51][row] = n.d;
        unsigned *slot = denominators + ((u64)12u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v137), starked_q_mul_base(d26, v137));
        const StarkedQm31 d = starked_q_mul(d26, d27);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[52][row] = n.a;
        outputs[53][row] = n.b;
        outputs[54][row] = n.c;
        outputs[55][row] = n.d;
        unsigned *slot = denominators + ((u64)13u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
