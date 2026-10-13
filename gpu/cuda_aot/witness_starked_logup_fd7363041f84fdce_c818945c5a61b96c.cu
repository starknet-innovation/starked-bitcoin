// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_ctx, digest f3c5aa620e580b60b2c905559b15c4301486d9515fc558a9fde6717ce340791b.
// 12 lookups in 6 batches, 40 source columns, tuples up to 17 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_fd7363041f84fdce(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v0 = sources[(u64)5u * rows + r_0];
    const unsigned v4 = sources[(u64)25u * rows + r_0];
    const unsigned v6 = sources[(u64)26u * rows + r_0];
    const unsigned v11 = sources[(u64)27u * rows + r_0];
    const unsigned v14 = sources[(u64)33u * rows + r_0];
    const unsigned v21 = sources[(u64)7u * rows + r_0];
    const unsigned v27 = sources[(u64)37u * rows + r_0];
    const unsigned v33 = sources[(u64)6u * rows + r_0];
    const unsigned v39 = 1u;
    const unsigned v48 = sources[(u64)8u * rows + r_0];
    const unsigned v82 = sources[(u64)9u * rows + r_0];
    const unsigned v86 = sources[(u64)10u * rows + r_0];
    const unsigned v90 = sources[(u64)11u * rows + r_0];
    const unsigned v94 = sources[(u64)12u * rows + r_0];
    const unsigned v98 = sources[(u64)13u * rows + r_0];
    const unsigned v102 = sources[(u64)14u * rows + r_0];
    const unsigned v106 = sources[(u64)15u * rows + r_0];
    const unsigned v110 = sources[(u64)16u * rows + r_0];
    const unsigned v114 = sources[(u64)17u * rows + r_0];
    const unsigned v118 = sources[(u64)18u * rows + r_0];
    const unsigned v122 = sources[(u64)19u * rows + r_0];
    const unsigned v126 = sources[(u64)20u * rows + r_0];
    const unsigned v130 = sources[(u64)21u * rows + r_0];
    const unsigned v134 = sources[(u64)22u * rows + r_0];
    const unsigned v138 = sources[(u64)23u * rows + r_0];
    const unsigned v142 = sources[(u64)24u * rows + r_0];
    const unsigned v145 = sources[(u64)0u * rows + r_0];
    const unsigned v219 = sources[(u64)34u * rows + r_0];
    const unsigned v232 = sources[(u64)29u * rows + r_0];
    const unsigned v239 = sources[(u64)32u * rows + r_0];
    const unsigned v252 = sources[(u64)28u * rows + r_0];
    const unsigned v259 = sources[(u64)30u * rows + r_0];
    const unsigned v263 = sources[(u64)31u * rows + r_0];
    const unsigned v276 = sources[(u64)35u * rows + r_0];
    const unsigned v280 = sources[(u64)36u * rows + r_0];
    const unsigned v299 = sources[(u64)38u * rows + r_0];
    const unsigned v332 = starked_neg(v21);
    const unsigned v333 = starked_neg(v39);
    const unsigned v334 = starked_neg(v145);
    const unsigned v335 = 0u;
    const unsigned v336 = starked_mul(v145, v263);
    const unsigned v337 = starked_neg(v336);
    const unsigned v338 = sources[(u64)39u * rows + r_0];
    const unsigned v339 = starked_mul(v145, v338);
    const unsigned v340 = 268435456u;
    const unsigned v341 = sources[(u64)2u * rows + r_0];
    const unsigned v342 = sources[(u64)1u * rows + r_0];
    const unsigned v343 = starked_sub(v341, v342);
    const unsigned v344 = starked_mul(v343, v27);
    const unsigned v345 = 268435457u;
    const unsigned v346 = starked_mul(v145, v27);
    const unsigned v347 = starked_neg(v346);
    const unsigned v348 = sources[(u64)4u * rows + r_0];
    const unsigned v349 = sources[(u64)3u * rows + r_0];
    const unsigned v350 = starked_sub(v348, v349);
    const unsigned v351 = starked_mul(v350, v27);
    const unsigned v352 = starked_neg(v351);
    const unsigned v353 = pubs[25];
    const unsigned v354 = pubs[26];
    const unsigned v355 = pubs[27];
    const unsigned v356 = pubs[28];
    const unsigned v357 = pubs[29];
    const unsigned v358 = pubs[30];
    const unsigned v359 = pubs[31];
    const unsigned v360 = pubs[32];
    const unsigned v361 = pubs[33];
    const unsigned v362 = pubs[34];
    const unsigned v363 = pubs[35];
    const unsigned v364 = pubs[36];
    const unsigned v365 = pubs[37];
    const unsigned v366 = pubs[38];
    const unsigned v367 = pubs[39];
    const unsigned v368 = pubs[40];
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
    d0.a = starked_add(d0.a, 3u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v0));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v33));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 9u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v48));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 4u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v335));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v4));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v6));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v11));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha5, v252));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 12u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v232));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v259));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v263));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 15u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v239));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 14u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v14));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v219));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 13u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v276));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v280));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 7u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v340));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha5, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha6, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha7, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha8, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha9, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha10, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha11, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha12, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha13, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha14, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha15, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha16, v335));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha17, v335));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 7u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v345));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v86));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha3, v82));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha4, v94));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha5, v90));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha6, v102));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha7, v98));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha8, v110));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha9, v106));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha10, v118));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha11, v114));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha12, v126));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha13, v122));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha14, v134));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha15, v130));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha16, v142));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha17, v138));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 16u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v299));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 7u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v299));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v86));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha3, v82));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha4, v94));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha5, v90));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha6, v102));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha7, v98));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha8, v110));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha9, v106));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha10, v118));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha11, v114));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha12, v126));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha13, v122));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha14, v134));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha15, v130));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha16, v142));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha17, v138));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 7u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v335));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v353));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha3, v354));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha4, v355));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha5, v356));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha6, v357));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha7, v358));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha8, v359));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha9, v360));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha10, v361));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha11, v362));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha12, v363));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha13, v364));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha14, v365));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha15, v366));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha16, v367));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha17, v368));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v332), starked_q_mul_base(d0, v333));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v334), starked_q_mul_base(d2, v334));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v334), starked_q_mul_base(d4, v337));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v145), starked_q_mul_base(d6, v339));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v344), starked_q_mul_base(d8, v347));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v352), starked_q_mul_base(d10, v334));
        const StarkedQm31 d = starked_q_mul(d10, d11);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[20][row] = n.a;
        outputs[21][row] = n.b;
        outputs[22][row] = n.c;
        outputs[23][row] = n.d;
        unsigned *slot = denominators + ((u64)5u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
