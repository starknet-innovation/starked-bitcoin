// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_ctx, digest 41d0d30ece6d2366593b6a5f7cf3841c0b9dffc726409a4ef87c294466221e70.
// 12 lookups in 6 batches, 42 source columns, tuples up to 17 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_c502e930afcedfe3(
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
    const unsigned v242 = sources[(u64)32u * rows + r_0];
    const unsigned v245 = sources[(u64)40u * rows + r_0];
    const unsigned v247 = sources[(u64)41u * rows + r_0];
    const unsigned v260 = sources[(u64)28u * rows + r_0];
    const unsigned v267 = sources[(u64)30u * rows + r_0];
    const unsigned v271 = sources[(u64)31u * rows + r_0];
    const unsigned v284 = sources[(u64)35u * rows + r_0];
    const unsigned v288 = sources[(u64)36u * rows + r_0];
    const unsigned v307 = sources[(u64)38u * rows + r_0];
    const unsigned v348 = starked_neg(v21);
    const unsigned v349 = starked_neg(v39);
    const unsigned v350 = starked_neg(v145);
    const unsigned v351 = 0u;
    const unsigned v352 = starked_mul(v145, v271);
    const unsigned v353 = starked_neg(v352);
    const unsigned v354 = sources[(u64)39u * rows + r_0];
    const unsigned v355 = starked_mul(v145, v354);
    const unsigned v356 = 268435456u;
    const unsigned v357 = sources[(u64)2u * rows + r_0];
    const unsigned v358 = sources[(u64)1u * rows + r_0];
    const unsigned v359 = starked_sub(v357, v358);
    const unsigned v360 = starked_mul(v359, v27);
    const unsigned v361 = 268435457u;
    const unsigned v362 = starked_mul(v145, v27);
    const unsigned v363 = starked_neg(v362);
    const unsigned v364 = sources[(u64)4u * rows + r_0];
    const unsigned v365 = sources[(u64)3u * rows + r_0];
    const unsigned v366 = starked_sub(v364, v365);
    const unsigned v367 = starked_mul(v366, v27);
    const unsigned v368 = starked_neg(v367);
    const unsigned v369 = pubs[25];
    const unsigned v370 = pubs[26];
    const unsigned v371 = pubs[27];
    const unsigned v372 = pubs[28];
    const unsigned v373 = pubs[29];
    const unsigned v374 = pubs[30];
    const unsigned v375 = pubs[31];
    const unsigned v376 = pubs[32];
    const unsigned v377 = pubs[33];
    const unsigned v378 = pubs[34];
    const unsigned v379 = pubs[35];
    const unsigned v380 = pubs[36];
    const unsigned v381 = pubs[37];
    const unsigned v382 = pubs[38];
    const unsigned v383 = pubs[39];
    const unsigned v384 = pubs[40];
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
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v351));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v4));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v6));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v11));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha5, v260));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 12u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v232));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v267));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v271));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v247));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 15u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v242));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v245));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 14u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v14));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v219));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 13u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v284));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v288));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 7u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v356));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha5, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha6, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha7, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha8, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha9, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha10, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha11, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha12, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha13, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha14, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha15, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha16, v351));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha17, v351));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 7u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v361));
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
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v307));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 7u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v307));
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
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v351));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v369));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha3, v370));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha4, v371));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha5, v372));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha6, v373));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha7, v374));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha8, v375));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha9, v376));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha10, v377));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha11, v378));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha12, v379));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha13, v380));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha14, v381));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha15, v382));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha16, v383));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha17, v384));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v348), starked_q_mul_base(d0, v349));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v350), starked_q_mul_base(d2, v350));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v350), starked_q_mul_base(d4, v353));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v145), starked_q_mul_base(d6, v355));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v360), starked_q_mul_base(d8, v363));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v368), starked_q_mul_base(d10, v350));
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
