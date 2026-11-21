// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_coin, digest 682beb1805721a2beff94a960f339552371911fd585405b0348fbde81de73cf7.
// 104 lookups in 52 batches, 147 source columns, tuples up to 17 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_dfcdc2f61371b201(
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
    const unsigned v4 = sources[(u64)2u * rows + r_0];
    const unsigned v7 = sources[(u64)3u * rows + r_0];
    const unsigned v10 = sources[(u64)72u * rows + r_0];
    const unsigned v22 = sources[(u64)89u * rows + r_0];
    const unsigned v25 = starked_add(v0, v4);
    const unsigned v26 = starked_add(v25, v7);
    const unsigned v29 = sources[(u64)0u * rows + r_0];
    const unsigned v30 = starked_sub(v1, v29);
    const unsigned v42 = sources[(u64)5u * rows + r_0];
    const unsigned v46 = sources[(u64)9u * rows + r_0];
    const unsigned v48 = sources[(u64)10u * rows + r_0];
    const unsigned v52 = sources[(u64)11u * rows + r_0];
    const unsigned v59 = sources[(u64)4u * rows + r_0];
    const unsigned v68 = sources[(u64)15u * rows + r_0];
    const unsigned v81 = sources[(u64)12u * rows + r_0];
    const unsigned v86 = sources[(u64)13u * rows + r_0];
    const unsigned v87 = sources[(u64)14u * rows + r_0];
    const unsigned v92 = sources[(u64)48u * rows + r_0];
    const unsigned v93 = sources[(u64)49u * rows + r_0];
    const unsigned v98 = sources[(u64)50u * rows + r_0];
    const unsigned v99 = sources[(u64)51u * rows + r_0];
    const unsigned v104 = sources[(u64)68u * rows + r_0];
    const unsigned v105 = sources[(u64)69u * rows + r_0];
    const unsigned v108 = 2u;
    const unsigned v114 = sources[(u64)70u * rows + r_0];
    const unsigned v115 = sources[(u64)71u * rows + r_0];
    const unsigned v120 = sources[(u64)76u * rows + r_0];
    const unsigned v123 = sources[(u64)87u * rows + r_0];
    const unsigned v124 = sources[(u64)6u * rows + r_0];
    const unsigned v132 = sources[(u64)73u * rows + r_0];
    const unsigned v133 = sources[(u64)74u * rows + r_0];
    const unsigned v136 = sources[(u64)75u * rows + r_0];
    const unsigned v145 = sources[(u64)77u * rows + r_0];
    const unsigned v146 = sources[(u64)78u * rows + r_0];
    const unsigned v149 = sources[(u64)79u * rows + r_0];
    const unsigned v164 = sources[(u64)80u * rows + r_0];
    const unsigned v165 = sources[(u64)81u * rows + r_0];
    const unsigned v168 = sources[(u64)82u * rows + r_0];
    const unsigned v174 = sources[(u64)8u * rows + r_0];
    const unsigned v181 = sources[(u64)88u * rows + r_0];
    const unsigned v189 = starked_sub(v1, v22);
    const unsigned v192 = sources[(u64)90u * rows + r_0];
    const unsigned v193 = sources[(u64)91u * rows + r_0];
    const unsigned v196 = sources[(u64)92u * rows + r_0];
    const unsigned v237 = sources[(u64)93u * rows + r_0];
    const unsigned v242 = sources[(u64)52u * rows + r_0];
    const unsigned v243 = sources[(u64)19u * rows + r_0];
    const unsigned v244 = sources[(u64)18u * rows + r_0];
    const unsigned v249 = sources[(u64)53u * rows + r_0];
    const unsigned v250 = sources[(u64)17u * rows + r_0];
    const unsigned v251 = sources[(u64)16u * rows + r_0];
    const unsigned v256 = sources[(u64)54u * rows + r_0];
    const unsigned v257 = sources[(u64)23u * rows + r_0];
    const unsigned v258 = sources[(u64)22u * rows + r_0];
    const unsigned v263 = sources[(u64)55u * rows + r_0];
    const unsigned v264 = sources[(u64)21u * rows + r_0];
    const unsigned v265 = sources[(u64)20u * rows + r_0];
    const unsigned v270 = sources[(u64)56u * rows + r_0];
    const unsigned v271 = sources[(u64)27u * rows + r_0];
    const unsigned v272 = sources[(u64)26u * rows + r_0];
    const unsigned v277 = sources[(u64)57u * rows + r_0];
    const unsigned v278 = sources[(u64)25u * rows + r_0];
    const unsigned v279 = sources[(u64)24u * rows + r_0];
    const unsigned v284 = sources[(u64)58u * rows + r_0];
    const unsigned v285 = sources[(u64)31u * rows + r_0];
    const unsigned v286 = sources[(u64)30u * rows + r_0];
    const unsigned v291 = sources[(u64)59u * rows + r_0];
    const unsigned v292 = sources[(u64)29u * rows + r_0];
    const unsigned v293 = sources[(u64)28u * rows + r_0];
    const unsigned v298 = sources[(u64)60u * rows + r_0];
    const unsigned v299 = sources[(u64)35u * rows + r_0];
    const unsigned v300 = sources[(u64)34u * rows + r_0];
    const unsigned v305 = sources[(u64)61u * rows + r_0];
    const unsigned v306 = sources[(u64)33u * rows + r_0];
    const unsigned v307 = sources[(u64)32u * rows + r_0];
    const unsigned v312 = sources[(u64)62u * rows + r_0];
    const unsigned v313 = sources[(u64)39u * rows + r_0];
    const unsigned v314 = sources[(u64)38u * rows + r_0];
    const unsigned v319 = sources[(u64)63u * rows + r_0];
    const unsigned v320 = sources[(u64)37u * rows + r_0];
    const unsigned v321 = sources[(u64)36u * rows + r_0];
    const unsigned v326 = sources[(u64)64u * rows + r_0];
    const unsigned v327 = sources[(u64)43u * rows + r_0];
    const unsigned v328 = sources[(u64)42u * rows + r_0];
    const unsigned v333 = sources[(u64)65u * rows + r_0];
    const unsigned v334 = sources[(u64)41u * rows + r_0];
    const unsigned v335 = sources[(u64)40u * rows + r_0];
    const unsigned v340 = sources[(u64)66u * rows + r_0];
    const unsigned v341 = sources[(u64)47u * rows + r_0];
    const unsigned v342 = sources[(u64)46u * rows + r_0];
    const unsigned v347 = sources[(u64)67u * rows + r_0];
    const unsigned v348 = sources[(u64)45u * rows + r_0];
    const unsigned v349 = sources[(u64)44u * rows + r_0];
    const unsigned v355 = 0u;
    const unsigned v677 = sources[(u64)83u * rows + r_0];
    const unsigned v694 = sources[(u64)84u * rows + r_0];
    const unsigned v711 = sources[(u64)85u * rows + r_0];
    const unsigned v728 = sources[(u64)86u * rows + r_0];
    const unsigned v1399 = sources[(u64)116u * rows + r_0];
    const unsigned v1402 = sources[(u64)117u * rows + r_0];
    const unsigned v1405 = sources[(u64)118u * rows + r_0];
    const unsigned v1421 = sources[(u64)94u * rows + r_0];
    const unsigned v1428 = sources[(u64)95u * rows + r_0];
    const unsigned v1433 = sources[(u64)103u * rows + r_0];
    const unsigned v1434 = sources[(u64)104u * rows + r_0];
    const unsigned v1437 = sources[(u64)105u * rows + r_0];
    const unsigned v1442 = sources[(u64)96u * rows + r_0];
    const unsigned v1443 = sources[(u64)97u * rows + r_0];
    const unsigned v1446 = sources[(u64)98u * rows + r_0];
    const unsigned v1455 = sources[(u64)99u * rows + r_0];
    const unsigned v1456 = sources[(u64)100u * rows + r_0];
    const unsigned v1459 = sources[(u64)101u * rows + r_0];
    const unsigned v1462 = sources[(u64)102u * rows + r_0];
    const unsigned v1516 = sources[(u64)106u * rows + r_0];
    const unsigned v1517 = sources[(u64)107u * rows + r_0];
    const unsigned v1520 = sources[(u64)108u * rows + r_0];
    const unsigned v1537 = sources[(u64)109u * rows + r_0];
    const unsigned v1538 = sources[(u64)110u * rows + r_0];
    const unsigned v1541 = sources[(u64)111u * rows + r_0];
    const unsigned v1552 = sources[(u64)112u * rows + r_0];
    const unsigned v1553 = sources[(u64)113u * rows + r_0];
    const unsigned v1556 = sources[(u64)114u * rows + r_0];
    const unsigned v1559 = sources[(u64)115u * rows + r_0];
    const unsigned v1569 = sources[(u64)119u * rows + r_0];
    const unsigned v1570 = 7u;
    const unsigned v1573 = sources[(u64)120u * rows + r_0];
    const unsigned v1579 = sources[(u64)121u * rows + r_0];
    const unsigned v1580 = sources[(u64)122u * rows + r_0];
    const unsigned v1583 = sources[(u64)123u * rows + r_0];
    const unsigned v1591 = sources[(u64)124u * rows + r_0];
    const unsigned v1592 = sources[(u64)125u * rows + r_0];
    const unsigned v1595 = sources[(u64)126u * rows + r_0];
    const unsigned v1598 = sources[(u64)127u * rows + r_0];
    const unsigned v1605 = sources[(u64)128u * rows + r_0];
    const unsigned v1608 = sources[(u64)130u * rows + r_0];
    const unsigned v1611 = sources[(u64)129u * rows + r_0];
    const unsigned v1613 = sources[(u64)132u * rows + r_0];
    const unsigned v1614 = sources[(u64)133u * rows + r_0];
    const unsigned v1617 = sources[(u64)134u * rows + r_0];
    const unsigned v1623 = sources[(u64)131u * rows + r_0];
    const unsigned v1635 = sources[(u64)146u * rows + r_0];
    const unsigned v1638 = sources[(u64)140u * rows + r_0];
    const unsigned v1640 = sources[(u64)141u * rows + r_0];
    const unsigned v1648 = sources[(u64)138u * rows + r_0];
    const unsigned v1656 = sources[(u64)142u * rows + r_0];
    const unsigned v1657 = sources[(u64)143u * rows + r_0];
    const unsigned v1663 = sources[(u64)139u * rows + r_0];
    const unsigned v1667 = sources[(u64)144u * rows + r_0];
    const unsigned v1668 = sources[(u64)145u * rows + r_0];
    const unsigned v2003 = starked_neg(v0);
    const unsigned v2004 = sources[(u64)7u * rows + r_0];
    const unsigned v2005 = starked_add(v4, v7);
    const unsigned v2006 = starked_neg(v2005);
    const unsigned v2007 = sources[(u64)135u * rows + r_0];
    const unsigned v2008 = sources[(u64)136u * rows + r_0];
    const unsigned v2009 = sources[(u64)137u * rows + r_0];
    const unsigned v2010 = starked_mul(v108, v59);
    const unsigned v2011 = starked_add(v2010, v1);
    const unsigned v2012 = starked_neg(v4);
    const unsigned v2013 = starked_neg(v25);
    const unsigned v2014 = starked_mul(v0, v189);
    const unsigned v2015 = starked_neg(v2014);
    const unsigned v2016 = starked_add(v42, v355);
    const unsigned v2017 = starked_add(v42, v1);
    const unsigned v2018 = starked_add(v42, v108);
    const unsigned v2019 = 3u;
    const unsigned v2020 = starked_add(v42, v2019);
    const unsigned v2021 = 4u;
    const unsigned v2022 = starked_add(v42, v2021);
    const unsigned v2023 = 5u;
    const unsigned v2024 = starked_add(v42, v2023);
    const unsigned v2025 = 6u;
    const unsigned v2026 = starked_add(v42, v2025);
    const unsigned v2027 = starked_add(v42, v1570);
    const unsigned v2028 = 8u;
    const unsigned v2029 = starked_add(v42, v2028);
    const unsigned v2030 = 9u;
    const unsigned v2031 = starked_add(v42, v2030);
    const unsigned v2032 = 10u;
    const unsigned v2033 = starked_add(v42, v2032);
    const unsigned v2034 = 11u;
    const unsigned v2035 = starked_add(v42, v2034);
    const unsigned v2036 = 12u;
    const unsigned v2037 = starked_add(v42, v2036);
    const unsigned v2038 = 13u;
    const unsigned v2039 = starked_add(v42, v2038);
    const unsigned v2040 = 14u;
    const unsigned v2041 = starked_add(v42, v2040);
    const unsigned v2042 = 15u;
    const unsigned v2043 = starked_add(v42, v2042);
    const unsigned v2044 = 16u;
    const unsigned v2045 = starked_add(v42, v2044);
    const unsigned v2046 = 17u;
    const unsigned v2047 = starked_add(v42, v2046);
    const unsigned v2048 = 18u;
    const unsigned v2049 = starked_add(v42, v2048);
    const unsigned v2050 = 19u;
    const unsigned v2051 = starked_add(v42, v2050);
    const unsigned v2052 = 20u;
    const unsigned v2053 = starked_add(v42, v2052);
    const unsigned v2054 = 21u;
    const unsigned v2055 = starked_add(v42, v2054);
    const unsigned v2056 = 22u;
    const unsigned v2057 = starked_add(v42, v2056);
    const unsigned v2058 = 23u;
    const unsigned v2059 = starked_add(v42, v2058);
    const unsigned v2060 = 24u;
    const unsigned v2061 = starked_add(v42, v2060);
    const unsigned v2062 = 25u;
    const unsigned v2063 = starked_add(v42, v2062);
    const unsigned v2064 = 26u;
    const unsigned v2065 = starked_add(v42, v2064);
    const unsigned v2066 = 27u;
    const unsigned v2067 = starked_add(v42, v2066);
    const unsigned v2068 = 28u;
    const unsigned v2069 = starked_add(v42, v2068);
    const unsigned v2070 = 29u;
    const unsigned v2071 = starked_add(v42, v2070);
    const unsigned v2072 = 30u;
    const unsigned v2073 = starked_add(v42, v2072);
    const unsigned v2074 = 31u;
    const unsigned v2075 = starked_add(v42, v2074);
    const unsigned v2076 = 32u;
    const unsigned v2077 = starked_add(v42, v2076);
    const unsigned v2078 = 33u;
    const unsigned v2079 = starked_add(v42, v2078);
    const unsigned v2080 = 34u;
    const unsigned v2081 = starked_add(v42, v2080);
    const unsigned v2082 = 35u;
    const unsigned v2083 = starked_add(v42, v2082);
    const unsigned v2084 = starked_mul(v30, v26);
    const unsigned v2085 = starked_neg(v2084);
    const unsigned v2086 = starked_mul(v4, v10);
    const unsigned v2087 = starked_neg(v2086);
    const unsigned v2088 = starked_neg(v1399);
    const unsigned v2089 = starked_neg(v1402);
    const unsigned v2090 = starked_neg(v26);
    const unsigned v2091 = starked_neg(v1405);
    const unsigned v2092 = starked_mul(v4, v1608);
    const unsigned v2093 = starked_neg(v2092);
    const unsigned v2094 = starked_neg(v1635);
    const unsigned v2095 = starked_mul(v108, v1638);
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
    d0.a = starked_add(d0.a, 24u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v59));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v42));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha3, v124));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha4, v2004));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha5, v174));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha6, v1421));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha7, v1428));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 25u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v59));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v42));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha3, v1611));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha4, v1608));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha5, v1623));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha6, v2007));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha7, v2008));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha8, v2009));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 7u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v2011));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v242));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v249));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v256));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha5, v263));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha6, v270));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha7, v277));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha8, v284));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha9, v291));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha10, v298));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha11, v305));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha12, v312));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha13, v319));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha14, v326));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha15, v333));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha16, v340));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha17, v347));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 23u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v68));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v104));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v105));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v1421));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha5, v1428));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha6, v120));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha7, v2007));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha8, v2008));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha9, v2009));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha10, v1648));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha11, v1663));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 21u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v355));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v42));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha3, v42));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha4, v124));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 22u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v4));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v237));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha3, v123));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha4, v677));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha5, v694));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha6, v711));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha7, v728));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 3u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v2004));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v181));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 3u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v2016));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v251));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 3u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v2017));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v250));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 3u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v2018));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v244));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 3u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v2020));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v243));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 3u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v2022));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v265));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 3u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v2024));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v264));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 3u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v2026));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v258));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 3u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v2027));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v257));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 3u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v2029));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v279));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 3u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v2031));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v278));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 3u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v2033));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v272));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 3u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v2035));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha2, v271));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 3u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v2037));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha2, v293));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 3u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v2039));
    d20 = starked_q_add(d20, starked_q_mul_base(alpha2, v292));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 3u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v2041));
    d21 = starked_q_add(d21, starked_q_mul_base(alpha2, v286));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 3u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v2043));
    d22 = starked_q_add(d22, starked_q_mul_base(alpha2, v285));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 3u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v2045));
    d23 = starked_q_add(d23, starked_q_mul_base(alpha2, v307));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 3u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v2047));
    d24 = starked_q_add(d24, starked_q_mul_base(alpha2, v306));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 3u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v2049));
    d25 = starked_q_add(d25, starked_q_mul_base(alpha2, v300));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 3u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v2051));
    d26 = starked_q_add(d26, starked_q_mul_base(alpha2, v299));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 3u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v2053));
    d27 = starked_q_add(d27, starked_q_mul_base(alpha2, v321));
    StarkedQm31 d28 = minus_z;
    d28.a = starked_add(d28.a, 3u);
    d28 = starked_q_add(d28, starked_q_mul_base(alpha1, v2055));
    d28 = starked_q_add(d28, starked_q_mul_base(alpha2, v320));
    StarkedQm31 d29 = minus_z;
    d29.a = starked_add(d29.a, 3u);
    d29 = starked_q_add(d29, starked_q_mul_base(alpha1, v2057));
    d29 = starked_q_add(d29, starked_q_mul_base(alpha2, v314));
    StarkedQm31 d30 = minus_z;
    d30.a = starked_add(d30.a, 3u);
    d30 = starked_q_add(d30, starked_q_mul_base(alpha1, v2059));
    d30 = starked_q_add(d30, starked_q_mul_base(alpha2, v313));
    StarkedQm31 d31 = minus_z;
    d31.a = starked_add(d31.a, 3u);
    d31 = starked_q_add(d31, starked_q_mul_base(alpha1, v2061));
    d31 = starked_q_add(d31, starked_q_mul_base(alpha2, v335));
    StarkedQm31 d32 = minus_z;
    d32.a = starked_add(d32.a, 3u);
    d32 = starked_q_add(d32, starked_q_mul_base(alpha1, v2063));
    d32 = starked_q_add(d32, starked_q_mul_base(alpha2, v334));
    StarkedQm31 d33 = minus_z;
    d33.a = starked_add(d33.a, 3u);
    d33 = starked_q_add(d33, starked_q_mul_base(alpha1, v2065));
    d33 = starked_q_add(d33, starked_q_mul_base(alpha2, v328));
    StarkedQm31 d34 = minus_z;
    d34.a = starked_add(d34.a, 3u);
    d34 = starked_q_add(d34, starked_q_mul_base(alpha1, v2067));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha2, v327));
    StarkedQm31 d35 = minus_z;
    d35.a = starked_add(d35.a, 3u);
    d35 = starked_q_add(d35, starked_q_mul_base(alpha1, v2069));
    d35 = starked_q_add(d35, starked_q_mul_base(alpha2, v349));
    StarkedQm31 d36 = minus_z;
    d36.a = starked_add(d36.a, 3u);
    d36 = starked_q_add(d36, starked_q_mul_base(alpha1, v2071));
    d36 = starked_q_add(d36, starked_q_mul_base(alpha2, v348));
    StarkedQm31 d37 = minus_z;
    d37.a = starked_add(d37.a, 3u);
    d37 = starked_q_add(d37, starked_q_mul_base(alpha1, v2073));
    d37 = starked_q_add(d37, starked_q_mul_base(alpha2, v342));
    StarkedQm31 d38 = minus_z;
    d38.a = starked_add(d38.a, 3u);
    d38 = starked_q_add(d38, starked_q_mul_base(alpha1, v2075));
    d38 = starked_q_add(d38, starked_q_mul_base(alpha2, v341));
    StarkedQm31 d39 = minus_z;
    d39.a = starked_add(d39.a, 3u);
    d39 = starked_q_add(d39, starked_q_mul_base(alpha1, v2077));
    d39 = starked_q_add(d39, starked_q_mul_base(alpha2, v92));
    StarkedQm31 d40 = minus_z;
    d40.a = starked_add(d40.a, 3u);
    d40 = starked_q_add(d40, starked_q_mul_base(alpha1, v2079));
    d40 = starked_q_add(d40, starked_q_mul_base(alpha2, v93));
    StarkedQm31 d41 = minus_z;
    d41.a = starked_add(d41.a, 3u);
    d41 = starked_q_add(d41, starked_q_mul_base(alpha1, v2081));
    d41 = starked_q_add(d41, starked_q_mul_base(alpha2, v98));
    StarkedQm31 d42 = minus_z;
    d42.a = starked_add(d42.a, 3u);
    d42 = starked_q_add(d42, starked_q_mul_base(alpha1, v2083));
    d42 = starked_q_add(d42, starked_q_mul_base(alpha2, v99));
    StarkedQm31 d43 = minus_z;
    d43.a = starked_add(d43.a, 9u);
    d43 = starked_q_add(d43, starked_q_mul_base(alpha1, v46));
    StarkedQm31 d44 = minus_z;
    d44.a = starked_add(d44.a, 9u);
    d44 = starked_q_add(d44, starked_q_mul_base(alpha1, v48));
    StarkedQm31 d45 = minus_z;
    d45.a = starked_add(d45.a, 9u);
    d45 = starked_q_add(d45, starked_q_mul_base(alpha1, v52));
    StarkedQm31 d46 = minus_z;
    d46.a = starked_add(d46.a, 9u);
    d46 = starked_q_add(d46, starked_q_mul_base(alpha1, v86));
    StarkedQm31 d47 = minus_z;
    d47.a = starked_add(d47.a, 9u);
    d47 = starked_q_add(d47, starked_q_mul_base(alpha1, v87));
    StarkedQm31 d48 = minus_z;
    d48.a = starked_add(d48.a, 9u);
    d48 = starked_q_add(d48, starked_q_mul_base(alpha1, v81));
    StarkedQm31 d49 = minus_z;
    d49.a = starked_add(d49.a, 9u);
    d49 = starked_q_add(d49, starked_q_mul_base(alpha1, v114));
    StarkedQm31 d50 = minus_z;
    d50.a = starked_add(d50.a, 9u);
    d50 = starked_q_add(d50, starked_q_mul_base(alpha1, v115));
    StarkedQm31 d51 = minus_z;
    d51.a = starked_add(d51.a, 9u);
    d51 = starked_q_add(d51, starked_q_mul_base(alpha1, v105));
    StarkedQm31 d52 = minus_z;
    d52.a = starked_add(d52.a, 9u);
    d52 = starked_q_add(d52, starked_q_mul_base(alpha1, v132));
    StarkedQm31 d53 = minus_z;
    d53.a = starked_add(d53.a, 9u);
    d53 = starked_q_add(d53, starked_q_mul_base(alpha1, v133));
    StarkedQm31 d54 = minus_z;
    d54.a = starked_add(d54.a, 9u);
    d54 = starked_q_add(d54, starked_q_mul_base(alpha1, v136));
    StarkedQm31 d55 = minus_z;
    d55.a = starked_add(d55.a, 9u);
    d55 = starked_q_add(d55, starked_q_mul_base(alpha1, v145));
    StarkedQm31 d56 = minus_z;
    d56.a = starked_add(d56.a, 9u);
    d56 = starked_q_add(d56, starked_q_mul_base(alpha1, v146));
    StarkedQm31 d57 = minus_z;
    d57.a = starked_add(d57.a, 9u);
    d57 = starked_q_add(d57, starked_q_mul_base(alpha1, v149));
    StarkedQm31 d58 = minus_z;
    d58.a = starked_add(d58.a, 9u);
    d58 = starked_q_add(d58, starked_q_mul_base(alpha1, v164));
    StarkedQm31 d59 = minus_z;
    d59.a = starked_add(d59.a, 9u);
    d59 = starked_q_add(d59, starked_q_mul_base(alpha1, v165));
    StarkedQm31 d60 = minus_z;
    d60.a = starked_add(d60.a, 9u);
    d60 = starked_q_add(d60, starked_q_mul_base(alpha1, v168));
    StarkedQm31 d61 = minus_z;
    d61.a = starked_add(d61.a, 9u);
    d61 = starked_q_add(d61, starked_q_mul_base(alpha1, v192));
    StarkedQm31 d62 = minus_z;
    d62.a = starked_add(d62.a, 9u);
    d62 = starked_q_add(d62, starked_q_mul_base(alpha1, v193));
    StarkedQm31 d63 = minus_z;
    d63.a = starked_add(d63.a, 9u);
    d63 = starked_q_add(d63, starked_q_mul_base(alpha1, v196));
    StarkedQm31 d64 = minus_z;
    d64.a = starked_add(d64.a, 9u);
    d64 = starked_q_add(d64, starked_q_mul_base(alpha1, v1433));
    StarkedQm31 d65 = minus_z;
    d65.a = starked_add(d65.a, 9u);
    d65 = starked_q_add(d65, starked_q_mul_base(alpha1, v1434));
    StarkedQm31 d66 = minus_z;
    d66.a = starked_add(d66.a, 9u);
    d66 = starked_q_add(d66, starked_q_mul_base(alpha1, v1437));
    StarkedQm31 d67 = minus_z;
    d67.a = starked_add(d67.a, 9u);
    d67 = starked_q_add(d67, starked_q_mul_base(alpha1, v1442));
    StarkedQm31 d68 = minus_z;
    d68.a = starked_add(d68.a, 9u);
    d68 = starked_q_add(d68, starked_q_mul_base(alpha1, v1443));
    StarkedQm31 d69 = minus_z;
    d69.a = starked_add(d69.a, 9u);
    d69 = starked_q_add(d69, starked_q_mul_base(alpha1, v1446));
    StarkedQm31 d70 = minus_z;
    d70.a = starked_add(d70.a, 9u);
    d70 = starked_q_add(d70, starked_q_mul_base(alpha1, v1455));
    StarkedQm31 d71 = minus_z;
    d71.a = starked_add(d71.a, 9u);
    d71 = starked_q_add(d71, starked_q_mul_base(alpha1, v1456));
    StarkedQm31 d72 = minus_z;
    d72.a = starked_add(d72.a, 9u);
    d72 = starked_q_add(d72, starked_q_mul_base(alpha1, v1459));
    StarkedQm31 d73 = minus_z;
    d73.a = starked_add(d73.a, 9u);
    d73 = starked_q_add(d73, starked_q_mul_base(alpha1, v1462));
    StarkedQm31 d74 = minus_z;
    d74.a = starked_add(d74.a, 9u);
    d74 = starked_q_add(d74, starked_q_mul_base(alpha1, v1516));
    StarkedQm31 d75 = minus_z;
    d75.a = starked_add(d75.a, 9u);
    d75 = starked_q_add(d75, starked_q_mul_base(alpha1, v1517));
    StarkedQm31 d76 = minus_z;
    d76.a = starked_add(d76.a, 9u);
    d76 = starked_q_add(d76, starked_q_mul_base(alpha1, v1520));
    StarkedQm31 d77 = minus_z;
    d77.a = starked_add(d77.a, 9u);
    d77 = starked_q_add(d77, starked_q_mul_base(alpha1, v1537));
    StarkedQm31 d78 = minus_z;
    d78.a = starked_add(d78.a, 9u);
    d78 = starked_q_add(d78, starked_q_mul_base(alpha1, v1538));
    StarkedQm31 d79 = minus_z;
    d79.a = starked_add(d79.a, 9u);
    d79 = starked_q_add(d79, starked_q_mul_base(alpha1, v1541));
    StarkedQm31 d80 = minus_z;
    d80.a = starked_add(d80.a, 9u);
    d80 = starked_q_add(d80, starked_q_mul_base(alpha1, v1552));
    StarkedQm31 d81 = minus_z;
    d81.a = starked_add(d81.a, 9u);
    d81 = starked_q_add(d81, starked_q_mul_base(alpha1, v1553));
    StarkedQm31 d82 = minus_z;
    d82.a = starked_add(d82.a, 9u);
    d82 = starked_q_add(d82, starked_q_mul_base(alpha1, v1556));
    StarkedQm31 d83 = minus_z;
    d83.a = starked_add(d83.a, 9u);
    d83 = starked_q_add(d83, starked_q_mul_base(alpha1, v1559));
    StarkedQm31 d84 = minus_z;
    d84.a = starked_add(d84.a, 9u);
    d84 = starked_q_add(d84, starked_q_mul_base(alpha1, v1569));
    StarkedQm31 d85 = minus_z;
    d85.a = starked_add(d85.a, 9u);
    d85 = starked_q_add(d85, starked_q_mul_base(alpha1, v1573));
    StarkedQm31 d86 = minus_z;
    d86.a = starked_add(d86.a, 9u);
    d86 = starked_q_add(d86, starked_q_mul_base(alpha1, v1579));
    StarkedQm31 d87 = minus_z;
    d87.a = starked_add(d87.a, 9u);
    d87 = starked_q_add(d87, starked_q_mul_base(alpha1, v1580));
    StarkedQm31 d88 = minus_z;
    d88.a = starked_add(d88.a, 9u);
    d88 = starked_q_add(d88, starked_q_mul_base(alpha1, v1583));
    StarkedQm31 d89 = minus_z;
    d89.a = starked_add(d89.a, 9u);
    d89 = starked_q_add(d89, starked_q_mul_base(alpha1, v1591));
    StarkedQm31 d90 = minus_z;
    d90.a = starked_add(d90.a, 9u);
    d90 = starked_q_add(d90, starked_q_mul_base(alpha1, v1592));
    StarkedQm31 d91 = minus_z;
    d91.a = starked_add(d91.a, 9u);
    d91 = starked_q_add(d91, starked_q_mul_base(alpha1, v1595));
    StarkedQm31 d92 = minus_z;
    d92.a = starked_add(d92.a, 9u);
    d92 = starked_q_add(d92, starked_q_mul_base(alpha1, v1598));
    StarkedQm31 d93 = minus_z;
    d93.a = starked_add(d93.a, 9u);
    d93 = starked_q_add(d93, starked_q_mul_base(alpha1, v1605));
    StarkedQm31 d94 = minus_z;
    d94.a = starked_add(d94.a, 9u);
    d94 = starked_q_add(d94, starked_q_mul_base(alpha1, v1613));
    StarkedQm31 d95 = minus_z;
    d95.a = starked_add(d95.a, 9u);
    d95 = starked_q_add(d95, starked_q_mul_base(alpha1, v1614));
    StarkedQm31 d96 = minus_z;
    d96.a = starked_add(d96.a, 9u);
    d96 = starked_q_add(d96, starked_q_mul_base(alpha1, v1617));
    StarkedQm31 d97 = minus_z;
    d97.a = starked_add(d97.a, 9u);
    d97 = starked_q_add(d97, starked_q_mul_base(alpha1, v1656));
    StarkedQm31 d98 = minus_z;
    d98.a = starked_add(d98.a, 9u);
    d98 = starked_q_add(d98, starked_q_mul_base(alpha1, v1657));
    StarkedQm31 d99 = minus_z;
    d99.a = starked_add(d99.a, 9u);
    d99 = starked_q_add(d99, starked_q_mul_base(alpha1, v1667));
    StarkedQm31 d100 = minus_z;
    d100.a = starked_add(d100.a, 9u);
    d100 = starked_q_add(d100, starked_q_mul_base(alpha1, v1668));
    StarkedQm31 d101 = minus_z;
    d101.a = starked_add(d101.a, 9u);
    d101 = starked_q_add(d101, starked_q_mul_base(alpha1, v1638));
    StarkedQm31 d102 = minus_z;
    d102.a = starked_add(d102.a, 9u);
    d102 = starked_q_add(d102, starked_q_mul_base(alpha1, v2095));
    StarkedQm31 d103 = minus_z;
    d103.a = starked_add(d103.a, 9u);
    d103 = starked_q_add(d103, starked_q_mul_base(alpha1, v1640));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v2003), starked_q_mul_base(d0, v2006));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v2003), starked_q_mul_base(d2, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v0), starked_q_mul_base(d4, v2013));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v2015), starked_q_mul_base(d6, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v2012), starked_q_mul_base(d8, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v2012), starked_q_mul_base(d10, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v2012), starked_q_mul_base(d12, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v2012), starked_q_mul_base(d14, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v2012), starked_q_mul_base(d16, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v2012), starked_q_mul_base(d18, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v2012), starked_q_mul_base(d20, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v2012), starked_q_mul_base(d22, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v2012), starked_q_mul_base(d24, v2012));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v2012), starked_q_mul_base(d26, v2012));
        const StarkedQm31 d = starked_q_mul(d26, d27);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[52][row] = n.a;
        outputs[53][row] = n.b;
        outputs[54][row] = n.c;
        outputs[55][row] = n.d;
        unsigned *slot = denominators + ((u64)13u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d29, v2012), starked_q_mul_base(d28, v2012));
        const StarkedQm31 d = starked_q_mul(d28, d29);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[56][row] = n.a;
        outputs[57][row] = n.b;
        outputs[58][row] = n.c;
        outputs[59][row] = n.d;
        unsigned *slot = denominators + ((u64)14u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d31, v2012), starked_q_mul_base(d30, v2012));
        const StarkedQm31 d = starked_q_mul(d30, d31);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[60][row] = n.a;
        outputs[61][row] = n.b;
        outputs[62][row] = n.c;
        outputs[63][row] = n.d;
        unsigned *slot = denominators + ((u64)15u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d33, v2012), starked_q_mul_base(d32, v2012));
        const StarkedQm31 d = starked_q_mul(d32, d33);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[64][row] = n.a;
        outputs[65][row] = n.b;
        outputs[66][row] = n.c;
        outputs[67][row] = n.d;
        unsigned *slot = denominators + ((u64)16u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d35, v2012), starked_q_mul_base(d34, v2012));
        const StarkedQm31 d = starked_q_mul(d34, d35);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[68][row] = n.a;
        outputs[69][row] = n.b;
        outputs[70][row] = n.c;
        outputs[71][row] = n.d;
        unsigned *slot = denominators + ((u64)17u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d37, v2012), starked_q_mul_base(d36, v2012));
        const StarkedQm31 d = starked_q_mul(d36, d37);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[72][row] = n.a;
        outputs[73][row] = n.b;
        outputs[74][row] = n.c;
        outputs[75][row] = n.d;
        unsigned *slot = denominators + ((u64)18u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d39, v2012), starked_q_mul_base(d38, v2012));
        const StarkedQm31 d = starked_q_mul(d38, d39);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[76][row] = n.a;
        outputs[77][row] = n.b;
        outputs[78][row] = n.c;
        outputs[79][row] = n.d;
        unsigned *slot = denominators + ((u64)19u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d41, v2012), starked_q_mul_base(d40, v2012));
        const StarkedQm31 d = starked_q_mul(d40, d41);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[80][row] = n.a;
        outputs[81][row] = n.b;
        outputs[82][row] = n.c;
        outputs[83][row] = n.d;
        unsigned *slot = denominators + ((u64)20u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d43, v2012), starked_q_mul_base(d42, v2085));
        const StarkedQm31 d = starked_q_mul(d42, d43);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[84][row] = n.a;
        outputs[85][row] = n.b;
        outputs[86][row] = n.c;
        outputs[87][row] = n.d;
        unsigned *slot = denominators + ((u64)21u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d45, v2085), starked_q_mul_base(d44, v2085));
        const StarkedQm31 d = starked_q_mul(d44, d45);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[88][row] = n.a;
        outputs[89][row] = n.b;
        outputs[90][row] = n.c;
        outputs[91][row] = n.d;
        unsigned *slot = denominators + ((u64)22u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d47, v2003), starked_q_mul_base(d46, v2003));
        const StarkedQm31 d = starked_q_mul(d46, d47);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[92][row] = n.a;
        outputs[93][row] = n.b;
        outputs[94][row] = n.c;
        outputs[95][row] = n.d;
        unsigned *slot = denominators + ((u64)23u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d49, v2003), starked_q_mul_base(d48, v2003));
        const StarkedQm31 d = starked_q_mul(d48, d49);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[96][row] = n.a;
        outputs[97][row] = n.b;
        outputs[98][row] = n.c;
        outputs[99][row] = n.d;
        unsigned *slot = denominators + ((u64)24u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d51, v2003), starked_q_mul_base(d50, v2003));
        const StarkedQm31 d = starked_q_mul(d50, d51);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[100][row] = n.a;
        outputs[101][row] = n.b;
        outputs[102][row] = n.c;
        outputs[103][row] = n.d;
        unsigned *slot = denominators + ((u64)25u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d53, v2012), starked_q_mul_base(d52, v2012));
        const StarkedQm31 d = starked_q_mul(d52, d53);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[104][row] = n.a;
        outputs[105][row] = n.b;
        outputs[106][row] = n.c;
        outputs[107][row] = n.d;
        unsigned *slot = denominators + ((u64)26u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d55, v2012), starked_q_mul_base(d54, v2012));
        const StarkedQm31 d = starked_q_mul(d54, d55);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[108][row] = n.a;
        outputs[109][row] = n.b;
        outputs[110][row] = n.c;
        outputs[111][row] = n.d;
        unsigned *slot = denominators + ((u64)27u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d57, v2012), starked_q_mul_base(d56, v2012));
        const StarkedQm31 d = starked_q_mul(d56, d57);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[112][row] = n.a;
        outputs[113][row] = n.b;
        outputs[114][row] = n.c;
        outputs[115][row] = n.d;
        unsigned *slot = denominators + ((u64)28u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d59, v2087), starked_q_mul_base(d58, v2087));
        const StarkedQm31 d = starked_q_mul(d58, d59);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[116][row] = n.a;
        outputs[117][row] = n.b;
        outputs[118][row] = n.c;
        outputs[119][row] = n.d;
        unsigned *slot = denominators + ((u64)29u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d61, v2087), starked_q_mul_base(d60, v2003));
        const StarkedQm31 d = starked_q_mul(d60, d61);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[120][row] = n.a;
        outputs[121][row] = n.b;
        outputs[122][row] = n.c;
        outputs[123][row] = n.d;
        unsigned *slot = denominators + ((u64)30u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d63, v2003), starked_q_mul_base(d62, v2003));
        const StarkedQm31 d = starked_q_mul(d62, d63);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[124][row] = n.a;
        outputs[125][row] = n.b;
        outputs[126][row] = n.c;
        outputs[127][row] = n.d;
        unsigned *slot = denominators + ((u64)31u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d65, v2088), starked_q_mul_base(d64, v2088));
        const StarkedQm31 d = starked_q_mul(d64, d65);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[128][row] = n.a;
        outputs[129][row] = n.b;
        outputs[130][row] = n.c;
        outputs[131][row] = n.d;
        unsigned *slot = denominators + ((u64)32u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d67, v2088), starked_q_mul_base(d66, v2089));
        const StarkedQm31 d = starked_q_mul(d66, d67);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[132][row] = n.a;
        outputs[133][row] = n.b;
        outputs[134][row] = n.c;
        outputs[135][row] = n.d;
        unsigned *slot = denominators + ((u64)33u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d69, v2089), starked_q_mul_base(d68, v2089));
        const StarkedQm31 d = starked_q_mul(d68, d69);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[136][row] = n.a;
        outputs[137][row] = n.b;
        outputs[138][row] = n.c;
        outputs[139][row] = n.d;
        unsigned *slot = denominators + ((u64)34u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d71, v2089), starked_q_mul_base(d70, v2089));
        const StarkedQm31 d = starked_q_mul(d70, d71);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[140][row] = n.a;
        outputs[141][row] = n.b;
        outputs[142][row] = n.c;
        outputs[143][row] = n.d;
        unsigned *slot = denominators + ((u64)35u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d73, v2089), starked_q_mul_base(d72, v2089));
        const StarkedQm31 d = starked_q_mul(d72, d73);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[144][row] = n.a;
        outputs[145][row] = n.b;
        outputs[146][row] = n.c;
        outputs[147][row] = n.d;
        unsigned *slot = denominators + ((u64)36u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d75, v2090), starked_q_mul_base(d74, v2090));
        const StarkedQm31 d = starked_q_mul(d74, d75);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[148][row] = n.a;
        outputs[149][row] = n.b;
        outputs[150][row] = n.c;
        outputs[151][row] = n.d;
        unsigned *slot = denominators + ((u64)37u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d77, v2090), starked_q_mul_base(d76, v2091));
        const StarkedQm31 d = starked_q_mul(d76, d77);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[152][row] = n.a;
        outputs[153][row] = n.b;
        outputs[154][row] = n.c;
        outputs[155][row] = n.d;
        unsigned *slot = denominators + ((u64)38u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d79, v2091), starked_q_mul_base(d78, v2091));
        const StarkedQm31 d = starked_q_mul(d78, d79);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[156][row] = n.a;
        outputs[157][row] = n.b;
        outputs[158][row] = n.c;
        outputs[159][row] = n.d;
        unsigned *slot = denominators + ((u64)39u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d81, v2091), starked_q_mul_base(d80, v2091));
        const StarkedQm31 d = starked_q_mul(d80, d81);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[160][row] = n.a;
        outputs[161][row] = n.b;
        outputs[162][row] = n.c;
        outputs[163][row] = n.d;
        unsigned *slot = denominators + ((u64)40u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d83, v2091), starked_q_mul_base(d82, v2091));
        const StarkedQm31 d = starked_q_mul(d82, d83);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[164][row] = n.a;
        outputs[165][row] = n.b;
        outputs[166][row] = n.c;
        outputs[167][row] = n.d;
        unsigned *slot = denominators + ((u64)41u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d85, v2089), starked_q_mul_base(d84, v2091));
        const StarkedQm31 d = starked_q_mul(d84, d85);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[168][row] = n.a;
        outputs[169][row] = n.b;
        outputs[170][row] = n.c;
        outputs[171][row] = n.d;
        unsigned *slot = denominators + ((u64)42u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d87, v2089), starked_q_mul_base(d86, v2089));
        const StarkedQm31 d = starked_q_mul(d86, d87);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[172][row] = n.a;
        outputs[173][row] = n.b;
        outputs[174][row] = n.c;
        outputs[175][row] = n.d;
        unsigned *slot = denominators + ((u64)43u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d89, v2089), starked_q_mul_base(d88, v2089));
        const StarkedQm31 d = starked_q_mul(d88, d89);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[176][row] = n.a;
        outputs[177][row] = n.b;
        outputs[178][row] = n.c;
        outputs[179][row] = n.d;
        unsigned *slot = denominators + ((u64)44u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d91, v2089), starked_q_mul_base(d90, v2089));
        const StarkedQm31 d = starked_q_mul(d90, d91);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[180][row] = n.a;
        outputs[181][row] = n.b;
        outputs[182][row] = n.c;
        outputs[183][row] = n.d;
        unsigned *slot = denominators + ((u64)45u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d93, v2089), starked_q_mul_base(d92, v2089));
        const StarkedQm31 d = starked_q_mul(d92, d93);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[184][row] = n.a;
        outputs[185][row] = n.b;
        outputs[186][row] = n.c;
        outputs[187][row] = n.d;
        unsigned *slot = denominators + ((u64)46u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d95, v2093), starked_q_mul_base(d94, v2093));
        const StarkedQm31 d = starked_q_mul(d94, d95);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[188][row] = n.a;
        outputs[189][row] = n.b;
        outputs[190][row] = n.c;
        outputs[191][row] = n.d;
        unsigned *slot = denominators + ((u64)47u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d97, v2093), starked_q_mul_base(d96, v2094));
        const StarkedQm31 d = starked_q_mul(d96, d97);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[192][row] = n.a;
        outputs[193][row] = n.b;
        outputs[194][row] = n.c;
        outputs[195][row] = n.d;
        unsigned *slot = denominators + ((u64)48u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d99, v2094), starked_q_mul_base(d98, v2094));
        const StarkedQm31 d = starked_q_mul(d98, d99);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[196][row] = n.a;
        outputs[197][row] = n.b;
        outputs[198][row] = n.c;
        outputs[199][row] = n.d;
        unsigned *slot = denominators + ((u64)49u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d101, v2094), starked_q_mul_base(d100, v2094));
        const StarkedQm31 d = starked_q_mul(d100, d101);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[200][row] = n.a;
        outputs[201][row] = n.b;
        outputs[202][row] = n.c;
        outputs[203][row] = n.d;
        unsigned *slot = denominators + ((u64)50u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d103, v2094), starked_q_mul_base(d102, v2094));
        const StarkedQm31 d = starked_q_mul(d102, d103);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[204][row] = n.a;
        outputs[205][row] = n.b;
        outputs[206][row] = n.c;
        outputs[207][row] = n.d;
        unsigned *slot = denominators + ((u64)51u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
