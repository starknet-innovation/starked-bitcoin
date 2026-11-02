// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_rec, digest 0a4f4753a445adeea838db289c4841c008e4b3c087f44a7198f4b06d70f49a55.
// 98 lookups in 49 batches, 128 source columns, tuples up to 7 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_6ce5361c1ab293e7(
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
    const unsigned v160 = sources[(u64)0u * rows + r_0];
    const unsigned v175 = sources[(u64)2u * rows + r_0];
    const unsigned v188 = sources[(u64)3u * rows + r_0];
    const unsigned v191 = 49u;
    const unsigned v198 = starked_add(v188, v191);
    const unsigned v199 = sources[(u64)61u * rows + r_0];
    const unsigned v204 = sources[(u64)69u * rows + r_0];
    const unsigned v205 = 256u;
    const unsigned v206 = sources[(u64)70u * rows + r_0];
    const unsigned v210 = sources[(u64)71u * rows + r_0];
    const unsigned v215 = sources[(u64)49u * rows + r_0];
    const unsigned v216 = sources[(u64)50u * rows + r_0];
    const unsigned v219 = sources[(u64)51u * rows + r_0];
    const unsigned v223 = sources[(u64)52u * rows + r_0];
    const unsigned v225 = 8u;
    const unsigned v227 = sources[(u64)66u * rows + r_0];
    const unsigned v228 = sources[(u64)67u * rows + r_0];
    const unsigned v231 = sources[(u64)68u * rows + r_0];
    const unsigned v236 = sources[(u64)44u * rows + r_0];
    const unsigned v240 = sources[(u64)43u * rows + r_0];
    const unsigned v242 = sources[(u64)62u * rows + r_0];
    const unsigned v243 = 2u;
    const unsigned v244 = sources[(u64)40u * rows + r_0];
    const unsigned v250 = sources[(u64)63u * rows + r_0];
    const unsigned v251 = sources[(u64)41u * rows + r_0];
    const unsigned v257 = sources[(u64)64u * rows + r_0];
    const unsigned v258 = sources[(u64)42u * rows + r_0];
    const unsigned v264 = sources[(u64)65u * rows + r_0];
    const unsigned v285 = sources[(u64)84u * rows + r_0];
    const unsigned v286 = sources[(u64)85u * rows + r_0];
    const unsigned v289 = sources[(u64)86u * rows + r_0];
    const unsigned v303 = 0u;
    const unsigned v340 = starked_sub(v0, v160);
    const unsigned v341 = pubs[3];
    const unsigned v342 = starked_mul(v160, v341);
    const unsigned v343 = starked_add(v340, v342);
    const unsigned v345 = sources[(u64)123u * rows + r_0];
    const unsigned v346 = sources[(u64)4u * rows + r_0];
    const unsigned v347 = sources[(u64)87u * rows + r_0];
    const unsigned v351 = sources[(u64)5u * rows + r_0];
    const unsigned v352 = sources[(u64)88u * rows + r_0];
    const unsigned v356 = sources[(u64)6u * rows + r_0];
    const unsigned v357 = sources[(u64)89u * rows + r_0];
    const unsigned v361 = sources[(u64)7u * rows + r_0];
    const unsigned v362 = sources[(u64)90u * rows + r_0];
    const unsigned v366 = sources[(u64)8u * rows + r_0];
    const unsigned v367 = sources[(u64)91u * rows + r_0];
    const unsigned v371 = sources[(u64)9u * rows + r_0];
    const unsigned v372 = sources[(u64)92u * rows + r_0];
    const unsigned v376 = sources[(u64)10u * rows + r_0];
    const unsigned v377 = sources[(u64)93u * rows + r_0];
    const unsigned v381 = sources[(u64)11u * rows + r_0];
    const unsigned v382 = sources[(u64)94u * rows + r_0];
    const unsigned v386 = sources[(u64)12u * rows + r_0];
    const unsigned v387 = sources[(u64)95u * rows + r_0];
    const unsigned v391 = sources[(u64)13u * rows + r_0];
    const unsigned v392 = sources[(u64)96u * rows + r_0];
    const unsigned v396 = sources[(u64)14u * rows + r_0];
    const unsigned v397 = sources[(u64)97u * rows + r_0];
    const unsigned v401 = sources[(u64)15u * rows + r_0];
    const unsigned v402 = sources[(u64)98u * rows + r_0];
    const unsigned v406 = sources[(u64)16u * rows + r_0];
    const unsigned v407 = sources[(u64)99u * rows + r_0];
    const unsigned v411 = sources[(u64)17u * rows + r_0];
    const unsigned v412 = sources[(u64)100u * rows + r_0];
    const unsigned v416 = sources[(u64)18u * rows + r_0];
    const unsigned v417 = sources[(u64)101u * rows + r_0];
    const unsigned v421 = sources[(u64)19u * rows + r_0];
    const unsigned v422 = sources[(u64)102u * rows + r_0];
    const unsigned v426 = sources[(u64)20u * rows + r_0];
    const unsigned v427 = sources[(u64)103u * rows + r_0];
    const unsigned v431 = sources[(u64)21u * rows + r_0];
    const unsigned v432 = sources[(u64)104u * rows + r_0];
    const unsigned v436 = sources[(u64)22u * rows + r_0];
    const unsigned v437 = sources[(u64)105u * rows + r_0];
    const unsigned v441 = sources[(u64)23u * rows + r_0];
    const unsigned v442 = sources[(u64)106u * rows + r_0];
    const unsigned v446 = sources[(u64)24u * rows + r_0];
    const unsigned v447 = sources[(u64)107u * rows + r_0];
    const unsigned v451 = sources[(u64)25u * rows + r_0];
    const unsigned v452 = sources[(u64)108u * rows + r_0];
    const unsigned v456 = sources[(u64)26u * rows + r_0];
    const unsigned v457 = sources[(u64)109u * rows + r_0];
    const unsigned v461 = sources[(u64)27u * rows + r_0];
    const unsigned v462 = sources[(u64)110u * rows + r_0];
    const unsigned v466 = sources[(u64)28u * rows + r_0];
    const unsigned v467 = sources[(u64)111u * rows + r_0];
    const unsigned v471 = sources[(u64)29u * rows + r_0];
    const unsigned v472 = sources[(u64)112u * rows + r_0];
    const unsigned v476 = sources[(u64)30u * rows + r_0];
    const unsigned v477 = sources[(u64)113u * rows + r_0];
    const unsigned v481 = sources[(u64)31u * rows + r_0];
    const unsigned v482 = sources[(u64)114u * rows + r_0];
    const unsigned v486 = sources[(u64)32u * rows + r_0];
    const unsigned v487 = sources[(u64)115u * rows + r_0];
    const unsigned v491 = sources[(u64)33u * rows + r_0];
    const unsigned v492 = sources[(u64)116u * rows + r_0];
    const unsigned v496 = sources[(u64)34u * rows + r_0];
    const unsigned v497 = sources[(u64)117u * rows + r_0];
    const unsigned v501 = sources[(u64)35u * rows + r_0];
    const unsigned v502 = sources[(u64)118u * rows + r_0];
    const unsigned v506 = sources[(u64)39u * rows + r_0];
    const unsigned v507 = sources[(u64)119u * rows + r_0];
    const unsigned v511 = sources[(u64)38u * rows + r_0];
    const unsigned v512 = sources[(u64)120u * rows + r_0];
    const unsigned v516 = sources[(u64)37u * rows + r_0];
    const unsigned v517 = sources[(u64)121u * rows + r_0];
    const unsigned v521 = sources[(u64)36u * rows + r_0];
    const unsigned v522 = sources[(u64)122u * rows + r_0];
    const unsigned v924 = sources[(u64)72u * rows + r_0];
    const unsigned v930 = sources[(u64)53u * rows + r_0];
    const unsigned v937 = sources[(u64)73u * rows + r_0];
    const unsigned v943 = sources[(u64)54u * rows + r_0];
    const unsigned v950 = sources[(u64)74u * rows + r_0];
    const unsigned v956 = sources[(u64)55u * rows + r_0];
    const unsigned v963 = sources[(u64)75u * rows + r_0];
    const unsigned v969 = sources[(u64)56u * rows + r_0];
    const unsigned v976 = sources[(u64)76u * rows + r_0];
    const unsigned v982 = sources[(u64)57u * rows + r_0];
    const unsigned v989 = sources[(u64)77u * rows + r_0];
    const unsigned v995 = sources[(u64)58u * rows + r_0];
    const unsigned v1002 = sources[(u64)78u * rows + r_0];
    const unsigned v1008 = sources[(u64)59u * rows + r_0];
    const unsigned v1015 = sources[(u64)79u * rows + r_0];
    const unsigned v1021 = sources[(u64)60u * rows + r_0];
    const unsigned v1028 = sources[(u64)80u * rows + r_0];
    const unsigned v1039 = sources[(u64)81u * rows + r_0];
    const unsigned v1050 = sources[(u64)82u * rows + r_0];
    const unsigned v1061 = sources[(u64)83u * rows + r_0];
    const unsigned v1469 = sources[(u64)124u * rows + r_0];
    const unsigned v1486 = sources[(u64)125u * rows + r_0];
    const unsigned v1503 = sources[(u64)126u * rows + r_0];
    const unsigned v1520 = sources[(u64)127u * rows + r_0];
    const unsigned v1553 = sources[(u64)45u * rows + r_0];
    const unsigned v1554 = sources[(u64)46u * rows + r_0];
    const unsigned v1557 = sources[(u64)47u * rows + r_0];
    const unsigned v1561 = sources[(u64)48u * rows + r_0];
    const unsigned v2210 = starked_neg(v0);
    const unsigned v2211 = starked_add(v188, v303);
    const unsigned v2212 = starked_add(v188, v1);
    const unsigned v2213 = starked_add(v188, v243);
    const unsigned v2214 = 3u;
    const unsigned v2215 = starked_add(v188, v2214);
    const unsigned v2216 = 4u;
    const unsigned v2217 = starked_add(v188, v2216);
    const unsigned v2218 = 5u;
    const unsigned v2219 = starked_add(v188, v2218);
    const unsigned v2220 = 6u;
    const unsigned v2221 = starked_add(v188, v2220);
    const unsigned v2222 = 7u;
    const unsigned v2223 = starked_add(v188, v2222);
    const unsigned v2224 = starked_add(v188, v225);
    const unsigned v2225 = 9u;
    const unsigned v2226 = starked_add(v188, v2225);
    const unsigned v2227 = 10u;
    const unsigned v2228 = starked_add(v188, v2227);
    const unsigned v2229 = 11u;
    const unsigned v2230 = starked_add(v188, v2229);
    const unsigned v2231 = 12u;
    const unsigned v2232 = starked_add(v188, v2231);
    const unsigned v2233 = 13u;
    const unsigned v2234 = starked_add(v188, v2233);
    const unsigned v2235 = 14u;
    const unsigned v2236 = starked_add(v188, v2235);
    const unsigned v2237 = 15u;
    const unsigned v2238 = starked_add(v188, v2237);
    const unsigned v2239 = 16u;
    const unsigned v2240 = starked_add(v188, v2239);
    const unsigned v2241 = 17u;
    const unsigned v2242 = starked_add(v188, v2241);
    const unsigned v2243 = 18u;
    const unsigned v2244 = starked_add(v188, v2243);
    const unsigned v2245 = 19u;
    const unsigned v2246 = starked_add(v188, v2245);
    const unsigned v2247 = 20u;
    const unsigned v2248 = starked_add(v188, v2247);
    const unsigned v2249 = 21u;
    const unsigned v2250 = starked_add(v188, v2249);
    const unsigned v2251 = 22u;
    const unsigned v2252 = starked_add(v188, v2251);
    const unsigned v2253 = 23u;
    const unsigned v2254 = starked_add(v188, v2253);
    const unsigned v2255 = 24u;
    const unsigned v2256 = starked_add(v188, v2255);
    const unsigned v2257 = 25u;
    const unsigned v2258 = starked_add(v188, v2257);
    const unsigned v2259 = 26u;
    const unsigned v2260 = starked_add(v188, v2259);
    const unsigned v2261 = 27u;
    const unsigned v2262 = starked_add(v188, v2261);
    const unsigned v2263 = 28u;
    const unsigned v2264 = starked_add(v188, v2263);
    const unsigned v2265 = 29u;
    const unsigned v2266 = starked_add(v188, v2265);
    const unsigned v2267 = 30u;
    const unsigned v2268 = starked_add(v188, v2267);
    const unsigned v2269 = 31u;
    const unsigned v2270 = starked_add(v188, v2269);
    const unsigned v2271 = 32u;
    const unsigned v2272 = starked_add(v188, v2271);
    const unsigned v2273 = 33u;
    const unsigned v2274 = starked_add(v188, v2273);
    const unsigned v2275 = 34u;
    const unsigned v2276 = starked_add(v188, v2275);
    const unsigned v2277 = 35u;
    const unsigned v2278 = starked_add(v188, v2277);
    const unsigned v2279 = 36u;
    const unsigned v2280 = starked_add(v188, v2279);
    const unsigned v2281 = 37u;
    const unsigned v2282 = starked_add(v188, v2281);
    const unsigned v2283 = 38u;
    const unsigned v2284 = starked_add(v188, v2283);
    const unsigned v2285 = 39u;
    const unsigned v2286 = starked_add(v188, v2285);
    const unsigned v2287 = 40u;
    const unsigned v2288 = starked_add(v188, v2287);
    const unsigned v2289 = 41u;
    const unsigned v2290 = starked_add(v188, v2289);
    const unsigned v2291 = 42u;
    const unsigned v2292 = starked_add(v188, v2291);
    const unsigned v2293 = 43u;
    const unsigned v2294 = starked_add(v188, v2293);
    const unsigned v2295 = 44u;
    const unsigned v2296 = starked_add(v188, v2295);
    const unsigned v2297 = 45u;
    const unsigned v2298 = starked_add(v188, v2297);
    const unsigned v2299 = 46u;
    const unsigned v2300 = starked_add(v188, v2299);
    const unsigned v2301 = 47u;
    const unsigned v2302 = starked_add(v188, v2301);
    const unsigned v2303 = 48u;
    const unsigned v2304 = starked_add(v188, v2303);
    const unsigned v2305 = 50u;
    const unsigned v2306 = starked_add(v188, v2305);
    const unsigned v2307 = 51u;
    const unsigned v2308 = starked_add(v188, v2307);
    const unsigned v2309 = 52u;
    const unsigned v2310 = starked_add(v188, v2309);
    const unsigned v2311 = 53u;
    const unsigned v2312 = starked_add(v188, v2311);
    const unsigned v2313 = 54u;
    const unsigned v2314 = starked_add(v188, v2313);
    const unsigned v2315 = 55u;
    const unsigned v2316 = starked_add(v188, v2315);
    const unsigned v2317 = 56u;
    const unsigned v2318 = starked_add(v188, v2317);
    const unsigned v2319 = starked_mul(v243, v0);
    const unsigned v2320 = starked_neg(v1);
    const unsigned v2321 = starked_neg(v343);
    const unsigned v2322 = starked_mul(v205, v352);
    const unsigned v2323 = starked_add(v347, v2322);
    const unsigned v2324 = starked_mul(v205, v362);
    const unsigned v2325 = starked_add(v357, v2324);
    const unsigned v2326 = starked_mul(v205, v372);
    const unsigned v2327 = starked_add(v367, v2326);
    const unsigned v2328 = starked_mul(v205, v382);
    const unsigned v2329 = starked_add(v377, v2328);
    const unsigned v2330 = starked_mul(v205, v392);
    const unsigned v2331 = starked_add(v387, v2330);
    const unsigned v2332 = starked_mul(v205, v402);
    const unsigned v2333 = starked_add(v397, v2332);
    const unsigned v2334 = starked_mul(v205, v412);
    const unsigned v2335 = starked_add(v407, v2334);
    const unsigned v2336 = starked_mul(v205, v422);
    const unsigned v2337 = starked_add(v417, v2336);
    const unsigned v2338 = starked_mul(v205, v432);
    const unsigned v2339 = starked_add(v427, v2338);
    const unsigned v2340 = starked_mul(v205, v442);
    const unsigned v2341 = starked_add(v437, v2340);
    const unsigned v2342 = starked_mul(v205, v452);
    const unsigned v2343 = starked_add(v447, v2342);
    const unsigned v2344 = starked_mul(v205, v462);
    const unsigned v2345 = starked_add(v457, v2344);
    const unsigned v2346 = starked_mul(v205, v472);
    const unsigned v2347 = starked_add(v467, v2346);
    const unsigned v2348 = starked_mul(v205, v482);
    const unsigned v2349 = starked_add(v477, v2348);
    const unsigned v2350 = starked_mul(v205, v492);
    const unsigned v2351 = starked_add(v487, v2350);
    const unsigned v2352 = starked_mul(v205, v502);
    const unsigned v2353 = starked_add(v497, v2352);
    const unsigned v2354 = starked_mul(v205, v512);
    const unsigned v2355 = starked_add(v507, v2354);
    const unsigned v2356 = starked_mul(v205, v522);
    const unsigned v2357 = starked_add(v517, v2356);
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
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v2211));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v346));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 3u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v2212));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v351));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 3u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v2213));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v356));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 3u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v2215));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v361));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 3u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v2217));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v366));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 3u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v2219));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v371));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 3u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v2221));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v376));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 3u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v2223));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v381));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 3u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v2224));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v386));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 3u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v2226));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v391));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 3u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v2228));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v396));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 3u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v2230));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v401));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 3u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v2232));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v406));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 3u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v2234));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v411));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 3u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v2236));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v416));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 3u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v2238));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v421));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 3u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v2240));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v426));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 3u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v2242));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v431));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 3u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v2244));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha2, v436));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 3u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v2246));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha2, v441));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 3u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v2248));
    d20 = starked_q_add(d20, starked_q_mul_base(alpha2, v446));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 3u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v2250));
    d21 = starked_q_add(d21, starked_q_mul_base(alpha2, v451));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 3u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v2252));
    d22 = starked_q_add(d22, starked_q_mul_base(alpha2, v456));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 3u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v2254));
    d23 = starked_q_add(d23, starked_q_mul_base(alpha2, v461));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 3u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v2256));
    d24 = starked_q_add(d24, starked_q_mul_base(alpha2, v466));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 3u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v2258));
    d25 = starked_q_add(d25, starked_q_mul_base(alpha2, v471));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 3u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v2260));
    d26 = starked_q_add(d26, starked_q_mul_base(alpha2, v476));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 3u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v2262));
    d27 = starked_q_add(d27, starked_q_mul_base(alpha2, v481));
    StarkedQm31 d28 = minus_z;
    d28.a = starked_add(d28.a, 3u);
    d28 = starked_q_add(d28, starked_q_mul_base(alpha1, v2264));
    d28 = starked_q_add(d28, starked_q_mul_base(alpha2, v486));
    StarkedQm31 d29 = minus_z;
    d29.a = starked_add(d29.a, 3u);
    d29 = starked_q_add(d29, starked_q_mul_base(alpha1, v2266));
    d29 = starked_q_add(d29, starked_q_mul_base(alpha2, v491));
    StarkedQm31 d30 = minus_z;
    d30.a = starked_add(d30.a, 3u);
    d30 = starked_q_add(d30, starked_q_mul_base(alpha1, v2268));
    d30 = starked_q_add(d30, starked_q_mul_base(alpha2, v496));
    StarkedQm31 d31 = minus_z;
    d31.a = starked_add(d31.a, 3u);
    d31 = starked_q_add(d31, starked_q_mul_base(alpha1, v2270));
    d31 = starked_q_add(d31, starked_q_mul_base(alpha2, v501));
    StarkedQm31 d32 = minus_z;
    d32.a = starked_add(d32.a, 3u);
    d32 = starked_q_add(d32, starked_q_mul_base(alpha1, v2272));
    d32 = starked_q_add(d32, starked_q_mul_base(alpha2, v521));
    StarkedQm31 d33 = minus_z;
    d33.a = starked_add(d33.a, 3u);
    d33 = starked_q_add(d33, starked_q_mul_base(alpha1, v2274));
    d33 = starked_q_add(d33, starked_q_mul_base(alpha2, v516));
    StarkedQm31 d34 = minus_z;
    d34.a = starked_add(d34.a, 3u);
    d34 = starked_q_add(d34, starked_q_mul_base(alpha1, v2276));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha2, v511));
    StarkedQm31 d35 = minus_z;
    d35.a = starked_add(d35.a, 3u);
    d35 = starked_q_add(d35, starked_q_mul_base(alpha1, v2278));
    d35 = starked_q_add(d35, starked_q_mul_base(alpha2, v506));
    StarkedQm31 d36 = minus_z;
    d36.a = starked_add(d36.a, 3u);
    d36 = starked_q_add(d36, starked_q_mul_base(alpha1, v2280));
    d36 = starked_q_add(d36, starked_q_mul_base(alpha2, v244));
    StarkedQm31 d37 = minus_z;
    d37.a = starked_add(d37.a, 3u);
    d37 = starked_q_add(d37, starked_q_mul_base(alpha1, v2282));
    d37 = starked_q_add(d37, starked_q_mul_base(alpha2, v251));
    StarkedQm31 d38 = minus_z;
    d38.a = starked_add(d38.a, 3u);
    d38 = starked_q_add(d38, starked_q_mul_base(alpha1, v2284));
    d38 = starked_q_add(d38, starked_q_mul_base(alpha2, v258));
    StarkedQm31 d39 = minus_z;
    d39.a = starked_add(d39.a, 3u);
    d39 = starked_q_add(d39, starked_q_mul_base(alpha1, v2286));
    d39 = starked_q_add(d39, starked_q_mul_base(alpha2, v240));
    StarkedQm31 d40 = minus_z;
    d40.a = starked_add(d40.a, 3u);
    d40 = starked_q_add(d40, starked_q_mul_base(alpha1, v2288));
    d40 = starked_q_add(d40, starked_q_mul_base(alpha2, v236));
    StarkedQm31 d41 = minus_z;
    d41.a = starked_add(d41.a, 3u);
    d41 = starked_q_add(d41, starked_q_mul_base(alpha1, v2290));
    d41 = starked_q_add(d41, starked_q_mul_base(alpha2, v1553));
    StarkedQm31 d42 = minus_z;
    d42.a = starked_add(d42.a, 3u);
    d42 = starked_q_add(d42, starked_q_mul_base(alpha1, v2292));
    d42 = starked_q_add(d42, starked_q_mul_base(alpha2, v1554));
    StarkedQm31 d43 = minus_z;
    d43.a = starked_add(d43.a, 3u);
    d43 = starked_q_add(d43, starked_q_mul_base(alpha1, v2294));
    d43 = starked_q_add(d43, starked_q_mul_base(alpha2, v1557));
    StarkedQm31 d44 = minus_z;
    d44.a = starked_add(d44.a, 3u);
    d44 = starked_q_add(d44, starked_q_mul_base(alpha1, v2296));
    d44 = starked_q_add(d44, starked_q_mul_base(alpha2, v1561));
    StarkedQm31 d45 = minus_z;
    d45.a = starked_add(d45.a, 3u);
    d45 = starked_q_add(d45, starked_q_mul_base(alpha1, v2298));
    d45 = starked_q_add(d45, starked_q_mul_base(alpha2, v215));
    StarkedQm31 d46 = minus_z;
    d46.a = starked_add(d46.a, 3u);
    d46 = starked_q_add(d46, starked_q_mul_base(alpha1, v2300));
    d46 = starked_q_add(d46, starked_q_mul_base(alpha2, v216));
    StarkedQm31 d47 = minus_z;
    d47.a = starked_add(d47.a, 3u);
    d47 = starked_q_add(d47, starked_q_mul_base(alpha1, v2302));
    d47 = starked_q_add(d47, starked_q_mul_base(alpha2, v219));
    StarkedQm31 d48 = minus_z;
    d48.a = starked_add(d48.a, 3u);
    d48 = starked_q_add(d48, starked_q_mul_base(alpha1, v2304));
    d48 = starked_q_add(d48, starked_q_mul_base(alpha2, v223));
    StarkedQm31 d49 = minus_z;
    d49.a = starked_add(d49.a, 3u);
    d49 = starked_q_add(d49, starked_q_mul_base(alpha1, v198));
    d49 = starked_q_add(d49, starked_q_mul_base(alpha2, v930));
    StarkedQm31 d50 = minus_z;
    d50.a = starked_add(d50.a, 3u);
    d50 = starked_q_add(d50, starked_q_mul_base(alpha1, v2306));
    d50 = starked_q_add(d50, starked_q_mul_base(alpha2, v943));
    StarkedQm31 d51 = minus_z;
    d51.a = starked_add(d51.a, 3u);
    d51 = starked_q_add(d51, starked_q_mul_base(alpha1, v2308));
    d51 = starked_q_add(d51, starked_q_mul_base(alpha2, v956));
    StarkedQm31 d52 = minus_z;
    d52.a = starked_add(d52.a, 3u);
    d52 = starked_q_add(d52, starked_q_mul_base(alpha1, v2310));
    d52 = starked_q_add(d52, starked_q_mul_base(alpha2, v969));
    StarkedQm31 d53 = minus_z;
    d53.a = starked_add(d53.a, 3u);
    d53 = starked_q_add(d53, starked_q_mul_base(alpha1, v2312));
    d53 = starked_q_add(d53, starked_q_mul_base(alpha2, v982));
    StarkedQm31 d54 = minus_z;
    d54.a = starked_add(d54.a, 3u);
    d54 = starked_q_add(d54, starked_q_mul_base(alpha1, v2314));
    d54 = starked_q_add(d54, starked_q_mul_base(alpha2, v995));
    StarkedQm31 d55 = minus_z;
    d55.a = starked_add(d55.a, 3u);
    d55 = starked_q_add(d55, starked_q_mul_base(alpha1, v2316));
    d55 = starked_q_add(d55, starked_q_mul_base(alpha2, v1008));
    StarkedQm31 d56 = minus_z;
    d56.a = starked_add(d56.a, 3u);
    d56 = starked_q_add(d56, starked_q_mul_base(alpha1, v2318));
    d56 = starked_q_add(d56, starked_q_mul_base(alpha2, v1021));
    StarkedQm31 d57 = minus_z;
    d57.a = starked_add(d57.a, 32u);
    d57 = starked_q_add(d57, starked_q_mul_base(alpha1, v175));
    d57 = starked_q_add(d57, starked_q_mul_base(alpha2, v188));
    d57 = starked_q_add(d57, starked_q_mul_base(alpha3, v199));
    StarkedQm31 d58 = minus_z;
    d58.a = starked_add(d58.a, 33u);
    d58 = starked_q_add(d58, starked_q_mul_base(alpha1, v175));
    d58 = starked_q_add(d58, starked_q_mul_base(alpha2, v303));
    d58 = starked_q_add(d58, starked_q_mul_base(alpha3, v242));
    StarkedQm31 d59 = minus_z;
    d59.a = starked_add(d59.a, 33u);
    d59 = starked_q_add(d59, starked_q_mul_base(alpha1, v175));
    d59 = starked_q_add(d59, starked_q_mul_base(alpha2, v1));
    d59 = starked_q_add(d59, starked_q_mul_base(alpha3, v250));
    StarkedQm31 d60 = minus_z;
    d60.a = starked_add(d60.a, 33u);
    d60 = starked_q_add(d60, starked_q_mul_base(alpha1, v175));
    d60 = starked_q_add(d60, starked_q_mul_base(alpha2, v243));
    d60 = starked_q_add(d60, starked_q_mul_base(alpha3, v257));
    StarkedQm31 d61 = minus_z;
    d61.a = starked_add(d61.a, 33u);
    d61 = starked_q_add(d61, starked_q_mul_base(alpha1, v175));
    d61 = starked_q_add(d61, starked_q_mul_base(alpha2, v2214));
    d61 = starked_q_add(d61, starked_q_mul_base(alpha3, v264));
    StarkedQm31 d62 = minus_z;
    d62.a = starked_add(d62.a, 21u);
    d62 = starked_q_add(d62, starked_q_mul_base(alpha1, v303));
    d62 = starked_q_add(d62, starked_q_mul_base(alpha2, v175));
    d62 = starked_q_add(d62, starked_q_mul_base(alpha3, v198));
    d62 = starked_q_add(d62, starked_q_mul_base(alpha4, v199));
    StarkedQm31 d63 = minus_z;
    d63.a = starked_add(d63.a, 22u);
    d63 = starked_q_add(d63, starked_q_mul_base(alpha1, v303));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha2, v175));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha3, v199));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha4, v1469));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha5, v1486));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha6, v1503));
    d63 = starked_q_add(d63, starked_q_mul_base(alpha7, v1520));
    StarkedQm31 d64 = minus_z;
    d64.a = starked_add(d64.a, 9u);
    d64 = starked_q_add(d64, starked_q_mul_base(alpha1, v242));
    StarkedQm31 d65 = minus_z;
    d65.a = starked_add(d65.a, 9u);
    d65 = starked_q_add(d65, starked_q_mul_base(alpha1, v250));
    StarkedQm31 d66 = minus_z;
    d66.a = starked_add(d66.a, 9u);
    d66 = starked_q_add(d66, starked_q_mul_base(alpha1, v257));
    StarkedQm31 d67 = minus_z;
    d67.a = starked_add(d67.a, 9u);
    d67 = starked_q_add(d67, starked_q_mul_base(alpha1, v227));
    StarkedQm31 d68 = minus_z;
    d68.a = starked_add(d68.a, 9u);
    d68 = starked_q_add(d68, starked_q_mul_base(alpha1, v228));
    StarkedQm31 d69 = minus_z;
    d69.a = starked_add(d69.a, 9u);
    d69 = starked_q_add(d69, starked_q_mul_base(alpha1, v231));
    StarkedQm31 d70 = minus_z;
    d70.a = starked_add(d70.a, 9u);
    d70 = starked_q_add(d70, starked_q_mul_base(alpha1, v204));
    StarkedQm31 d71 = minus_z;
    d71.a = starked_add(d71.a, 9u);
    d71 = starked_q_add(d71, starked_q_mul_base(alpha1, v206));
    StarkedQm31 d72 = minus_z;
    d72.a = starked_add(d72.a, 9u);
    d72 = starked_q_add(d72, starked_q_mul_base(alpha1, v210));
    StarkedQm31 d73 = minus_z;
    d73.a = starked_add(d73.a, 9u);
    d73 = starked_q_add(d73, starked_q_mul_base(alpha1, v285));
    StarkedQm31 d74 = minus_z;
    d74.a = starked_add(d74.a, 9u);
    d74 = starked_q_add(d74, starked_q_mul_base(alpha1, v286));
    StarkedQm31 d75 = minus_z;
    d75.a = starked_add(d75.a, 9u);
    d75 = starked_q_add(d75, starked_q_mul_base(alpha1, v289));
    StarkedQm31 d76 = minus_z;
    d76.a = starked_add(d76.a, 9u);
    d76 = starked_q_add(d76, starked_q_mul_base(alpha1, v924));
    StarkedQm31 d77 = minus_z;
    d77.a = starked_add(d77.a, 9u);
    d77 = starked_q_add(d77, starked_q_mul_base(alpha1, v937));
    StarkedQm31 d78 = minus_z;
    d78.a = starked_add(d78.a, 9u);
    d78 = starked_q_add(d78, starked_q_mul_base(alpha1, v950));
    StarkedQm31 d79 = minus_z;
    d79.a = starked_add(d79.a, 9u);
    d79 = starked_q_add(d79, starked_q_mul_base(alpha1, v963));
    StarkedQm31 d80 = minus_z;
    d80.a = starked_add(d80.a, 9u);
    d80 = starked_q_add(d80, starked_q_mul_base(alpha1, v976));
    StarkedQm31 d81 = minus_z;
    d81.a = starked_add(d81.a, 9u);
    d81 = starked_q_add(d81, starked_q_mul_base(alpha1, v989));
    StarkedQm31 d82 = minus_z;
    d82.a = starked_add(d82.a, 9u);
    d82 = starked_q_add(d82, starked_q_mul_base(alpha1, v1002));
    StarkedQm31 d83 = minus_z;
    d83.a = starked_add(d83.a, 9u);
    d83 = starked_q_add(d83, starked_q_mul_base(alpha1, v1015));
    StarkedQm31 d84 = minus_z;
    d84.a = starked_add(d84.a, 9u);
    d84 = starked_q_add(d84, starked_q_mul_base(alpha1, v1028));
    StarkedQm31 d85 = minus_z;
    d85.a = starked_add(d85.a, 9u);
    d85 = starked_q_add(d85, starked_q_mul_base(alpha1, v1039));
    StarkedQm31 d86 = minus_z;
    d86.a = starked_add(d86.a, 9u);
    d86 = starked_q_add(d86, starked_q_mul_base(alpha1, v1050));
    StarkedQm31 d87 = minus_z;
    d87.a = starked_add(d87.a, 9u);
    d87 = starked_q_add(d87, starked_q_mul_base(alpha1, v1061));
    StarkedQm31 d88 = minus_z;
    d88.a = starked_add(d88.a, 9u);
    d88 = starked_q_add(d88, starked_q_mul_base(alpha1, v345));
    StarkedQm31 d89 = minus_z;
    d89.a = starked_add(d89.a, 36u);
    d89 = starked_q_add(d89, starked_q_mul_base(alpha1, v175));
    d89 = starked_q_add(d89, starked_q_mul_base(alpha2, v303));
    d89 = starked_q_add(d89, starked_q_mul_base(alpha3, v2323));
    d89 = starked_q_add(d89, starked_q_mul_base(alpha4, v2325));
    StarkedQm31 d90 = minus_z;
    d90.a = starked_add(d90.a, 36u);
    d90 = starked_q_add(d90, starked_q_mul_base(alpha1, v175));
    d90 = starked_q_add(d90, starked_q_mul_base(alpha2, v1));
    d90 = starked_q_add(d90, starked_q_mul_base(alpha3, v2327));
    d90 = starked_q_add(d90, starked_q_mul_base(alpha4, v2329));
    StarkedQm31 d91 = minus_z;
    d91.a = starked_add(d91.a, 36u);
    d91 = starked_q_add(d91, starked_q_mul_base(alpha1, v175));
    d91 = starked_q_add(d91, starked_q_mul_base(alpha2, v243));
    d91 = starked_q_add(d91, starked_q_mul_base(alpha3, v2331));
    d91 = starked_q_add(d91, starked_q_mul_base(alpha4, v2333));
    StarkedQm31 d92 = minus_z;
    d92.a = starked_add(d92.a, 36u);
    d92 = starked_q_add(d92, starked_q_mul_base(alpha1, v175));
    d92 = starked_q_add(d92, starked_q_mul_base(alpha2, v2214));
    d92 = starked_q_add(d92, starked_q_mul_base(alpha3, v2335));
    d92 = starked_q_add(d92, starked_q_mul_base(alpha4, v2337));
    StarkedQm31 d93 = minus_z;
    d93.a = starked_add(d93.a, 36u);
    d93 = starked_q_add(d93, starked_q_mul_base(alpha1, v175));
    d93 = starked_q_add(d93, starked_q_mul_base(alpha2, v2216));
    d93 = starked_q_add(d93, starked_q_mul_base(alpha3, v2339));
    d93 = starked_q_add(d93, starked_q_mul_base(alpha4, v2341));
    StarkedQm31 d94 = minus_z;
    d94.a = starked_add(d94.a, 36u);
    d94 = starked_q_add(d94, starked_q_mul_base(alpha1, v175));
    d94 = starked_q_add(d94, starked_q_mul_base(alpha2, v2218));
    d94 = starked_q_add(d94, starked_q_mul_base(alpha3, v2343));
    d94 = starked_q_add(d94, starked_q_mul_base(alpha4, v2345));
    StarkedQm31 d95 = minus_z;
    d95.a = starked_add(d95.a, 36u);
    d95 = starked_q_add(d95, starked_q_mul_base(alpha1, v175));
    d95 = starked_q_add(d95, starked_q_mul_base(alpha2, v2220));
    d95 = starked_q_add(d95, starked_q_mul_base(alpha3, v2347));
    d95 = starked_q_add(d95, starked_q_mul_base(alpha4, v2349));
    StarkedQm31 d96 = minus_z;
    d96.a = starked_add(d96.a, 36u);
    d96 = starked_q_add(d96, starked_q_mul_base(alpha1, v175));
    d96 = starked_q_add(d96, starked_q_mul_base(alpha2, v2222));
    d96 = starked_q_add(d96, starked_q_mul_base(alpha3, v2351));
    d96 = starked_q_add(d96, starked_q_mul_base(alpha4, v2353));
    StarkedQm31 d97 = minus_z;
    d97.a = starked_add(d97.a, 36u);
    d97 = starked_q_add(d97, starked_q_mul_base(alpha1, v175));
    d97 = starked_q_add(d97, starked_q_mul_base(alpha2, v225));
    d97 = starked_q_add(d97, starked_q_mul_base(alpha3, v2355));
    d97 = starked_q_add(d97, starked_q_mul_base(alpha4, v2357));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v2210), starked_q_mul_base(d0, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v2210), starked_q_mul_base(d2, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v2210), starked_q_mul_base(d4, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v2210), starked_q_mul_base(d6, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v2210), starked_q_mul_base(d8, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v2210), starked_q_mul_base(d10, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v2210), starked_q_mul_base(d12, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v2210), starked_q_mul_base(d14, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v2210), starked_q_mul_base(d16, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v2210), starked_q_mul_base(d18, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v2210), starked_q_mul_base(d20, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v2210), starked_q_mul_base(d22, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v2210), starked_q_mul_base(d24, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v2210), starked_q_mul_base(d26, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d29, v2210), starked_q_mul_base(d28, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d31, v2210), starked_q_mul_base(d30, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d33, v2210), starked_q_mul_base(d32, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d35, v2210), starked_q_mul_base(d34, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d37, v2210), starked_q_mul_base(d36, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d39, v2210), starked_q_mul_base(d38, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d41, v2210), starked_q_mul_base(d40, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d43, v2210), starked_q_mul_base(d42, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d45, v2210), starked_q_mul_base(d44, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d47, v2210), starked_q_mul_base(d46, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d49, v2210), starked_q_mul_base(d48, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d51, v2210), starked_q_mul_base(d50, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d53, v2210), starked_q_mul_base(d52, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d55, v2210), starked_q_mul_base(d54, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d57, v2210), starked_q_mul_base(d56, v2319));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d59, v0), starked_q_mul_base(d58, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d61, v0), starked_q_mul_base(d60, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d63, v0), starked_q_mul_base(d62, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d65, v2210), starked_q_mul_base(d64, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d67, v2210), starked_q_mul_base(d66, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d69, v2210), starked_q_mul_base(d68, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d71, v2210), starked_q_mul_base(d70, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d73, v2210), starked_q_mul_base(d72, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d75, v2210), starked_q_mul_base(d74, v2210));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d77, v2320), starked_q_mul_base(d76, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d79, v2320), starked_q_mul_base(d78, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d81, v2320), starked_q_mul_base(d80, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d83, v2320), starked_q_mul_base(d82, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d85, v2320), starked_q_mul_base(d84, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d87, v2320), starked_q_mul_base(d86, v2320));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d89, v2321), starked_q_mul_base(d88, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d91, v0), starked_q_mul_base(d90, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d93, v0), starked_q_mul_base(d92, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d95, v0), starked_q_mul_base(d94, v0));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d97, v0), starked_q_mul_base(d96, v0));
        const StarkedQm31 d = starked_q_mul(d96, d97);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[192][row] = n.a;
        outputs[193][row] = n.b;
        outputs[194][row] = n.c;
        outputs[195][row] = n.d;
        unsigned *slot = denominators + ((u64)48u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
