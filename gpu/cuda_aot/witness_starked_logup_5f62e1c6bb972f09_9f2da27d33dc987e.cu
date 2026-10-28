// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_shac, digest 8e6a1c1f6fbc11e815b0b6e305afe30beac19af24ee51347e34feeaf53535a67.
// 2 lookups in 1 batches, 38 source columns, tuples up to 3 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_5f62e1c6bb972f09(
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
    const unsigned v193 = sources[(u64)3u * rows + r_0];
    const unsigned v196 = sources[(u64)4u * rows + r_0];
    const unsigned v199 = sources[(u64)5u * rows + r_0];
    const unsigned v202 = sources[(u64)6u * rows + r_0];
    const unsigned v205 = sources[(u64)7u * rows + r_0];
    const unsigned v208 = sources[(u64)8u * rows + r_0];
    const unsigned v211 = sources[(u64)9u * rows + r_0];
    const unsigned v214 = sources[(u64)10u * rows + r_0];
    const unsigned v217 = sources[(u64)11u * rows + r_0];
    const unsigned v220 = sources[(u64)12u * rows + r_0];
    const unsigned v223 = sources[(u64)13u * rows + r_0];
    const unsigned v226 = sources[(u64)14u * rows + r_0];
    const unsigned v229 = sources[(u64)15u * rows + r_0];
    const unsigned v232 = sources[(u64)16u * rows + r_0];
    const unsigned v235 = sources[(u64)17u * rows + r_0];
    const unsigned v238 = sources[(u64)18u * rows + r_0];
    const unsigned v241 = sources[(u64)19u * rows + r_0];
    const unsigned v244 = sources[(u64)20u * rows + r_0];
    const unsigned v247 = sources[(u64)21u * rows + r_0];
    const unsigned v250 = sources[(u64)22u * rows + r_0];
    const unsigned v253 = sources[(u64)23u * rows + r_0];
    const unsigned v256 = sources[(u64)24u * rows + r_0];
    const unsigned v259 = sources[(u64)25u * rows + r_0];
    const unsigned v262 = sources[(u64)26u * rows + r_0];
    const unsigned v265 = sources[(u64)27u * rows + r_0];
    const unsigned v268 = sources[(u64)28u * rows + r_0];
    const unsigned v271 = sources[(u64)29u * rows + r_0];
    const unsigned v274 = sources[(u64)30u * rows + r_0];
    const unsigned v277 = sources[(u64)31u * rows + r_0];
    const unsigned v280 = sources[(u64)32u * rows + r_0];
    const unsigned v283 = sources[(u64)33u * rows + r_0];
    const unsigned v286 = sources[(u64)34u * rows + r_0];
    const unsigned v338 = 0u;
    const unsigned v344 = 2u;
    const unsigned v352 = 4u;
    const unsigned v392 = 8u;
    const unsigned v410 = 16u;
    const unsigned v428 = 32u;
    const unsigned v446 = 64u;
    const unsigned v464 = 128u;
    const unsigned v482 = 256u;
    const unsigned v500 = 512u;
    const unsigned v517 = 1024u;
    const unsigned v534 = 2048u;
    const unsigned v550 = 4096u;
    const unsigned v565 = 8192u;
    const unsigned v580 = 16384u;
    const unsigned v595 = 32768u;
    const unsigned v2887 = starked_mul(v1, v193);
    const unsigned v2888 = starked_add(v338, v2887);
    const unsigned v2889 = starked_mul(v344, v196);
    const unsigned v2890 = starked_add(v2888, v2889);
    const unsigned v2891 = starked_mul(v352, v199);
    const unsigned v2892 = starked_add(v2890, v2891);
    const unsigned v2893 = starked_mul(v392, v202);
    const unsigned v2894 = starked_add(v2892, v2893);
    const unsigned v2895 = starked_mul(v410, v205);
    const unsigned v2896 = starked_add(v2894, v2895);
    const unsigned v2897 = starked_mul(v428, v208);
    const unsigned v2898 = starked_add(v2896, v2897);
    const unsigned v2899 = starked_mul(v446, v211);
    const unsigned v2900 = starked_add(v2898, v2899);
    const unsigned v2901 = starked_mul(v464, v214);
    const unsigned v2902 = starked_add(v2900, v2901);
    const unsigned v2903 = starked_mul(v482, v217);
    const unsigned v2904 = starked_add(v2902, v2903);
    const unsigned v2905 = starked_mul(v500, v220);
    const unsigned v2906 = starked_add(v2904, v2905);
    const unsigned v2907 = starked_mul(v517, v223);
    const unsigned v2908 = starked_add(v2906, v2907);
    const unsigned v2909 = starked_mul(v534, v226);
    const unsigned v2910 = starked_add(v2908, v2909);
    const unsigned v2911 = starked_mul(v550, v229);
    const unsigned v2912 = starked_add(v2910, v2911);
    const unsigned v2913 = starked_mul(v565, v232);
    const unsigned v2914 = starked_add(v2912, v2913);
    const unsigned v2915 = starked_mul(v580, v235);
    const unsigned v2916 = starked_add(v2914, v2915);
    const unsigned v2917 = starked_mul(v595, v238);
    const unsigned v2918 = starked_add(v2916, v2917);
    const unsigned v3018 = starked_mul(v1, v241);
    const unsigned v3019 = starked_add(v338, v3018);
    const unsigned v3020 = starked_mul(v344, v244);
    const unsigned v3021 = starked_add(v3019, v3020);
    const unsigned v3022 = starked_mul(v352, v247);
    const unsigned v3023 = starked_add(v3021, v3022);
    const unsigned v3024 = starked_mul(v392, v250);
    const unsigned v3025 = starked_add(v3023, v3024);
    const unsigned v3026 = starked_mul(v410, v253);
    const unsigned v3027 = starked_add(v3025, v3026);
    const unsigned v3028 = starked_mul(v428, v256);
    const unsigned v3029 = starked_add(v3027, v3028);
    const unsigned v3030 = starked_mul(v446, v259);
    const unsigned v3031 = starked_add(v3029, v3030);
    const unsigned v3032 = starked_mul(v464, v262);
    const unsigned v3033 = starked_add(v3031, v3032);
    const unsigned v3034 = starked_mul(v482, v265);
    const unsigned v3035 = starked_add(v3033, v3034);
    const unsigned v3036 = starked_mul(v500, v268);
    const unsigned v3037 = starked_add(v3035, v3036);
    const unsigned v3038 = starked_mul(v517, v271);
    const unsigned v3039 = starked_add(v3037, v3038);
    const unsigned v3040 = starked_mul(v534, v274);
    const unsigned v3041 = starked_add(v3039, v3040);
    const unsigned v3042 = starked_mul(v550, v277);
    const unsigned v3043 = starked_add(v3041, v3042);
    const unsigned v3044 = starked_mul(v565, v280);
    const unsigned v3045 = starked_add(v3043, v3044);
    const unsigned v3046 = starked_mul(v580, v283);
    const unsigned v3047 = starked_add(v3045, v3046);
    const unsigned v3048 = starked_mul(v595, v286);
    const unsigned v3049 = starked_add(v3047, v3048);
    const unsigned v3721 = sources[(u64)36u * rows + r_0];
    const unsigned v3724 = sources[(u64)37u * rows + r_0];
    const unsigned v3733 = sources[(u64)35u * rows + r_0];
    const unsigned v3832 = sources[(u64)2u * rows + r_0];
    const unsigned v3833 = starked_mul(v3721, v3832);
    const unsigned v4266 = sources[(u64)0u * rows + r_0];
    const unsigned v4267 = starked_mul(v4266, v3724);
    const unsigned v4268 = starked_neg(v4267);
    const unsigned v4269 = starked_mul(v446, v3733);
    const unsigned v4270 = sources[(u64)1u * rows + r_0];
    const unsigned v4271 = starked_mul(v352, v4270);
    const unsigned v4272 = starked_sub(v4271, v410);
    const unsigned v4273 = starked_add(v4269, v4272);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 34u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v4273));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v2918));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha3, v3049));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 35u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v3733));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v4268), starked_q_mul_base(d0, v3833));
        const StarkedQm31 d = starked_q_mul(d0, d1);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[0][row] = n.a;
        outputs[1][row] = n.b;
        outputs[2][row] = n.c;
        outputs[3][row] = n.d;
        unsigned *slot = denominators + ((u64)0u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
