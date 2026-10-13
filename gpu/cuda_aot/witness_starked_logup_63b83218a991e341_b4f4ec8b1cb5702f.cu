// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_fields, digest f824c28a2b1caac7a3b63d663ab143fa98475a1ae21150b2c585534f7917930f.
// 36 lookups in 18 batches, 57 source columns, tuples up to 7 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_63b83218a991e341(
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
    const unsigned v4 = sources[(u64)2u * rows + r_0];
    const unsigned v7 = sources[(u64)3u * rows + r_0];
    const unsigned v13 = sources[(u64)4u * rows + r_0];
    const unsigned v22 = sources[(u64)5u * rows + r_0];
    const unsigned v25 = sources[(u64)6u * rows + r_0];
    const unsigned v28 = 0u;
    const unsigned v39 = sources[(u64)0u * rows + r_0];
    const unsigned v41 = sources[(u64)1u * rows + r_0];
    const unsigned v42 = starked_sub(v1, v41);
    const unsigned v98 = sources[(u64)7u * rows + r_0];
    const unsigned v108 = sources[(u64)8u * rows + r_0];
    const unsigned v111 = 3u;
    const unsigned v112 = sources[(u64)12u * rows + r_0];
    const unsigned v114 = 5u;
    const unsigned v115 = sources[(u64)13u * rows + r_0];
    const unsigned v121 = 4u;
    const unsigned v122 = 2u;
    const unsigned v123 = sources[(u64)10u * rows + r_0];
    const unsigned v130 = sources[(u64)9u * rows + r_0];
    const unsigned v178 = 256u;
    const unsigned v210 = 65536u;
    const unsigned v242 = 16777216u;
    const unsigned v247 = sources[(u64)11u * rows + r_0];
    const unsigned v257 = starked_add(v112, v115);
    const unsigned v259 = starked_add(v22, v25);
    const unsigned v260 = starked_sub(v1, v259);
    const unsigned v262 = sources[(u64)14u * rows + r_0];
    const unsigned v264 = sources[(u64)15u * rows + r_0];
    const unsigned v265 = sources[(u64)16u * rows + r_0];
    const unsigned v269 = sources[(u64)17u * rows + r_0];
    const unsigned v271 = sources[(u64)18u * rows + r_0];
    const unsigned v727 = sources[(u64)19u * rows + r_0];
    const unsigned v734 = sources[(u64)20u * rows + r_0];
    const unsigned v741 = sources[(u64)21u * rows + r_0];
    const unsigned v781 = sources[(u64)23u * rows + r_0];
    const unsigned v786 = sources[(u64)31u * rows + r_0];
    const unsigned v788 = sources[(u64)35u * rows + r_0];
    const unsigned v789 = 7u;
    const unsigned v790 = sources[(u64)30u * rows + r_0];
    const unsigned v795 = sources[(u64)36u * rows + r_0];
    const unsigned v796 = sources[(u64)37u * rows + r_0];
    const unsigned v799 = sources[(u64)38u * rows + r_0];
    const unsigned v804 = sources[(u64)39u * rows + r_0];
    const unsigned v805 = sources[(u64)40u * rows + r_0];
    const unsigned v808 = sources[(u64)41u * rows + r_0];
    const unsigned v818 = sources[(u64)42u * rows + r_0];
    const unsigned v819 = sources[(u64)43u * rows + r_0];
    const unsigned v822 = sources[(u64)44u * rows + r_0];
    const unsigned v825 = sources[(u64)45u * rows + r_0];
    const unsigned v834 = sources[(u64)46u * rows + r_0];
    const unsigned v848 = sources[(u64)24u * rows + r_0];
    const unsigned v849 = sources[(u64)25u * rows + r_0];
    const unsigned v850 = starked_mul(v178, v849);
    const unsigned v851 = starked_add(v848, v850);
    const unsigned v852 = sources[(u64)26u * rows + r_0];
    const unsigned v853 = starked_mul(v210, v852);
    const unsigned v854 = starked_add(v851, v853);
    const unsigned v863 = sources[(u64)27u * rows + r_0];
    const unsigned v864 = sources[(u64)28u * rows + r_0];
    const unsigned v865 = starked_mul(v178, v864);
    const unsigned v866 = starked_add(v863, v865);
    const unsigned v867 = sources[(u64)29u * rows + r_0];
    const unsigned v868 = starked_mul(v210, v867);
    const unsigned v869 = starked_add(v866, v868);
    const unsigned v870 = starked_mul(v242, v790);
    const unsigned v871 = starked_add(v869, v870);
    const unsigned v889 = sources[(u64)34u * rows + r_0];
    const unsigned v931 = sources[(u64)56u * rows + r_0];
    const unsigned v946 = sources[(u64)32u * rows + r_0];
    const unsigned v961 = sources[(u64)52u * rows + r_0];
    const unsigned v1001 = starked_add(v889, v931);
    const unsigned v1002 = sources[(u64)33u * rows + r_0];
    const unsigned v1063 = sources[(u64)48u * rows + r_0];
    const unsigned v1073 = sources[(u64)49u * rows + r_0];
    const unsigned v1089 = starked_mul(v4, v123);
    const unsigned v1094 = sources[(u64)50u * rows + r_0];
    const unsigned v1100 = sources[(u64)51u * rows + r_0];
    const unsigned v1106 = starked_add(v98, v247);
    const unsigned v1109 = sources[(u64)53u * rows + r_0];
    const unsigned v1113 = starked_sub(v1, v1109);
    const unsigned v1123 = sources[(u64)54u * rows + r_0];
    const unsigned v1136 = sources[(u64)55u * rows + r_0];
    const unsigned v1160 = sources[(u64)47u * rows + r_0];
    const unsigned v1165 = starked_neg(v260);
    const unsigned v1166 = starked_neg(v257);
    const unsigned v1167 = starked_add(v1106, v1);
    const unsigned v1168 = starked_add(v1106, v122);
    const unsigned v1169 = starked_neg(v115);
    const unsigned v1170 = starked_add(v1106, v111);
    const unsigned v1171 = starked_add(v1106, v121);
    const unsigned v1172 = starked_neg(v1089);
    const unsigned v1173 = starked_add(v98, v121);
    const unsigned v1174 = starked_add(v98, v114);
    const unsigned v1175 = sources[(u64)22u * rows + r_0];
    const unsigned v1176 = starked_mul(v22, v1175);
    const unsigned v1177 = starked_add(v22, v7);
    const unsigned v1178 = starked_add(v13, v1177);
    const unsigned v1179 = starked_neg(v1178);
    const unsigned v1180 = starked_add(v781, v28);
    const unsigned v1181 = starked_add(v781, v1);
    const unsigned v1182 = starked_add(v781, v122);
    const unsigned v1183 = starked_add(v781, v111);
    const unsigned v1184 = starked_neg(v13);
    const unsigned v1185 = starked_add(v781, v121);
    const unsigned v1186 = starked_add(v781, v114);
    const unsigned v1187 = 6u;
    const unsigned v1188 = starked_add(v781, v1187);
    const unsigned v1189 = starked_add(v781, v789);
    const unsigned v1190 = starked_neg(v1001);
    const unsigned v1191 = starked_neg(v1);
    const unsigned v1192 = starked_add(v7, v13);
    const unsigned v1193 = starked_mul(v1192, v1113);
    const unsigned v1194 = starked_neg(v39);
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
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v1106));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v262));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 3u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v1167));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v264));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 3u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v1168));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v265));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 3u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v1170));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v269));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 3u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v1171));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v271));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 3u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v1173));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v28));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 3u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v1174));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v1));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 4u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v741));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v727));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v123));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v734));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha5, v98));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 3u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v1180));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v848));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 3u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v1181));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v849));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 3u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v1182));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v852));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 3u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v1183));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v863));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 3u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v1185));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v864));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 3u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v1186));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v867));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 3u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v1188));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v790));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 3u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v1189));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v786));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 3u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v946));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v1002));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 9u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v788));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 9u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v795));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 9u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v796));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 9u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v799));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 9u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v804));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 9u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v805));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 9u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v808));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 9u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v818));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 9u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v819));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 9u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v822));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 9u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v825));
    StarkedQm31 d28 = minus_z;
    d28.a = starked_add(d28.a, 9u);
    d28 = starked_q_add(d28, starked_q_mul_base(alpha1, v834));
    StarkedQm31 d29 = minus_z;
    d29.a = starked_add(d29.a, 9u);
    d29 = starked_q_add(d29, starked_q_mul_base(alpha1, v1160));
    StarkedQm31 d30 = minus_z;
    d30.a = starked_add(d30.a, 11u);
    d30 = starked_q_add(d30, starked_q_mul_base(alpha1, v961));
    d30 = starked_q_add(d30, starked_q_mul_base(alpha2, v130));
    StarkedQm31 d31 = minus_z;
    d31.a = starked_add(d31.a, 12u);
    d31 = starked_q_add(d31, starked_q_mul_base(alpha1, v1094));
    d31 = starked_q_add(d31, starked_q_mul_base(alpha2, v1100));
    d31 = starked_q_add(d31, starked_q_mul_base(alpha3, v1136));
    StarkedQm31 d32 = minus_z;
    d32.a = starked_add(d32.a, 13u);
    d32 = starked_q_add(d32, starked_q_mul_base(alpha1, v1063));
    d32 = starked_q_add(d32, starked_q_mul_base(alpha2, v1073));
    StarkedQm31 d33 = minus_z;
    d33.a = starked_add(d33.a, 14u);
    d33 = starked_q_add(d33, starked_q_mul_base(alpha1, v961));
    d33 = starked_q_add(d33, starked_q_mul_base(alpha2, v130));
    StarkedQm31 d34 = minus_z;
    d34.a = starked_add(d34.a, 24u);
    d34 = starked_q_add(d34, starked_q_mul_base(alpha1, v741));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha2, v98));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha3, v108));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha4, v961));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha5, v130));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha6, v854));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha7, v871));
    StarkedQm31 d35 = minus_z;
    d35.a = starked_add(d35.a, 25u);
    d35 = starked_q_add(d35, starked_q_mul_base(alpha1, v741));
    d35 = starked_q_add(d35, starked_q_mul_base(alpha2, v98));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v1165), starked_q_mul_base(d0, v1166));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v1166), starked_q_mul_base(d2, v1169));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v1169), starked_q_mul_base(d4, v1172));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v1172), starked_q_mul_base(d6, v1176));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v1179), starked_q_mul_base(d8, v1179));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v1179), starked_q_mul_base(d10, v1179));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v1184), starked_q_mul_base(d12, v1184));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v1184), starked_q_mul_base(d14, v1184));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v1190), starked_q_mul_base(d16, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v1191), starked_q_mul_base(d18, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v1191), starked_q_mul_base(d20, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v1191), starked_q_mul_base(d22, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v1191), starked_q_mul_base(d24, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v1191), starked_q_mul_base(d26, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d29, v1191), starked_q_mul_base(d28, v1191));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d31, v1193), starked_q_mul_base(d30, v42));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d33, v1194), starked_q_mul_base(d32, v1123));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d35, v13), starked_q_mul_base(d34, v7));
        const StarkedQm31 d = starked_q_mul(d34, d35);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[68][row] = n.a;
        outputs[69][row] = n.b;
        outputs[70][row] = n.c;
        outputs[71][row] = n.d;
        unsigned *slot = denominators + ((u64)17u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
