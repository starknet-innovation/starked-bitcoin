// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR set_mt, digest 2cdfac5edbf111f58ef8d4bbf253afd8322a269c77f1349be7ccb184ec42e101.
// 33 lookups in 17 batches, 94 source columns, tuples up to 4 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_f3c8e1434d43fe86(
    const unsigned *sources, unsigned *const *outputs, const unsigned *pubs,
    const unsigned *powers, const unsigned *z, unsigned *denominators,
    unsigned *error, unsigned log_size) {
    const unsigned rows = 1u << log_size;
    const unsigned row = blockIdx.x * blockDim.x + threadIdx.x;
    if (row >= rows) return;
    const unsigned natural = starked_natural_row(row, log_size);
    (void)natural; (void)pubs;
    const u64 r_0 = row;
    const unsigned v0 = sources[(u64)7u * rows + r_0];
    const unsigned v1 = 1u;
    const unsigned v4 = sources[(u64)8u * rows + r_0];
    const unsigned v7 = sources[(u64)9u * rows + r_0];
    const unsigned v10 = sources[(u64)10u * rows + r_0];
    const unsigned v13 = sources[(u64)11u * rows + r_0];
    const unsigned v16 = sources[(u64)12u * rows + r_0];
    const unsigned v19 = sources[(u64)13u * rows + r_0];
    const unsigned v22 = sources[(u64)14u * rows + r_0];
    const unsigned v25 = sources[(u64)15u * rows + r_0];
    const unsigned v28 = sources[(u64)16u * rows + r_0];
    const unsigned v31 = sources[(u64)17u * rows + r_0];
    const unsigned v34 = sources[(u64)18u * rows + r_0];
    const unsigned v37 = sources[(u64)19u * rows + r_0];
    const unsigned v40 = sources[(u64)20u * rows + r_0];
    const unsigned v43 = sources[(u64)21u * rows + r_0];
    const unsigned v46 = sources[(u64)22u * rows + r_0];
    const unsigned v49 = sources[(u64)23u * rows + r_0];
    const unsigned v52 = sources[(u64)24u * rows + r_0];
    const unsigned v55 = sources[(u64)25u * rows + r_0];
    const unsigned v58 = sources[(u64)26u * rows + r_0];
    const unsigned v61 = sources[(u64)27u * rows + r_0];
    const unsigned v64 = sources[(u64)28u * rows + r_0];
    const unsigned v67 = sources[(u64)29u * rows + r_0];
    const unsigned v70 = sources[(u64)30u * rows + r_0];
    const unsigned v73 = sources[(u64)31u * rows + r_0];
    const unsigned v76 = sources[(u64)32u * rows + r_0];
    const unsigned v79 = sources[(u64)33u * rows + r_0];
    const unsigned v82 = sources[(u64)34u * rows + r_0];
    const unsigned v85 = sources[(u64)35u * rows + r_0];
    const unsigned v88 = sources[(u64)36u * rows + r_0];
    const unsigned v91 = sources[(u64)37u * rows + r_0];
    const unsigned v94 = sources[(u64)38u * rows + r_0];
    const unsigned v97 = sources[(u64)39u * rows + r_0];
    const unsigned v100 = sources[(u64)40u * rows + r_0];
    const unsigned v103 = sources[(u64)41u * rows + r_0];
    const unsigned v106 = sources[(u64)42u * rows + r_0];
    const unsigned v109 = sources[(u64)43u * rows + r_0];
    const unsigned v112 = sources[(u64)44u * rows + r_0];
    const unsigned v115 = sources[(u64)45u * rows + r_0];
    const unsigned v118 = sources[(u64)46u * rows + r_0];
    const unsigned v121 = sources[(u64)47u * rows + r_0];
    const unsigned v124 = sources[(u64)48u * rows + r_0];
    const unsigned v127 = sources[(u64)49u * rows + r_0];
    const unsigned v130 = sources[(u64)50u * rows + r_0];
    const unsigned v133 = sources[(u64)51u * rows + r_0];
    const unsigned v136 = sources[(u64)52u * rows + r_0];
    const unsigned v139 = sources[(u64)53u * rows + r_0];
    const unsigned v142 = sources[(u64)54u * rows + r_0];
    const unsigned v145 = sources[(u64)55u * rows + r_0];
    const unsigned v148 = sources[(u64)56u * rows + r_0];
    const unsigned v151 = sources[(u64)57u * rows + r_0];
    const unsigned v154 = sources[(u64)58u * rows + r_0];
    const unsigned v157 = sources[(u64)59u * rows + r_0];
    const unsigned v160 = sources[(u64)60u * rows + r_0];
    const unsigned v163 = sources[(u64)61u * rows + r_0];
    const unsigned v166 = sources[(u64)62u * rows + r_0];
    const unsigned v169 = sources[(u64)63u * rows + r_0];
    const unsigned v172 = sources[(u64)64u * rows + r_0];
    const unsigned v175 = sources[(u64)65u * rows + r_0];
    const unsigned v178 = sources[(u64)66u * rows + r_0];
    const unsigned v181 = sources[(u64)67u * rows + r_0];
    const unsigned v184 = sources[(u64)68u * rows + r_0];
    const unsigned v187 = sources[(u64)69u * rows + r_0];
    const unsigned v190 = sources[(u64)70u * rows + r_0];
    const unsigned v806 = 0u;
    const unsigned v810 = 2u;
    const unsigned v814 = 4u;
    const unsigned v818 = 8u;
    const unsigned v822 = 16u;
    const unsigned v826 = 32u;
    const unsigned v830 = 64u;
    const unsigned v834 = 128u;
    const unsigned v838 = 256u;
    const unsigned v842 = 512u;
    const unsigned v846 = 1024u;
    const unsigned v850 = 2048u;
    const unsigned v854 = 4096u;
    const unsigned v858 = 8192u;
    const unsigned v862 = 16384u;
    const unsigned v866 = 32768u;
    const unsigned v985 = starked_mul(v1, v0);
    const unsigned v986 = starked_add(v806, v985);
    const unsigned v987 = starked_mul(v810, v4);
    const unsigned v988 = starked_add(v986, v987);
    const unsigned v989 = starked_mul(v814, v7);
    const unsigned v990 = starked_add(v988, v989);
    const unsigned v991 = starked_mul(v818, v10);
    const unsigned v992 = starked_add(v990, v991);
    const unsigned v993 = starked_mul(v822, v13);
    const unsigned v994 = starked_add(v992, v993);
    const unsigned v995 = starked_mul(v826, v16);
    const unsigned v996 = starked_add(v994, v995);
    const unsigned v997 = starked_mul(v830, v19);
    const unsigned v998 = starked_add(v996, v997);
    const unsigned v999 = starked_mul(v834, v22);
    const unsigned v1000 = starked_add(v998, v999);
    const unsigned v1001 = starked_mul(v838, v25);
    const unsigned v1002 = starked_add(v1000, v1001);
    const unsigned v1003 = starked_mul(v842, v28);
    const unsigned v1004 = starked_add(v1002, v1003);
    const unsigned v1005 = starked_mul(v846, v31);
    const unsigned v1006 = starked_add(v1004, v1005);
    const unsigned v1007 = starked_mul(v850, v34);
    const unsigned v1008 = starked_add(v1006, v1007);
    const unsigned v1009 = starked_mul(v854, v37);
    const unsigned v1010 = starked_add(v1008, v1009);
    const unsigned v1011 = starked_mul(v858, v40);
    const unsigned v1012 = starked_add(v1010, v1011);
    const unsigned v1013 = starked_mul(v862, v43);
    const unsigned v1014 = starked_add(v1012, v1013);
    const unsigned v1015 = starked_mul(v866, v46);
    const unsigned v1016 = starked_add(v1014, v1015);
    const unsigned v1174 = starked_mul(v1, v49);
    const unsigned v1175 = starked_add(v806, v1174);
    const unsigned v1176 = starked_mul(v810, v52);
    const unsigned v1177 = starked_add(v1175, v1176);
    const unsigned v1178 = starked_mul(v814, v55);
    const unsigned v1179 = starked_add(v1177, v1178);
    const unsigned v1180 = starked_mul(v818, v58);
    const unsigned v1181 = starked_add(v1179, v1180);
    const unsigned v1182 = starked_mul(v822, v61);
    const unsigned v1183 = starked_add(v1181, v1182);
    const unsigned v1184 = starked_mul(v826, v64);
    const unsigned v1185 = starked_add(v1183, v1184);
    const unsigned v1186 = starked_mul(v830, v67);
    const unsigned v1187 = starked_add(v1185, v1186);
    const unsigned v1188 = starked_mul(v834, v70);
    const unsigned v1189 = starked_add(v1187, v1188);
    const unsigned v1190 = starked_mul(v838, v73);
    const unsigned v1191 = starked_add(v1189, v1190);
    const unsigned v1192 = starked_mul(v842, v76);
    const unsigned v1193 = starked_add(v1191, v1192);
    const unsigned v1194 = starked_mul(v846, v79);
    const unsigned v1195 = starked_add(v1193, v1194);
    const unsigned v1196 = starked_mul(v850, v82);
    const unsigned v1197 = starked_add(v1195, v1196);
    const unsigned v1198 = starked_mul(v854, v85);
    const unsigned v1199 = starked_add(v1197, v1198);
    const unsigned v1200 = starked_mul(v858, v88);
    const unsigned v1201 = starked_add(v1199, v1200);
    const unsigned v1202 = starked_mul(v862, v91);
    const unsigned v1203 = starked_add(v1201, v1202);
    const unsigned v1204 = starked_mul(v866, v94);
    const unsigned v1205 = starked_add(v1203, v1204);
    const unsigned v1263 = starked_mul(v1, v97);
    const unsigned v1264 = starked_add(v806, v1263);
    const unsigned v1265 = starked_mul(v810, v100);
    const unsigned v1266 = starked_add(v1264, v1265);
    const unsigned v1267 = starked_mul(v814, v103);
    const unsigned v1268 = starked_add(v1266, v1267);
    const unsigned v1269 = starked_mul(v818, v106);
    const unsigned v1270 = starked_add(v1268, v1269);
    const unsigned v1271 = starked_mul(v822, v109);
    const unsigned v1272 = starked_add(v1270, v1271);
    const unsigned v1273 = starked_mul(v826, v112);
    const unsigned v1274 = starked_add(v1272, v1273);
    const unsigned v1275 = starked_mul(v830, v115);
    const unsigned v1276 = starked_add(v1274, v1275);
    const unsigned v1277 = starked_mul(v834, v118);
    const unsigned v1278 = starked_add(v1276, v1277);
    const unsigned v1279 = starked_mul(v838, v121);
    const unsigned v1280 = starked_add(v1278, v1279);
    const unsigned v1281 = starked_mul(v842, v124);
    const unsigned v1282 = starked_add(v1280, v1281);
    const unsigned v1283 = starked_mul(v846, v127);
    const unsigned v1284 = starked_add(v1282, v1283);
    const unsigned v1285 = starked_mul(v850, v130);
    const unsigned v1286 = starked_add(v1284, v1285);
    const unsigned v1287 = starked_mul(v854, v133);
    const unsigned v1288 = starked_add(v1286, v1287);
    const unsigned v1289 = starked_mul(v858, v136);
    const unsigned v1290 = starked_add(v1288, v1289);
    const unsigned v1291 = starked_mul(v862, v139);
    const unsigned v1292 = starked_add(v1290, v1291);
    const unsigned v1293 = starked_mul(v866, v142);
    const unsigned v1294 = starked_add(v1292, v1293);
    const unsigned v1381 = starked_mul(v1, v145);
    const unsigned v1382 = starked_add(v806, v1381);
    const unsigned v1383 = starked_mul(v810, v148);
    const unsigned v1384 = starked_add(v1382, v1383);
    const unsigned v1385 = starked_mul(v814, v151);
    const unsigned v1386 = starked_add(v1384, v1385);
    const unsigned v1387 = starked_mul(v818, v154);
    const unsigned v1388 = starked_add(v1386, v1387);
    const unsigned v1389 = starked_mul(v822, v157);
    const unsigned v1390 = starked_add(v1388, v1389);
    const unsigned v1391 = starked_mul(v826, v160);
    const unsigned v1392 = starked_add(v1390, v1391);
    const unsigned v1393 = starked_mul(v830, v163);
    const unsigned v1394 = starked_add(v1392, v1393);
    const unsigned v1395 = starked_mul(v834, v166);
    const unsigned v1396 = starked_add(v1394, v1395);
    const unsigned v1397 = starked_mul(v838, v169);
    const unsigned v1398 = starked_add(v1396, v1397);
    const unsigned v1399 = starked_mul(v842, v172);
    const unsigned v1400 = starked_add(v1398, v1399);
    const unsigned v1401 = starked_mul(v846, v175);
    const unsigned v1402 = starked_add(v1400, v1401);
    const unsigned v1403 = starked_mul(v850, v178);
    const unsigned v1404 = starked_add(v1402, v1403);
    const unsigned v1405 = starked_mul(v854, v181);
    const unsigned v1406 = starked_add(v1404, v1405);
    const unsigned v1407 = starked_mul(v858, v184);
    const unsigned v1408 = starked_add(v1406, v1407);
    const unsigned v1409 = starked_mul(v862, v187);
    const unsigned v1410 = starked_add(v1408, v1409);
    const unsigned v1411 = starked_mul(v866, v190);
    const unsigned v1412 = starked_add(v1410, v1411);
    const unsigned v5110 = sources[(u64)0u * rows + r_0];
    const unsigned v6007 = sources[(u64)1u * rows + r_0];
    const unsigned v6136 = sources[(u64)2u * rows + r_0];
    const unsigned v6617 = sources[(u64)3u * rows + r_0];
    const unsigned v6855 = sources[(u64)72u * rows + r_0];
    const unsigned v6858 = sources[(u64)76u * rows + r_0];
    const unsigned v6861 = sources[(u64)77u * rows + r_0];
    const unsigned v6864 = sources[(u64)78u * rows + r_0];
    const unsigned v6890 = sources[(u64)75u * rows + r_0];
    const unsigned v6891 = sources[(u64)71u * rows + r_0];
    const unsigned v6905 = sources[(u64)79u * rows + r_0];
    const unsigned v6906 = sources[(u64)80u * rows + r_0];
    const unsigned v6909 = sources[(u64)81u * rows + r_0];
    const unsigned v6925 = sources[(u64)82u * rows + r_0];
    const unsigned v6926 = sources[(u64)83u * rows + r_0];
    const unsigned v6929 = sources[(u64)84u * rows + r_0];
    const unsigned v6941 = sources[(u64)85u * rows + r_0];
    const unsigned v6942 = sources[(u64)86u * rows + r_0];
    const unsigned v6945 = sources[(u64)87u * rows + r_0];
    const unsigned v6950 = sources[(u64)6u * rows + r_0];
    const unsigned v6952 = sources[(u64)88u * rows + r_0];
    const unsigned v6953 = sources[(u64)89u * rows + r_0];
    const unsigned v6956 = sources[(u64)90u * rows + r_0];
    const unsigned v6961 = sources[(u64)91u * rows + r_0];
    const unsigned v6962 = sources[(u64)92u * rows + r_0];
    const unsigned v6965 = sources[(u64)93u * rows + r_0];
    const unsigned v6970 = sources[(u64)73u * rows + r_0];
    const unsigned v6973 = sources[(u64)74u * rows + r_0];
    const unsigned v6976 = sources[(u64)4u * rows + r_0];
    const unsigned v7715 = starked_neg(v6861);
    const unsigned v7716 = sources[(u64)5u * rows + r_0];
    const unsigned v7717 = starked_neg(v6864);
    const unsigned v7718 = starked_mul(v6855, v5110);
    const unsigned v7719 = 5u;
    const unsigned v7720 = starked_mul(v6855, v6007);
    const unsigned v7721 = 6u;
    const unsigned v7722 = starked_mul(v6855, v6136);
    const unsigned v7723 = 7u;
    const unsigned v7724 = starked_mul(v6855, v6617);
    const unsigned v7725 = 3u;
    const unsigned v7726 = starked_neg(v6950);
    const unsigned v7727 = pubs[550];
    const unsigned v7728 = pubs[551];
    const unsigned v7729 = pubs[552];
    const unsigned v7730 = pubs[553];
    const unsigned v7731 = pubs[554];
    const unsigned v7732 = pubs[555];
    const unsigned v7733 = pubs[556];
    const unsigned v7734 = pubs[557];
    const unsigned v7735 = pubs[558];
    const unsigned v7736 = pubs[559];
    const unsigned v7737 = pubs[560];
    const unsigned v7738 = pubs[561];
    const unsigned v7739 = pubs[562];
    const unsigned v7740 = pubs[563];
    const unsigned v7741 = pubs[564];
    const unsigned v7742 = pubs[565];
    const unsigned v7743 = starked_mul(v6855, v6976);
    const unsigned v7744 = starked_neg(v7743);
    const unsigned v7745 = starked_mul(v6858, v6976);
    const unsigned v7746 = starked_neg(v7745);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 40u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v6890));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v7716));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha3, v6970));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha4, v6973));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 39u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v6890));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v7716));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha3, v6970));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha4, v6973));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 40u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v6891));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v806));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha3, v1016));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha4, v1205));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 40u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v6891));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v7719));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha3, v1294));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v1412));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 40u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v6891));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v1));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha3, v1016));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha4, v1205));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 40u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v6891));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v7721));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha3, v1294));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha4, v1412));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 40u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v6891));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v810));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha3, v1016));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha4, v1205));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 40u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v6891));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v7723));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha3, v1294));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha4, v1412));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 40u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v6891));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v7725));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha3, v1016));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha4, v1205));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 40u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v6891));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v814));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha3, v1294));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha4, v1412));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 40u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v1));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v806));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha3, v7727));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha4, v7728));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 40u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v1));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v1));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha3, v7729));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha4, v7730));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 40u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v1));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v810));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha3, v7731));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha4, v7732));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 40u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v1));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v7725));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha3, v7733));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha4, v7734));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 40u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v1));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v814));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha3, v7735));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha4, v7736));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 40u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v1));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v7719));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha3, v7737));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha4, v7738));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 40u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v1));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v7721));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha3, v7739));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha4, v7740));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 40u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v1));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v7723));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha3, v7741));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha4, v7742));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 9u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v6905));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 9u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v6906));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 9u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v6909));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 9u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v6925));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 9u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v6926));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 9u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v6929));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 9u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v6941));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 9u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v6942));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 9u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v6945));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 9u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v6952));
    StarkedQm31 d28 = minus_z;
    d28.a = starked_add(d28.a, 9u);
    d28 = starked_q_add(d28, starked_q_mul_base(alpha1, v6953));
    StarkedQm31 d29 = minus_z;
    d29.a = starked_add(d29.a, 9u);
    d29 = starked_q_add(d29, starked_q_mul_base(alpha1, v6956));
    StarkedQm31 d30 = minus_z;
    d30.a = starked_add(d30.a, 9u);
    d30 = starked_q_add(d30, starked_q_mul_base(alpha1, v6961));
    StarkedQm31 d31 = minus_z;
    d31.a = starked_add(d31.a, 9u);
    d31 = starked_q_add(d31, starked_q_mul_base(alpha1, v6962));
    StarkedQm31 d32 = minus_z;
    d32.a = starked_add(d32.a, 9u);
    d32 = starked_q_add(d32, starked_q_mul_base(alpha1, v6965));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v7715), starked_q_mul_base(d0, v7717));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v7718), starked_q_mul_base(d2, v7718));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v7720), starked_q_mul_base(d4, v7720));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v7722), starked_q_mul_base(d6, v7722));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v7724), starked_q_mul_base(d8, v7724));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v7726), starked_q_mul_base(d10, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v7726), starked_q_mul_base(d12, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v7726), starked_q_mul_base(d14, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v7726), starked_q_mul_base(d16, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v7744), starked_q_mul_base(d18, v7744));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v7744), starked_q_mul_base(d20, v7746));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v7746), starked_q_mul_base(d22, v7746));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v7746), starked_q_mul_base(d24, v7746));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v7746), starked_q_mul_base(d26, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d29, v7726), starked_q_mul_base(d28, v7726));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d31, v7726), starked_q_mul_base(d30, v7726));
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
        const StarkedQm31 n = {v7726, 0u, 0u, 0u};
        const StarkedQm31 d = d32;
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[64][row] = n.a;
        outputs[65][row] = n.b;
        outputs[66][row] = n.c;
        outputs[67][row] = n.d;
        unsigned *slot = denominators + ((u64)16u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
