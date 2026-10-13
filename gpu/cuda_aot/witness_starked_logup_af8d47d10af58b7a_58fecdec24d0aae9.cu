// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_urec, digest 3f6634ab7c50ea594a1e6a65b4455709793f87d8b7eca138215614b12fdb417d.
// 20 lookups in 10 batches, 22 source columns, tuples up to 6 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_af8d47d10af58b7a(
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
    const unsigned v34 = starked_add(v20, v24);
    const unsigned v35 = sources[(u64)4u * rows + r_0];
    const unsigned v44 = sources[(u64)20u * rows + r_0];
    const unsigned v45 = 256u;
    const unsigned v46 = sources[(u64)21u * rows + r_0];
    const unsigned v51 = starked_neg(v4);
    const unsigned v52 = 0u;
    const unsigned v53 = starked_neg(v0);
    const unsigned v54 = starked_add(v20, v52);
    const unsigned v55 = sources[(u64)5u * rows + r_0];
    const unsigned v56 = starked_add(v20, v1);
    const unsigned v57 = sources[(u64)6u * rows + r_0];
    const unsigned v58 = 2u;
    const unsigned v59 = starked_add(v20, v58);
    const unsigned v60 = sources[(u64)7u * rows + r_0];
    const unsigned v61 = 3u;
    const unsigned v62 = starked_add(v20, v61);
    const unsigned v63 = sources[(u64)8u * rows + r_0];
    const unsigned v64 = sources[(u64)9u * rows + r_0];
    const unsigned v65 = 10u;
    const unsigned v66 = starked_add(v20, v65);
    const unsigned v67 = sources[(u64)10u * rows + r_0];
    const unsigned v68 = 11u;
    const unsigned v69 = starked_add(v20, v68);
    const unsigned v70 = sources[(u64)11u * rows + r_0];
    const unsigned v71 = 12u;
    const unsigned v72 = starked_add(v20, v71);
    const unsigned v73 = sources[(u64)12u * rows + r_0];
    const unsigned v74 = 13u;
    const unsigned v75 = starked_add(v20, v74);
    const unsigned v76 = sources[(u64)13u * rows + r_0];
    const unsigned v77 = 14u;
    const unsigned v78 = starked_add(v20, v77);
    const unsigned v79 = sources[(u64)14u * rows + r_0];
    const unsigned v80 = 15u;
    const unsigned v81 = starked_add(v20, v80);
    const unsigned v82 = sources[(u64)15u * rows + r_0];
    const unsigned v83 = 16u;
    const unsigned v84 = starked_add(v20, v83);
    const unsigned v85 = sources[(u64)16u * rows + r_0];
    const unsigned v86 = 4u;
    const unsigned v87 = starked_add(v20, v86);
    const unsigned v88 = sources[(u64)17u * rows + r_0];
    const unsigned v89 = 5u;
    const unsigned v90 = starked_add(v20, v89);
    const unsigned v91 = sources[(u64)18u * rows + r_0];
    const unsigned v92 = 6u;
    const unsigned v93 = starked_add(v20, v92);
    const unsigned v94 = sources[(u64)19u * rows + r_0];
    const unsigned v95 = 7u;
    const unsigned v96 = starked_add(v20, v95);
    const unsigned v97 = 8u;
    const unsigned v98 = starked_add(v20, v97);
    const unsigned v99 = starked_mul(v45, v57);
    const unsigned v100 = starked_add(v55, v99);
    const unsigned v101 = starked_mul(v45, v63);
    const unsigned v102 = starked_add(v60, v101);
    const unsigned v103 = starked_mul(v45, v67);
    const unsigned v104 = starked_add(v64, v103);
    const unsigned v105 = 65536u;
    const unsigned v106 = starked_mul(v105, v70);
    const unsigned v107 = starked_add(v104, v106);
    const unsigned v108 = starked_mul(v45, v76);
    const unsigned v109 = starked_add(v73, v108);
    const unsigned v110 = starked_mul(v105, v79);
    const unsigned v111 = starked_add(v109, v110);
    const unsigned v112 = 16777216u;
    const unsigned v113 = starked_mul(v112, v82);
    const unsigned v114 = starked_add(v111, v113);
    const unsigned v115 = starked_mul(v45, v91);
    const unsigned v116 = starked_add(v88, v115);
    const unsigned v117 = starked_mul(v105, v94);
    const unsigned v118 = starked_add(v116, v117);
    const StarkedQm31 minus_z = {starked_neg(z[0]), starked_neg(z[1]), starked_neg(z[2]), starked_neg(z[3])};
    const StarkedQm31 alpha1 = starked_q_load(powers + 4);
    const StarkedQm31 alpha2 = starked_q_load(powers + 8);
    const StarkedQm31 alpha3 = starked_q_load(powers + 12);
    const StarkedQm31 alpha4 = starked_q_load(powers + 16);
    const StarkedQm31 alpha5 = starked_q_load(powers + 20);
    const StarkedQm31 alpha6 = starked_q_load(powers + 24);
    StarkedQm31 d0 = minus_z;
    d0.a = starked_add(d0.a, 17u);
    d0 = starked_q_add(d0, starked_q_mul_base(alpha1, v52));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha2, v1));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 17u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v54));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v55));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 17u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v56));
    d2 = starked_q_add(d2, starked_q_mul_base(alpha2, v57));
    StarkedQm31 d3 = minus_z;
    d3.a = starked_add(d3.a, 17u);
    d3 = starked_q_add(d3, starked_q_mul_base(alpha1, v59));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha2, v60));
    StarkedQm31 d4 = minus_z;
    d4.a = starked_add(d4.a, 17u);
    d4 = starked_q_add(d4, starked_q_mul_base(alpha1, v62));
    d4 = starked_q_add(d4, starked_q_mul_base(alpha2, v63));
    StarkedQm31 d5 = minus_z;
    d5.a = starked_add(d5.a, 17u);
    d5 = starked_q_add(d5, starked_q_mul_base(alpha1, v34));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha2, v64));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 17u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v66));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v67));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 17u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v69));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v70));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 17u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v72));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v73));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 17u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v75));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v76));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 17u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v78));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v79));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 17u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v81));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v82));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 17u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v84));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v85));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 17u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v87));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v88));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 17u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v90));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v91));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 17u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v93));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v94));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 17u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v96));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v44));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 17u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v98));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v46));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 21u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v1));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha2, v13));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha3, v34));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha4, v35));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 23u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v13));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha2, v100));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha3, v102));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha4, v107));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha5, v114));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha6, v118));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v51), starked_q_mul_base(d0, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v53), starked_q_mul_base(d2, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v53), starked_q_mul_base(d4, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v53), starked_q_mul_base(d6, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v53), starked_q_mul_base(d8, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v53), starked_q_mul_base(d10, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v53), starked_q_mul_base(d12, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v53), starked_q_mul_base(d14, v53));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v53), starked_q_mul_base(d16, v53));
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
}
