// starked-bitcoin LogUp fraction kernel v1 (src/gpu/cuda/logup.zig): AIR block_coin, digest 469ded29ae2fd7bc3c3f14c584f2ea844ba4d3c8579383cfab5c528239d5087c.
// 108 lookups in 54 batches, 149 source columns, tuples up to 17 values.
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
extern "C" __global__ void __launch_bounds__(256) starked_logup_v1_4525161bef8c67ef(
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
    const unsigned v745 = 4u;
    const unsigned v1393 = sources[(u64)116u * rows + r_0];
    const unsigned v1396 = sources[(u64)117u * rows + r_0];
    const unsigned v1399 = sources[(u64)118u * rows + r_0];
    const unsigned v1415 = sources[(u64)94u * rows + r_0];
    const unsigned v1422 = sources[(u64)95u * rows + r_0];
    const unsigned v1427 = sources[(u64)103u * rows + r_0];
    const unsigned v1428 = sources[(u64)104u * rows + r_0];
    const unsigned v1431 = sources[(u64)105u * rows + r_0];
    const unsigned v1436 = sources[(u64)96u * rows + r_0];
    const unsigned v1437 = sources[(u64)97u * rows + r_0];
    const unsigned v1440 = sources[(u64)98u * rows + r_0];
    const unsigned v1449 = sources[(u64)99u * rows + r_0];
    const unsigned v1450 = sources[(u64)100u * rows + r_0];
    const unsigned v1453 = sources[(u64)101u * rows + r_0];
    const unsigned v1456 = sources[(u64)102u * rows + r_0];
    const unsigned v1510 = sources[(u64)106u * rows + r_0];
    const unsigned v1511 = sources[(u64)107u * rows + r_0];
    const unsigned v1514 = sources[(u64)108u * rows + r_0];
    const unsigned v1531 = sources[(u64)109u * rows + r_0];
    const unsigned v1532 = sources[(u64)110u * rows + r_0];
    const unsigned v1535 = sources[(u64)111u * rows + r_0];
    const unsigned v1546 = sources[(u64)112u * rows + r_0];
    const unsigned v1547 = sources[(u64)113u * rows + r_0];
    const unsigned v1550 = sources[(u64)114u * rows + r_0];
    const unsigned v1553 = sources[(u64)115u * rows + r_0];
    const unsigned v1563 = sources[(u64)119u * rows + r_0];
    const unsigned v1564 = 7u;
    const unsigned v1567 = sources[(u64)120u * rows + r_0];
    const unsigned v1573 = sources[(u64)121u * rows + r_0];
    const unsigned v1574 = sources[(u64)122u * rows + r_0];
    const unsigned v1577 = sources[(u64)123u * rows + r_0];
    const unsigned v1585 = sources[(u64)124u * rows + r_0];
    const unsigned v1586 = sources[(u64)125u * rows + r_0];
    const unsigned v1589 = sources[(u64)126u * rows + r_0];
    const unsigned v1592 = sources[(u64)127u * rows + r_0];
    const unsigned v1599 = sources[(u64)128u * rows + r_0];
    const unsigned v1602 = sources[(u64)130u * rows + r_0];
    const unsigned v1605 = sources[(u64)129u * rows + r_0];
    const unsigned v1607 = sources[(u64)132u * rows + r_0];
    const unsigned v1608 = sources[(u64)133u * rows + r_0];
    const unsigned v1611 = sources[(u64)134u * rows + r_0];
    const unsigned v1617 = sources[(u64)131u * rows + r_0];
    const unsigned v1629 = sources[(u64)148u * rows + r_0];
    const unsigned v1632 = sources[(u64)142u * rows + r_0];
    const unsigned v1634 = sources[(u64)143u * rows + r_0];
    const unsigned v1642 = sources[(u64)138u * rows + r_0];
    const unsigned v1643 = sources[(u64)139u * rows + r_0];
    const unsigned v1653 = sources[(u64)144u * rows + r_0];
    const unsigned v1654 = sources[(u64)145u * rows + r_0];
    const unsigned v1660 = sources[(u64)140u * rows + r_0];
    const unsigned v1661 = sources[(u64)141u * rows + r_0];
    const unsigned v1667 = sources[(u64)146u * rows + r_0];
    const unsigned v1668 = sources[(u64)147u * rows + r_0];
    const unsigned v1677 = sources[(u64)83u * rows + r_0];
    const unsigned v1680 = sources[(u64)84u * rows + r_0];
    const unsigned v1684 = sources[(u64)85u * rows + r_0];
    const unsigned v1687 = sources[(u64)86u * rows + r_0];
    const unsigned v1841 = starked_neg(v0);
    const unsigned v1842 = sources[(u64)7u * rows + r_0];
    const unsigned v1843 = starked_add(v4, v7);
    const unsigned v1844 = starked_neg(v1843);
    const unsigned v1845 = sources[(u64)135u * rows + r_0];
    const unsigned v1846 = sources[(u64)136u * rows + r_0];
    const unsigned v1847 = sources[(u64)137u * rows + r_0];
    const unsigned v1848 = starked_mul(v108, v59);
    const unsigned v1849 = starked_add(v1848, v1);
    const unsigned v1850 = starked_neg(v4);
    const unsigned v1851 = starked_neg(v25);
    const unsigned v1852 = starked_mul(v0, v189);
    const unsigned v1853 = starked_neg(v1852);
    const unsigned v1854 = starked_add(v42, v355);
    const unsigned v1855 = starked_add(v42, v1);
    const unsigned v1856 = starked_add(v42, v108);
    const unsigned v1857 = 3u;
    const unsigned v1858 = starked_add(v42, v1857);
    const unsigned v1859 = starked_add(v42, v745);
    const unsigned v1860 = 5u;
    const unsigned v1861 = starked_add(v42, v1860);
    const unsigned v1862 = 6u;
    const unsigned v1863 = starked_add(v42, v1862);
    const unsigned v1864 = starked_add(v42, v1564);
    const unsigned v1865 = 8u;
    const unsigned v1866 = starked_add(v42, v1865);
    const unsigned v1867 = 9u;
    const unsigned v1868 = starked_add(v42, v1867);
    const unsigned v1869 = 10u;
    const unsigned v1870 = starked_add(v42, v1869);
    const unsigned v1871 = 11u;
    const unsigned v1872 = starked_add(v42, v1871);
    const unsigned v1873 = 12u;
    const unsigned v1874 = starked_add(v42, v1873);
    const unsigned v1875 = 13u;
    const unsigned v1876 = starked_add(v42, v1875);
    const unsigned v1877 = 14u;
    const unsigned v1878 = starked_add(v42, v1877);
    const unsigned v1879 = 15u;
    const unsigned v1880 = starked_add(v42, v1879);
    const unsigned v1881 = 16u;
    const unsigned v1882 = starked_add(v42, v1881);
    const unsigned v1883 = 17u;
    const unsigned v1884 = starked_add(v42, v1883);
    const unsigned v1885 = 18u;
    const unsigned v1886 = starked_add(v42, v1885);
    const unsigned v1887 = 19u;
    const unsigned v1888 = starked_add(v42, v1887);
    const unsigned v1889 = 20u;
    const unsigned v1890 = starked_add(v42, v1889);
    const unsigned v1891 = 21u;
    const unsigned v1892 = starked_add(v42, v1891);
    const unsigned v1893 = 22u;
    const unsigned v1894 = starked_add(v42, v1893);
    const unsigned v1895 = 23u;
    const unsigned v1896 = starked_add(v42, v1895);
    const unsigned v1897 = 24u;
    const unsigned v1898 = starked_add(v42, v1897);
    const unsigned v1899 = 25u;
    const unsigned v1900 = starked_add(v42, v1899);
    const unsigned v1901 = 26u;
    const unsigned v1902 = starked_add(v42, v1901);
    const unsigned v1903 = 27u;
    const unsigned v1904 = starked_add(v42, v1903);
    const unsigned v1905 = 28u;
    const unsigned v1906 = starked_add(v42, v1905);
    const unsigned v1907 = 29u;
    const unsigned v1908 = starked_add(v42, v1907);
    const unsigned v1909 = 30u;
    const unsigned v1910 = starked_add(v42, v1909);
    const unsigned v1911 = 31u;
    const unsigned v1912 = starked_add(v42, v1911);
    const unsigned v1913 = 32u;
    const unsigned v1914 = starked_add(v42, v1913);
    const unsigned v1915 = 33u;
    const unsigned v1916 = starked_add(v42, v1915);
    const unsigned v1917 = 34u;
    const unsigned v1918 = starked_add(v42, v1917);
    const unsigned v1919 = 35u;
    const unsigned v1920 = starked_add(v42, v1919);
    const unsigned v1921 = starked_mul(v30, v26);
    const unsigned v1922 = starked_neg(v1921);
    const unsigned v1923 = starked_mul(v4, v10);
    const unsigned v1924 = starked_neg(v1923);
    const unsigned v1925 = starked_neg(v1393);
    const unsigned v1926 = starked_neg(v1396);
    const unsigned v1927 = starked_neg(v26);
    const unsigned v1928 = starked_neg(v1399);
    const unsigned v1929 = starked_mul(v4, v1602);
    const unsigned v1930 = starked_neg(v1929);
    const unsigned v1931 = starked_neg(v1629);
    const unsigned v1932 = starked_mul(v108, v1632);
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
    d0 = starked_q_add(d0, starked_q_mul_base(alpha4, v1842));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha5, v174));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha6, v1415));
    d0 = starked_q_add(d0, starked_q_mul_base(alpha7, v1422));
    StarkedQm31 d1 = minus_z;
    d1.a = starked_add(d1.a, 25u);
    d1 = starked_q_add(d1, starked_q_mul_base(alpha1, v59));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha2, v42));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha3, v1605));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha4, v1602));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha5, v1617));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha6, v1845));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha7, v1846));
    d1 = starked_q_add(d1, starked_q_mul_base(alpha8, v1847));
    StarkedQm31 d2 = minus_z;
    d2.a = starked_add(d2.a, 7u);
    d2 = starked_q_add(d2, starked_q_mul_base(alpha1, v1849));
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
    d3 = starked_q_add(d3, starked_q_mul_base(alpha4, v1415));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha5, v1422));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha6, v120));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha7, v1845));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha8, v1846));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha9, v1847));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha10, v1642));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha11, v1643));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha12, v1660));
    d3 = starked_q_add(d3, starked_q_mul_base(alpha13, v1661));
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
    d5 = starked_q_add(d5, starked_q_mul_base(alpha4, v1677));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha5, v1680));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha6, v1684));
    d5 = starked_q_add(d5, starked_q_mul_base(alpha7, v1687));
    StarkedQm31 d6 = minus_z;
    d6.a = starked_add(d6.a, 3u);
    d6 = starked_q_add(d6, starked_q_mul_base(alpha1, v1842));
    d6 = starked_q_add(d6, starked_q_mul_base(alpha2, v181));
    StarkedQm31 d7 = minus_z;
    d7.a = starked_add(d7.a, 3u);
    d7 = starked_q_add(d7, starked_q_mul_base(alpha1, v1854));
    d7 = starked_q_add(d7, starked_q_mul_base(alpha2, v251));
    StarkedQm31 d8 = minus_z;
    d8.a = starked_add(d8.a, 3u);
    d8 = starked_q_add(d8, starked_q_mul_base(alpha1, v1855));
    d8 = starked_q_add(d8, starked_q_mul_base(alpha2, v250));
    StarkedQm31 d9 = minus_z;
    d9.a = starked_add(d9.a, 3u);
    d9 = starked_q_add(d9, starked_q_mul_base(alpha1, v1856));
    d9 = starked_q_add(d9, starked_q_mul_base(alpha2, v244));
    StarkedQm31 d10 = minus_z;
    d10.a = starked_add(d10.a, 3u);
    d10 = starked_q_add(d10, starked_q_mul_base(alpha1, v1858));
    d10 = starked_q_add(d10, starked_q_mul_base(alpha2, v243));
    StarkedQm31 d11 = minus_z;
    d11.a = starked_add(d11.a, 3u);
    d11 = starked_q_add(d11, starked_q_mul_base(alpha1, v1859));
    d11 = starked_q_add(d11, starked_q_mul_base(alpha2, v265));
    StarkedQm31 d12 = minus_z;
    d12.a = starked_add(d12.a, 3u);
    d12 = starked_q_add(d12, starked_q_mul_base(alpha1, v1861));
    d12 = starked_q_add(d12, starked_q_mul_base(alpha2, v264));
    StarkedQm31 d13 = minus_z;
    d13.a = starked_add(d13.a, 3u);
    d13 = starked_q_add(d13, starked_q_mul_base(alpha1, v1863));
    d13 = starked_q_add(d13, starked_q_mul_base(alpha2, v258));
    StarkedQm31 d14 = minus_z;
    d14.a = starked_add(d14.a, 3u);
    d14 = starked_q_add(d14, starked_q_mul_base(alpha1, v1864));
    d14 = starked_q_add(d14, starked_q_mul_base(alpha2, v257));
    StarkedQm31 d15 = minus_z;
    d15.a = starked_add(d15.a, 3u);
    d15 = starked_q_add(d15, starked_q_mul_base(alpha1, v1866));
    d15 = starked_q_add(d15, starked_q_mul_base(alpha2, v279));
    StarkedQm31 d16 = minus_z;
    d16.a = starked_add(d16.a, 3u);
    d16 = starked_q_add(d16, starked_q_mul_base(alpha1, v1868));
    d16 = starked_q_add(d16, starked_q_mul_base(alpha2, v278));
    StarkedQm31 d17 = minus_z;
    d17.a = starked_add(d17.a, 3u);
    d17 = starked_q_add(d17, starked_q_mul_base(alpha1, v1870));
    d17 = starked_q_add(d17, starked_q_mul_base(alpha2, v272));
    StarkedQm31 d18 = minus_z;
    d18.a = starked_add(d18.a, 3u);
    d18 = starked_q_add(d18, starked_q_mul_base(alpha1, v1872));
    d18 = starked_q_add(d18, starked_q_mul_base(alpha2, v271));
    StarkedQm31 d19 = minus_z;
    d19.a = starked_add(d19.a, 3u);
    d19 = starked_q_add(d19, starked_q_mul_base(alpha1, v1874));
    d19 = starked_q_add(d19, starked_q_mul_base(alpha2, v293));
    StarkedQm31 d20 = minus_z;
    d20.a = starked_add(d20.a, 3u);
    d20 = starked_q_add(d20, starked_q_mul_base(alpha1, v1876));
    d20 = starked_q_add(d20, starked_q_mul_base(alpha2, v292));
    StarkedQm31 d21 = minus_z;
    d21.a = starked_add(d21.a, 3u);
    d21 = starked_q_add(d21, starked_q_mul_base(alpha1, v1878));
    d21 = starked_q_add(d21, starked_q_mul_base(alpha2, v286));
    StarkedQm31 d22 = minus_z;
    d22.a = starked_add(d22.a, 3u);
    d22 = starked_q_add(d22, starked_q_mul_base(alpha1, v1880));
    d22 = starked_q_add(d22, starked_q_mul_base(alpha2, v285));
    StarkedQm31 d23 = minus_z;
    d23.a = starked_add(d23.a, 3u);
    d23 = starked_q_add(d23, starked_q_mul_base(alpha1, v1882));
    d23 = starked_q_add(d23, starked_q_mul_base(alpha2, v307));
    StarkedQm31 d24 = minus_z;
    d24.a = starked_add(d24.a, 3u);
    d24 = starked_q_add(d24, starked_q_mul_base(alpha1, v1884));
    d24 = starked_q_add(d24, starked_q_mul_base(alpha2, v306));
    StarkedQm31 d25 = minus_z;
    d25.a = starked_add(d25.a, 3u);
    d25 = starked_q_add(d25, starked_q_mul_base(alpha1, v1886));
    d25 = starked_q_add(d25, starked_q_mul_base(alpha2, v300));
    StarkedQm31 d26 = minus_z;
    d26.a = starked_add(d26.a, 3u);
    d26 = starked_q_add(d26, starked_q_mul_base(alpha1, v1888));
    d26 = starked_q_add(d26, starked_q_mul_base(alpha2, v299));
    StarkedQm31 d27 = minus_z;
    d27.a = starked_add(d27.a, 3u);
    d27 = starked_q_add(d27, starked_q_mul_base(alpha1, v1890));
    d27 = starked_q_add(d27, starked_q_mul_base(alpha2, v321));
    StarkedQm31 d28 = minus_z;
    d28.a = starked_add(d28.a, 3u);
    d28 = starked_q_add(d28, starked_q_mul_base(alpha1, v1892));
    d28 = starked_q_add(d28, starked_q_mul_base(alpha2, v320));
    StarkedQm31 d29 = minus_z;
    d29.a = starked_add(d29.a, 3u);
    d29 = starked_q_add(d29, starked_q_mul_base(alpha1, v1894));
    d29 = starked_q_add(d29, starked_q_mul_base(alpha2, v314));
    StarkedQm31 d30 = minus_z;
    d30.a = starked_add(d30.a, 3u);
    d30 = starked_q_add(d30, starked_q_mul_base(alpha1, v1896));
    d30 = starked_q_add(d30, starked_q_mul_base(alpha2, v313));
    StarkedQm31 d31 = minus_z;
    d31.a = starked_add(d31.a, 3u);
    d31 = starked_q_add(d31, starked_q_mul_base(alpha1, v1898));
    d31 = starked_q_add(d31, starked_q_mul_base(alpha2, v335));
    StarkedQm31 d32 = minus_z;
    d32.a = starked_add(d32.a, 3u);
    d32 = starked_q_add(d32, starked_q_mul_base(alpha1, v1900));
    d32 = starked_q_add(d32, starked_q_mul_base(alpha2, v334));
    StarkedQm31 d33 = minus_z;
    d33.a = starked_add(d33.a, 3u);
    d33 = starked_q_add(d33, starked_q_mul_base(alpha1, v1902));
    d33 = starked_q_add(d33, starked_q_mul_base(alpha2, v328));
    StarkedQm31 d34 = minus_z;
    d34.a = starked_add(d34.a, 3u);
    d34 = starked_q_add(d34, starked_q_mul_base(alpha1, v1904));
    d34 = starked_q_add(d34, starked_q_mul_base(alpha2, v327));
    StarkedQm31 d35 = minus_z;
    d35.a = starked_add(d35.a, 3u);
    d35 = starked_q_add(d35, starked_q_mul_base(alpha1, v1906));
    d35 = starked_q_add(d35, starked_q_mul_base(alpha2, v349));
    StarkedQm31 d36 = minus_z;
    d36.a = starked_add(d36.a, 3u);
    d36 = starked_q_add(d36, starked_q_mul_base(alpha1, v1908));
    d36 = starked_q_add(d36, starked_q_mul_base(alpha2, v348));
    StarkedQm31 d37 = minus_z;
    d37.a = starked_add(d37.a, 3u);
    d37 = starked_q_add(d37, starked_q_mul_base(alpha1, v1910));
    d37 = starked_q_add(d37, starked_q_mul_base(alpha2, v342));
    StarkedQm31 d38 = minus_z;
    d38.a = starked_add(d38.a, 3u);
    d38 = starked_q_add(d38, starked_q_mul_base(alpha1, v1912));
    d38 = starked_q_add(d38, starked_q_mul_base(alpha2, v341));
    StarkedQm31 d39 = minus_z;
    d39.a = starked_add(d39.a, 3u);
    d39 = starked_q_add(d39, starked_q_mul_base(alpha1, v1914));
    d39 = starked_q_add(d39, starked_q_mul_base(alpha2, v92));
    StarkedQm31 d40 = minus_z;
    d40.a = starked_add(d40.a, 3u);
    d40 = starked_q_add(d40, starked_q_mul_base(alpha1, v1916));
    d40 = starked_q_add(d40, starked_q_mul_base(alpha2, v93));
    StarkedQm31 d41 = minus_z;
    d41.a = starked_add(d41.a, 3u);
    d41 = starked_q_add(d41, starked_q_mul_base(alpha1, v1918));
    d41 = starked_q_add(d41, starked_q_mul_base(alpha2, v98));
    StarkedQm31 d42 = minus_z;
    d42.a = starked_add(d42.a, 3u);
    d42 = starked_q_add(d42, starked_q_mul_base(alpha1, v1920));
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
    d64 = starked_q_add(d64, starked_q_mul_base(alpha1, v1427));
    StarkedQm31 d65 = minus_z;
    d65.a = starked_add(d65.a, 9u);
    d65 = starked_q_add(d65, starked_q_mul_base(alpha1, v1428));
    StarkedQm31 d66 = minus_z;
    d66.a = starked_add(d66.a, 9u);
    d66 = starked_q_add(d66, starked_q_mul_base(alpha1, v1431));
    StarkedQm31 d67 = minus_z;
    d67.a = starked_add(d67.a, 9u);
    d67 = starked_q_add(d67, starked_q_mul_base(alpha1, v1436));
    StarkedQm31 d68 = minus_z;
    d68.a = starked_add(d68.a, 9u);
    d68 = starked_q_add(d68, starked_q_mul_base(alpha1, v1437));
    StarkedQm31 d69 = minus_z;
    d69.a = starked_add(d69.a, 9u);
    d69 = starked_q_add(d69, starked_q_mul_base(alpha1, v1440));
    StarkedQm31 d70 = minus_z;
    d70.a = starked_add(d70.a, 9u);
    d70 = starked_q_add(d70, starked_q_mul_base(alpha1, v1449));
    StarkedQm31 d71 = minus_z;
    d71.a = starked_add(d71.a, 9u);
    d71 = starked_q_add(d71, starked_q_mul_base(alpha1, v1450));
    StarkedQm31 d72 = minus_z;
    d72.a = starked_add(d72.a, 9u);
    d72 = starked_q_add(d72, starked_q_mul_base(alpha1, v1453));
    StarkedQm31 d73 = minus_z;
    d73.a = starked_add(d73.a, 9u);
    d73 = starked_q_add(d73, starked_q_mul_base(alpha1, v1456));
    StarkedQm31 d74 = minus_z;
    d74.a = starked_add(d74.a, 9u);
    d74 = starked_q_add(d74, starked_q_mul_base(alpha1, v1510));
    StarkedQm31 d75 = minus_z;
    d75.a = starked_add(d75.a, 9u);
    d75 = starked_q_add(d75, starked_q_mul_base(alpha1, v1511));
    StarkedQm31 d76 = minus_z;
    d76.a = starked_add(d76.a, 9u);
    d76 = starked_q_add(d76, starked_q_mul_base(alpha1, v1514));
    StarkedQm31 d77 = minus_z;
    d77.a = starked_add(d77.a, 9u);
    d77 = starked_q_add(d77, starked_q_mul_base(alpha1, v1531));
    StarkedQm31 d78 = minus_z;
    d78.a = starked_add(d78.a, 9u);
    d78 = starked_q_add(d78, starked_q_mul_base(alpha1, v1532));
    StarkedQm31 d79 = minus_z;
    d79.a = starked_add(d79.a, 9u);
    d79 = starked_q_add(d79, starked_q_mul_base(alpha1, v1535));
    StarkedQm31 d80 = minus_z;
    d80.a = starked_add(d80.a, 9u);
    d80 = starked_q_add(d80, starked_q_mul_base(alpha1, v1546));
    StarkedQm31 d81 = minus_z;
    d81.a = starked_add(d81.a, 9u);
    d81 = starked_q_add(d81, starked_q_mul_base(alpha1, v1547));
    StarkedQm31 d82 = minus_z;
    d82.a = starked_add(d82.a, 9u);
    d82 = starked_q_add(d82, starked_q_mul_base(alpha1, v1550));
    StarkedQm31 d83 = minus_z;
    d83.a = starked_add(d83.a, 9u);
    d83 = starked_q_add(d83, starked_q_mul_base(alpha1, v1553));
    StarkedQm31 d84 = minus_z;
    d84.a = starked_add(d84.a, 9u);
    d84 = starked_q_add(d84, starked_q_mul_base(alpha1, v1563));
    StarkedQm31 d85 = minus_z;
    d85.a = starked_add(d85.a, 9u);
    d85 = starked_q_add(d85, starked_q_mul_base(alpha1, v1567));
    StarkedQm31 d86 = minus_z;
    d86.a = starked_add(d86.a, 9u);
    d86 = starked_q_add(d86, starked_q_mul_base(alpha1, v1573));
    StarkedQm31 d87 = minus_z;
    d87.a = starked_add(d87.a, 9u);
    d87 = starked_q_add(d87, starked_q_mul_base(alpha1, v1574));
    StarkedQm31 d88 = minus_z;
    d88.a = starked_add(d88.a, 9u);
    d88 = starked_q_add(d88, starked_q_mul_base(alpha1, v1577));
    StarkedQm31 d89 = minus_z;
    d89.a = starked_add(d89.a, 9u);
    d89 = starked_q_add(d89, starked_q_mul_base(alpha1, v1585));
    StarkedQm31 d90 = minus_z;
    d90.a = starked_add(d90.a, 9u);
    d90 = starked_q_add(d90, starked_q_mul_base(alpha1, v1586));
    StarkedQm31 d91 = minus_z;
    d91.a = starked_add(d91.a, 9u);
    d91 = starked_q_add(d91, starked_q_mul_base(alpha1, v1589));
    StarkedQm31 d92 = minus_z;
    d92.a = starked_add(d92.a, 9u);
    d92 = starked_q_add(d92, starked_q_mul_base(alpha1, v1592));
    StarkedQm31 d93 = minus_z;
    d93.a = starked_add(d93.a, 9u);
    d93 = starked_q_add(d93, starked_q_mul_base(alpha1, v1599));
    StarkedQm31 d94 = minus_z;
    d94.a = starked_add(d94.a, 9u);
    d94 = starked_q_add(d94, starked_q_mul_base(alpha1, v1607));
    StarkedQm31 d95 = minus_z;
    d95.a = starked_add(d95.a, 9u);
    d95 = starked_q_add(d95, starked_q_mul_base(alpha1, v1608));
    StarkedQm31 d96 = minus_z;
    d96.a = starked_add(d96.a, 9u);
    d96 = starked_q_add(d96, starked_q_mul_base(alpha1, v1611));
    StarkedQm31 d97 = minus_z;
    d97.a = starked_add(d97.a, 9u);
    d97 = starked_q_add(d97, starked_q_mul_base(alpha1, v1653));
    StarkedQm31 d98 = minus_z;
    d98.a = starked_add(d98.a, 9u);
    d98 = starked_q_add(d98, starked_q_mul_base(alpha1, v1654));
    StarkedQm31 d99 = minus_z;
    d99.a = starked_add(d99.a, 9u);
    d99 = starked_q_add(d99, starked_q_mul_base(alpha1, v1667));
    StarkedQm31 d100 = minus_z;
    d100.a = starked_add(d100.a, 9u);
    d100 = starked_q_add(d100, starked_q_mul_base(alpha1, v1668));
    StarkedQm31 d101 = minus_z;
    d101.a = starked_add(d101.a, 9u);
    d101 = starked_q_add(d101, starked_q_mul_base(alpha1, v1632));
    StarkedQm31 d102 = minus_z;
    d102.a = starked_add(d102.a, 9u);
    d102 = starked_q_add(d102, starked_q_mul_base(alpha1, v1932));
    StarkedQm31 d103 = minus_z;
    d103.a = starked_add(d103.a, 9u);
    d103 = starked_q_add(d103, starked_q_mul_base(alpha1, v1634));
    StarkedQm31 d104 = minus_z;
    d104.a = starked_add(d104.a, 9u);
    d104 = starked_q_add(d104, starked_q_mul_base(alpha1, v1642));
    StarkedQm31 d105 = minus_z;
    d105.a = starked_add(d105.a, 9u);
    d105 = starked_q_add(d105, starked_q_mul_base(alpha1, v1643));
    StarkedQm31 d106 = minus_z;
    d106.a = starked_add(d106.a, 9u);
    d106 = starked_q_add(d106, starked_q_mul_base(alpha1, v1660));
    StarkedQm31 d107 = minus_z;
    d107.a = starked_add(d107.a, 9u);
    d107 = starked_q_add(d107, starked_q_mul_base(alpha1, v1661));
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d1, v1841), starked_q_mul_base(d0, v1844));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d3, v1841), starked_q_mul_base(d2, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d5, v0), starked_q_mul_base(d4, v1851));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d7, v1853), starked_q_mul_base(d6, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d9, v1850), starked_q_mul_base(d8, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d11, v1850), starked_q_mul_base(d10, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d13, v1850), starked_q_mul_base(d12, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d15, v1850), starked_q_mul_base(d14, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d17, v1850), starked_q_mul_base(d16, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d19, v1850), starked_q_mul_base(d18, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d21, v1850), starked_q_mul_base(d20, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d23, v1850), starked_q_mul_base(d22, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d25, v1850), starked_q_mul_base(d24, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d27, v1850), starked_q_mul_base(d26, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d29, v1850), starked_q_mul_base(d28, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d31, v1850), starked_q_mul_base(d30, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d33, v1850), starked_q_mul_base(d32, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d35, v1850), starked_q_mul_base(d34, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d37, v1850), starked_q_mul_base(d36, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d39, v1850), starked_q_mul_base(d38, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d41, v1850), starked_q_mul_base(d40, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d43, v1850), starked_q_mul_base(d42, v1922));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d45, v1922), starked_q_mul_base(d44, v1922));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d47, v1841), starked_q_mul_base(d46, v1841));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d49, v1841), starked_q_mul_base(d48, v1841));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d51, v1841), starked_q_mul_base(d50, v1841));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d53, v1850), starked_q_mul_base(d52, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d55, v1850), starked_q_mul_base(d54, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d57, v1850), starked_q_mul_base(d56, v1850));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d59, v1924), starked_q_mul_base(d58, v1924));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d61, v1924), starked_q_mul_base(d60, v1841));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d63, v1841), starked_q_mul_base(d62, v1841));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d65, v1925), starked_q_mul_base(d64, v1925));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d67, v1925), starked_q_mul_base(d66, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d69, v1926), starked_q_mul_base(d68, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d71, v1926), starked_q_mul_base(d70, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d73, v1926), starked_q_mul_base(d72, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d75, v1927), starked_q_mul_base(d74, v1927));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d77, v1927), starked_q_mul_base(d76, v1928));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d79, v1928), starked_q_mul_base(d78, v1928));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d81, v1928), starked_q_mul_base(d80, v1928));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d83, v1928), starked_q_mul_base(d82, v1928));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d85, v1926), starked_q_mul_base(d84, v1928));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d87, v1926), starked_q_mul_base(d86, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d89, v1926), starked_q_mul_base(d88, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d91, v1926), starked_q_mul_base(d90, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d93, v1926), starked_q_mul_base(d92, v1926));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d95, v1930), starked_q_mul_base(d94, v1930));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d97, v1930), starked_q_mul_base(d96, v1931));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d99, v1931), starked_q_mul_base(d98, v1931));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d101, v1931), starked_q_mul_base(d100, v1931));
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
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d103, v1931), starked_q_mul_base(d102, v1931));
        const StarkedQm31 d = starked_q_mul(d102, d103);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[204][row] = n.a;
        outputs[205][row] = n.b;
        outputs[206][row] = n.c;
        outputs[207][row] = n.d;
        unsigned *slot = denominators + ((u64)51u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d105, v1841), starked_q_mul_base(d104, v1841));
        const StarkedQm31 d = starked_q_mul(d104, d105);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[208][row] = n.a;
        outputs[209][row] = n.b;
        outputs[210][row] = n.c;
        outputs[211][row] = n.d;
        unsigned *slot = denominators + ((u64)52u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
    {
        const StarkedQm31 n = starked_q_add(starked_q_mul_base(d107, v1841), starked_q_mul_base(d106, v1841));
        const StarkedQm31 d = starked_q_mul(d106, d107);
        if ((d.a | d.b | d.c | d.d) == 0u) atomicOr(error, 2u);
        outputs[212][row] = n.a;
        outputs[213][row] = n.b;
        outputs[214][row] = n.c;
        outputs[215][row] = n.d;
        unsigned *slot = denominators + ((u64)53u * rows + row) * 4u;
        slot[0] = d.a; slot[1] = d.b; slot[2] = d.c; slot[3] = d.d;
    }
}
