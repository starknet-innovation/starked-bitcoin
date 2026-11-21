// stwo-zig Cairo CUDA evaluation codegen v1.
typedef unsigned long long u64;
#define STWO_M31_P 2147483647u
struct StwoCairoQm31 { unsigned a, b, c, d; };
struct StwoCairoEvalArgs {
    u64 trace_offsets;
    u64 interaction_offsets;
    u64 base_params;
    u64 ext_params;
    u64 random_coeffs;
    u64 denom_inv;
    u64 coord_0;
    u64 coord_1;
    u64 coord_2;
    u64 coord_3;
    unsigned row_count;
    unsigned trace_log_size;
    unsigned domain_log_size;
    unsigned rc_base;
};
__device__ __forceinline__ unsigned stwo_m31_add(
    unsigned lhs, unsigned rhs) {
    const unsigned sum = lhs + rhs;
    return sum < STWO_M31_P ? sum : sum - STWO_M31_P;
}
__device__ __forceinline__ unsigned stwo_m31_sub(
    unsigned lhs, unsigned rhs) {
    return lhs >= rhs ? lhs - rhs : lhs + STWO_M31_P - rhs;
}
__device__ __forceinline__ unsigned stwo_m31_mul(
    unsigned lhs, unsigned rhs) {
    const u64 product = (u64)lhs * rhs;
    const unsigned folded = (unsigned)(product & STWO_M31_P) +
        (unsigned)(product >> 31u);
    return folded < STWO_M31_P ? folded : folded - STWO_M31_P;
}
__device__ __forceinline__ unsigned stwo_m31_neg(unsigned value) {
    return value == 0u ? 0u : STWO_M31_P - value;
}
__device__ __forceinline__ unsigned stwo_m31_inv(unsigned value) {
    unsigned result = 1u, base = value, exponent = STWO_M31_P - 2u;
    while (exponent != 0u) {
        if ((exponent & 1u) != 0u)
            result = stwo_m31_mul(result, base);
        base = stwo_m31_mul(base, base);
        exponent >>= 1u;
    }
    return result;
}
__device__ __forceinline__ StwoCairoQm31 stwo_qm31_add(
    StwoCairoQm31 lhs, StwoCairoQm31 rhs) {
    return {
        stwo_m31_add(lhs.a, rhs.a), stwo_m31_add(lhs.b, rhs.b),
        stwo_m31_add(lhs.c, rhs.c), stwo_m31_add(lhs.d, rhs.d)
    };
}
__device__ __forceinline__ StwoCairoQm31 stwo_qm31_sub(
    StwoCairoQm31 lhs, StwoCairoQm31 rhs) {
    return {
        stwo_m31_sub(lhs.a, rhs.a), stwo_m31_sub(lhs.b, rhs.b),
        stwo_m31_sub(lhs.c, rhs.c), stwo_m31_sub(lhs.d, rhs.d)
    };
}
__device__ __forceinline__ StwoCairoQm31 stwo_qm31_neg(
    StwoCairoQm31 value) {
    return {
        stwo_m31_neg(value.a), stwo_m31_neg(value.b),
        stwo_m31_neg(value.c), stwo_m31_neg(value.d)
    };
}
__device__ __forceinline__ StwoCairoQm31 stwo_qm31_mul_base(
    StwoCairoQm31 value, unsigned scalar) {
    return {
        stwo_m31_mul(value.a, scalar), stwo_m31_mul(value.b, scalar),
        stwo_m31_mul(value.c, scalar), stwo_m31_mul(value.d, scalar)
    };
}
__device__ __forceinline__ StwoCairoQm31 stwo_qm31_mul(
    StwoCairoQm31 lhs, StwoCairoQm31 rhs) {
    unsigned x0 = stwo_m31_sub(
        stwo_m31_mul(lhs.a, rhs.a), stwo_m31_mul(lhs.b, rhs.b));
    unsigned x1 = stwo_m31_add(
        stwo_m31_mul(lhs.a, rhs.b), stwo_m31_mul(lhs.b, rhs.a));
    unsigned y0 = stwo_m31_sub(
        stwo_m31_mul(lhs.c, rhs.c), stwo_m31_mul(lhs.d, rhs.d));
    unsigned y1 = stwo_m31_add(
        stwo_m31_mul(lhs.c, rhs.d), stwo_m31_mul(lhs.d, rhs.c));
    unsigned c0 = stwo_m31_sub(
        stwo_m31_mul(lhs.a, rhs.c), stwo_m31_mul(lhs.b, rhs.d));
    unsigned c1 = stwo_m31_add(
        stwo_m31_mul(lhs.a, rhs.d), stwo_m31_mul(lhs.b, rhs.c));
    unsigned c2 = stwo_m31_sub(
        stwo_m31_mul(lhs.c, rhs.a), stwo_m31_mul(lhs.d, rhs.b));
    unsigned c3 = stwo_m31_add(
        stwo_m31_mul(lhs.c, rhs.b), stwo_m31_mul(lhs.d, rhs.a));
    return {
        stwo_m31_add(x0, stwo_m31_sub(stwo_m31_add(y0, y0), y1)),
        stwo_m31_add(x1, stwo_m31_add(y0, stwo_m31_add(y1, y1))),
        stwo_m31_add(c0, c2), stwo_m31_add(c1, c3)
    };
}
__device__ __forceinline__ StwoCairoQm31 stwo_load_qm31(
    const unsigned *arena, u64 offset) {
    return {
        arena[offset], arena[offset + 1u],
        arena[offset + 2u], arena[offset + 3u]
    };
}
__device__ __forceinline__ unsigned stwo_bit_reverse(
    unsigned value, unsigned bits) {
    #if defined(STWO_CUMETAL)
    value = ((value >> 1u) & 0x55555555u) | ((value & 0x55555555u) << 1u);
    value = ((value >> 2u) & 0x33333333u) | ((value & 0x33333333u) << 2u);
    value = ((value >> 4u) & 0x0f0f0f0fu) | ((value & 0x0f0f0f0fu) << 4u);
    value = ((value >> 8u) & 0x00ff00ffu) | ((value & 0x00ff00ffu) << 8u);
    value = (value >> 16u) | (value << 16u);
    return bits == 0u ? 0u : value >> (32u - bits);
#else
    return bits == 0u ? 0u : __brev(value) >> (32u - bits);
#endif
}
__device__ __forceinline__ unsigned stwo_offset_circle(
    unsigned row, unsigned domain_log, unsigned evaluation_log,
    int offset) {
    unsigned previous = stwo_bit_reverse(row, evaluation_log);
    unsigned half_size = 1u << (evaluation_log - 1u);
    int step = offset * (int)(1u <<
        (evaluation_log - domain_log - 1u));
    if (previous < half_size) {
        int position = ((int)previous + step) % (int)half_size;
        if (position < 0) position += (int)half_size;
        previous = (unsigned)position;
    } else {
        int position = ((int)previous - step) % (int)half_size;
        if (position < 0) position += (int)half_size;
        previous = (unsigned)position + half_size;
    }
    return stwo_bit_reverse(previous, evaluation_log);
}
__device__ __forceinline__ unsigned stwo_trace_value(
    const unsigned *arena, const StwoCairoEvalArgs &args,
    unsigned interaction, unsigned column, unsigned row, int offset) {
    const unsigned evaluation_log =
        31u - (unsigned)__clz(args.row_count);
    const unsigned target = offset == 0 ? row : stwo_offset_circle(
        row, args.domain_log_size, evaluation_log, offset);
    const u64 global =
        (u64)arena[args.interaction_offsets + interaction] + column;
    const u64 address = (u64)arena[args.trace_offsets + 2u * global] | ((u64)arena[args.trace_offsets + 2u * global + 1u] << 32u); return arena[address + target];
}
extern "C" __global__ void __launch_bounds__(256)
stwo_cairo_cuda_eval_v6_f09518496b226864(
    unsigned *arena,
    u64 arena_words,
    const StwoCairoEvalArgs *args) {
    const unsigned row =
        blockIdx.x * blockDim.x + threadIdx.x;
    if (arena == nullptr || args == nullptr ||
        row >= args->row_count) return;
    StwoCairoQm31 part_acc = { 0u, 0u, 0u, 0u };
    unsigned b0 = stwo_trace_value(arena, *args, 1u, 0u, row, -1);
    unsigned b1 = stwo_trace_value(arena, *args, 1u, 0u, row, 0);
    unsigned b2 = stwo_trace_value(arena, *args, 1u, 1u, row, 0);
    unsigned b3 = stwo_trace_value(arena, *args, 1u, 2u, row, -1);
    unsigned b4 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 3u, row, -1);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 21u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 22u, row, 0);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 23u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 24u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 25u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 26u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 27u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 28u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 1u, 29u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 1u, 30u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 1u, 31u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 1u, 32u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 1u, 33u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 1u, 34u, row, -1);
    unsigned b38 = stwo_trace_value(arena, *args, 1u, 34u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 1u, 35u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 1u, 36u, row, -1);
    unsigned b41 = stwo_trace_value(arena, *args, 1u, 36u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 1u, 37u, row, -1);
    unsigned b43 = stwo_trace_value(arena, *args, 1u, 37u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 1u, 38u, row, -1);
    unsigned b45 = stwo_trace_value(arena, *args, 1u, 38u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 1u, 39u, row, -1);
    unsigned b47 = stwo_trace_value(arena, *args, 1u, 39u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 1u, 40u, row, -1);
    unsigned b49 = stwo_trace_value(arena, *args, 1u, 40u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 1u, 41u, row, -1);
    unsigned b51 = stwo_trace_value(arena, *args, 1u, 41u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 1u, 42u, row, -1);
    unsigned b53 = stwo_trace_value(arena, *args, 1u, 42u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 1u, 43u, row, -1);
    unsigned b55 = stwo_trace_value(arena, *args, 1u, 43u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 1u, 44u, row, -1);
    unsigned b57 = stwo_trace_value(arena, *args, 1u, 44u, row, 0);
    unsigned b58 = stwo_trace_value(arena, *args, 1u, 45u, row, -1);
    unsigned b59 = stwo_trace_value(arena, *args, 1u, 45u, row, 0);
    unsigned b60 = stwo_trace_value(arena, *args, 1u, 46u, row, -1);
    unsigned b61 = stwo_trace_value(arena, *args, 1u, 46u, row, 0);
    unsigned b62 = stwo_trace_value(arena, *args, 1u, 47u, row, -1);
    unsigned b63 = stwo_trace_value(arena, *args, 1u, 47u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 1u, 48u, row, -1);
    unsigned b65 = stwo_trace_value(arena, *args, 1u, 48u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 1u, 49u, row, -1);
    unsigned b67 = stwo_trace_value(arena, *args, 1u, 49u, row, 0);
    unsigned b68 = stwo_trace_value(arena, *args, 1u, 50u, row, 0);
    unsigned b69 = stwo_trace_value(arena, *args, 1u, 51u, row, -1);
    unsigned b70 = stwo_trace_value(arena, *args, 1u, 51u, row, 0);
    unsigned b71 = stwo_trace_value(arena, *args, 1u, 52u, row, -1);
    unsigned b72 = stwo_trace_value(arena, *args, 1u, 52u, row, 0);
    unsigned b73 = stwo_trace_value(arena, *args, 1u, 53u, row, 0);
    unsigned b74 = stwo_trace_value(arena, *args, 1u, 54u, row, 0);
    unsigned b75 = stwo_trace_value(arena, *args, 1u, 55u, row, 0);
    unsigned b76 = stwo_trace_value(arena, *args, 1u, 56u, row, -1);
    unsigned b77 = stwo_trace_value(arena, *args, 1u, 56u, row, 0);
    unsigned b78 = stwo_trace_value(arena, *args, 1u, 57u, row, 0);
    unsigned b79 = stwo_trace_value(arena, *args, 1u, 58u, row, 0);
    unsigned b80 = stwo_trace_value(arena, *args, 1u, 59u, row, -1);
    unsigned b81 = stwo_trace_value(arena, *args, 1u, 59u, row, 0);
    unsigned b82 = stwo_trace_value(arena, *args, 1u, 60u, row, -1);
    unsigned b83 = stwo_trace_value(arena, *args, 1u, 60u, row, 0);
    unsigned b84 = stwo_trace_value(arena, *args, 1u, 61u, row, -1);
    unsigned b85 = stwo_trace_value(arena, *args, 1u, 61u, row, 0);
    unsigned b86 = stwo_trace_value(arena, *args, 1u, 62u, row, 0);
    unsigned b87 = stwo_trace_value(arena, *args, 1u, 63u, row, 0);
    unsigned b88 = stwo_trace_value(arena, *args, 1u, 64u, row, 0);
    unsigned b89 = stwo_trace_value(arena, *args, 1u, 65u, row, 0);
    unsigned b90 = stwo_trace_value(arena, *args, 1u, 66u, row, -1);
    unsigned b91 = stwo_trace_value(arena, *args, 1u, 66u, row, 0);
    unsigned b92 = stwo_trace_value(arena, *args, 1u, 67u, row, 0);
    unsigned b93 = stwo_trace_value(arena, *args, 1u, 68u, row, 0);
    unsigned b94 = stwo_trace_value(arena, *args, 1u, 69u, row, 0);
    unsigned b95 = stwo_trace_value(arena, *args, 1u, 70u, row, -1);
    unsigned b96 = stwo_trace_value(arena, *args, 1u, 70u, row, 0);
    unsigned b97 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b98 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b99 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b100 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b101 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b102 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b103 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b104 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b105 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b106 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b107 = stwo_trace_value(arena, *args, 2u, 8u, row, -1);
    unsigned b108 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b109 = stwo_trace_value(arena, *args, 2u, 9u, row, -1);
    unsigned b110 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b111 = stwo_trace_value(arena, *args, 2u, 10u, row, -1);
    unsigned b112 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b113 = stwo_trace_value(arena, *args, 2u, 11u, row, -1);
    unsigned b114 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b115 = arena[args->base_params + 0u];
    unsigned b116 = stwo_m31_sub(b1, b115);
    unsigned b117 = stwo_m31_mul(b1, b116);
    unsigned b118 = stwo_m31_sub(b2, b115);
    unsigned b119 = stwo_m31_mul(b2, b118);
    unsigned b120 = stwo_m31_sub(b8, b115);
    unsigned b121 = stwo_m31_mul(b8, b120);
    unsigned b122 = stwo_m31_sub(b9, b115);
    unsigned b123 = stwo_m31_mul(b9, b122);
    unsigned b124 = stwo_m31_sub(b10, b115);
    unsigned b125 = stwo_m31_mul(b10, b124);
    unsigned b126 = stwo_m31_sub(b11, b115);
    unsigned b127 = stwo_m31_mul(b11, b126);
    unsigned b128 = stwo_m31_sub(b18, b115);
    unsigned b129 = stwo_m31_mul(b18, b128);
    unsigned b130 = stwo_m31_sub(b19, b115);
    unsigned b131 = stwo_m31_mul(b19, b130);
    unsigned b132 = stwo_m31_sub(b20, b115);
    unsigned b133 = stwo_m31_mul(b20, b132);
    unsigned b134 = stwo_m31_sub(b21, b115);
    unsigned b135 = stwo_m31_mul(b21, b134);
    unsigned b136 = stwo_m31_sub(b22, b115);
    unsigned b137 = stwo_m31_mul(b22, b136);
    unsigned b138 = stwo_m31_sub(b23, b115);
    unsigned b139 = stwo_m31_mul(b23, b138);
    unsigned b140 = stwo_m31_sub(b24, b115);
    unsigned b141 = stwo_m31_mul(b24, b140);
    unsigned b142 = stwo_m31_sub(b31, b115);
    unsigned b143 = stwo_m31_mul(b31, b142);
    unsigned b144 = stwo_m31_add(b10, b11);
    unsigned b145 = stwo_m31_add(b9, b144);
    unsigned b146 = stwo_m31_add(b8, b145);
    unsigned b147 = stwo_m31_sub(b146, b1);
    unsigned b148 = stwo_m31_sub(b115, b1);
    unsigned b149 = stwo_m31_mul(b2, b148);
    unsigned b150 = stwo_m31_sub(b115, b8);
    unsigned b151 = stwo_m31_mul(b2, b150);
    unsigned b152 = arena[args->base_params + 1u];
    unsigned b153 = stwo_m31_mul(b152, b19);
    unsigned b154 = arena[args->base_params + 2u];
    unsigned b155 = stwo_m31_mul(b154, b20);
    unsigned b156 = arena[args->base_params + 3u];
    unsigned b157 = stwo_m31_mul(b156, b21);
    unsigned b158 = stwo_m31_add(b155, b157);
    unsigned b159 = stwo_m31_add(b153, b158);
    unsigned b160 = stwo_m31_add(b18, b159);
    unsigned b161 = stwo_m31_mul(b7, b160);
    unsigned b162 = stwo_m31_add(b25, b161);
    unsigned b163 = stwo_m31_sub(b27, b162);
    unsigned b164 = stwo_m31_mul(b18, b22);
    unsigned b165 = stwo_m31_mul(b19, b23);
    unsigned b166 = stwo_m31_mul(b21, b24);
    unsigned b167 = stwo_m31_add(b165, b166);
    unsigned b168 = stwo_m31_add(b164, b167);
    unsigned b169 = stwo_m31_sub(b28, b168);
    unsigned b170 = stwo_m31_mul(b9, b28);
    unsigned b171 = stwo_m31_sub(b29, b170);
    unsigned b172 = stwo_m31_sub(b115, b31);
    unsigned b173 = stwo_m31_mul(b29, b172);
    unsigned b174 = stwo_m31_sub(b30, b173);
    unsigned b175 = stwo_m31_sub(b115, b24);
    unsigned b176 = stwo_m31_mul(b31, b175);
    unsigned b177 = stwo_m31_sub(b115, b29);
    unsigned b178 = stwo_m31_mul(b31, b177);
    unsigned b179 = stwo_m31_mul(b30, b24);
    unsigned b180 = stwo_m31_sub(b32, b179);
    unsigned b181 = stwo_m31_sub(b7, b115);
    unsigned b182 = stwo_m31_mul(b7, b181);
    unsigned b183 = stwo_m31_mul(b32, b182);
    unsigned b184 = stwo_m31_sub(b33, b115);
    unsigned b185 = stwo_m31_mul(b33, b184);
    unsigned b186 = stwo_m31_mul(b33, b27);
    unsigned b187 = stwo_m31_sub(b115, b33);
    unsigned b188 = stwo_m31_mul(b27, b34);
    unsigned b189 = stwo_m31_sub(b188, b115);
    unsigned b190 = stwo_m31_mul(b187, b189);
    unsigned b191 = stwo_m31_sub(b35, b115);
    unsigned b192 = stwo_m31_mul(b35, b191);
    unsigned b193 = stwo_m31_sub(b26, b115);
    unsigned b194 = stwo_m31_mul(b35, b193);
    unsigned b195 = stwo_m31_sub(b115, b35);
    unsigned b196 = stwo_m31_mul(b193, b36);
    unsigned b197 = stwo_m31_sub(b196, b115);
    unsigned b198 = stwo_m31_mul(b195, b197);
    unsigned b199 = stwo_m31_sub(b38, b115);
    unsigned b200 = stwo_m31_mul(b38, b199);
    unsigned b201 = stwo_m31_sub(b6, b115);
    unsigned b202 = stwo_m31_mul(b38, b201);
    unsigned b203 = stwo_m31_sub(b115, b38);
    unsigned b204 = stwo_m31_mul(b201, b39);
    unsigned b205 = stwo_m31_sub(b204, b115);
    unsigned b206 = stwo_m31_mul(b203, b205);
    unsigned b207 = stwo_m31_add(b14, b15);
    unsigned b208 = stwo_m31_add(b13, b207);
    unsigned b209 = stwo_m31_add(b17, b208);
    unsigned b210 = stwo_m31_sub(b115, b209);
    unsigned b211 = stwo_m31_mul(b8, b210);
    unsigned b212 = stwo_m31_mul(b30, b33);
    unsigned b213 = stwo_m31_mul(b10, b35);
    unsigned b214 = stwo_m31_add(b212, b213);
    unsigned b215 = stwo_m31_add(b211, b214);
    unsigned b216 = stwo_m31_sub(b41, b215);
    unsigned b217 = stwo_m31_mul(b8, b17);
    unsigned b218 = stwo_m31_mul(b30, b187);
    unsigned b219 = stwo_m31_mul(b10, b195);
    unsigned b220 = stwo_m31_add(b218, b219);
    unsigned b221 = stwo_m31_add(b217, b220);
    unsigned b222 = stwo_m31_sub(b45, b221);
    unsigned b223 = stwo_m31_mul(b8, b208);
    unsigned b224 = stwo_m31_sub(b9, b29);
    unsigned b225 = stwo_m31_add(b223, b224);
    unsigned b226 = stwo_m31_sub(b43, b225);
    unsigned b227 = stwo_m31_mul(b29, b31);
    unsigned b228 = stwo_m31_add(b227, b11);
    unsigned b229 = stwo_m31_sub(b47, b228);
    unsigned b230 = stwo_m31_mul(b8, b12);
    unsigned b231 = stwo_m31_mul(b30, b27);
    unsigned b232 = stwo_m31_mul(b10, b193);
    unsigned b233 = stwo_m31_add(b231, b232);
    unsigned b234 = stwo_m31_add(b230, b233);
    unsigned b235 = stwo_m31_sub(b49, b234);
    unsigned b236 = stwo_m31_mul(b224, b27);
    unsigned b237 = stwo_m31_sub(b51, b236);
    unsigned b238 = stwo_m31_sub(b53, b223);
    unsigned b239 = stwo_m31_mul(b224, b18);
    unsigned b240 = stwo_m31_sub(b55, b239);
    unsigned b241 = stwo_m31_mul(b224, b19);
    unsigned b242 = stwo_m31_sub(b57, b241);
    unsigned b243 = stwo_m31_mul(b224, b20);
    unsigned b244 = stwo_m31_sub(b59, b243);
    unsigned b245 = stwo_m31_mul(b8, b13);
    unsigned b246 = stwo_m31_mul(b224, b22);
    unsigned b247 = stwo_m31_add(b245, b246);
    unsigned b248 = stwo_m31_sub(b61, b247);
    unsigned b249 = stwo_m31_mul(b8, b14);
    unsigned b250 = stwo_m31_mul(b224, b23);
    unsigned b251 = stwo_m31_add(b249, b250);
    unsigned b252 = stwo_m31_sub(b63, b251);
    unsigned b253 = stwo_m31_mul(b8, b15);
    unsigned b254 = stwo_m31_mul(b224, b24);
    unsigned b255 = stwo_m31_add(b253, b254);
    unsigned b256 = stwo_m31_sub(b65, b255);
    unsigned b257 = stwo_m31_sub(b115, b2);
    unsigned b258 = stwo_m31_mul(b1, b257);
    unsigned b259 = stwo_m31_sub(b68, b258);
    unsigned b260 = stwo_m31_sub(b8, b40);
    unsigned b261 = stwo_m31_mul(b68, b260);
    unsigned b262 = stwo_m31_sub(b9, b42);
    unsigned b263 = stwo_m31_mul(b68, b262);
    unsigned b264 = stwo_m31_sub(b10, b44);
    unsigned b265 = stwo_m31_mul(b68, b264);
    unsigned b266 = stwo_m31_sub(b11, b46);
    unsigned b267 = stwo_m31_mul(b68, b266);
    unsigned b268 = stwo_m31_sub(b26, b48);
    unsigned b269 = stwo_m31_mul(b68, b268);
    unsigned b270 = stwo_m31_sub(b25, b50);
    unsigned b271 = stwo_m31_mul(b68, b270);
    unsigned b272 = stwo_m31_sub(b18, b52);
    unsigned b273 = stwo_m31_mul(b68, b272);
    unsigned b274 = stwo_m31_sub(b19, b54);
    unsigned b275 = stwo_m31_mul(b68, b274);
    unsigned b276 = stwo_m31_sub(b20, b56);
    unsigned b277 = stwo_m31_mul(b68, b276);
    unsigned b278 = stwo_m31_sub(b21, b58);
    unsigned b279 = stwo_m31_mul(b68, b278);
    unsigned b280 = stwo_m31_sub(b22, b60);
    unsigned b281 = stwo_m31_mul(b68, b280);
    unsigned b282 = stwo_m31_sub(b23, b62);
    unsigned b283 = stwo_m31_mul(b68, b282);
    unsigned b284 = stwo_m31_sub(b24, b64);
    unsigned b285 = stwo_m31_mul(b68, b284);
    unsigned b286 = stwo_m31_sub(b4, b3);
    unsigned b287 = stwo_m31_sub(b286, b115);
    unsigned b288 = stwo_m31_mul(b68, b287);
    unsigned b289 = stwo_m31_sub(b6, b5);
    unsigned b290 = stwo_m31_add(b289, b115);
    unsigned b291 = stwo_m31_mul(b68, b290);
    unsigned b292 = stwo_m31_mul(b68, b37);
    unsigned b293 = stwo_m31_mul(b97, b258);
    unsigned b294 = stwo_m31_sub(b115, b97);
    unsigned b295 = stwo_m31_sub(b115, b0);
    unsigned b296 = stwo_m31_mul(b1, b295);
    unsigned b297 = stwo_m31_mul(b294, b296);
    unsigned b298 = stwo_m31_sub(b115, b37);
    unsigned b299 = stwo_m31_mul(b2, b298);
    unsigned b300 = stwo_m31_mul(b294, b299);
    unsigned b301 = stwo_m31_sub(b0, b1);
    unsigned b302 = stwo_m31_mul(b301, b298);
    unsigned b303 = stwo_m31_mul(b294, b302);
    unsigned b304 = stwo_m31_sub(b115, b98);
    unsigned b305 = stwo_m31_mul(b304, b1);
    unsigned b306 = stwo_m31_mul(b8, b94);
    unsigned b307 = stwo_m31_sub(b67, b306);
    unsigned b308 = stwo_m31_mul(b97, b307);
    unsigned b309 = stwo_m31_sub(b67, b66);
    unsigned b310 = stwo_m31_sub(b309, b306);
    unsigned b311 = stwo_m31_mul(b294, b310);
    unsigned b312 = stwo_m31_sub(b70, b115);
    unsigned b313 = stwo_m31_mul(b70, b312);
    unsigned b314 = stwo_m31_sub(b72, b115);
    unsigned b315 = stwo_m31_mul(b72, b314);
    unsigned b316 = stwo_m31_sub(b115, b70);
    unsigned b317 = stwo_m31_mul(b72, b316);
    unsigned b318 = stwo_m31_sub(b70, b69);
    unsigned b319 = stwo_m31_mul(b68, b318);
    unsigned b320 = stwo_m31_sub(b72, b71);
    unsigned b321 = stwo_m31_mul(b68, b320);
    unsigned b322 = stwo_m31_sub(b81, b80);
    unsigned b323 = stwo_m31_mul(b68, b322);
    unsigned b324 = stwo_m31_sub(b83, b82);
    unsigned b325 = stwo_m31_mul(b68, b324);
    unsigned b326 = stwo_m31_sub(b85, b84);
    unsigned b327 = stwo_m31_mul(b68, b326);
    unsigned b328 = stwo_m31_mul(b68, b76);
    unsigned b329 = stwo_m31_mul(b8, b73);
    unsigned b330 = stwo_m31_add(b328, b329);
    unsigned b331 = stwo_m31_sub(b77, b330);
    unsigned b332 = stwo_m31_sub(b78, b115);
    unsigned b333 = stwo_m31_mul(b78, b332);
    unsigned b334 = stwo_m31_mul(b78, b77);
    unsigned b335 = stwo_m31_sub(b115, b78);
    unsigned b336 = stwo_m31_mul(b77, b79);
    unsigned b337 = stwo_m31_sub(b336, b115);
    unsigned b338 = stwo_m31_mul(b335, b337);
    unsigned b339 = stwo_m31_mul(b78, b41);
    unsigned b340 = stwo_m31_sub(b81, b339);
    unsigned b341 = stwo_m31_mul(b38, b340);
    unsigned b342 = stwo_m31_sub(b86, b115);
    unsigned b343 = stwo_m31_mul(b86, b342);
    unsigned b344 = stwo_m31_sub(b49, b6);
    unsigned b345 = stwo_m31_add(b344, b115);
    unsigned b346 = stwo_m31_mul(b86, b345);
    unsigned b347 = stwo_m31_sub(b115, b86);
    unsigned b348 = stwo_m31_mul(b345, b87);
    unsigned b349 = stwo_m31_sub(b348, b115);
    unsigned b350 = stwo_m31_mul(b347, b349);
    unsigned b351 = stwo_m31_add(b217, b218);
    unsigned b352 = stwo_m31_mul(b351, b86);
    unsigned b353 = stwo_m31_sub(b88, b352);
    unsigned b354 = stwo_m31_sub(b85, b49);
    unsigned b355 = stwo_m31_mul(b88, b354);
    unsigned b356 = stwo_m31_sub(b83, b4);
    unsigned b357 = stwo_m31_sub(b356, b115);
    unsigned b358 = stwo_m31_mul(b88, b357);
    unsigned b359 = stwo_m31_sub(b115, b10);
    unsigned b360 = stwo_m31_mul(b359, b85);
    unsigned b361 = stwo_m31_mul(b38, b360);
    unsigned b362 = arena[args->base_params + 4u];
    unsigned b363 = stwo_m31_sub(b89, b362);
    unsigned b364 = stwo_m31_mul(b2, b363);
    unsigned b365 = stwo_m31_sub(b89, b90);
    unsigned b366 = stwo_m31_mul(b68, b365);
    unsigned b367 = stwo_m31_mul(b8, b75);
    unsigned b368 = stwo_m31_mul(b150, b89);
    unsigned b369 = stwo_m31_add(b367, b368);
    unsigned b370 = stwo_m31_sub(b91, b369);
    unsigned b371 = stwo_m31_mul(b74, b89);
    unsigned b372 = stwo_m31_sub(b92, b371);
    unsigned b373 = arena[args->base_params + 5u];
    unsigned b374 = stwo_m31_mul(b373, b72);
    unsigned b375 = stwo_m31_add(b70, b374);
    unsigned b376 = stwo_m31_mul(b362, b74);
    unsigned b377 = stwo_m31_sub(b16, b376);
    unsigned b378 = stwo_m31_add(b377, b92);
    unsigned b379 = stwo_m31_mul(b375, b378);
    unsigned b380 = stwo_m31_sub(b93, b379);
    unsigned b381 = stwo_m31_mul(b316, b16);
    unsigned b382 = stwo_m31_sub(b94, b381);
    unsigned b383 = stwo_m31_mul(b8, b93);
    unsigned b384 = stwo_m31_sub(b96, b383);
    unsigned b385 = stwo_m31_mul(b97, b384);
    unsigned b386 = stwo_m31_sub(b96, b95);
    unsigned b387 = stwo_m31_sub(b386, b383);
    unsigned b388 = stwo_m31_mul(b294, b387);
    unsigned b389 = stwo_m31_mul(b2, b316);
    unsigned b390 = stwo_m31_neg(b389);
    unsigned b391 = stwo_m31_neg(b1);
    unsigned b392 = stwo_m31_neg(b8);
    unsigned b393 = stwo_m31_neg(b31);
    unsigned b394 = arena[args->base_params + 6u];
    unsigned b395 = stwo_m31_sub(b7, b394);
    unsigned b396 = stwo_m31_mul(b2, b70);
    unsigned b397 = stwo_m31_neg(b396);
    unsigned b398 = arena[args->base_params + 7u];
    StwoCairoQm31 e0 = { b117, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b119, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b121, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b123, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b125, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b127, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b129, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b131, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b133, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b135, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b137, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b139, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b141, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b143, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b147, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b149, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b151, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b163, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b169, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b171, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b174, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b176, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b178, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b180, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b183, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b185, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b186, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b190, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b192, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b194, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b198, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b200, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b202, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b206, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b216, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b222, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b226, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b229, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b235, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b237, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b238, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b240, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b242, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b244, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b248, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b252, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b256, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b259, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = { b261, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e48, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e49 = { b263, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e49, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e50 = { b265, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e50, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
    StwoCairoQm31 e51 = { b267, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e51, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 51u) * 4u)));
    StwoCairoQm31 e52 = { b269, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e52, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 52u) * 4u)));
    StwoCairoQm31 e53 = { b271, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e53, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 53u) * 4u)));
    StwoCairoQm31 e54 = { b273, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e54, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 54u) * 4u)));
    StwoCairoQm31 e55 = { b275, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e55, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 55u) * 4u)));
    StwoCairoQm31 e56 = { b277, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e56, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 56u) * 4u)));
    StwoCairoQm31 e57 = { b279, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e57, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 57u) * 4u)));
    StwoCairoQm31 e58 = { b281, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e58, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 58u) * 4u)));
    StwoCairoQm31 e59 = { b283, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e59, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 59u) * 4u)));
    StwoCairoQm31 e60 = { b285, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e60, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 60u) * 4u)));
    StwoCairoQm31 e61 = { b288, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e61, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 61u) * 4u)));
    StwoCairoQm31 e62 = { b291, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e62, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 62u) * 4u)));
    StwoCairoQm31 e63 = { b292, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e63, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 63u) * 4u)));
    StwoCairoQm31 e64 = { b293, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e64, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 64u) * 4u)));
    StwoCairoQm31 e65 = { b297, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e65, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 65u) * 4u)));
    StwoCairoQm31 e66 = { b300, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e66, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 66u) * 4u)));
    StwoCairoQm31 e67 = { b303, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e67, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 67u) * 4u)));
    StwoCairoQm31 e68 = { b305, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e68, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 68u) * 4u)));
    StwoCairoQm31 e69 = { b308, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e69, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 69u) * 4u)));
    StwoCairoQm31 e70 = { b311, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e70, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 70u) * 4u)));
    StwoCairoQm31 e71 = { b313, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e71, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 71u) * 4u)));
    StwoCairoQm31 e72 = { b315, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e72, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 72u) * 4u)));
    StwoCairoQm31 e73 = { b317, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e73, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 73u) * 4u)));
    StwoCairoQm31 e74 = { b319, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e74, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 74u) * 4u)));
    StwoCairoQm31 e75 = { b321, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e75, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 75u) * 4u)));
    StwoCairoQm31 e76 = { b323, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e76, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 76u) * 4u)));
    StwoCairoQm31 e77 = { b325, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e77, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 77u) * 4u)));
    StwoCairoQm31 e78 = { b327, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e78, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 78u) * 4u)));
    StwoCairoQm31 e79 = { b331, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e79, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 79u) * 4u)));
    StwoCairoQm31 e80 = { b333, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e80, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 80u) * 4u)));
    StwoCairoQm31 e81 = { b334, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e81, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 81u) * 4u)));
    StwoCairoQm31 e82 = { b338, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e82, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 82u) * 4u)));
    StwoCairoQm31 e83 = { b341, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e83, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 83u) * 4u)));
    StwoCairoQm31 e84 = { b343, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e84, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 84u) * 4u)));
    StwoCairoQm31 e85 = { b346, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e85, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 85u) * 4u)));
    StwoCairoQm31 e86 = { b350, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e86, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 86u) * 4u)));
    StwoCairoQm31 e87 = { b353, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e87, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 87u) * 4u)));
    StwoCairoQm31 e88 = { b355, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e88, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 88u) * 4u)));
    StwoCairoQm31 e89 = { b358, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e89, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 89u) * 4u)));
    StwoCairoQm31 e90 = { b361, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e90, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 90u) * 4u)));
    StwoCairoQm31 e91 = { b364, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e91, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 91u) * 4u)));
    StwoCairoQm31 e92 = { b366, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e92, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 92u) * 4u)));
    StwoCairoQm31 e93 = { b370, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e93, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 93u) * 4u)));
    StwoCairoQm31 e94 = { b372, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e94, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 94u) * 4u)));
    StwoCairoQm31 e95 = { b380, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e95, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 95u) * 4u)));
    StwoCairoQm31 e96 = { b382, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e96, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 96u) * 4u)));
    StwoCairoQm31 e97 = { b385, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e97, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 97u) * 4u)));
    StwoCairoQm31 e98 = { b388, b398, b398, b398 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e98, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 98u) * 4u)));
    StwoCairoQm31 e99 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e100 = stwo_load_qm31(arena, args->ext_params + 11u * 4u);
    StwoCairoQm31 e101 = { b390, b398, b398, b398 };
    StwoCairoQm31 e102 = { 11u, 0u, 0u, 0u };
    StwoCairoQm31 e103 = { b4, b398, b398, b398 };
    StwoCairoQm31 e104 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e105 = stwo_qm31_mul(e103, e104);
    StwoCairoQm31 e106 = stwo_qm31_add(e102, e105);
    StwoCairoQm31 e107 = { b6, b398, b398, b398 };
    StwoCairoQm31 e108 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e109 = stwo_qm31_mul(e107, e108);
    StwoCairoQm31 e110 = stwo_qm31_add(e106, e109);
    StwoCairoQm31 e111 = { b81, b398, b398, b398 };
    StwoCairoQm31 e112 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e113 = stwo_qm31_mul(e111, e112);
    StwoCairoQm31 e114 = stwo_qm31_add(e110, e113);
    StwoCairoQm31 e115 = { b83, b398, b398, b398 };
    StwoCairoQm31 e116 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e117 = stwo_qm31_mul(e115, e116);
    StwoCairoQm31 e118 = stwo_qm31_add(e114, e117);
    StwoCairoQm31 e119 = { b85, b398, b398, b398 };
    StwoCairoQm31 e120 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e121 = stwo_qm31_mul(e119, e120);
    StwoCairoQm31 e122 = stwo_qm31_add(e118, e121);
    StwoCairoQm31 e123 = stwo_qm31_sub(e122, e99);
    StwoCairoQm31 e124 = { b391, b398, b398, b398 };
    StwoCairoQm31 e125 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e126 = { b4, b398, b398, b398 };
    StwoCairoQm31 e127 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e128 = stwo_qm31_mul(e126, e127);
    StwoCairoQm31 e129 = stwo_qm31_add(e125, e128);
    StwoCairoQm31 e130 = { b7, b398, b398, b398 };
    StwoCairoQm31 e131 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e132 = stwo_qm31_mul(e130, e131);
    StwoCairoQm31 e133 = stwo_qm31_add(e129, e132);
    StwoCairoQm31 e134 = stwo_qm31_sub(e133, e99);
    StwoCairoQm31 e135 = { b392, b398, b398, b398 };
    StwoCairoQm31 e136 = { 10u, 0u, 0u, 0u };
    StwoCairoQm31 e137 = { b7, b398, b398, b398 };
    StwoCairoQm31 e138 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e139 = stwo_qm31_mul(e137, e138);
    StwoCairoQm31 e140 = stwo_qm31_add(e136, e139);
    StwoCairoQm31 e141 = { b12, b398, b398, b398 };
    StwoCairoQm31 e142 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e143 = stwo_qm31_mul(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_add(e140, e143);
    StwoCairoQm31 e145 = { b13, b398, b398, b398 };
    StwoCairoQm31 e146 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e147 = stwo_qm31_mul(e145, e146);
    StwoCairoQm31 e148 = stwo_qm31_add(e144, e147);
    StwoCairoQm31 e149 = { b14, b398, b398, b398 };
    StwoCairoQm31 e150 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e151 = stwo_qm31_mul(e149, e150);
    StwoCairoQm31 e152 = stwo_qm31_add(e148, e151);
    StwoCairoQm31 e153 = { b15, b398, b398, b398 };
    StwoCairoQm31 e154 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e155 = stwo_qm31_mul(e153, e154);
    StwoCairoQm31 e156 = stwo_qm31_add(e152, e155);
    StwoCairoQm31 e157 = { b16, b398, b398, b398 };
    StwoCairoQm31 e158 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e159 = stwo_qm31_mul(e157, e158);
    StwoCairoQm31 e160 = stwo_qm31_add(e156, e159);
    StwoCairoQm31 e161 = { b17, b398, b398, b398 };
    StwoCairoQm31 e162 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e163 = stwo_qm31_mul(e161, e162);
    StwoCairoQm31 e164 = stwo_qm31_add(e160, e163);
    StwoCairoQm31 e165 = { b73, b398, b398, b398 };
    StwoCairoQm31 e166 = stwo_load_qm31(arena, args->ext_params + 8u * 4u);
    StwoCairoQm31 e167 = stwo_qm31_mul(e165, e166);
    StwoCairoQm31 e168 = stwo_qm31_add(e164, e167);
    StwoCairoQm31 e169 = { b74, b398, b398, b398 };
    StwoCairoQm31 e170 = stwo_load_qm31(arena, args->ext_params + 9u * 4u);
    StwoCairoQm31 e171 = stwo_qm31_mul(e169, e170);
    StwoCairoQm31 e172 = stwo_qm31_add(e168, e171);
    StwoCairoQm31 e173 = { b75, b398, b398, b398 };
    StwoCairoQm31 e174 = stwo_load_qm31(arena, args->ext_params + 10u * 4u);
    StwoCairoQm31 e175 = stwo_qm31_mul(e173, e174);
    StwoCairoQm31 e176 = stwo_qm31_add(e172, e175);
    StwoCairoQm31 e177 = stwo_qm31_sub(e176, e99);
    StwoCairoQm31 e178 = { b393, b398, b398, b398 };
    StwoCairoQm31 e179 = { 9u, 0u, 0u, 0u };
    StwoCairoQm31 e180 = { b395, b398, b398, b398 };
    StwoCairoQm31 e181 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e182 = stwo_qm31_mul(e180, e181);
    StwoCairoQm31 e183 = stwo_qm31_add(e179, e182);
    StwoCairoQm31 e184 = stwo_qm31_sub(e183, e99);
    StwoCairoQm31 e185 = { b304, b398, b398, b398 };
    StwoCairoQm31 e186 = { 15u, 0u, 0u, 0u };
    StwoCairoQm31 e187 = { b67, b398, b398, b398 };
    StwoCairoQm31 e188 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e189 = stwo_qm31_mul(e187, e188);
    StwoCairoQm31 e190 = stwo_qm31_add(e186, e189);
    StwoCairoQm31 e191 = { b96, b398, b398, b398 };
    StwoCairoQm31 e192 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e193 = stwo_qm31_mul(e191, e192);
    StwoCairoQm31 e194 = stwo_qm31_add(e190, e193);
    StwoCairoQm31 e195 = stwo_qm31_sub(e194, e99);
    StwoCairoQm31 e196 = { b397, b398, b398, b398 };
    StwoCairoQm31 e197 = { 26u, 0u, 0u, 0u };
    StwoCairoQm31 e198 = { b4, b398, b398, b398 };
    StwoCairoQm31 e199 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e200 = stwo_qm31_mul(e198, e199);
    StwoCairoQm31 e201 = stwo_qm31_add(e197, e200);
    StwoCairoQm31 e202 = { b6, b398, b398, b398 };
    StwoCairoQm31 e203 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e204 = stwo_qm31_mul(e202, e203);
    StwoCairoQm31 e205 = stwo_qm31_add(e201, e204);
    StwoCairoQm31 e206 = { b72, b398, b398, b398 };
    StwoCairoQm31 e207 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e208 = stwo_qm31_mul(e206, e207);
    StwoCairoQm31 e209 = stwo_qm31_add(e205, e208);
    StwoCairoQm31 e210 = stwo_qm31_sub(e209, e99);
    StwoCairoQm31 e211 = { b99, b100, b101, b102 };
    StwoCairoQm31 e212 = { b103, b104, b105, b106 };
    StwoCairoQm31 e213 = { b108, b110, b112, b114 };
    StwoCairoQm31 e214 = { b107, b109, b111, b113 };
    StwoCairoQm31 e215 = stwo_qm31_mul(e101, e134);
    StwoCairoQm31 e216 = stwo_qm31_mul(e124, e123);
    StwoCairoQm31 e217 = stwo_qm31_add(e215, e216);
    StwoCairoQm31 e218 = stwo_qm31_mul(e123, e134);
    StwoCairoQm31 e219 = stwo_qm31_mul(e211, e218);
    StwoCairoQm31 e220 = stwo_qm31_sub(e219, e217);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e220, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 99u) * 4u)));
    StwoCairoQm31 e221 = stwo_qm31_mul(e135, e184);
    StwoCairoQm31 e222 = stwo_qm31_mul(e178, e177);
    StwoCairoQm31 e223 = stwo_qm31_add(e221, e222);
    StwoCairoQm31 e224 = stwo_qm31_mul(e177, e184);
    StwoCairoQm31 e225 = stwo_qm31_sub(e212, e211);
    StwoCairoQm31 e226 = stwo_qm31_mul(e225, e224);
    StwoCairoQm31 e227 = stwo_qm31_sub(e226, e223);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e227, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 100u) * 4u)));
    StwoCairoQm31 e228 = stwo_qm31_mul(e185, e210);
    StwoCairoQm31 e229 = stwo_qm31_mul(e196, e195);
    StwoCairoQm31 e230 = stwo_qm31_add(e228, e229);
    StwoCairoQm31 e231 = stwo_qm31_mul(e195, e210);
    StwoCairoQm31 e232 = stwo_qm31_sub(e213, e214);
    StwoCairoQm31 e233 = stwo_qm31_sub(e232, e212);
    StwoCairoQm31 e234 = stwo_qm31_add(e233, e100);
    StwoCairoQm31 e235 = stwo_qm31_mul(e234, e231);
    StwoCairoQm31 e236 = stwo_qm31_sub(e235, e230);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e236, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 101u) * 4u)));
    StwoCairoQm31 result = stwo_qm31_mul_base(
        part_acc,
        arena[args->denom_inv +
            (row >> args->trace_log_size)]);
    StwoCairoQm31 cumulative = {
        arena[args->coord_0 + row],
        arena[args->coord_1 + row],
        arena[args->coord_2 + row],
        arena[args->coord_3 + row]
    };
    cumulative = stwo_qm31_add(cumulative, result);
    arena[args->coord_0 + row] = cumulative.a;
    arena[args->coord_1 + row] = cumulative.b;
    arena[args->coord_2 + row] = cumulative.c;
    arena[args->coord_3 + row] = cumulative.d;
    (void)arena_words;
}
