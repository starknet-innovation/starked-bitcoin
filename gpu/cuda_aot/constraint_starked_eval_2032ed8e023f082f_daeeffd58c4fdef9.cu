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
stwo_cairo_cuda_eval_v6_2032ed8e023f082f(
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
    unsigned b2 = stwo_trace_value(arena, *args, 1u, 0u, row, 1);
    unsigned b3 = stwo_trace_value(arena, *args, 1u, 1u, row, -1);
    unsigned b4 = stwo_trace_value(arena, *args, 1u, 1u, row, 0);
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 2u, row, -1);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 3u, row, -1);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 21u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 22u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 23u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 24u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 25u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 26u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 1u, 27u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 1u, 28u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 1u, 29u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 1u, 30u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 1u, 31u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 1u, 32u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 1u, 33u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 1u, 34u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 1u, 35u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 1u, 36u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 1u, 37u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 1u, 38u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 1u, 39u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 1u, 40u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 1u, 41u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 1u, 42u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b58 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b60 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b61 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b62 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b63 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b65 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 2u, 16u, row, 0);
    unsigned b67 = stwo_trace_value(arena, *args, 2u, 17u, row, 0);
    unsigned b68 = stwo_trace_value(arena, *args, 2u, 18u, row, 0);
    unsigned b69 = stwo_trace_value(arena, *args, 2u, 19u, row, 0);
    unsigned b70 = stwo_trace_value(arena, *args, 2u, 20u, row, 0);
    unsigned b71 = stwo_trace_value(arena, *args, 2u, 21u, row, 0);
    unsigned b72 = stwo_trace_value(arena, *args, 2u, 22u, row, 0);
    unsigned b73 = stwo_trace_value(arena, *args, 2u, 23u, row, 0);
    unsigned b74 = stwo_trace_value(arena, *args, 2u, 24u, row, 0);
    unsigned b75 = stwo_trace_value(arena, *args, 2u, 25u, row, 0);
    unsigned b76 = stwo_trace_value(arena, *args, 2u, 26u, row, 0);
    unsigned b77 = stwo_trace_value(arena, *args, 2u, 27u, row, 0);
    unsigned b78 = stwo_trace_value(arena, *args, 2u, 28u, row, 0);
    unsigned b79 = stwo_trace_value(arena, *args, 2u, 29u, row, 0);
    unsigned b80 = stwo_trace_value(arena, *args, 2u, 30u, row, 0);
    unsigned b81 = stwo_trace_value(arena, *args, 2u, 31u, row, 0);
    unsigned b82 = stwo_trace_value(arena, *args, 2u, 32u, row, 0);
    unsigned b83 = stwo_trace_value(arena, *args, 2u, 33u, row, 0);
    unsigned b84 = stwo_trace_value(arena, *args, 2u, 34u, row, 0);
    unsigned b85 = stwo_trace_value(arena, *args, 2u, 35u, row, 0);
    unsigned b86 = stwo_trace_value(arena, *args, 2u, 36u, row, 0);
    unsigned b87 = stwo_trace_value(arena, *args, 2u, 37u, row, 0);
    unsigned b88 = stwo_trace_value(arena, *args, 2u, 38u, row, 0);
    unsigned b89 = stwo_trace_value(arena, *args, 2u, 39u, row, 0);
    unsigned b90 = stwo_trace_value(arena, *args, 2u, 40u, row, 0);
    unsigned b91 = stwo_trace_value(arena, *args, 2u, 41u, row, 0);
    unsigned b92 = stwo_trace_value(arena, *args, 2u, 42u, row, 0);
    unsigned b93 = stwo_trace_value(arena, *args, 2u, 43u, row, 0);
    unsigned b94 = stwo_trace_value(arena, *args, 2u, 44u, row, 0);
    unsigned b95 = stwo_trace_value(arena, *args, 2u, 45u, row, 0);
    unsigned b96 = stwo_trace_value(arena, *args, 2u, 46u, row, 0);
    unsigned b97 = stwo_trace_value(arena, *args, 2u, 47u, row, 0);
    unsigned b98 = stwo_trace_value(arena, *args, 2u, 48u, row, 0);
    unsigned b99 = stwo_trace_value(arena, *args, 2u, 49u, row, 0);
    unsigned b100 = stwo_trace_value(arena, *args, 2u, 50u, row, 0);
    unsigned b101 = stwo_trace_value(arena, *args, 2u, 51u, row, 0);
    unsigned b102 = stwo_trace_value(arena, *args, 2u, 52u, row, -1);
    unsigned b103 = stwo_trace_value(arena, *args, 2u, 52u, row, 0);
    unsigned b104 = stwo_trace_value(arena, *args, 2u, 53u, row, -1);
    unsigned b105 = stwo_trace_value(arena, *args, 2u, 53u, row, 0);
    unsigned b106 = stwo_trace_value(arena, *args, 2u, 54u, row, -1);
    unsigned b107 = stwo_trace_value(arena, *args, 2u, 54u, row, 0);
    unsigned b108 = stwo_trace_value(arena, *args, 2u, 55u, row, -1);
    unsigned b109 = stwo_trace_value(arena, *args, 2u, 55u, row, 0);
    unsigned b110 = arena[args->base_params + 0u];
    unsigned b111 = stwo_m31_sub(b1, b110);
    unsigned b112 = stwo_m31_mul(b1, b111);
    unsigned b113 = stwo_m31_sub(b110, b48);
    unsigned b114 = stwo_m31_sub(b110, b0);
    unsigned b115 = stwo_m31_mul(b1, b114);
    unsigned b116 = stwo_m31_mul(b113, b115);
    unsigned b117 = stwo_m31_sub(b110, b49);
    unsigned b118 = stwo_m31_mul(b117, b1);
    unsigned b119 = stwo_m31_mul(b48, b4);
    unsigned b120 = stwo_m31_sub(b4, b3);
    unsigned b121 = stwo_m31_sub(b120, b110);
    unsigned b122 = stwo_m31_mul(b1, b121);
    unsigned b123 = stwo_m31_mul(b113, b122);
    unsigned b124 = stwo_m31_sub(b6, b110);
    unsigned b125 = stwo_m31_mul(b48, b124);
    unsigned b126 = arena[args->base_params + 1u];
    unsigned b127 = stwo_m31_add(b5, b126);
    unsigned b128 = stwo_m31_add(b127, b7);
    unsigned b129 = arena[args->base_params + 2u];
    unsigned b130 = stwo_m31_add(b128, b129);
    unsigned b131 = stwo_m31_sub(b6, b130);
    unsigned b132 = stwo_m31_mul(b1, b131);
    unsigned b133 = stwo_m31_mul(b113, b132);
    unsigned b134 = stwo_m31_sub(b1, b2);
    unsigned b135 = stwo_m31_mul(b49, b134);
    unsigned b136 = stwo_m31_add(b6, b126);
    unsigned b137 = stwo_m31_add(b136, b8);
    unsigned b138 = stwo_m31_add(b137, b129);
    unsigned b139 = arena[args->base_params + 3u];
    unsigned b140 = stwo_m31_sub(b138, b139);
    unsigned b141 = stwo_m31_mul(b135, b140);
    unsigned b142 = stwo_m31_sub(b110, b1);
    unsigned b143 = stwo_m31_sub(b139, b110);
    unsigned b144 = stwo_m31_mul(b142, b143);
    unsigned b145 = stwo_m31_mul(b48, b144);
    unsigned b146 = arena[args->base_params + 4u];
    unsigned b147 = stwo_m31_mul(b146, b25);
    unsigned b148 = stwo_m31_add(b24, b147);
    unsigned b149 = stwo_m31_sub(b8, b148);
    unsigned b150 = stwo_m31_mul(b1, b149);
    unsigned b151 = stwo_m31_sub(b30, b110);
    unsigned b152 = stwo_m31_mul(b30, b151);
    unsigned b153 = arena[args->base_params + 5u];
    unsigned b154 = stwo_m31_sub(b26, b153);
    unsigned b155 = stwo_m31_mul(b30, b154);
    unsigned b156 = stwo_m31_sub(b110, b30);
    unsigned b157 = stwo_m31_mul(b154, b31);
    unsigned b158 = stwo_m31_sub(b157, b110);
    unsigned b159 = stwo_m31_mul(b156, b158);
    unsigned b160 = stwo_m31_sub(b32, b110);
    unsigned b161 = stwo_m31_mul(b32, b160);
    unsigned b162 = arena[args->base_params + 6u];
    unsigned b163 = stwo_m31_sub(b26, b162);
    unsigned b164 = stwo_m31_mul(b32, b163);
    unsigned b165 = stwo_m31_sub(b110, b32);
    unsigned b166 = stwo_m31_mul(b163, b33);
    unsigned b167 = stwo_m31_sub(b166, b110);
    unsigned b168 = stwo_m31_mul(b165, b167);
    unsigned b169 = stwo_m31_sub(b34, b110);
    unsigned b170 = stwo_m31_mul(b34, b169);
    unsigned b171 = arena[args->base_params + 7u];
    unsigned b172 = stwo_m31_sub(b26, b171);
    unsigned b173 = stwo_m31_mul(b34, b172);
    unsigned b174 = stwo_m31_sub(b110, b34);
    unsigned b175 = stwo_m31_mul(b172, b35);
    unsigned b176 = stwo_m31_sub(b175, b110);
    unsigned b177 = stwo_m31_mul(b174, b176);
    unsigned b178 = stwo_m31_sub(b36, b110);
    unsigned b179 = stwo_m31_mul(b36, b178);
    unsigned b180 = arena[args->base_params + 8u];
    unsigned b181 = stwo_m31_mul(b180, b32);
    unsigned b182 = stwo_m31_sub(b27, b181);
    unsigned b183 = arena[args->base_params + 9u];
    unsigned b184 = stwo_m31_add(b30, b32);
    unsigned b185 = stwo_m31_mul(b183, b184);
    unsigned b186 = stwo_m31_sub(b28, b185);
    unsigned b187 = arena[args->base_params + 10u];
    unsigned b188 = stwo_m31_mul(b187, b34);
    unsigned b189 = stwo_m31_sub(b186, b188);
    unsigned b190 = stwo_m31_mul(b146, b189);
    unsigned b191 = stwo_m31_add(b182, b190);
    unsigned b192 = stwo_m31_mul(b36, b191);
    unsigned b193 = stwo_m31_sub(b110, b36);
    unsigned b194 = stwo_m31_mul(b191, b37);
    unsigned b195 = stwo_m31_sub(b194, b110);
    unsigned b196 = stwo_m31_mul(b193, b195);
    unsigned b197 = stwo_m31_mul(b32, b36);
    unsigned b198 = stwo_m31_sub(b38, b197);
    unsigned b199 = stwo_m31_sub(b39, b110);
    unsigned b200 = stwo_m31_mul(b39, b199);
    unsigned b201 = arena[args->base_params + 11u];
    unsigned b202 = stwo_m31_sub(b29, b201);
    unsigned b203 = stwo_m31_mul(b39, b202);
    unsigned b204 = stwo_m31_sub(b110, b39);
    unsigned b205 = stwo_m31_mul(b202, b40);
    unsigned b206 = stwo_m31_sub(b205, b110);
    unsigned b207 = stwo_m31_mul(b204, b206);
    unsigned b208 = stwo_m31_mul(b38, b39);
    unsigned b209 = stwo_m31_sub(b41, b208);
    unsigned b210 = stwo_m31_mul(b30, b36);
    unsigned b211 = stwo_m31_sub(b42, b210);
    unsigned b212 = stwo_m31_mul(b34, b36);
    unsigned b213 = stwo_m31_sub(b43, b212);
    unsigned b214 = stwo_m31_neg(b48);
    unsigned b215 = arena[args->base_params + 12u];
    unsigned b216 = stwo_m31_neg(b1);
    unsigned b217 = stwo_m31_add(b6, b215);
    unsigned b218 = stwo_m31_add(b6, b110);
    unsigned b219 = arena[args->base_params + 13u];
    unsigned b220 = stwo_m31_add(b6, b219);
    unsigned b221 = arena[args->base_params + 14u];
    unsigned b222 = stwo_m31_add(b6, b221);
    unsigned b223 = arena[args->base_params + 15u];
    unsigned b224 = stwo_m31_add(b6, b223);
    unsigned b225 = arena[args->base_params + 16u];
    unsigned b226 = stwo_m31_add(b6, b225);
    unsigned b227 = arena[args->base_params + 17u];
    unsigned b228 = stwo_m31_add(b6, b227);
    unsigned b229 = arena[args->base_params + 18u];
    unsigned b230 = stwo_m31_add(b6, b229);
    unsigned b231 = arena[args->base_params + 19u];
    unsigned b232 = stwo_m31_add(b6, b231);
    unsigned b233 = arena[args->base_params + 20u];
    unsigned b234 = stwo_m31_add(b6, b233);
    unsigned b235 = arena[args->base_params + 21u];
    unsigned b236 = stwo_m31_add(b6, b235);
    unsigned b237 = stwo_m31_add(b6, b129);
    unsigned b238 = arena[args->base_params + 22u];
    unsigned b239 = stwo_m31_add(b6, b238);
    unsigned b240 = arena[args->base_params + 23u];
    unsigned b241 = stwo_m31_add(b6, b240);
    unsigned b242 = arena[args->base_params + 24u];
    unsigned b243 = stwo_m31_add(b6, b242);
    unsigned b244 = arena[args->base_params + 25u];
    unsigned b245 = stwo_m31_add(b6, b244);
    unsigned b246 = stwo_m31_mul(b146, b10);
    unsigned b247 = stwo_m31_add(b9, b246);
    unsigned b248 = stwo_m31_mul(b146, b12);
    unsigned b249 = stwo_m31_add(b11, b248);
    unsigned b250 = stwo_m31_mul(b146, b14);
    unsigned b251 = stwo_m31_add(b13, b250);
    unsigned b252 = arena[args->base_params + 26u];
    unsigned b253 = stwo_m31_mul(b252, b15);
    unsigned b254 = stwo_m31_add(b251, b253);
    unsigned b255 = stwo_m31_mul(b146, b17);
    unsigned b256 = stwo_m31_add(b16, b255);
    unsigned b257 = stwo_m31_mul(b252, b18);
    unsigned b258 = stwo_m31_add(b256, b257);
    unsigned b259 = arena[args->base_params + 27u];
    unsigned b260 = stwo_m31_mul(b259, b19);
    unsigned b261 = stwo_m31_add(b258, b260);
    unsigned b262 = stwo_m31_mul(b146, b22);
    unsigned b263 = stwo_m31_add(b21, b262);
    unsigned b264 = stwo_m31_mul(b252, b23);
    unsigned b265 = stwo_m31_add(b263, b264);
    unsigned b266 = stwo_m31_mul(b146, b45);
    unsigned b267 = stwo_m31_add(b44, b266);
    unsigned b268 = stwo_m31_mul(b146, b47);
    unsigned b269 = stwo_m31_add(b46, b268);
    unsigned b270 = arena[args->base_params + 28u];
    unsigned b271 = stwo_m31_add(b6, b270);
    unsigned b272 = stwo_m31_add(b32, b34);
    unsigned b273 = stwo_m31_add(b30, b272);
    unsigned b274 = stwo_m31_mul(b1, b273);
    unsigned b275 = stwo_m31_neg(b274);
    unsigned b276 = arena[args->base_params + 29u];
    unsigned b277 = stwo_m31_add(b6, b276);
    unsigned b278 = arena[args->base_params + 30u];
    unsigned b279 = stwo_m31_add(b6, b278);
    unsigned b280 = stwo_m31_mul(b1, b38);
    unsigned b281 = stwo_m31_neg(b280);
    unsigned b282 = arena[args->base_params + 31u];
    unsigned b283 = stwo_m31_add(b6, b282);
    unsigned b284 = stwo_m31_add(b224, b8);
    unsigned b285 = stwo_m31_add(b226, b8);
    unsigned b286 = stwo_m31_add(b228, b8);
    StwoCairoQm31 e0 = { b112, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b116, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b118, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b119, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b123, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b125, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b133, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b141, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b145, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b150, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b152, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b155, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b159, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b161, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b164, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b168, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b170, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b173, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b177, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b179, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b192, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b196, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b198, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b200, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b203, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b207, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b209, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b211, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b213, b215, b215, b215 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e30 = stwo_load_qm31(arena, args->ext_params + 12u * 4u);
    StwoCairoQm31 e31 = { b214, b215, b215, b215 };
    StwoCairoQm31 e32 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e33 = { b215, b215, b215, b215 };
    StwoCairoQm31 e34 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e35 = stwo_qm31_mul(e33, e34);
    StwoCairoQm31 e36 = stwo_qm31_add(e32, e35);
    StwoCairoQm31 e37 = { b110, b215, b215, b215 };
    StwoCairoQm31 e38 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e39 = stwo_qm31_mul(e37, e38);
    StwoCairoQm31 e40 = stwo_qm31_add(e36, e39);
    StwoCairoQm31 e41 = stwo_qm31_sub(e40, e29);
    StwoCairoQm31 e42 = { b216, b215, b215, b215 };
    StwoCairoQm31 e43 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e44 = { b217, b215, b215, b215 };
    StwoCairoQm31 e45 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e46 = stwo_qm31_mul(e44, e45);
    StwoCairoQm31 e47 = stwo_qm31_add(e43, e46);
    StwoCairoQm31 e48 = { b9, b215, b215, b215 };
    StwoCairoQm31 e49 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e50 = stwo_qm31_mul(e48, e49);
    StwoCairoQm31 e51 = stwo_qm31_add(e47, e50);
    StwoCairoQm31 e52 = stwo_qm31_sub(e51, e29);
    StwoCairoQm31 e53 = { b216, b215, b215, b215 };
    StwoCairoQm31 e54 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e55 = { b218, b215, b215, b215 };
    StwoCairoQm31 e56 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e57 = stwo_qm31_mul(e55, e56);
    StwoCairoQm31 e58 = stwo_qm31_add(e54, e57);
    StwoCairoQm31 e59 = { b10, b215, b215, b215 };
    StwoCairoQm31 e60 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e61 = stwo_qm31_mul(e59, e60);
    StwoCairoQm31 e62 = stwo_qm31_add(e58, e61);
    StwoCairoQm31 e63 = stwo_qm31_sub(e62, e29);
    StwoCairoQm31 e64 = { b216, b215, b215, b215 };
    StwoCairoQm31 e65 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e66 = { b220, b215, b215, b215 };
    StwoCairoQm31 e67 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e68 = stwo_qm31_mul(e66, e67);
    StwoCairoQm31 e69 = stwo_qm31_add(e65, e68);
    StwoCairoQm31 e70 = { b11, b215, b215, b215 };
    StwoCairoQm31 e71 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e72 = stwo_qm31_mul(e70, e71);
    StwoCairoQm31 e73 = stwo_qm31_add(e69, e72);
    StwoCairoQm31 e74 = stwo_qm31_sub(e73, e29);
    StwoCairoQm31 e75 = { b216, b215, b215, b215 };
    StwoCairoQm31 e76 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e77 = { b222, b215, b215, b215 };
    StwoCairoQm31 e78 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e79 = stwo_qm31_mul(e77, e78);
    StwoCairoQm31 e80 = stwo_qm31_add(e76, e79);
    StwoCairoQm31 e81 = { b12, b215, b215, b215 };
    StwoCairoQm31 e82 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e83 = stwo_qm31_mul(e81, e82);
    StwoCairoQm31 e84 = stwo_qm31_add(e80, e83);
    StwoCairoQm31 e85 = stwo_qm31_sub(e84, e29);
    StwoCairoQm31 e86 = { b216, b215, b215, b215 };
    StwoCairoQm31 e87 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e88 = { b136, b215, b215, b215 };
    StwoCairoQm31 e89 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e90 = stwo_qm31_mul(e88, e89);
    StwoCairoQm31 e91 = stwo_qm31_add(e87, e90);
    StwoCairoQm31 e92 = { b13, b215, b215, b215 };
    StwoCairoQm31 e93 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e94 = stwo_qm31_mul(e92, e93);
    StwoCairoQm31 e95 = stwo_qm31_add(e91, e94);
    StwoCairoQm31 e96 = stwo_qm31_sub(e95, e29);
    StwoCairoQm31 e97 = { b216, b215, b215, b215 };
    StwoCairoQm31 e98 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e99 = { b224, b215, b215, b215 };
    StwoCairoQm31 e100 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e101 = stwo_qm31_mul(e99, e100);
    StwoCairoQm31 e102 = stwo_qm31_add(e98, e101);
    StwoCairoQm31 e103 = { b14, b215, b215, b215 };
    StwoCairoQm31 e104 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e105 = stwo_qm31_mul(e103, e104);
    StwoCairoQm31 e106 = stwo_qm31_add(e102, e105);
    StwoCairoQm31 e107 = stwo_qm31_sub(e106, e29);
    StwoCairoQm31 e108 = { b216, b215, b215, b215 };
    StwoCairoQm31 e109 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e110 = { b226, b215, b215, b215 };
    StwoCairoQm31 e111 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e112 = stwo_qm31_mul(e110, e111);
    StwoCairoQm31 e113 = stwo_qm31_add(e109, e112);
    StwoCairoQm31 e114 = { b15, b215, b215, b215 };
    StwoCairoQm31 e115 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e116 = stwo_qm31_mul(e114, e115);
    StwoCairoQm31 e117 = stwo_qm31_add(e113, e116);
    StwoCairoQm31 e118 = stwo_qm31_sub(e117, e29);
    StwoCairoQm31 e119 = { b216, b215, b215, b215 };
    StwoCairoQm31 e120 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e121 = { b228, b215, b215, b215 };
    StwoCairoQm31 e122 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e123 = stwo_qm31_mul(e121, e122);
    StwoCairoQm31 e124 = stwo_qm31_add(e120, e123);
    StwoCairoQm31 e125 = { b16, b215, b215, b215 };
    StwoCairoQm31 e126 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e127 = stwo_qm31_mul(e125, e126);
    StwoCairoQm31 e128 = stwo_qm31_add(e124, e127);
    StwoCairoQm31 e129 = stwo_qm31_sub(e128, e29);
    StwoCairoQm31 e130 = { b216, b215, b215, b215 };
    StwoCairoQm31 e131 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e132 = { b230, b215, b215, b215 };
    StwoCairoQm31 e133 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e134 = stwo_qm31_mul(e132, e133);
    StwoCairoQm31 e135 = stwo_qm31_add(e131, e134);
    StwoCairoQm31 e136 = { b17, b215, b215, b215 };
    StwoCairoQm31 e137 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e138 = stwo_qm31_mul(e136, e137);
    StwoCairoQm31 e139 = stwo_qm31_add(e135, e138);
    StwoCairoQm31 e140 = stwo_qm31_sub(e139, e29);
    StwoCairoQm31 e141 = { b216, b215, b215, b215 };
    StwoCairoQm31 e142 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e143 = { b232, b215, b215, b215 };
    StwoCairoQm31 e144 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e145 = stwo_qm31_mul(e143, e144);
    StwoCairoQm31 e146 = stwo_qm31_add(e142, e145);
    StwoCairoQm31 e147 = { b18, b215, b215, b215 };
    StwoCairoQm31 e148 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e149 = stwo_qm31_mul(e147, e148);
    StwoCairoQm31 e150 = stwo_qm31_add(e146, e149);
    StwoCairoQm31 e151 = stwo_qm31_sub(e150, e29);
    StwoCairoQm31 e152 = { b216, b215, b215, b215 };
    StwoCairoQm31 e153 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e154 = { b234, b215, b215, b215 };
    StwoCairoQm31 e155 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e156 = stwo_qm31_mul(e154, e155);
    StwoCairoQm31 e157 = stwo_qm31_add(e153, e156);
    StwoCairoQm31 e158 = { b19, b215, b215, b215 };
    StwoCairoQm31 e159 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e160 = stwo_qm31_mul(e158, e159);
    StwoCairoQm31 e161 = stwo_qm31_add(e157, e160);
    StwoCairoQm31 e162 = stwo_qm31_sub(e161, e29);
    StwoCairoQm31 e163 = { b216, b215, b215, b215 };
    StwoCairoQm31 e164 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e165 = { b236, b215, b215, b215 };
    StwoCairoQm31 e166 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e167 = stwo_qm31_mul(e165, e166);
    StwoCairoQm31 e168 = stwo_qm31_add(e164, e167);
    StwoCairoQm31 e169 = { b20, b215, b215, b215 };
    StwoCairoQm31 e170 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e171 = stwo_qm31_mul(e169, e170);
    StwoCairoQm31 e172 = stwo_qm31_add(e168, e171);
    StwoCairoQm31 e173 = stwo_qm31_sub(e172, e29);
    StwoCairoQm31 e174 = { b216, b215, b215, b215 };
    StwoCairoQm31 e175 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e176 = { b237, b215, b215, b215 };
    StwoCairoQm31 e177 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e178 = stwo_qm31_mul(e176, e177);
    StwoCairoQm31 e179 = stwo_qm31_add(e175, e178);
    StwoCairoQm31 e180 = { b21, b215, b215, b215 };
    StwoCairoQm31 e181 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e182 = stwo_qm31_mul(e180, e181);
    StwoCairoQm31 e183 = stwo_qm31_add(e179, e182);
    StwoCairoQm31 e184 = stwo_qm31_sub(e183, e29);
    StwoCairoQm31 e185 = { b216, b215, b215, b215 };
    StwoCairoQm31 e186 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e187 = { b239, b215, b215, b215 };
    StwoCairoQm31 e188 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e189 = stwo_qm31_mul(e187, e188);
    StwoCairoQm31 e190 = stwo_qm31_add(e186, e189);
    StwoCairoQm31 e191 = { b22, b215, b215, b215 };
    StwoCairoQm31 e192 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e193 = stwo_qm31_mul(e191, e192);
    StwoCairoQm31 e194 = stwo_qm31_add(e190, e193);
    StwoCairoQm31 e195 = stwo_qm31_sub(e194, e29);
    StwoCairoQm31 e196 = { b216, b215, b215, b215 };
    StwoCairoQm31 e197 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e198 = { b241, b215, b215, b215 };
    StwoCairoQm31 e199 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e200 = stwo_qm31_mul(e198, e199);
    StwoCairoQm31 e201 = stwo_qm31_add(e197, e200);
    StwoCairoQm31 e202 = { b23, b215, b215, b215 };
    StwoCairoQm31 e203 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e204 = stwo_qm31_mul(e202, e203);
    StwoCairoQm31 e205 = stwo_qm31_add(e201, e204);
    StwoCairoQm31 e206 = stwo_qm31_sub(e205, e29);
    StwoCairoQm31 e207 = { b216, b215, b215, b215 };
    StwoCairoQm31 e208 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e209 = { b243, b215, b215, b215 };
    StwoCairoQm31 e210 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e211 = stwo_qm31_mul(e209, e210);
    StwoCairoQm31 e212 = stwo_qm31_add(e208, e211);
    StwoCairoQm31 e213 = { b24, b215, b215, b215 };
    StwoCairoQm31 e214 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e215 = stwo_qm31_mul(e213, e214);
    StwoCairoQm31 e216 = stwo_qm31_add(e212, e215);
    StwoCairoQm31 e217 = stwo_qm31_sub(e216, e29);
    StwoCairoQm31 e218 = { b216, b215, b215, b215 };
    StwoCairoQm31 e219 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e220 = { b245, b215, b215, b215 };
    StwoCairoQm31 e221 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e222 = stwo_qm31_mul(e220, e221);
    StwoCairoQm31 e223 = stwo_qm31_add(e219, e222);
    StwoCairoQm31 e224 = { b25, b215, b215, b215 };
    StwoCairoQm31 e225 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e226 = stwo_qm31_mul(e224, e225);
    StwoCairoQm31 e227 = stwo_qm31_add(e223, e226);
    StwoCairoQm31 e228 = stwo_qm31_sub(e227, e29);
    StwoCairoQm31 e229 = { b1, b215, b215, b215 };
    StwoCairoQm31 e230 = { 21u, 0u, 0u, 0u };
    StwoCairoQm31 e231 = { b110, b215, b215, b215 };
    StwoCairoQm31 e232 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e233 = stwo_qm31_mul(e231, e232);
    StwoCairoQm31 e234 = stwo_qm31_add(e230, e233);
    StwoCairoQm31 e235 = { b4, b215, b215, b215 };
    StwoCairoQm31 e236 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e237 = stwo_qm31_mul(e235, e236);
    StwoCairoQm31 e238 = stwo_qm31_add(e234, e237);
    StwoCairoQm31 e239 = { b136, b215, b215, b215 };
    StwoCairoQm31 e240 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e241 = stwo_qm31_mul(e239, e240);
    StwoCairoQm31 e242 = stwo_qm31_add(e238, e241);
    StwoCairoQm31 e243 = { b8, b215, b215, b215 };
    StwoCairoQm31 e244 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e245 = stwo_qm31_mul(e243, e244);
    StwoCairoQm31 e246 = stwo_qm31_add(e242, e245);
    StwoCairoQm31 e247 = stwo_qm31_sub(e246, e29);
    StwoCairoQm31 e248 = { b1, b215, b215, b215 };
    StwoCairoQm31 e249 = { 23u, 0u, 0u, 0u };
    StwoCairoQm31 e250 = { b4, b215, b215, b215 };
    StwoCairoQm31 e251 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e252 = stwo_qm31_mul(e250, e251);
    StwoCairoQm31 e253 = stwo_qm31_add(e249, e252);
    StwoCairoQm31 e254 = { b247, b215, b215, b215 };
    StwoCairoQm31 e255 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e256 = stwo_qm31_mul(e254, e255);
    StwoCairoQm31 e257 = stwo_qm31_add(e253, e256);
    StwoCairoQm31 e258 = { b249, b215, b215, b215 };
    StwoCairoQm31 e259 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e260 = stwo_qm31_mul(e258, e259);
    StwoCairoQm31 e261 = stwo_qm31_add(e257, e260);
    StwoCairoQm31 e262 = { b254, b215, b215, b215 };
    StwoCairoQm31 e263 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e264 = stwo_qm31_mul(e262, e263);
    StwoCairoQm31 e265 = stwo_qm31_add(e261, e264);
    StwoCairoQm31 e266 = { b261, b215, b215, b215 };
    StwoCairoQm31 e267 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e268 = stwo_qm31_mul(e266, e267);
    StwoCairoQm31 e269 = stwo_qm31_add(e265, e268);
    StwoCairoQm31 e270 = { b265, b215, b215, b215 };
    StwoCairoQm31 e271 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e272 = stwo_qm31_mul(e270, e271);
    StwoCairoQm31 e273 = stwo_qm31_add(e269, e272);
    StwoCairoQm31 e274 = { b41, b215, b215, b215 };
    StwoCairoQm31 e275 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e276 = stwo_qm31_mul(e274, e275);
    StwoCairoQm31 e277 = stwo_qm31_add(e273, e276);
    StwoCairoQm31 e278 = { b42, b215, b215, b215 };
    StwoCairoQm31 e279 = stwo_load_qm31(arena, args->ext_params + 8u * 4u);
    StwoCairoQm31 e280 = stwo_qm31_mul(e278, e279);
    StwoCairoQm31 e281 = stwo_qm31_add(e277, e280);
    StwoCairoQm31 e282 = { b43, b215, b215, b215 };
    StwoCairoQm31 e283 = stwo_load_qm31(arena, args->ext_params + 9u * 4u);
    StwoCairoQm31 e284 = stwo_qm31_mul(e282, e283);
    StwoCairoQm31 e285 = stwo_qm31_add(e281, e284);
    StwoCairoQm31 e286 = { b267, b215, b215, b215 };
    StwoCairoQm31 e287 = stwo_load_qm31(arena, args->ext_params + 10u * 4u);
    StwoCairoQm31 e288 = stwo_qm31_mul(e286, e287);
    StwoCairoQm31 e289 = stwo_qm31_add(e285, e288);
    StwoCairoQm31 e290 = { b269, b215, b215, b215 };
    StwoCairoQm31 e291 = stwo_load_qm31(arena, args->ext_params + 11u * 4u);
    StwoCairoQm31 e292 = stwo_qm31_mul(e290, e291);
    StwoCairoQm31 e293 = stwo_qm31_add(e289, e292);
    StwoCairoQm31 e294 = stwo_qm31_sub(e293, e29);
    StwoCairoQm31 e295 = { b216, b215, b215, b215 };
    StwoCairoQm31 e296 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e297 = { b271, b215, b215, b215 };
    StwoCairoQm31 e298 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e299 = stwo_qm31_mul(e297, e298);
    StwoCairoQm31 e300 = stwo_qm31_add(e296, e299);
    StwoCairoQm31 e301 = { b26, b215, b215, b215 };
    StwoCairoQm31 e302 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e303 = stwo_qm31_mul(e301, e302);
    StwoCairoQm31 e304 = stwo_qm31_add(e300, e303);
    StwoCairoQm31 e305 = stwo_qm31_sub(e304, e29);
    StwoCairoQm31 e306 = { b275, b215, b215, b215 };
    StwoCairoQm31 e307 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e308 = { b277, b215, b215, b215 };
    StwoCairoQm31 e309 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e310 = stwo_qm31_mul(e308, e309);
    StwoCairoQm31 e311 = stwo_qm31_add(e307, e310);
    StwoCairoQm31 e312 = { b27, b215, b215, b215 };
    StwoCairoQm31 e313 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e314 = stwo_qm31_mul(e312, e313);
    StwoCairoQm31 e315 = stwo_qm31_add(e311, e314);
    StwoCairoQm31 e316 = stwo_qm31_sub(e315, e29);
    StwoCairoQm31 e317 = { b275, b215, b215, b215 };
    StwoCairoQm31 e318 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e319 = { b279, b215, b215, b215 };
    StwoCairoQm31 e320 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e321 = stwo_qm31_mul(e319, e320);
    StwoCairoQm31 e322 = stwo_qm31_add(e318, e321);
    StwoCairoQm31 e323 = { b28, b215, b215, b215 };
    StwoCairoQm31 e324 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e325 = stwo_qm31_mul(e323, e324);
    StwoCairoQm31 e326 = stwo_qm31_add(e322, e325);
    StwoCairoQm31 e327 = stwo_qm31_sub(e326, e29);
    StwoCairoQm31 e328 = { b281, b215, b215, b215 };
    StwoCairoQm31 e329 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e330 = { b283, b215, b215, b215 };
    StwoCairoQm31 e331 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e332 = stwo_qm31_mul(e330, e331);
    StwoCairoQm31 e333 = stwo_qm31_add(e329, e332);
    StwoCairoQm31 e334 = { b29, b215, b215, b215 };
    StwoCairoQm31 e335 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e336 = stwo_qm31_mul(e334, e335);
    StwoCairoQm31 e337 = stwo_qm31_add(e333, e336);
    StwoCairoQm31 e338 = stwo_qm31_sub(e337, e29);
    StwoCairoQm31 e339 = { b216, b215, b215, b215 };
    StwoCairoQm31 e340 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e341 = { b137, b215, b215, b215 };
    StwoCairoQm31 e342 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e343 = stwo_qm31_mul(e341, e342);
    StwoCairoQm31 e344 = stwo_qm31_add(e340, e343);
    StwoCairoQm31 e345 = { b44, b215, b215, b215 };
    StwoCairoQm31 e346 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e347 = stwo_qm31_mul(e345, e346);
    StwoCairoQm31 e348 = stwo_qm31_add(e344, e347);
    StwoCairoQm31 e349 = stwo_qm31_sub(e348, e29);
    StwoCairoQm31 e350 = { b216, b215, b215, b215 };
    StwoCairoQm31 e351 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e352 = { b284, b215, b215, b215 };
    StwoCairoQm31 e353 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e354 = stwo_qm31_mul(e352, e353);
    StwoCairoQm31 e355 = stwo_qm31_add(e351, e354);
    StwoCairoQm31 e356 = { b45, b215, b215, b215 };
    StwoCairoQm31 e357 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e358 = stwo_qm31_mul(e356, e357);
    StwoCairoQm31 e359 = stwo_qm31_add(e355, e358);
    StwoCairoQm31 e360 = stwo_qm31_sub(e359, e29);
    StwoCairoQm31 e361 = { b216, b215, b215, b215 };
    StwoCairoQm31 e362 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e363 = { b285, b215, b215, b215 };
    StwoCairoQm31 e364 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e365 = stwo_qm31_mul(e363, e364);
    StwoCairoQm31 e366 = stwo_qm31_add(e362, e365);
    StwoCairoQm31 e367 = { b46, b215, b215, b215 };
    StwoCairoQm31 e368 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e369 = stwo_qm31_mul(e367, e368);
    StwoCairoQm31 e370 = stwo_qm31_add(e366, e369);
    StwoCairoQm31 e371 = stwo_qm31_sub(e370, e29);
    StwoCairoQm31 e372 = { b216, b215, b215, b215 };
    StwoCairoQm31 e373 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e374 = { b286, b215, b215, b215 };
    StwoCairoQm31 e375 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e376 = stwo_qm31_mul(e374, e375);
    StwoCairoQm31 e377 = stwo_qm31_add(e373, e376);
    StwoCairoQm31 e378 = { b47, b215, b215, b215 };
    StwoCairoQm31 e379 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e380 = stwo_qm31_mul(e378, e379);
    StwoCairoQm31 e381 = stwo_qm31_add(e377, e380);
    StwoCairoQm31 e382 = stwo_qm31_sub(e381, e29);
    StwoCairoQm31 e383 = { b50, b51, b52, b53 };
    StwoCairoQm31 e384 = { b54, b55, b56, b57 };
    StwoCairoQm31 e385 = { b58, b59, b60, b61 };
    StwoCairoQm31 e386 = { b62, b63, b64, b65 };
    StwoCairoQm31 e387 = { b66, b67, b68, b69 };
    StwoCairoQm31 e388 = { b70, b71, b72, b73 };
    StwoCairoQm31 e389 = { b74, b75, b76, b77 };
    StwoCairoQm31 e390 = { b78, b79, b80, b81 };
    StwoCairoQm31 e391 = { b82, b83, b84, b85 };
    StwoCairoQm31 e392 = { b86, b87, b88, b89 };
    StwoCairoQm31 e393 = { b90, b91, b92, b93 };
    StwoCairoQm31 e394 = { b94, b95, b96, b97 };
    StwoCairoQm31 e395 = { b98, b99, b100, b101 };
    StwoCairoQm31 e396 = { b103, b105, b107, b109 };
    StwoCairoQm31 e397 = { b102, b104, b106, b108 };
    StwoCairoQm31 e398 = stwo_qm31_mul(e31, e52);
    StwoCairoQm31 e399 = stwo_qm31_mul(e42, e41);
    StwoCairoQm31 e400 = stwo_qm31_add(e398, e399);
    StwoCairoQm31 e401 = stwo_qm31_mul(e41, e52);
    StwoCairoQm31 e402 = stwo_qm31_mul(e383, e401);
    StwoCairoQm31 e403 = stwo_qm31_sub(e402, e400);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e403, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e404 = stwo_qm31_mul(e53, e74);
    StwoCairoQm31 e405 = stwo_qm31_mul(e64, e63);
    StwoCairoQm31 e406 = stwo_qm31_add(e404, e405);
    StwoCairoQm31 e407 = stwo_qm31_mul(e63, e74);
    StwoCairoQm31 e408 = stwo_qm31_sub(e384, e383);
    StwoCairoQm31 e409 = stwo_qm31_mul(e408, e407);
    StwoCairoQm31 e410 = stwo_qm31_sub(e409, e406);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e410, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e411 = stwo_qm31_mul(e75, e96);
    StwoCairoQm31 e412 = stwo_qm31_mul(e86, e85);
    StwoCairoQm31 e413 = stwo_qm31_add(e411, e412);
    StwoCairoQm31 e414 = stwo_qm31_mul(e85, e96);
    StwoCairoQm31 e415 = stwo_qm31_sub(e385, e384);
    StwoCairoQm31 e416 = stwo_qm31_mul(e415, e414);
    StwoCairoQm31 e417 = stwo_qm31_sub(e416, e413);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e417, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e418 = stwo_qm31_mul(e97, e118);
    StwoCairoQm31 e419 = stwo_qm31_mul(e108, e107);
    StwoCairoQm31 e420 = stwo_qm31_add(e418, e419);
    StwoCairoQm31 e421 = stwo_qm31_mul(e107, e118);
    StwoCairoQm31 e422 = stwo_qm31_sub(e386, e385);
    StwoCairoQm31 e423 = stwo_qm31_mul(e422, e421);
    StwoCairoQm31 e424 = stwo_qm31_sub(e423, e420);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e424, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e425 = stwo_qm31_mul(e119, e140);
    StwoCairoQm31 e426 = stwo_qm31_mul(e130, e129);
    StwoCairoQm31 e427 = stwo_qm31_add(e425, e426);
    StwoCairoQm31 e428 = stwo_qm31_mul(e129, e140);
    StwoCairoQm31 e429 = stwo_qm31_sub(e387, e386);
    StwoCairoQm31 e430 = stwo_qm31_mul(e429, e428);
    StwoCairoQm31 e431 = stwo_qm31_sub(e430, e427);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e431, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e432 = stwo_qm31_mul(e141, e162);
    StwoCairoQm31 e433 = stwo_qm31_mul(e152, e151);
    StwoCairoQm31 e434 = stwo_qm31_add(e432, e433);
    StwoCairoQm31 e435 = stwo_qm31_mul(e151, e162);
    StwoCairoQm31 e436 = stwo_qm31_sub(e388, e387);
    StwoCairoQm31 e437 = stwo_qm31_mul(e436, e435);
    StwoCairoQm31 e438 = stwo_qm31_sub(e437, e434);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e438, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e439 = stwo_qm31_mul(e163, e184);
    StwoCairoQm31 e440 = stwo_qm31_mul(e174, e173);
    StwoCairoQm31 e441 = stwo_qm31_add(e439, e440);
    StwoCairoQm31 e442 = stwo_qm31_mul(e173, e184);
    StwoCairoQm31 e443 = stwo_qm31_sub(e389, e388);
    StwoCairoQm31 e444 = stwo_qm31_mul(e443, e442);
    StwoCairoQm31 e445 = stwo_qm31_sub(e444, e441);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e445, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e446 = stwo_qm31_mul(e185, e206);
    StwoCairoQm31 e447 = stwo_qm31_mul(e196, e195);
    StwoCairoQm31 e448 = stwo_qm31_add(e446, e447);
    StwoCairoQm31 e449 = stwo_qm31_mul(e195, e206);
    StwoCairoQm31 e450 = stwo_qm31_sub(e390, e389);
    StwoCairoQm31 e451 = stwo_qm31_mul(e450, e449);
    StwoCairoQm31 e452 = stwo_qm31_sub(e451, e448);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e452, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e453 = stwo_qm31_mul(e207, e228);
    StwoCairoQm31 e454 = stwo_qm31_mul(e218, e217);
    StwoCairoQm31 e455 = stwo_qm31_add(e453, e454);
    StwoCairoQm31 e456 = stwo_qm31_mul(e217, e228);
    StwoCairoQm31 e457 = stwo_qm31_sub(e391, e390);
    StwoCairoQm31 e458 = stwo_qm31_mul(e457, e456);
    StwoCairoQm31 e459 = stwo_qm31_sub(e458, e455);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e459, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e460 = stwo_qm31_mul(e229, e294);
    StwoCairoQm31 e461 = stwo_qm31_mul(e248, e247);
    StwoCairoQm31 e462 = stwo_qm31_add(e460, e461);
    StwoCairoQm31 e463 = stwo_qm31_mul(e247, e294);
    StwoCairoQm31 e464 = stwo_qm31_sub(e392, e391);
    StwoCairoQm31 e465 = stwo_qm31_mul(e464, e463);
    StwoCairoQm31 e466 = stwo_qm31_sub(e465, e462);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e466, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e467 = stwo_qm31_mul(e295, e316);
    StwoCairoQm31 e468 = stwo_qm31_mul(e306, e305);
    StwoCairoQm31 e469 = stwo_qm31_add(e467, e468);
    StwoCairoQm31 e470 = stwo_qm31_mul(e305, e316);
    StwoCairoQm31 e471 = stwo_qm31_sub(e393, e392);
    StwoCairoQm31 e472 = stwo_qm31_mul(e471, e470);
    StwoCairoQm31 e473 = stwo_qm31_sub(e472, e469);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e473, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e474 = stwo_qm31_mul(e317, e338);
    StwoCairoQm31 e475 = stwo_qm31_mul(e328, e327);
    StwoCairoQm31 e476 = stwo_qm31_add(e474, e475);
    StwoCairoQm31 e477 = stwo_qm31_mul(e327, e338);
    StwoCairoQm31 e478 = stwo_qm31_sub(e394, e393);
    StwoCairoQm31 e479 = stwo_qm31_mul(e478, e477);
    StwoCairoQm31 e480 = stwo_qm31_sub(e479, e476);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e480, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e481 = stwo_qm31_mul(e339, e360);
    StwoCairoQm31 e482 = stwo_qm31_mul(e350, e349);
    StwoCairoQm31 e483 = stwo_qm31_add(e481, e482);
    StwoCairoQm31 e484 = stwo_qm31_mul(e349, e360);
    StwoCairoQm31 e485 = stwo_qm31_sub(e395, e394);
    StwoCairoQm31 e486 = stwo_qm31_mul(e485, e484);
    StwoCairoQm31 e487 = stwo_qm31_sub(e486, e483);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e487, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e488 = stwo_qm31_mul(e361, e382);
    StwoCairoQm31 e489 = stwo_qm31_mul(e372, e371);
    StwoCairoQm31 e490 = stwo_qm31_add(e488, e489);
    StwoCairoQm31 e491 = stwo_qm31_mul(e371, e382);
    StwoCairoQm31 e492 = stwo_qm31_sub(e396, e397);
    StwoCairoQm31 e493 = stwo_qm31_sub(e492, e395);
    StwoCairoQm31 e494 = stwo_qm31_add(e493, e30);
    StwoCairoQm31 e495 = stwo_qm31_mul(e494, e491);
    StwoCairoQm31 e496 = stwo_qm31_sub(e495, e490);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e496, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
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
