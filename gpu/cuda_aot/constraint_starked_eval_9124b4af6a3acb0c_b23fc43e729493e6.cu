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
stwo_cairo_cuda_eval_v6_9124b4af6a3acb0c(
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
    unsigned b3 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b4 = stwo_trace_value(arena, *args, 1u, 3u, row, -1);
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 5u, row, -1);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 6u, row, -1);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 7u, row, -1);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 9u, row, -1);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 18u, row, -1);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 21u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 1u, 22u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 1u, 23u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 1u, 24u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 1u, 25u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 1u, 26u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 1u, 27u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 1u, 28u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 1u, 29u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 1u, 30u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 1u, 31u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 1u, 32u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 1u, 33u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 1u, 34u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 1u, 35u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 1u, 36u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 1u, 37u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 1u, 38u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 1u, 39u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 1u, 40u, row, 0);
    unsigned b51 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b58 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b60 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b61 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b62 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b63 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b65 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b67 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b68 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b69 = stwo_trace_value(arena, *args, 2u, 16u, row, 0);
    unsigned b70 = stwo_trace_value(arena, *args, 2u, 17u, row, 0);
    unsigned b71 = stwo_trace_value(arena, *args, 2u, 18u, row, 0);
    unsigned b72 = stwo_trace_value(arena, *args, 2u, 19u, row, 0);
    unsigned b73 = stwo_trace_value(arena, *args, 2u, 20u, row, -1);
    unsigned b74 = stwo_trace_value(arena, *args, 2u, 20u, row, 0);
    unsigned b75 = stwo_trace_value(arena, *args, 2u, 21u, row, -1);
    unsigned b76 = stwo_trace_value(arena, *args, 2u, 21u, row, 0);
    unsigned b77 = stwo_trace_value(arena, *args, 2u, 22u, row, -1);
    unsigned b78 = stwo_trace_value(arena, *args, 2u, 22u, row, 0);
    unsigned b79 = stwo_trace_value(arena, *args, 2u, 23u, row, -1);
    unsigned b80 = stwo_trace_value(arena, *args, 2u, 23u, row, 0);
    unsigned b81 = arena[args->base_params + 0u];
    unsigned b82 = stwo_m31_sub(b1, b81);
    unsigned b83 = stwo_m31_mul(b1, b82);
    unsigned b84 = stwo_m31_sub(b2, b81);
    unsigned b85 = stwo_m31_mul(b2, b84);
    unsigned b86 = stwo_m31_sub(b3, b81);
    unsigned b87 = stwo_m31_mul(b3, b86);
    unsigned b88 = stwo_m31_sub(b13, b81);
    unsigned b89 = stwo_m31_mul(b13, b88);
    unsigned b90 = stwo_m31_sub(b19, b81);
    unsigned b91 = stwo_m31_mul(b19, b90);
    unsigned b92 = stwo_m31_mul(b1, b2);
    unsigned b93 = stwo_m31_add(b1, b2);
    unsigned b94 = stwo_m31_sub(b93, b81);
    unsigned b95 = stwo_m31_mul(b51, b94);
    unsigned b96 = stwo_m31_sub(b81, b51);
    unsigned b97 = stwo_m31_sub(b81, b27);
    unsigned b98 = stwo_m31_mul(b0, b97);
    unsigned b99 = stwo_m31_sub(b1, b98);
    unsigned b100 = stwo_m31_mul(b96, b99);
    unsigned b101 = stwo_m31_mul(b0, b27);
    unsigned b102 = stwo_m31_sub(b2, b101);
    unsigned b103 = stwo_m31_mul(b96, b102);
    unsigned b104 = arena[args->base_params + 1u];
    unsigned b105 = stwo_m31_sub(b104, b81);
    unsigned b106 = stwo_m31_mul(b2, b105);
    unsigned b107 = stwo_m31_mul(b51, b106);
    unsigned b108 = stwo_m31_sub(b81, b52);
    unsigned b109 = stwo_m31_mul(b108, b1);
    unsigned b110 = stwo_m31_sub(b8, b10);
    unsigned b111 = stwo_m31_add(b110, b81);
    unsigned b112 = stwo_m31_mul(b5, b111);
    unsigned b113 = stwo_m31_sub(b81, b5);
    unsigned b114 = stwo_m31_mul(b111, b6);
    unsigned b115 = stwo_m31_sub(b114, b81);
    unsigned b116 = stwo_m31_mul(b113, b115);
    unsigned b117 = stwo_m31_sub(b10, b81);
    unsigned b118 = stwo_m31_mul(b25, b117);
    unsigned b119 = stwo_m31_sub(b81, b25);
    unsigned b120 = stwo_m31_mul(b117, b26);
    unsigned b121 = stwo_m31_sub(b120, b81);
    unsigned b122 = stwo_m31_mul(b119, b121);
    unsigned b123 = stwo_m31_mul(b5, b25);
    unsigned b124 = stwo_m31_sub(b28, b123);
    unsigned b125 = stwo_m31_sub(b12, b81);
    unsigned b126 = stwo_m31_mul(b125, b29);
    unsigned b127 = stwo_m31_sub(b126, b81);
    unsigned b128 = stwo_m31_mul(b1, b127);
    unsigned b129 = arena[args->base_params + 2u];
    unsigned b130 = stwo_m31_mul(b129, b10);
    unsigned b131 = stwo_m31_add(b12, b13);
    unsigned b132 = stwo_m31_sub(b130, b131);
    unsigned b133 = stwo_m31_mul(b1, b132);
    unsigned b134 = stwo_m31_mul(b51, b21);
    unsigned b135 = stwo_m31_mul(b51, b86);
    unsigned b136 = stwo_m31_mul(b51, b90);
    unsigned b137 = stwo_m31_mul(b51, b15);
    unsigned b138 = stwo_m31_sub(b12, b104);
    unsigned b139 = stwo_m31_mul(b51, b138);
    unsigned b140 = stwo_m31_sub(b21, b20);
    unsigned b141 = stwo_m31_sub(b140, b81);
    unsigned b142 = stwo_m31_mul(b96, b141);
    unsigned b143 = stwo_m31_sub(b3, b4);
    unsigned b144 = stwo_m31_mul(b1, b143);
    unsigned b145 = stwo_m31_mul(b96, b144);
    unsigned b146 = stwo_m31_mul(b3, b8);
    unsigned b147 = stwo_m31_sub(b81, b3);
    unsigned b148 = stwo_m31_mul(b1, b147);
    unsigned b149 = stwo_m31_sub(b33, b148);
    unsigned b150 = stwo_m31_mul(b1, b3);
    unsigned b151 = stwo_m31_sub(b34, b150);
    unsigned b152 = stwo_m31_sub(b8, b7);
    unsigned b153 = stwo_m31_sub(b152, b81);
    unsigned b154 = stwo_m31_mul(b33, b153);
    unsigned b155 = stwo_m31_sub(b10, b9);
    unsigned b156 = stwo_m31_mul(b33, b155);
    unsigned b157 = stwo_m31_sub(b12, b11);
    unsigned b158 = stwo_m31_mul(b33, b157);
    unsigned b159 = stwo_m31_sub(b15, b14);
    unsigned b160 = stwo_m31_mul(b33, b159);
    unsigned b161 = stwo_m31_sub(b17, b16);
    unsigned b162 = stwo_m31_mul(b33, b161);
    unsigned b163 = stwo_m31_sub(b19, b18);
    unsigned b164 = stwo_m31_mul(b33, b163);
    unsigned b165 = stwo_m31_sub(b12, b9);
    unsigned b166 = stwo_m31_mul(b34, b165);
    unsigned b167 = stwo_m31_mul(b96, b166);
    unsigned b168 = stwo_m31_sub(b15, b21);
    unsigned b169 = stwo_m31_mul(b34, b168);
    unsigned b170 = stwo_m31_mul(b96, b169);
    unsigned b171 = stwo_m31_sub(b17, b14);
    unsigned b172 = stwo_m31_mul(b34, b171);
    unsigned b173 = stwo_m31_mul(b96, b172);
    unsigned b174 = stwo_m31_mul(b34, b19);
    unsigned b175 = stwo_m31_mul(b96, b174);
    unsigned b176 = stwo_m31_mul(b13, b5);
    unsigned b177 = stwo_m31_sub(b24, b176);
    unsigned b178 = arena[args->base_params + 3u];
    unsigned b179 = stwo_m31_mul(b178, b8);
    unsigned b180 = stwo_m31_add(b179, b81);
    unsigned b181 = stwo_m31_mul(b19, b180);
    unsigned b182 = stwo_m31_sub(b81, b19);
    unsigned b183 = arena[args->base_params + 4u];
    unsigned b184 = stwo_m31_add(b183, b17);
    unsigned b185 = stwo_m31_mul(b129, b8);
    unsigned b186 = stwo_m31_add(b184, b185);
    unsigned b187 = stwo_m31_mul(b182, b186);
    unsigned b188 = stwo_m31_add(b181, b187);
    unsigned b189 = stwo_m31_sub(b22, b188);
    unsigned b190 = stwo_m31_sub(b81, b24);
    unsigned b191 = stwo_m31_add(b19, b81);
    unsigned b192 = stwo_m31_mul(b190, b191);
    unsigned b193 = stwo_m31_add(b22, b192);
    unsigned b194 = stwo_m31_sub(b23, b193);
    unsigned b195 = stwo_m31_add(b32, b81);
    unsigned b196 = stwo_m31_add(b183, b21);
    unsigned b197 = stwo_m31_sub(b195, b196);
    unsigned b198 = stwo_m31_mul(b2, b197);
    unsigned b199 = stwo_m31_mul(b96, b198);
    unsigned b200 = stwo_m31_sub(b32, b81);
    unsigned b201 = stwo_m31_mul(b2, b200);
    unsigned b202 = stwo_m31_mul(b51, b201);
    unsigned b203 = stwo_m31_mul(b1, b30);
    unsigned b204 = stwo_m31_mul(b1, b31);
    unsigned b205 = arena[args->base_params + 5u];
    unsigned b206 = stwo_m31_neg(b2);
    unsigned b207 = arena[args->base_params + 6u];
    unsigned b208 = arena[args->base_params + 7u];
    unsigned b209 = arena[args->base_params + 8u];
    unsigned b210 = arena[args->base_params + 9u];
    unsigned b211 = arena[args->base_params + 10u];
    unsigned b212 = arena[args->base_params + 11u];
    unsigned b213 = arena[args->base_params + 12u];
    unsigned b214 = arena[args->base_params + 13u];
    unsigned b215 = arena[args->base_params + 14u];
    StwoCairoQm31 e0 = { b83, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b85, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b87, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b89, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b91, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b92, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b95, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b100, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b103, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b107, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b109, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b112, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b116, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b118, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b122, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b124, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b128, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b133, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b134, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b135, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b136, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b137, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b139, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b142, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b145, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b146, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b149, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b151, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b154, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b156, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b158, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b160, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b162, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b164, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b167, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b170, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b173, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b175, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b177, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b189, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b194, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b199, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b202, b207, b207, b207 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e44 = stwo_load_qm31(arena, args->ext_params + 18u * 4u);
    StwoCairoQm31 e45 = { b203, b207, b207, b207 };
    StwoCairoQm31 e46 = { 8u, 0u, 0u, 0u };
    StwoCairoQm31 e47 = { b196, b207, b207, b207 };
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e49 = stwo_qm31_mul(e47, e48);
    StwoCairoQm31 e50 = stwo_qm31_add(e46, e49);
    StwoCairoQm31 e51 = { b22, b207, b207, b207 };
    StwoCairoQm31 e52 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e53 = stwo_qm31_mul(e51, e52);
    StwoCairoQm31 e54 = stwo_qm31_add(e50, e53);
    StwoCairoQm31 e55 = { b23, b207, b207, b207 };
    StwoCairoQm31 e56 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e57 = stwo_qm31_mul(e55, e56);
    StwoCairoQm31 e58 = stwo_qm31_add(e54, e57);
    StwoCairoQm31 e59 = { b24, b207, b207, b207 };
    StwoCairoQm31 e60 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e61 = stwo_qm31_mul(e59, e60);
    StwoCairoQm31 e62 = stwo_qm31_add(e58, e61);
    StwoCairoQm31 e63 = stwo_qm31_sub(e62, e43);
    StwoCairoQm31 e64 = { b204, b207, b207, b207 };
    StwoCairoQm31 e65 = { 6u, 0u, 0u, 0u };
    StwoCairoQm31 e66 = { b196, b207, b207, b207 };
    StwoCairoQm31 e67 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e68 = stwo_qm31_mul(e66, e67);
    StwoCairoQm31 e69 = stwo_qm31_add(e65, e68);
    StwoCairoQm31 e70 = { b205, b207, b207, b207 };
    StwoCairoQm31 e71 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e72 = stwo_qm31_mul(e70, e71);
    StwoCairoQm31 e73 = stwo_qm31_add(e69, e72);
    StwoCairoQm31 e74 = stwo_qm31_sub(e73, e43);
    StwoCairoQm31 e75 = { b206, b207, b207, b207 };
    StwoCairoQm31 e76 = { 7u, 0u, 0u, 0u };
    StwoCairoQm31 e77 = { b32, b207, b207, b207 };
    StwoCairoQm31 e78 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e79 = stwo_qm31_mul(e77, e78);
    StwoCairoQm31 e80 = stwo_qm31_add(e76, e79);
    StwoCairoQm31 e81 = { b35, b207, b207, b207 };
    StwoCairoQm31 e82 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e83 = stwo_qm31_mul(e81, e82);
    StwoCairoQm31 e84 = stwo_qm31_add(e80, e83);
    StwoCairoQm31 e85 = { b36, b207, b207, b207 };
    StwoCairoQm31 e86 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e87 = stwo_qm31_mul(e85, e86);
    StwoCairoQm31 e88 = stwo_qm31_add(e84, e87);
    StwoCairoQm31 e89 = { b37, b207, b207, b207 };
    StwoCairoQm31 e90 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e91 = stwo_qm31_mul(e89, e90);
    StwoCairoQm31 e92 = stwo_qm31_add(e88, e91);
    StwoCairoQm31 e93 = { b38, b207, b207, b207 };
    StwoCairoQm31 e94 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e95 = stwo_qm31_mul(e93, e94);
    StwoCairoQm31 e96 = stwo_qm31_add(e92, e95);
    StwoCairoQm31 e97 = { b39, b207, b207, b207 };
    StwoCairoQm31 e98 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e99 = stwo_qm31_mul(e97, e98);
    StwoCairoQm31 e100 = stwo_qm31_add(e96, e99);
    StwoCairoQm31 e101 = { b40, b207, b207, b207 };
    StwoCairoQm31 e102 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e103 = stwo_qm31_mul(e101, e102);
    StwoCairoQm31 e104 = stwo_qm31_add(e100, e103);
    StwoCairoQm31 e105 = { b41, b207, b207, b207 };
    StwoCairoQm31 e106 = stwo_load_qm31(arena, args->ext_params + 8u * 4u);
    StwoCairoQm31 e107 = stwo_qm31_mul(e105, e106);
    StwoCairoQm31 e108 = stwo_qm31_add(e104, e107);
    StwoCairoQm31 e109 = { b42, b207, b207, b207 };
    StwoCairoQm31 e110 = stwo_load_qm31(arena, args->ext_params + 9u * 4u);
    StwoCairoQm31 e111 = stwo_qm31_mul(e109, e110);
    StwoCairoQm31 e112 = stwo_qm31_add(e108, e111);
    StwoCairoQm31 e113 = { b43, b207, b207, b207 };
    StwoCairoQm31 e114 = stwo_load_qm31(arena, args->ext_params + 10u * 4u);
    StwoCairoQm31 e115 = stwo_qm31_mul(e113, e114);
    StwoCairoQm31 e116 = stwo_qm31_add(e112, e115);
    StwoCairoQm31 e117 = { b44, b207, b207, b207 };
    StwoCairoQm31 e118 = stwo_load_qm31(arena, args->ext_params + 11u * 4u);
    StwoCairoQm31 e119 = stwo_qm31_mul(e117, e118);
    StwoCairoQm31 e120 = stwo_qm31_add(e116, e119);
    StwoCairoQm31 e121 = { b45, b207, b207, b207 };
    StwoCairoQm31 e122 = stwo_load_qm31(arena, args->ext_params + 12u * 4u);
    StwoCairoQm31 e123 = stwo_qm31_mul(e121, e122);
    StwoCairoQm31 e124 = stwo_qm31_add(e120, e123);
    StwoCairoQm31 e125 = { b46, b207, b207, b207 };
    StwoCairoQm31 e126 = stwo_load_qm31(arena, args->ext_params + 13u * 4u);
    StwoCairoQm31 e127 = stwo_qm31_mul(e125, e126);
    StwoCairoQm31 e128 = stwo_qm31_add(e124, e127);
    StwoCairoQm31 e129 = { b47, b207, b207, b207 };
    StwoCairoQm31 e130 = stwo_load_qm31(arena, args->ext_params + 14u * 4u);
    StwoCairoQm31 e131 = stwo_qm31_mul(e129, e130);
    StwoCairoQm31 e132 = stwo_qm31_add(e128, e131);
    StwoCairoQm31 e133 = { b48, b207, b207, b207 };
    StwoCairoQm31 e134 = stwo_load_qm31(arena, args->ext_params + 15u * 4u);
    StwoCairoQm31 e135 = stwo_qm31_mul(e133, e134);
    StwoCairoQm31 e136 = stwo_qm31_add(e132, e135);
    StwoCairoQm31 e137 = { b49, b207, b207, b207 };
    StwoCairoQm31 e138 = stwo_load_qm31(arena, args->ext_params + 16u * 4u);
    StwoCairoQm31 e139 = stwo_qm31_mul(e137, e138);
    StwoCairoQm31 e140 = stwo_qm31_add(e136, e139);
    StwoCairoQm31 e141 = { b50, b207, b207, b207 };
    StwoCairoQm31 e142 = stwo_load_qm31(arena, args->ext_params + 17u * 4u);
    StwoCairoQm31 e143 = stwo_qm31_mul(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_add(e140, e143);
    StwoCairoQm31 e145 = stwo_qm31_sub(e144, e43);
    StwoCairoQm31 e146 = { b206, b207, b207, b207 };
    StwoCairoQm31 e147 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e148 = { b207, b207, b207, b207 };
    StwoCairoQm31 e149 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e150 = stwo_qm31_mul(e148, e149);
    StwoCairoQm31 e151 = stwo_qm31_add(e147, e150);
    StwoCairoQm31 e152 = { b208, b207, b207, b207 };
    StwoCairoQm31 e153 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e154 = stwo_qm31_mul(e152, e153);
    StwoCairoQm31 e155 = stwo_qm31_add(e151, e154);
    StwoCairoQm31 e156 = { b35, b207, b207, b207 };
    StwoCairoQm31 e157 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e158 = stwo_qm31_mul(e156, e157);
    StwoCairoQm31 e159 = stwo_qm31_add(e155, e158);
    StwoCairoQm31 e160 = { b36, b207, b207, b207 };
    StwoCairoQm31 e161 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e162 = stwo_qm31_mul(e160, e161);
    StwoCairoQm31 e163 = stwo_qm31_add(e159, e162);
    StwoCairoQm31 e164 = stwo_qm31_sub(e163, e43);
    StwoCairoQm31 e165 = { b206, b207, b207, b207 };
    StwoCairoQm31 e166 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e167 = { b207, b207, b207, b207 };
    StwoCairoQm31 e168 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e169 = stwo_qm31_mul(e167, e168);
    StwoCairoQm31 e170 = stwo_qm31_add(e166, e169);
    StwoCairoQm31 e171 = { b209, b207, b207, b207 };
    StwoCairoQm31 e172 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e173 = stwo_qm31_mul(e171, e172);
    StwoCairoQm31 e174 = stwo_qm31_add(e170, e173);
    StwoCairoQm31 e175 = { b37, b207, b207, b207 };
    StwoCairoQm31 e176 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e177 = stwo_qm31_mul(e175, e176);
    StwoCairoQm31 e178 = stwo_qm31_add(e174, e177);
    StwoCairoQm31 e179 = { b38, b207, b207, b207 };
    StwoCairoQm31 e180 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e181 = stwo_qm31_mul(e179, e180);
    StwoCairoQm31 e182 = stwo_qm31_add(e178, e181);
    StwoCairoQm31 e183 = stwo_qm31_sub(e182, e43);
    StwoCairoQm31 e184 = { b206, b207, b207, b207 };
    StwoCairoQm31 e185 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e186 = { b207, b207, b207, b207 };
    StwoCairoQm31 e187 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e188 = stwo_qm31_mul(e186, e187);
    StwoCairoQm31 e189 = stwo_qm31_add(e185, e188);
    StwoCairoQm31 e190 = { b210, b207, b207, b207 };
    StwoCairoQm31 e191 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e192 = stwo_qm31_mul(e190, e191);
    StwoCairoQm31 e193 = stwo_qm31_add(e189, e192);
    StwoCairoQm31 e194 = { b39, b207, b207, b207 };
    StwoCairoQm31 e195 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e196 = stwo_qm31_mul(e194, e195);
    StwoCairoQm31 e197 = stwo_qm31_add(e193, e196);
    StwoCairoQm31 e198 = { b40, b207, b207, b207 };
    StwoCairoQm31 e199 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e200 = stwo_qm31_mul(e198, e199);
    StwoCairoQm31 e201 = stwo_qm31_add(e197, e200);
    StwoCairoQm31 e202 = stwo_qm31_sub(e201, e43);
    StwoCairoQm31 e203 = { b206, b207, b207, b207 };
    StwoCairoQm31 e204 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e205 = { b207, b207, b207, b207 };
    StwoCairoQm31 e206 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e207 = stwo_qm31_mul(e205, e206);
    StwoCairoQm31 e208 = stwo_qm31_add(e204, e207);
    StwoCairoQm31 e209 = { b211, b207, b207, b207 };
    StwoCairoQm31 e210 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e211 = stwo_qm31_mul(e209, e210);
    StwoCairoQm31 e212 = stwo_qm31_add(e208, e211);
    StwoCairoQm31 e213 = { b41, b207, b207, b207 };
    StwoCairoQm31 e214 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e215 = stwo_qm31_mul(e213, e214);
    StwoCairoQm31 e216 = stwo_qm31_add(e212, e215);
    StwoCairoQm31 e217 = { b42, b207, b207, b207 };
    StwoCairoQm31 e218 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e219 = stwo_qm31_mul(e217, e218);
    StwoCairoQm31 e220 = stwo_qm31_add(e216, e219);
    StwoCairoQm31 e221 = stwo_qm31_sub(e220, e43);
    StwoCairoQm31 e222 = { b206, b207, b207, b207 };
    StwoCairoQm31 e223 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e224 = { b207, b207, b207, b207 };
    StwoCairoQm31 e225 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e226 = stwo_qm31_mul(e224, e225);
    StwoCairoQm31 e227 = stwo_qm31_add(e223, e226);
    StwoCairoQm31 e228 = { b212, b207, b207, b207 };
    StwoCairoQm31 e229 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e230 = stwo_qm31_mul(e228, e229);
    StwoCairoQm31 e231 = stwo_qm31_add(e227, e230);
    StwoCairoQm31 e232 = { b43, b207, b207, b207 };
    StwoCairoQm31 e233 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e234 = stwo_qm31_mul(e232, e233);
    StwoCairoQm31 e235 = stwo_qm31_add(e231, e234);
    StwoCairoQm31 e236 = { b44, b207, b207, b207 };
    StwoCairoQm31 e237 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e238 = stwo_qm31_mul(e236, e237);
    StwoCairoQm31 e239 = stwo_qm31_add(e235, e238);
    StwoCairoQm31 e240 = stwo_qm31_sub(e239, e43);
    StwoCairoQm31 e241 = { b206, b207, b207, b207 };
    StwoCairoQm31 e242 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e243 = { b207, b207, b207, b207 };
    StwoCairoQm31 e244 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e245 = stwo_qm31_mul(e243, e244);
    StwoCairoQm31 e246 = stwo_qm31_add(e242, e245);
    StwoCairoQm31 e247 = { b213, b207, b207, b207 };
    StwoCairoQm31 e248 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e249 = stwo_qm31_mul(e247, e248);
    StwoCairoQm31 e250 = stwo_qm31_add(e246, e249);
    StwoCairoQm31 e251 = { b45, b207, b207, b207 };
    StwoCairoQm31 e252 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e253 = stwo_qm31_mul(e251, e252);
    StwoCairoQm31 e254 = stwo_qm31_add(e250, e253);
    StwoCairoQm31 e255 = { b46, b207, b207, b207 };
    StwoCairoQm31 e256 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e257 = stwo_qm31_mul(e255, e256);
    StwoCairoQm31 e258 = stwo_qm31_add(e254, e257);
    StwoCairoQm31 e259 = stwo_qm31_sub(e258, e43);
    StwoCairoQm31 e260 = { b206, b207, b207, b207 };
    StwoCairoQm31 e261 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e262 = { b207, b207, b207, b207 };
    StwoCairoQm31 e263 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e264 = stwo_qm31_mul(e262, e263);
    StwoCairoQm31 e265 = stwo_qm31_add(e261, e264);
    StwoCairoQm31 e266 = { b214, b207, b207, b207 };
    StwoCairoQm31 e267 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e268 = stwo_qm31_mul(e266, e267);
    StwoCairoQm31 e269 = stwo_qm31_add(e265, e268);
    StwoCairoQm31 e270 = { b47, b207, b207, b207 };
    StwoCairoQm31 e271 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e272 = stwo_qm31_mul(e270, e271);
    StwoCairoQm31 e273 = stwo_qm31_add(e269, e272);
    StwoCairoQm31 e274 = { b48, b207, b207, b207 };
    StwoCairoQm31 e275 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e276 = stwo_qm31_mul(e274, e275);
    StwoCairoQm31 e277 = stwo_qm31_add(e273, e276);
    StwoCairoQm31 e278 = stwo_qm31_sub(e277, e43);
    StwoCairoQm31 e279 = { b206, b207, b207, b207 };
    StwoCairoQm31 e280 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e281 = { b207, b207, b207, b207 };
    StwoCairoQm31 e282 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e283 = stwo_qm31_mul(e281, e282);
    StwoCairoQm31 e284 = stwo_qm31_add(e280, e283);
    StwoCairoQm31 e285 = { b215, b207, b207, b207 };
    StwoCairoQm31 e286 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e287 = stwo_qm31_mul(e285, e286);
    StwoCairoQm31 e288 = stwo_qm31_add(e284, e287);
    StwoCairoQm31 e289 = { b49, b207, b207, b207 };
    StwoCairoQm31 e290 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e291 = stwo_qm31_mul(e289, e290);
    StwoCairoQm31 e292 = stwo_qm31_add(e288, e291);
    StwoCairoQm31 e293 = { b50, b207, b207, b207 };
    StwoCairoQm31 e294 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e295 = stwo_qm31_mul(e293, e294);
    StwoCairoQm31 e296 = stwo_qm31_add(e292, e295);
    StwoCairoQm31 e297 = stwo_qm31_sub(e296, e43);
    StwoCairoQm31 e298 = { b53, b54, b55, b56 };
    StwoCairoQm31 e299 = { b57, b58, b59, b60 };
    StwoCairoQm31 e300 = { b61, b62, b63, b64 };
    StwoCairoQm31 e301 = { b65, b66, b67, b68 };
    StwoCairoQm31 e302 = { b69, b70, b71, b72 };
    StwoCairoQm31 e303 = { b74, b76, b78, b80 };
    StwoCairoQm31 e304 = { b73, b75, b77, b79 };
    StwoCairoQm31 e305 = stwo_qm31_mul(e45, e74);
    StwoCairoQm31 e306 = stwo_qm31_mul(e64, e63);
    StwoCairoQm31 e307 = stwo_qm31_add(e305, e306);
    StwoCairoQm31 e308 = stwo_qm31_mul(e63, e74);
    StwoCairoQm31 e309 = stwo_qm31_mul(e298, e308);
    StwoCairoQm31 e310 = stwo_qm31_sub(e309, e307);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e310, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e311 = stwo_qm31_mul(e75, e164);
    StwoCairoQm31 e312 = stwo_qm31_mul(e146, e145);
    StwoCairoQm31 e313 = stwo_qm31_add(e311, e312);
    StwoCairoQm31 e314 = stwo_qm31_mul(e145, e164);
    StwoCairoQm31 e315 = stwo_qm31_sub(e299, e298);
    StwoCairoQm31 e316 = stwo_qm31_mul(e315, e314);
    StwoCairoQm31 e317 = stwo_qm31_sub(e316, e313);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e317, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e318 = stwo_qm31_mul(e165, e202);
    StwoCairoQm31 e319 = stwo_qm31_mul(e184, e183);
    StwoCairoQm31 e320 = stwo_qm31_add(e318, e319);
    StwoCairoQm31 e321 = stwo_qm31_mul(e183, e202);
    StwoCairoQm31 e322 = stwo_qm31_sub(e300, e299);
    StwoCairoQm31 e323 = stwo_qm31_mul(e322, e321);
    StwoCairoQm31 e324 = stwo_qm31_sub(e323, e320);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e324, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e325 = stwo_qm31_mul(e203, e240);
    StwoCairoQm31 e326 = stwo_qm31_mul(e222, e221);
    StwoCairoQm31 e327 = stwo_qm31_add(e325, e326);
    StwoCairoQm31 e328 = stwo_qm31_mul(e221, e240);
    StwoCairoQm31 e329 = stwo_qm31_sub(e301, e300);
    StwoCairoQm31 e330 = stwo_qm31_mul(e329, e328);
    StwoCairoQm31 e331 = stwo_qm31_sub(e330, e327);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e331, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e332 = stwo_qm31_mul(e241, e278);
    StwoCairoQm31 e333 = stwo_qm31_mul(e260, e259);
    StwoCairoQm31 e334 = stwo_qm31_add(e332, e333);
    StwoCairoQm31 e335 = stwo_qm31_mul(e259, e278);
    StwoCairoQm31 e336 = stwo_qm31_sub(e302, e301);
    StwoCairoQm31 e337 = stwo_qm31_mul(e336, e335);
    StwoCairoQm31 e338 = stwo_qm31_sub(e337, e334);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e338, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e339 = stwo_qm31_sub(e303, e304);
    StwoCairoQm31 e340 = stwo_qm31_sub(e339, e302);
    StwoCairoQm31 e341 = stwo_qm31_add(e340, e44);
    StwoCairoQm31 e342 = stwo_qm31_mul(e341, e297);
    StwoCairoQm31 e343 = stwo_qm31_sub(e342, e279);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e343, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
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
