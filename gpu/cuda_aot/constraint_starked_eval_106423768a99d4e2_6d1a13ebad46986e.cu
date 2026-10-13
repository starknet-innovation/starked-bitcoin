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
stwo_cairo_cuda_eval_v6_106423768a99d4e2(
    unsigned *arena,
    u64 arena_words,
    const StwoCairoEvalArgs *args) {
    const unsigned row =
        blockIdx.x * blockDim.x + threadIdx.x;
    if (arena == nullptr || args == nullptr ||
        row >= args->row_count) return;
    StwoCairoQm31 part_acc = { 0u, 0u, 0u, 0u };
    unsigned b0 = stwo_trace_value(arena, *args, 1u, 0u, row, 0);
    unsigned b1 = stwo_trace_value(arena, *args, 1u, 1u, row, -1);
    unsigned b2 = stwo_trace_value(arena, *args, 1u, 1u, row, 0);
    unsigned b3 = stwo_trace_value(arena, *args, 1u, 2u, row, -1);
    unsigned b4 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 3u, row, -1);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 4u, row, -1);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 6u, row, -1);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 7u, row, -1);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 8u, row, -1);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 13u, row, -1);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 14u, row, -1);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 15u, row, -1);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 16u, row, -1);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 1u, 18u, row, -1);
    unsigned b33 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 1u, 20u, row, -3);
    unsigned b36 = stwo_trace_value(arena, *args, 1u, 20u, row, -2);
    unsigned b37 = stwo_trace_value(arena, *args, 1u, 20u, row, -1);
    unsigned b38 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 1u, 21u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 1u, 22u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 1u, 23u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 1u, 24u, row, -3);
    unsigned b43 = stwo_trace_value(arena, *args, 1u, 24u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 1u, 25u, row, -3);
    unsigned b45 = stwo_trace_value(arena, *args, 1u, 25u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 1u, 26u, row, -3);
    unsigned b47 = stwo_trace_value(arena, *args, 1u, 26u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 1u, 27u, row, -3);
    unsigned b49 = stwo_trace_value(arena, *args, 1u, 27u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 1u, 28u, row, -3);
    unsigned b51 = stwo_trace_value(arena, *args, 1u, 28u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 1u, 29u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 1u, 30u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 1u, 31u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 1u, 32u, row, -1);
    unsigned b56 = stwo_trace_value(arena, *args, 1u, 32u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 1u, 33u, row, -1);
    unsigned b58 = stwo_trace_value(arena, *args, 1u, 33u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 1u, 34u, row, -1);
    unsigned b60 = stwo_trace_value(arena, *args, 1u, 34u, row, 0);
    unsigned b61 = stwo_trace_value(arena, *args, 1u, 35u, row, -1);
    unsigned b62 = stwo_trace_value(arena, *args, 1u, 35u, row, 0);
    unsigned b63 = stwo_trace_value(arena, *args, 1u, 36u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 1u, 37u, row, 0);
    unsigned b65 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b67 = stwo_trace_value(arena, *args, 0u, 2u, row, 0);
    unsigned b68 = stwo_trace_value(arena, *args, 0u, 3u, row, 0);
    unsigned b69 = stwo_trace_value(arena, *args, 0u, 5u, row, 0);
    unsigned b70 = stwo_trace_value(arena, *args, 0u, 6u, row, 0);
    unsigned b71 = stwo_trace_value(arena, *args, 0u, 7u, row, 0);
    unsigned b72 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b73 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b74 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b75 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b76 = stwo_trace_value(arena, *args, 2u, 4u, row, -1);
    unsigned b77 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b78 = stwo_trace_value(arena, *args, 2u, 5u, row, -1);
    unsigned b79 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b80 = stwo_trace_value(arena, *args, 2u, 6u, row, -1);
    unsigned b81 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b82 = stwo_trace_value(arena, *args, 2u, 7u, row, -1);
    unsigned b83 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b84 = arena[args->base_params + 0u];
    unsigned b85 = stwo_m31_sub(b0, b84);
    unsigned b86 = stwo_m31_mul(b0, b85);
    unsigned b87 = stwo_m31_sub(b2, b84);
    unsigned b88 = stwo_m31_mul(b2, b87);
    unsigned b89 = stwo_m31_sub(b4, b84);
    unsigned b90 = stwo_m31_mul(b4, b89);
    unsigned b91 = stwo_m31_sub(b6, b84);
    unsigned b92 = stwo_m31_mul(b6, b91);
    unsigned b93 = stwo_m31_sub(b8, b84);
    unsigned b94 = stwo_m31_mul(b8, b93);
    unsigned b95 = stwo_m31_sub(b9, b84);
    unsigned b96 = stwo_m31_mul(b9, b95);
    unsigned b97 = stwo_m31_sub(b11, b84);
    unsigned b98 = stwo_m31_mul(b11, b97);
    unsigned b99 = stwo_m31_sub(b13, b84);
    unsigned b100 = stwo_m31_mul(b13, b99);
    unsigned b101 = stwo_m31_sub(b15, b84);
    unsigned b102 = stwo_m31_mul(b15, b101);
    unsigned b103 = stwo_m31_sub(b18, b84);
    unsigned b104 = stwo_m31_mul(b18, b103);
    unsigned b105 = stwo_m31_sub(b20, b84);
    unsigned b106 = stwo_m31_mul(b20, b105);
    unsigned b107 = stwo_m31_sub(b22, b84);
    unsigned b108 = stwo_m31_mul(b22, b107);
    unsigned b109 = stwo_m31_sub(b53, b84);
    unsigned b110 = stwo_m31_mul(b53, b109);
    unsigned b111 = stwo_m31_sub(b39, b84);
    unsigned b112 = stwo_m31_mul(b39, b111);
    unsigned b113 = stwo_m31_sub(b40, b84);
    unsigned b114 = stwo_m31_mul(b40, b113);
    unsigned b115 = stwo_m31_sub(b41, b84);
    unsigned b116 = stwo_m31_mul(b41, b115);
    unsigned b117 = stwo_m31_sub(b43, b84);
    unsigned b118 = stwo_m31_mul(b43, b117);
    unsigned b119 = stwo_m31_sub(b45, b84);
    unsigned b120 = stwo_m31_mul(b45, b119);
    unsigned b121 = stwo_m31_sub(b47, b84);
    unsigned b122 = stwo_m31_mul(b47, b121);
    unsigned b123 = stwo_m31_sub(b49, b84);
    unsigned b124 = stwo_m31_mul(b49, b123);
    unsigned b125 = stwo_m31_sub(b51, b84);
    unsigned b126 = stwo_m31_mul(b51, b125);
    unsigned b127 = arena[args->base_params + 1u];
    unsigned b128 = stwo_m31_add(b8, b127);
    unsigned b129 = stwo_m31_add(b6, b128);
    unsigned b130 = stwo_m31_add(b4, b129);
    unsigned b131 = stwo_m31_add(b2, b130);
    unsigned b132 = stwo_m31_add(b0, b131);
    unsigned b133 = stwo_m31_sub(b132, b84);
    unsigned b134 = stwo_m31_sub(b84, b0);
    unsigned b135 = stwo_m31_mul(b9, b134);
    unsigned b136 = stwo_m31_sub(b84, b67);
    unsigned b137 = stwo_m31_mul(b9, b136);
    unsigned b138 = stwo_m31_sub(b84, b66);
    unsigned b139 = stwo_m31_sub(b84, b8);
    unsigned b140 = stwo_m31_mul(b138, b139);
    unsigned b141 = stwo_m31_sub(b84, b53);
    unsigned b142 = stwo_m31_mul(b0, b141);
    unsigned b143 = stwo_m31_sub(b56, b142);
    unsigned b144 = stwo_m31_add(b11, b13);
    unsigned b145 = stwo_m31_mul(b16, b144);
    unsigned b146 = stwo_m31_mul(b53, b145);
    unsigned b147 = stwo_m31_sub(b58, b146);
    unsigned b148 = stwo_m31_mul(b0, b53);
    unsigned b149 = stwo_m31_sub(b148, b58);
    unsigned b150 = stwo_m31_sub(b60, b149);
    unsigned b151 = stwo_m31_sub(b0, b9);
    unsigned b152 = stwo_m31_add(b55, b57);
    unsigned b153 = stwo_m31_sub(b151, b152);
    unsigned b154 = stwo_m31_sub(b2, b59);
    unsigned b155 = stwo_m31_add(b1, b3);
    unsigned b156 = stwo_m31_sub(b84, b71);
    unsigned b157 = stwo_m31_mul(b155, b156);
    unsigned b158 = stwo_m31_sub(b4, b157);
    unsigned b159 = stwo_m31_mul(b155, b71);
    unsigned b160 = stwo_m31_mul(b5, b136);
    unsigned b161 = stwo_m31_add(b159, b160);
    unsigned b162 = stwo_m31_sub(b6, b161);
    unsigned b163 = stwo_m31_add(b8, b9);
    unsigned b164 = stwo_m31_mul(b5, b67);
    unsigned b165 = stwo_m31_add(b164, b7);
    unsigned b166 = stwo_m31_sub(b163, b165);
    unsigned b167 = stwo_m31_add(b13, b15);
    unsigned b168 = stwo_m31_add(b11, b167);
    unsigned b169 = stwo_m31_sub(b168, b0);
    unsigned b170 = stwo_m31_sub(b11, b9);
    unsigned b171 = stwo_m31_mul(b55, b10);
    unsigned b172 = stwo_m31_sub(b170, b171);
    unsigned b173 = stwo_m31_mul(b55, b12);
    unsigned b174 = stwo_m31_mul(b57, b10);
    unsigned b175 = stwo_m31_add(b173, b174);
    unsigned b176 = stwo_m31_sub(b13, b175);
    unsigned b177 = stwo_m31_mul(b55, b14);
    unsigned b178 = stwo_m31_mul(b57, b12);
    unsigned b179 = stwo_m31_add(b177, b178);
    unsigned b180 = stwo_m31_sub(b15, b179);
    unsigned b181 = stwo_m31_sub(b84, b20);
    unsigned b182 = stwo_m31_sub(b181, b18);
    unsigned b183 = stwo_m31_mul(b182, b22);
    unsigned b184 = stwo_m31_sub(b16, b183);
    unsigned b185 = stwo_m31_mul(b18, b26);
    unsigned b186 = arena[args->base_params + 2u];
    unsigned b187 = stwo_m31_sub(b30, b186);
    unsigned b188 = stwo_m31_mul(b18, b187);
    unsigned b189 = stwo_m31_mul(b20, b18);
    unsigned b190 = stwo_m31_sub(b84, b18);
    unsigned b191 = arena[args->base_params + 3u];
    unsigned b192 = stwo_m31_mul(b191, b24);
    unsigned b193 = stwo_m31_add(b84, b192);
    unsigned b194 = stwo_m31_add(b193, b20);
    unsigned b195 = stwo_m31_mul(b190, b194);
    unsigned b196 = stwo_m31_sub(b31, b195);
    unsigned b197 = stwo_m31_add(b26, b33);
    unsigned b198 = stwo_m31_mul(b191, b13);
    unsigned b199 = stwo_m31_add(b197, b198);
    unsigned b200 = stwo_m31_sub(b30, b28);
    unsigned b201 = stwo_m31_add(b200, b191);
    unsigned b202 = stwo_m31_mul(b15, b201);
    unsigned b203 = stwo_m31_add(b199, b202);
    unsigned b204 = stwo_m31_sub(b34, b203);
    unsigned b205 = stwo_m31_mul(b0, b204);
    unsigned b206 = arena[args->base_params + 4u];
    unsigned b207 = stwo_m31_sub(b33, b206);
    unsigned b208 = stwo_m31_mul(b11, b207);
    unsigned b209 = stwo_m31_sub(b34, b28);
    unsigned b210 = stwo_m31_add(b209, b84);
    unsigned b211 = stwo_m31_mul(b13, b210);
    unsigned b212 = stwo_m31_add(b30, b206);
    unsigned b213 = stwo_m31_sub(b34, b212);
    unsigned b214 = stwo_m31_mul(b15, b213);
    unsigned b215 = stwo_m31_add(b211, b214);
    unsigned b216 = stwo_m31_add(b208, b215);
    unsigned b217 = stwo_m31_mul(b16, b216);
    unsigned b218 = stwo_m31_sub(b84, b16);
    unsigned b219 = stwo_m31_mul(b218, b213);
    unsigned b220 = stwo_m31_add(b217, b219);
    unsigned b221 = stwo_m31_sub(b52, b220);
    unsigned b222 = stwo_m31_mul(b53, b52);
    unsigned b223 = stwo_m31_mul(b52, b54);
    unsigned b224 = stwo_m31_sub(b223, b84);
    unsigned b225 = stwo_m31_mul(b141, b224);
    unsigned b226 = stwo_m31_mul(b9, b33);
    unsigned b227 = stwo_m31_sub(b84, b9);
    unsigned b228 = stwo_m31_sub(b84, b65);
    unsigned b229 = stwo_m31_sub(b33, b32);
    unsigned b230 = stwo_m31_sub(b229, b84);
    unsigned b231 = stwo_m31_mul(b228, b230);
    unsigned b232 = stwo_m31_mul(b227, b231);
    unsigned b233 = stwo_m31_sub(b18, b17);
    unsigned b234 = stwo_m31_mul(b228, b233);
    unsigned b235 = stwo_m31_mul(b227, b234);
    unsigned b236 = stwo_m31_sub(b20, b19);
    unsigned b237 = stwo_m31_mul(b228, b236);
    unsigned b238 = stwo_m31_mul(b227, b237);
    unsigned b239 = stwo_m31_sub(b22, b21);
    unsigned b240 = stwo_m31_mul(b228, b239);
    unsigned b241 = stwo_m31_mul(b227, b240);
    unsigned b242 = stwo_m31_sub(b24, b23);
    unsigned b243 = stwo_m31_mul(b228, b242);
    unsigned b244 = stwo_m31_mul(b227, b243);
    unsigned b245 = stwo_m31_sub(b26, b25);
    unsigned b246 = stwo_m31_mul(b228, b245);
    unsigned b247 = stwo_m31_mul(b227, b246);
    unsigned b248 = stwo_m31_sub(b28, b27);
    unsigned b249 = stwo_m31_mul(b228, b248);
    unsigned b250 = stwo_m31_mul(b227, b249);
    unsigned b251 = stwo_m31_sub(b30, b29);
    unsigned b252 = stwo_m31_mul(b228, b251);
    unsigned b253 = stwo_m31_mul(b227, b252);
    unsigned b254 = stwo_m31_mul(b84, b39);
    unsigned b255 = stwo_m31_add(b127, b254);
    unsigned b256 = stwo_m31_mul(b191, b40);
    unsigned b257 = stwo_m31_add(b255, b256);
    unsigned b258 = arena[args->base_params + 5u];
    unsigned b259 = stwo_m31_mul(b258, b41);
    unsigned b260 = stwo_m31_add(b257, b259);
    unsigned b261 = arena[args->base_params + 6u];
    unsigned b262 = stwo_m31_mul(b261, b43);
    unsigned b263 = stwo_m31_add(b260, b262);
    unsigned b264 = arena[args->base_params + 7u];
    unsigned b265 = stwo_m31_mul(b264, b45);
    unsigned b266 = stwo_m31_add(b263, b265);
    unsigned b267 = arena[args->base_params + 8u];
    unsigned b268 = stwo_m31_mul(b267, b47);
    unsigned b269 = stwo_m31_add(b266, b268);
    unsigned b270 = arena[args->base_params + 9u];
    unsigned b271 = stwo_m31_mul(b270, b49);
    unsigned b272 = stwo_m31_add(b269, b271);
    unsigned b273 = arena[args->base_params + 10u];
    unsigned b274 = stwo_m31_mul(b273, b51);
    unsigned b275 = stwo_m31_add(b272, b274);
    unsigned b276 = stwo_m31_sub(b38, b275);
    unsigned b277 = stwo_m31_sub(b38, b273);
    unsigned b278 = stwo_m31_mul(b2, b277);
    unsigned b279 = stwo_m31_mul(b4, b38);
    unsigned b280 = stwo_m31_mul(b70, b38);
    unsigned b281 = stwo_m31_mul(b6, b280);
    unsigned b282 = arena[args->base_params + 11u];
    unsigned b283 = stwo_m31_mul(b282, b35);
    unsigned b284 = arena[args->base_params + 12u];
    unsigned b285 = stwo_m31_mul(b284, b36);
    unsigned b286 = stwo_m31_add(b283, b285);
    unsigned b287 = arena[args->base_params + 13u];
    unsigned b288 = stwo_m31_mul(b287, b37);
    unsigned b289 = stwo_m31_add(b286, b288);
    unsigned b290 = stwo_m31_add(b289, b38);
    unsigned b291 = stwo_m31_mul(b261, b62);
    unsigned b292 = stwo_m31_sub(b290, b291);
    unsigned b293 = stwo_m31_mul(b6, b292);
    unsigned b294 = stwo_m31_mul(b69, b293);
    unsigned b295 = stwo_m31_sub(b62, b33);
    unsigned b296 = stwo_m31_mul(b2, b295);
    unsigned b297 = stwo_m31_sub(b84, b2);
    unsigned b298 = stwo_m31_sub(b62, b61);
    unsigned b299 = stwo_m31_mul(b228, b298);
    unsigned b300 = stwo_m31_mul(b297, b299);
    unsigned b301 = stwo_m31_mul(b63, b8);
    unsigned b302 = stwo_m31_sub(b84, b69);
    unsigned b303 = stwo_m31_mul(b64, b302);
    unsigned b304 = stwo_m31_sub(b84, b6);
    unsigned b305 = stwo_m31_mul(b64, b304);
    unsigned b306 = stwo_m31_add(b50, b127);
    unsigned b307 = stwo_m31_add(b48, b306);
    unsigned b308 = stwo_m31_add(b46, b307);
    unsigned b309 = stwo_m31_add(b44, b308);
    unsigned b310 = stwo_m31_add(b42, b309);
    unsigned b311 = stwo_m31_mul(b6, b310);
    unsigned b312 = stwo_m31_mul(b69, b311);
    unsigned b313 = stwo_m31_neg(b0);
    unsigned b314 = stwo_m31_mul(b9, b190);
    unsigned b315 = stwo_m31_neg(b314);
    unsigned b316 = stwo_m31_mul(b68, b63);
    unsigned b317 = stwo_m31_add(b288, b38);
    unsigned b318 = stwo_m31_mul(b287, b35);
    unsigned b319 = stwo_m31_add(b318, b36);
    unsigned b320 = stwo_m31_mul(b6, b64);
    unsigned b321 = stwo_m31_add(b33, b84);
    StwoCairoQm31 e0 = { b86, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b88, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b90, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b92, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b94, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b96, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b98, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b100, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b102, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b104, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b106, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b108, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b110, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b112, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b114, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b116, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b118, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b120, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b122, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b124, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b126, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b133, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b135, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b137, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b140, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b143, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b147, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b150, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b153, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b154, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b158, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b162, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b166, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b169, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b172, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b176, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b180, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b184, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b185, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b188, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b189, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b196, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b205, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b221, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b222, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b225, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b226, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b232, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = { b235, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e48, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e49 = { b238, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e49, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e50 = { b241, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e50, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
    StwoCairoQm31 e51 = { b244, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e51, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 51u) * 4u)));
    StwoCairoQm31 e52 = { b247, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e52, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 52u) * 4u)));
    StwoCairoQm31 e53 = { b250, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e53, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 53u) * 4u)));
    StwoCairoQm31 e54 = { b253, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e54, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 54u) * 4u)));
    StwoCairoQm31 e55 = { b276, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e55, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 55u) * 4u)));
    StwoCairoQm31 e56 = { b278, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e56, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 56u) * 4u)));
    StwoCairoQm31 e57 = { b279, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e57, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 57u) * 4u)));
    StwoCairoQm31 e58 = { b281, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e58, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 58u) * 4u)));
    StwoCairoQm31 e59 = { b294, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e59, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 59u) * 4u)));
    StwoCairoQm31 e60 = { b296, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e60, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 60u) * 4u)));
    StwoCairoQm31 e61 = { b300, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e61, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 61u) * 4u)));
    StwoCairoQm31 e62 = { b301, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e62, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 62u) * 4u)));
    StwoCairoQm31 e63 = { b303, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e63, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 63u) * 4u)));
    StwoCairoQm31 e64 = { b305, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e64, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 64u) * 4u)));
    StwoCairoQm31 e65 = { b312, b127, b127, b127 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e65, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 65u) * 4u)));
    StwoCairoQm31 e66 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e67 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e68 = { b313, b127, b127, b127 };
    StwoCairoQm31 e69 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e70 = { b34, b127, b127, b127 };
    StwoCairoQm31 e71 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e72 = stwo_qm31_mul(e70, e71);
    StwoCairoQm31 e73 = stwo_qm31_add(e69, e72);
    StwoCairoQm31 e74 = { b38, b127, b127, b127 };
    StwoCairoQm31 e75 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e76 = stwo_qm31_mul(e74, e75);
    StwoCairoQm31 e77 = stwo_qm31_add(e73, e76);
    StwoCairoQm31 e78 = stwo_qm31_sub(e77, e66);
    StwoCairoQm31 e79 = { b315, b127, b127, b127 };
    StwoCairoQm31 e80 = { 4u, 0u, 0u, 0u };
    StwoCairoQm31 e81 = { b24, b127, b127, b127 };
    StwoCairoQm31 e82 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e83 = stwo_qm31_mul(e81, e82);
    StwoCairoQm31 e84 = stwo_qm31_add(e80, e83);
    StwoCairoQm31 e85 = { b26, b127, b127, b127 };
    StwoCairoQm31 e86 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e87 = stwo_qm31_mul(e85, e86);
    StwoCairoQm31 e88 = stwo_qm31_add(e84, e87);
    StwoCairoQm31 e89 = { b22, b127, b127, b127 };
    StwoCairoQm31 e90 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e91 = stwo_qm31_mul(e89, e90);
    StwoCairoQm31 e92 = stwo_qm31_add(e88, e91);
    StwoCairoQm31 e93 = { b28, b127, b127, b127 };
    StwoCairoQm31 e94 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e95 = stwo_qm31_mul(e93, e94);
    StwoCairoQm31 e96 = stwo_qm31_add(e92, e95);
    StwoCairoQm31 e97 = { b30, b127, b127, b127 };
    StwoCairoQm31 e98 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e99 = stwo_qm31_mul(e97, e98);
    StwoCairoQm31 e100 = stwo_qm31_add(e96, e99);
    StwoCairoQm31 e101 = stwo_qm31_sub(e100, e66);
    StwoCairoQm31 e102 = { b316, b127, b127, b127 };
    StwoCairoQm31 e103 = { 5u, 0u, 0u, 0u };
    StwoCairoQm31 e104 = { b31, b127, b127, b127 };
    StwoCairoQm31 e105 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e106 = stwo_qm31_mul(e104, e105);
    StwoCairoQm31 e107 = stwo_qm31_add(e103, e106);
    StwoCairoQm31 e108 = { b207, b127, b127, b127 };
    StwoCairoQm31 e109 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e110 = stwo_qm31_mul(e108, e109);
    StwoCairoQm31 e111 = stwo_qm31_add(e107, e110);
    StwoCairoQm31 e112 = { b317, b127, b127, b127 };
    StwoCairoQm31 e113 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e114 = stwo_qm31_mul(e112, e113);
    StwoCairoQm31 e115 = stwo_qm31_add(e111, e114);
    StwoCairoQm31 e116 = { b319, b127, b127, b127 };
    StwoCairoQm31 e117 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e118 = stwo_qm31_mul(e116, e117);
    StwoCairoQm31 e119 = stwo_qm31_add(e115, e118);
    StwoCairoQm31 e120 = stwo_qm31_sub(e119, e66);
    StwoCairoQm31 e121 = { b320, b127, b127, b127 };
    StwoCairoQm31 e122 = { 6u, 0u, 0u, 0u };
    StwoCairoQm31 e123 = { b31, b127, b127, b127 };
    StwoCairoQm31 e124 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e125 = stwo_qm31_mul(e123, e124);
    StwoCairoQm31 e126 = stwo_qm31_add(e122, e125);
    StwoCairoQm31 e127 = { b321, b127, b127, b127 };
    StwoCairoQm31 e128 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e129 = stwo_qm31_mul(e127, e128);
    StwoCairoQm31 e130 = stwo_qm31_add(e126, e129);
    StwoCairoQm31 e131 = stwo_qm31_sub(e130, e66);
    StwoCairoQm31 e132 = { b72, b73, b74, b75 };
    StwoCairoQm31 e133 = { b77, b79, b81, b83 };
    StwoCairoQm31 e134 = { b76, b78, b80, b82 };
    StwoCairoQm31 e135 = stwo_qm31_mul(e68, e101);
    StwoCairoQm31 e136 = stwo_qm31_mul(e79, e78);
    StwoCairoQm31 e137 = stwo_qm31_add(e135, e136);
    StwoCairoQm31 e138 = stwo_qm31_mul(e78, e101);
    StwoCairoQm31 e139 = stwo_qm31_mul(e132, e138);
    StwoCairoQm31 e140 = stwo_qm31_sub(e139, e137);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e140, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 66u) * 4u)));
    StwoCairoQm31 e141 = stwo_qm31_mul(e102, e131);
    StwoCairoQm31 e142 = stwo_qm31_mul(e121, e120);
    StwoCairoQm31 e143 = stwo_qm31_add(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_mul(e120, e131);
    StwoCairoQm31 e145 = stwo_qm31_sub(e133, e134);
    StwoCairoQm31 e146 = stwo_qm31_sub(e145, e132);
    StwoCairoQm31 e147 = stwo_qm31_add(e146, e67);
    StwoCairoQm31 e148 = stwo_qm31_mul(e147, e144);
    StwoCairoQm31 e149 = stwo_qm31_sub(e148, e143);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e149, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 67u) * 4u)));
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
