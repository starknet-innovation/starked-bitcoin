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
stwo_cairo_cuda_eval_v6_1ea84a3f50acffd2(
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
    unsigned b69 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b70 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b71 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b72 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b73 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b74 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b75 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b76 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b77 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b78 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b79 = stwo_trace_value(arena, *args, 2u, 8u, row, -1);
    unsigned b80 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b81 = stwo_trace_value(arena, *args, 2u, 9u, row, -1);
    unsigned b82 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b83 = stwo_trace_value(arena, *args, 2u, 10u, row, -1);
    unsigned b84 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b85 = stwo_trace_value(arena, *args, 2u, 11u, row, -1);
    unsigned b86 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b87 = arena[args->base_params + 0u];
    unsigned b88 = stwo_m31_sub(b1, b87);
    unsigned b89 = stwo_m31_mul(b1, b88);
    unsigned b90 = stwo_m31_sub(b2, b87);
    unsigned b91 = stwo_m31_mul(b2, b90);
    unsigned b92 = stwo_m31_sub(b8, b87);
    unsigned b93 = stwo_m31_mul(b8, b92);
    unsigned b94 = stwo_m31_sub(b9, b87);
    unsigned b95 = stwo_m31_mul(b9, b94);
    unsigned b96 = stwo_m31_sub(b10, b87);
    unsigned b97 = stwo_m31_mul(b10, b96);
    unsigned b98 = stwo_m31_sub(b11, b87);
    unsigned b99 = stwo_m31_mul(b11, b98);
    unsigned b100 = stwo_m31_sub(b18, b87);
    unsigned b101 = stwo_m31_mul(b18, b100);
    unsigned b102 = stwo_m31_sub(b19, b87);
    unsigned b103 = stwo_m31_mul(b19, b102);
    unsigned b104 = stwo_m31_sub(b20, b87);
    unsigned b105 = stwo_m31_mul(b20, b104);
    unsigned b106 = stwo_m31_sub(b21, b87);
    unsigned b107 = stwo_m31_mul(b21, b106);
    unsigned b108 = stwo_m31_sub(b22, b87);
    unsigned b109 = stwo_m31_mul(b22, b108);
    unsigned b110 = stwo_m31_sub(b23, b87);
    unsigned b111 = stwo_m31_mul(b23, b110);
    unsigned b112 = stwo_m31_sub(b24, b87);
    unsigned b113 = stwo_m31_mul(b24, b112);
    unsigned b114 = stwo_m31_sub(b31, b87);
    unsigned b115 = stwo_m31_mul(b31, b114);
    unsigned b116 = stwo_m31_add(b10, b11);
    unsigned b117 = stwo_m31_add(b9, b116);
    unsigned b118 = stwo_m31_add(b8, b117);
    unsigned b119 = stwo_m31_sub(b118, b1);
    unsigned b120 = stwo_m31_sub(b87, b1);
    unsigned b121 = stwo_m31_mul(b2, b120);
    unsigned b122 = stwo_m31_sub(b87, b8);
    unsigned b123 = stwo_m31_mul(b2, b122);
    unsigned b124 = arena[args->base_params + 1u];
    unsigned b125 = stwo_m31_mul(b124, b19);
    unsigned b126 = arena[args->base_params + 2u];
    unsigned b127 = stwo_m31_mul(b126, b20);
    unsigned b128 = arena[args->base_params + 3u];
    unsigned b129 = stwo_m31_mul(b128, b21);
    unsigned b130 = stwo_m31_add(b127, b129);
    unsigned b131 = stwo_m31_add(b125, b130);
    unsigned b132 = stwo_m31_add(b18, b131);
    unsigned b133 = stwo_m31_mul(b7, b132);
    unsigned b134 = stwo_m31_add(b25, b133);
    unsigned b135 = stwo_m31_sub(b27, b134);
    unsigned b136 = stwo_m31_mul(b18, b22);
    unsigned b137 = stwo_m31_mul(b19, b23);
    unsigned b138 = stwo_m31_mul(b21, b24);
    unsigned b139 = stwo_m31_add(b137, b138);
    unsigned b140 = stwo_m31_add(b136, b139);
    unsigned b141 = stwo_m31_sub(b28, b140);
    unsigned b142 = stwo_m31_mul(b9, b28);
    unsigned b143 = stwo_m31_sub(b29, b142);
    unsigned b144 = stwo_m31_sub(b87, b31);
    unsigned b145 = stwo_m31_mul(b29, b144);
    unsigned b146 = stwo_m31_sub(b30, b145);
    unsigned b147 = stwo_m31_sub(b87, b24);
    unsigned b148 = stwo_m31_mul(b31, b147);
    unsigned b149 = stwo_m31_sub(b87, b29);
    unsigned b150 = stwo_m31_mul(b31, b149);
    unsigned b151 = stwo_m31_mul(b30, b24);
    unsigned b152 = stwo_m31_sub(b32, b151);
    unsigned b153 = stwo_m31_sub(b7, b87);
    unsigned b154 = stwo_m31_mul(b7, b153);
    unsigned b155 = stwo_m31_mul(b32, b154);
    unsigned b156 = stwo_m31_sub(b33, b87);
    unsigned b157 = stwo_m31_mul(b33, b156);
    unsigned b158 = stwo_m31_mul(b33, b27);
    unsigned b159 = stwo_m31_sub(b87, b33);
    unsigned b160 = stwo_m31_mul(b27, b34);
    unsigned b161 = stwo_m31_sub(b160, b87);
    unsigned b162 = stwo_m31_mul(b159, b161);
    unsigned b163 = stwo_m31_sub(b35, b87);
    unsigned b164 = stwo_m31_mul(b35, b163);
    unsigned b165 = stwo_m31_sub(b26, b87);
    unsigned b166 = stwo_m31_mul(b35, b165);
    unsigned b167 = stwo_m31_sub(b87, b35);
    unsigned b168 = stwo_m31_mul(b165, b36);
    unsigned b169 = stwo_m31_sub(b168, b87);
    unsigned b170 = stwo_m31_mul(b167, b169);
    unsigned b171 = stwo_m31_sub(b38, b87);
    unsigned b172 = stwo_m31_mul(b38, b171);
    unsigned b173 = stwo_m31_sub(b6, b87);
    unsigned b174 = stwo_m31_mul(b38, b173);
    unsigned b175 = stwo_m31_sub(b87, b38);
    unsigned b176 = stwo_m31_mul(b173, b39);
    unsigned b177 = stwo_m31_sub(b176, b87);
    unsigned b178 = stwo_m31_mul(b175, b177);
    unsigned b179 = stwo_m31_add(b14, b15);
    unsigned b180 = stwo_m31_add(b13, b179);
    unsigned b181 = stwo_m31_add(b17, b180);
    unsigned b182 = stwo_m31_sub(b87, b181);
    unsigned b183 = stwo_m31_mul(b8, b182);
    unsigned b184 = stwo_m31_mul(b30, b33);
    unsigned b185 = stwo_m31_mul(b10, b35);
    unsigned b186 = stwo_m31_add(b184, b185);
    unsigned b187 = stwo_m31_add(b183, b186);
    unsigned b188 = stwo_m31_sub(b41, b187);
    unsigned b189 = stwo_m31_mul(b8, b17);
    unsigned b190 = stwo_m31_mul(b30, b159);
    unsigned b191 = stwo_m31_mul(b10, b167);
    unsigned b192 = stwo_m31_add(b190, b191);
    unsigned b193 = stwo_m31_add(b189, b192);
    unsigned b194 = stwo_m31_sub(b45, b193);
    unsigned b195 = stwo_m31_mul(b8, b180);
    unsigned b196 = stwo_m31_sub(b9, b29);
    unsigned b197 = stwo_m31_add(b195, b196);
    unsigned b198 = stwo_m31_sub(b43, b197);
    unsigned b199 = stwo_m31_mul(b29, b31);
    unsigned b200 = stwo_m31_add(b199, b11);
    unsigned b201 = stwo_m31_sub(b47, b200);
    unsigned b202 = stwo_m31_mul(b8, b12);
    unsigned b203 = stwo_m31_mul(b30, b27);
    unsigned b204 = stwo_m31_mul(b10, b165);
    unsigned b205 = stwo_m31_add(b203, b204);
    unsigned b206 = stwo_m31_add(b202, b205);
    unsigned b207 = stwo_m31_sub(b49, b206);
    unsigned b208 = stwo_m31_mul(b196, b27);
    unsigned b209 = stwo_m31_sub(b51, b208);
    unsigned b210 = stwo_m31_sub(b53, b195);
    unsigned b211 = stwo_m31_mul(b196, b18);
    unsigned b212 = stwo_m31_sub(b55, b211);
    unsigned b213 = stwo_m31_mul(b196, b19);
    unsigned b214 = stwo_m31_sub(b57, b213);
    unsigned b215 = stwo_m31_mul(b196, b20);
    unsigned b216 = stwo_m31_sub(b59, b215);
    unsigned b217 = stwo_m31_mul(b8, b13);
    unsigned b218 = stwo_m31_mul(b196, b22);
    unsigned b219 = stwo_m31_add(b217, b218);
    unsigned b220 = stwo_m31_sub(b61, b219);
    unsigned b221 = stwo_m31_mul(b8, b14);
    unsigned b222 = stwo_m31_mul(b196, b23);
    unsigned b223 = stwo_m31_add(b221, b222);
    unsigned b224 = stwo_m31_sub(b63, b223);
    unsigned b225 = stwo_m31_mul(b8, b15);
    unsigned b226 = stwo_m31_mul(b196, b24);
    unsigned b227 = stwo_m31_add(b225, b226);
    unsigned b228 = stwo_m31_sub(b65, b227);
    unsigned b229 = stwo_m31_sub(b87, b2);
    unsigned b230 = stwo_m31_mul(b1, b229);
    unsigned b231 = stwo_m31_sub(b68, b230);
    unsigned b232 = stwo_m31_sub(b8, b40);
    unsigned b233 = stwo_m31_mul(b68, b232);
    unsigned b234 = stwo_m31_sub(b9, b42);
    unsigned b235 = stwo_m31_mul(b68, b234);
    unsigned b236 = stwo_m31_sub(b10, b44);
    unsigned b237 = stwo_m31_mul(b68, b236);
    unsigned b238 = stwo_m31_sub(b11, b46);
    unsigned b239 = stwo_m31_mul(b68, b238);
    unsigned b240 = stwo_m31_sub(b26, b48);
    unsigned b241 = stwo_m31_mul(b68, b240);
    unsigned b242 = stwo_m31_sub(b25, b50);
    unsigned b243 = stwo_m31_mul(b68, b242);
    unsigned b244 = stwo_m31_sub(b18, b52);
    unsigned b245 = stwo_m31_mul(b68, b244);
    unsigned b246 = stwo_m31_sub(b19, b54);
    unsigned b247 = stwo_m31_mul(b68, b246);
    unsigned b248 = stwo_m31_sub(b20, b56);
    unsigned b249 = stwo_m31_mul(b68, b248);
    unsigned b250 = stwo_m31_sub(b21, b58);
    unsigned b251 = stwo_m31_mul(b68, b250);
    unsigned b252 = stwo_m31_sub(b22, b60);
    unsigned b253 = stwo_m31_mul(b68, b252);
    unsigned b254 = stwo_m31_sub(b23, b62);
    unsigned b255 = stwo_m31_mul(b68, b254);
    unsigned b256 = stwo_m31_sub(b24, b64);
    unsigned b257 = stwo_m31_mul(b68, b256);
    unsigned b258 = stwo_m31_sub(b4, b3);
    unsigned b259 = stwo_m31_sub(b258, b87);
    unsigned b260 = stwo_m31_mul(b68, b259);
    unsigned b261 = stwo_m31_sub(b6, b5);
    unsigned b262 = stwo_m31_add(b261, b87);
    unsigned b263 = stwo_m31_mul(b68, b262);
    unsigned b264 = stwo_m31_mul(b68, b37);
    unsigned b265 = stwo_m31_mul(b69, b230);
    unsigned b266 = stwo_m31_sub(b87, b69);
    unsigned b267 = stwo_m31_sub(b87, b0);
    unsigned b268 = stwo_m31_mul(b1, b267);
    unsigned b269 = stwo_m31_mul(b266, b268);
    unsigned b270 = stwo_m31_sub(b87, b37);
    unsigned b271 = stwo_m31_mul(b2, b270);
    unsigned b272 = stwo_m31_mul(b266, b271);
    unsigned b273 = stwo_m31_sub(b0, b1);
    unsigned b274 = stwo_m31_mul(b273, b270);
    unsigned b275 = stwo_m31_mul(b266, b274);
    unsigned b276 = stwo_m31_sub(b87, b70);
    unsigned b277 = stwo_m31_mul(b276, b1);
    unsigned b278 = stwo_m31_mul(b8, b16);
    unsigned b279 = stwo_m31_sub(b67, b278);
    unsigned b280 = stwo_m31_mul(b69, b279);
    unsigned b281 = stwo_m31_sub(b67, b66);
    unsigned b282 = stwo_m31_sub(b281, b278);
    unsigned b283 = stwo_m31_mul(b266, b282);
    unsigned b284 = stwo_m31_neg(b2);
    unsigned b285 = stwo_m31_neg(b1);
    unsigned b286 = stwo_m31_neg(b8);
    unsigned b287 = stwo_m31_neg(b31);
    unsigned b288 = arena[args->base_params + 4u];
    unsigned b289 = stwo_m31_sub(b7, b288);
    unsigned b290 = arena[args->base_params + 5u];
    StwoCairoQm31 e0 = { b89, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b91, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b93, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b95, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b97, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b99, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b101, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b103, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b105, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b107, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b109, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b111, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b113, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b115, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b119, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b121, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b123, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b135, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b141, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b143, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b146, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b148, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b150, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b152, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b155, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b157, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b158, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b162, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b164, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b166, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b170, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b172, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b174, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b178, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b188, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b194, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b198, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b201, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b207, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b209, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b210, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b212, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b214, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b216, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b220, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b224, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b228, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b231, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = { b233, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e48, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e49 = { b235, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e49, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e50 = { b237, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e50, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
    StwoCairoQm31 e51 = { b239, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e51, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 51u) * 4u)));
    StwoCairoQm31 e52 = { b241, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e52, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 52u) * 4u)));
    StwoCairoQm31 e53 = { b243, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e53, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 53u) * 4u)));
    StwoCairoQm31 e54 = { b245, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e54, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 54u) * 4u)));
    StwoCairoQm31 e55 = { b247, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e55, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 55u) * 4u)));
    StwoCairoQm31 e56 = { b249, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e56, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 56u) * 4u)));
    StwoCairoQm31 e57 = { b251, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e57, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 57u) * 4u)));
    StwoCairoQm31 e58 = { b253, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e58, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 58u) * 4u)));
    StwoCairoQm31 e59 = { b255, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e59, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 59u) * 4u)));
    StwoCairoQm31 e60 = { b257, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e60, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 60u) * 4u)));
    StwoCairoQm31 e61 = { b260, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e61, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 61u) * 4u)));
    StwoCairoQm31 e62 = { b263, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e62, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 62u) * 4u)));
    StwoCairoQm31 e63 = { b264, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e63, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 63u) * 4u)));
    StwoCairoQm31 e64 = { b265, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e64, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 64u) * 4u)));
    StwoCairoQm31 e65 = { b269, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e65, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 65u) * 4u)));
    StwoCairoQm31 e66 = { b272, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e66, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 66u) * 4u)));
    StwoCairoQm31 e67 = { b275, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e67, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 67u) * 4u)));
    StwoCairoQm31 e68 = { b277, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e68, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 68u) * 4u)));
    StwoCairoQm31 e69 = { b280, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e69, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 69u) * 4u)));
    StwoCairoQm31 e70 = { b283, b290, b290, b290 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e70, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 70u) * 4u)));
    StwoCairoQm31 e71 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e72 = stwo_load_qm31(arena, args->ext_params + 8u * 4u);
    StwoCairoQm31 e73 = { b284, b290, b290, b290 };
    StwoCairoQm31 e74 = { 11u, 0u, 0u, 0u };
    StwoCairoQm31 e75 = { b4, b290, b290, b290 };
    StwoCairoQm31 e76 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e77 = stwo_qm31_mul(e75, e76);
    StwoCairoQm31 e78 = stwo_qm31_add(e74, e77);
    StwoCairoQm31 e79 = { b6, b290, b290, b290 };
    StwoCairoQm31 e80 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e81 = stwo_qm31_mul(e79, e80);
    StwoCairoQm31 e82 = stwo_qm31_add(e78, e81);
    StwoCairoQm31 e83 = stwo_qm31_sub(e82, e71);
    StwoCairoQm31 e84 = { b285, b290, b290, b290 };
    StwoCairoQm31 e85 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e86 = { b4, b290, b290, b290 };
    StwoCairoQm31 e87 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e88 = stwo_qm31_mul(e86, e87);
    StwoCairoQm31 e89 = stwo_qm31_add(e85, e88);
    StwoCairoQm31 e90 = { b7, b290, b290, b290 };
    StwoCairoQm31 e91 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e92 = stwo_qm31_mul(e90, e91);
    StwoCairoQm31 e93 = stwo_qm31_add(e89, e92);
    StwoCairoQm31 e94 = stwo_qm31_sub(e93, e71);
    StwoCairoQm31 e95 = { b286, b290, b290, b290 };
    StwoCairoQm31 e96 = { 10u, 0u, 0u, 0u };
    StwoCairoQm31 e97 = { b7, b290, b290, b290 };
    StwoCairoQm31 e98 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e99 = stwo_qm31_mul(e97, e98);
    StwoCairoQm31 e100 = stwo_qm31_add(e96, e99);
    StwoCairoQm31 e101 = { b12, b290, b290, b290 };
    StwoCairoQm31 e102 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e103 = stwo_qm31_mul(e101, e102);
    StwoCairoQm31 e104 = stwo_qm31_add(e100, e103);
    StwoCairoQm31 e105 = { b13, b290, b290, b290 };
    StwoCairoQm31 e106 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e107 = stwo_qm31_mul(e105, e106);
    StwoCairoQm31 e108 = stwo_qm31_add(e104, e107);
    StwoCairoQm31 e109 = { b14, b290, b290, b290 };
    StwoCairoQm31 e110 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e111 = stwo_qm31_mul(e109, e110);
    StwoCairoQm31 e112 = stwo_qm31_add(e108, e111);
    StwoCairoQm31 e113 = { b15, b290, b290, b290 };
    StwoCairoQm31 e114 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e115 = stwo_qm31_mul(e113, e114);
    StwoCairoQm31 e116 = stwo_qm31_add(e112, e115);
    StwoCairoQm31 e117 = { b16, b290, b290, b290 };
    StwoCairoQm31 e118 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e119 = stwo_qm31_mul(e117, e118);
    StwoCairoQm31 e120 = stwo_qm31_add(e116, e119);
    StwoCairoQm31 e121 = { b17, b290, b290, b290 };
    StwoCairoQm31 e122 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e123 = stwo_qm31_mul(e121, e122);
    StwoCairoQm31 e124 = stwo_qm31_add(e120, e123);
    StwoCairoQm31 e125 = stwo_qm31_sub(e124, e71);
    StwoCairoQm31 e126 = { b287, b290, b290, b290 };
    StwoCairoQm31 e127 = { 9u, 0u, 0u, 0u };
    StwoCairoQm31 e128 = { b289, b290, b290, b290 };
    StwoCairoQm31 e129 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e130 = stwo_qm31_mul(e128, e129);
    StwoCairoQm31 e131 = stwo_qm31_add(e127, e130);
    StwoCairoQm31 e132 = stwo_qm31_sub(e131, e71);
    StwoCairoQm31 e133 = { b276, b290, b290, b290 };
    StwoCairoQm31 e134 = { 15u, 0u, 0u, 0u };
    StwoCairoQm31 e135 = { b67, b290, b290, b290 };
    StwoCairoQm31 e136 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e137 = stwo_qm31_mul(e135, e136);
    StwoCairoQm31 e138 = stwo_qm31_add(e134, e137);
    StwoCairoQm31 e139 = stwo_qm31_sub(e138, e71);
    StwoCairoQm31 e140 = { b71, b72, b73, b74 };
    StwoCairoQm31 e141 = { b75, b76, b77, b78 };
    StwoCairoQm31 e142 = { b80, b82, b84, b86 };
    StwoCairoQm31 e143 = { b79, b81, b83, b85 };
    StwoCairoQm31 e144 = stwo_qm31_mul(e73, e94);
    StwoCairoQm31 e145 = stwo_qm31_mul(e84, e83);
    StwoCairoQm31 e146 = stwo_qm31_add(e144, e145);
    StwoCairoQm31 e147 = stwo_qm31_mul(e83, e94);
    StwoCairoQm31 e148 = stwo_qm31_mul(e140, e147);
    StwoCairoQm31 e149 = stwo_qm31_sub(e148, e146);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e149, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 71u) * 4u)));
    StwoCairoQm31 e150 = stwo_qm31_mul(e95, e132);
    StwoCairoQm31 e151 = stwo_qm31_mul(e126, e125);
    StwoCairoQm31 e152 = stwo_qm31_add(e150, e151);
    StwoCairoQm31 e153 = stwo_qm31_mul(e125, e132);
    StwoCairoQm31 e154 = stwo_qm31_sub(e141, e140);
    StwoCairoQm31 e155 = stwo_qm31_mul(e154, e153);
    StwoCairoQm31 e156 = stwo_qm31_sub(e155, e152);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e156, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 72u) * 4u)));
    StwoCairoQm31 e157 = stwo_qm31_sub(e142, e143);
    StwoCairoQm31 e158 = stwo_qm31_sub(e157, e141);
    StwoCairoQm31 e159 = stwo_qm31_add(e158, e72);
    StwoCairoQm31 e160 = stwo_qm31_mul(e159, e139);
    StwoCairoQm31 e161 = stwo_qm31_sub(e160, e133);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e161, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 73u) * 4u)));
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
