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
stwo_cairo_cuda_eval_v6_ee5278456b6a0ec0(
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
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 14u, row, -1);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 16u, row, -1);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 17u, row, -1);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 21u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 0u, 2u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 0u, 3u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 0u, 4u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 0u, 5u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 0u, 6u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 2u, 16u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 17u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 18u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 19u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 20u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 21u, row, 0);
    unsigned b58 = stwo_trace_value(arena, *args, 2u, 22u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 2u, 23u, row, 0);
    unsigned b60 = stwo_trace_value(arena, *args, 2u, 24u, row, -1);
    unsigned b61 = stwo_trace_value(arena, *args, 2u, 24u, row, 0);
    unsigned b62 = stwo_trace_value(arena, *args, 2u, 25u, row, -1);
    unsigned b63 = stwo_trace_value(arena, *args, 2u, 25u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 2u, 26u, row, -1);
    unsigned b65 = stwo_trace_value(arena, *args, 2u, 26u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 2u, 27u, row, -1);
    unsigned b67 = stwo_trace_value(arena, *args, 2u, 27u, row, 0);
    unsigned b68 = arena[args->base_params + 0u];
    unsigned b69 = stwo_m31_sub(b1, b68);
    unsigned b70 = stwo_m31_mul(b1, b69);
    unsigned b71 = stwo_m31_sub(b20, b68);
    unsigned b72 = stwo_m31_mul(b20, b71);
    unsigned b73 = stwo_m31_sub(b10, b68);
    unsigned b74 = stwo_m31_mul(b10, b73);
    unsigned b75 = stwo_m31_sub(b11, b68);
    unsigned b76 = stwo_m31_mul(b11, b75);
    unsigned b77 = stwo_m31_sub(b12, b68);
    unsigned b78 = stwo_m31_mul(b12, b77);
    unsigned b79 = stwo_m31_sub(b14, b68);
    unsigned b80 = stwo_m31_mul(b14, b79);
    unsigned b81 = stwo_m31_sub(b15, b68);
    unsigned b82 = stwo_m31_mul(b15, b81);
    unsigned b83 = stwo_m31_sub(b16, b68);
    unsigned b84 = stwo_m31_mul(b16, b83);
    unsigned b85 = stwo_m31_sub(b17, b68);
    unsigned b86 = stwo_m31_mul(b17, b85);
    unsigned b87 = stwo_m31_sub(b19, b68);
    unsigned b88 = stwo_m31_mul(b19, b87);
    unsigned b89 = stwo_m31_sub(b68, b1);
    unsigned b90 = stwo_m31_mul(b29, b89);
    unsigned b91 = stwo_m31_mul(b29, b4);
    unsigned b92 = stwo_m31_sub(b68, b30);
    unsigned b93 = stwo_m31_mul(b92, b1);
    unsigned b94 = stwo_m31_sub(b68, b29);
    unsigned b95 = stwo_m31_sub(b68, b0);
    unsigned b96 = stwo_m31_mul(b1, b95);
    unsigned b97 = stwo_m31_mul(b94, b96);
    unsigned b98 = stwo_m31_mul(b94, b1);
    unsigned b99 = stwo_m31_sub(b26, b98);
    unsigned b100 = stwo_m31_add(b3, b68);
    unsigned b101 = stwo_m31_mul(b26, b100);
    unsigned b102 = stwo_m31_sub(b4, b101);
    unsigned b103 = stwo_m31_mul(b32, b102);
    unsigned b104 = stwo_m31_sub(b68, b32);
    unsigned b105 = stwo_m31_sub(b4, b3);
    unsigned b106 = stwo_m31_mul(b104, b105);
    unsigned b107 = arena[args->base_params + 1u];
    unsigned b108 = stwo_m31_mul(b107, b4);
    unsigned b109 = arena[args->base_params + 2u];
    unsigned b110 = stwo_m31_mul(b109, b31);
    unsigned b111 = stwo_m31_add(b108, b110);
    unsigned b112 = stwo_m31_sub(b5, b111);
    unsigned b113 = arena[args->base_params + 3u];
    unsigned b114 = arena[args->base_params + 4u];
    unsigned b115 = stwo_m31_sub(b113, b114);
    unsigned b116 = stwo_m31_sub(b4, b115);
    unsigned b117 = stwo_m31_mul(b20, b116);
    unsigned b118 = stwo_m31_mul(b116, b25);
    unsigned b119 = stwo_m31_sub(b68, b20);
    unsigned b120 = stwo_m31_sub(b118, b119);
    unsigned b121 = stwo_m31_mul(b29, b20);
    unsigned b122 = stwo_m31_sub(b68, b2);
    unsigned b123 = stwo_m31_mul(b1, b122);
    unsigned b124 = stwo_m31_sub(b27, b123);
    unsigned b125 = stwo_m31_mul(b27, b119);
    unsigned b126 = stwo_m31_sub(b68, b33);
    unsigned b127 = stwo_m31_mul(b27, b126);
    unsigned b128 = stwo_m31_mul(b33, b2);
    unsigned b129 = stwo_m31_mul(b20, b128);
    unsigned b130 = stwo_m31_mul(b1, b119);
    unsigned b131 = stwo_m31_sub(b28, b130);
    unsigned b132 = stwo_m31_sub(b68, b13);
    unsigned b133 = stwo_m31_mul(b10, b132);
    unsigned b134 = stwo_m31_mul(b104, b133);
    unsigned b135 = stwo_m31_sub(b68, b10);
    unsigned b136 = stwo_m31_mul(b32, b135);
    unsigned b137 = stwo_m31_mul(b20, b136);
    unsigned b138 = stwo_m31_mul(b104, b21);
    unsigned b139 = stwo_m31_add(b10, b11);
    unsigned b140 = stwo_m31_add(b12, b14);
    unsigned b141 = stwo_m31_add(b139, b140);
    unsigned b142 = stwo_m31_add(b138, b141);
    unsigned b143 = stwo_m31_sub(b22, b142);
    unsigned b144 = arena[args->base_params + 5u];
    unsigned b145 = stwo_m31_sub(b22, b144);
    unsigned b146 = stwo_m31_mul(b27, b145);
    unsigned b147 = stwo_m31_mul(b107, b115);
    unsigned b148 = stwo_m31_add(b144, b147);
    unsigned b149 = arena[args->base_params + 6u];
    unsigned b150 = arena[args->base_params + 7u];
    unsigned b151 = stwo_m31_add(b149, b150);
    unsigned b152 = stwo_m31_sub(b148, b151);
    unsigned b153 = stwo_m31_mul(b29, b152);
    unsigned b154 = stwo_m31_sub(b68, b18);
    unsigned b155 = stwo_m31_mul(b15, b154);
    unsigned b156 = stwo_m31_mul(b104, b155);
    unsigned b157 = stwo_m31_mul(b104, b23);
    unsigned b158 = stwo_m31_add(b15, b16);
    unsigned b159 = stwo_m31_add(b17, b19);
    unsigned b160 = stwo_m31_add(b158, b159);
    unsigned b161 = stwo_m31_add(b157, b160);
    unsigned b162 = stwo_m31_sub(b24, b161);
    unsigned b163 = stwo_m31_sub(b34, b35);
    unsigned b164 = stwo_m31_sub(b24, b149);
    unsigned b165 = stwo_m31_mul(b163, b164);
    unsigned b166 = stwo_m31_mul(b28, b135);
    unsigned b167 = stwo_m31_sub(b68, b11);
    unsigned b168 = stwo_m31_mul(b28, b167);
    unsigned b169 = stwo_m31_sub(b68, b12);
    unsigned b170 = stwo_m31_mul(b28, b169);
    unsigned b171 = stwo_m31_sub(b68, b14);
    unsigned b172 = stwo_m31_mul(b28, b171);
    unsigned b173 = stwo_m31_mul(b10, b89);
    unsigned b174 = stwo_m31_mul(b11, b89);
    unsigned b175 = stwo_m31_mul(b12, b89);
    unsigned b176 = stwo_m31_mul(b14, b89);
    unsigned b177 = stwo_m31_mul(b6, b135);
    unsigned b178 = stwo_m31_mul(b7, b167);
    unsigned b179 = stwo_m31_mul(b8, b169);
    unsigned b180 = stwo_m31_mul(b9, b171);
    unsigned b181 = stwo_m31_mul(b11, b135);
    unsigned b182 = stwo_m31_mul(b12, b167);
    unsigned b183 = stwo_m31_mul(b14, b169);
    unsigned b184 = stwo_m31_mul(b15, b4);
    unsigned b185 = stwo_m31_mul(b16, b4);
    unsigned b186 = stwo_m31_mul(b17, b4);
    unsigned b187 = stwo_m31_mul(b19, b4);
    unsigned b188 = stwo_m31_mul(b15, b135);
    unsigned b189 = stwo_m31_mul(b16, b167);
    unsigned b190 = stwo_m31_mul(b17, b169);
    unsigned b191 = stwo_m31_mul(b19, b171);
    unsigned b192 = stwo_m31_sub(b68, b15);
    unsigned b193 = stwo_m31_mul(b16, b192);
    unsigned b194 = stwo_m31_sub(b68, b16);
    unsigned b195 = stwo_m31_mul(b17, b194);
    unsigned b196 = stwo_m31_sub(b68, b17);
    unsigned b197 = stwo_m31_mul(b19, b196);
    unsigned b198 = stwo_m31_neg(b15);
    unsigned b199 = arena[args->base_params + 8u];
    unsigned b200 = stwo_m31_add(b5, b199);
    unsigned b201 = stwo_m31_neg(b16);
    unsigned b202 = stwo_m31_add(b5, b68);
    unsigned b203 = stwo_m31_neg(b17);
    unsigned b204 = arena[args->base_params + 9u];
    unsigned b205 = stwo_m31_add(b5, b204);
    unsigned b206 = stwo_m31_neg(b19);
    unsigned b207 = arena[args->base_params + 10u];
    unsigned b208 = stwo_m31_add(b5, b207);
    unsigned b209 = stwo_m31_sub(b10, b15);
    unsigned b210 = stwo_m31_neg(b209);
    unsigned b211 = stwo_m31_sub(b200, b149);
    unsigned b212 = stwo_m31_sub(b11, b16);
    unsigned b213 = stwo_m31_neg(b212);
    unsigned b214 = stwo_m31_sub(b202, b149);
    unsigned b215 = stwo_m31_sub(b12, b17);
    unsigned b216 = stwo_m31_neg(b215);
    unsigned b217 = stwo_m31_sub(b205, b149);
    unsigned b218 = stwo_m31_sub(b14, b19);
    unsigned b219 = stwo_m31_neg(b218);
    unsigned b220 = stwo_m31_sub(b208, b149);
    unsigned b221 = stwo_m31_mul(b20, b10);
    unsigned b222 = stwo_m31_neg(b221);
    unsigned b223 = stwo_m31_add(b110, b199);
    unsigned b224 = stwo_m31_mul(b20, b11);
    unsigned b225 = stwo_m31_neg(b224);
    unsigned b226 = stwo_m31_add(b110, b68);
    unsigned b227 = stwo_m31_mul(b20, b12);
    unsigned b228 = stwo_m31_neg(b227);
    unsigned b229 = stwo_m31_add(b110, b204);
    unsigned b230 = stwo_m31_mul(b20, b14);
    unsigned b231 = stwo_m31_neg(b230);
    unsigned b232 = stwo_m31_add(b110, b207);
    unsigned b233 = arena[args->base_params + 11u];
    unsigned b234 = stwo_m31_mul(b233, b7);
    unsigned b235 = stwo_m31_add(b6, b234);
    unsigned b236 = stwo_m31_mul(b233, b9);
    unsigned b237 = stwo_m31_add(b8, b236);
    unsigned b238 = stwo_m31_neg(b29);
    unsigned b239 = stwo_m31_sub(b115, b68);
    StwoCairoQm31 e0 = { b70, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b72, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b74, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b76, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b78, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b80, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b82, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b84, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b86, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b88, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b90, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b91, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b93, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b97, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b99, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b103, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b106, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b112, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b117, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b120, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b121, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b124, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b125, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b127, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b129, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b131, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b134, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b137, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b143, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b146, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b153, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b156, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b162, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b165, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b166, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b168, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b170, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b172, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b173, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b174, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b175, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b176, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b177, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b178, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b179, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b180, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b181, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b182, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = { b183, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e48, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e49 = { b184, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e49, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e50 = { b185, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e50, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
    StwoCairoQm31 e51 = { b186, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e51, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 51u) * 4u)));
    StwoCairoQm31 e52 = { b187, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e52, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 52u) * 4u)));
    StwoCairoQm31 e53 = { b188, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e53, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 53u) * 4u)));
    StwoCairoQm31 e54 = { b189, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e54, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 54u) * 4u)));
    StwoCairoQm31 e55 = { b190, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e55, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 55u) * 4u)));
    StwoCairoQm31 e56 = { b191, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e56, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 56u) * 4u)));
    StwoCairoQm31 e57 = { b193, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e57, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 57u) * 4u)));
    StwoCairoQm31 e58 = { b195, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e58, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 58u) * 4u)));
    StwoCairoQm31 e59 = { b197, b199, b199, b199 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e59, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 59u) * 4u)));
    StwoCairoQm31 e60 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e61 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e62 = { b198, b199, b199, b199 };
    StwoCairoQm31 e63 = { 26u, 0u, 0u, 0u };
    StwoCairoQm31 e64 = { b200, b199, b199, b199 };
    StwoCairoQm31 e65 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e66 = stwo_qm31_mul(e64, e65);
    StwoCairoQm31 e67 = stwo_qm31_add(e63, e66);
    StwoCairoQm31 e68 = { b6, b199, b199, b199 };
    StwoCairoQm31 e69 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e70 = stwo_qm31_mul(e68, e69);
    StwoCairoQm31 e71 = stwo_qm31_add(e67, e70);
    StwoCairoQm31 e72 = stwo_qm31_sub(e71, e60);
    StwoCairoQm31 e73 = { b201, b199, b199, b199 };
    StwoCairoQm31 e74 = { 26u, 0u, 0u, 0u };
    StwoCairoQm31 e75 = { b202, b199, b199, b199 };
    StwoCairoQm31 e76 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e77 = stwo_qm31_mul(e75, e76);
    StwoCairoQm31 e78 = stwo_qm31_add(e74, e77);
    StwoCairoQm31 e79 = { b7, b199, b199, b199 };
    StwoCairoQm31 e80 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e81 = stwo_qm31_mul(e79, e80);
    StwoCairoQm31 e82 = stwo_qm31_add(e78, e81);
    StwoCairoQm31 e83 = stwo_qm31_sub(e82, e60);
    StwoCairoQm31 e84 = { b203, b199, b199, b199 };
    StwoCairoQm31 e85 = { 26u, 0u, 0u, 0u };
    StwoCairoQm31 e86 = { b205, b199, b199, b199 };
    StwoCairoQm31 e87 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e88 = stwo_qm31_mul(e86, e87);
    StwoCairoQm31 e89 = stwo_qm31_add(e85, e88);
    StwoCairoQm31 e90 = { b8, b199, b199, b199 };
    StwoCairoQm31 e91 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e92 = stwo_qm31_mul(e90, e91);
    StwoCairoQm31 e93 = stwo_qm31_add(e89, e92);
    StwoCairoQm31 e94 = stwo_qm31_sub(e93, e60);
    StwoCairoQm31 e95 = { b206, b199, b199, b199 };
    StwoCairoQm31 e96 = { 26u, 0u, 0u, 0u };
    StwoCairoQm31 e97 = { b208, b199, b199, b199 };
    StwoCairoQm31 e98 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e99 = stwo_qm31_mul(e97, e98);
    StwoCairoQm31 e100 = stwo_qm31_add(e96, e99);
    StwoCairoQm31 e101 = { b9, b199, b199, b199 };
    StwoCairoQm31 e102 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e103 = stwo_qm31_mul(e101, e102);
    StwoCairoQm31 e104 = stwo_qm31_add(e100, e103);
    StwoCairoQm31 e105 = stwo_qm31_sub(e104, e60);
    StwoCairoQm31 e106 = { b210, b199, b199, b199 };
    StwoCairoQm31 e107 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e108 = { b211, b199, b199, b199 };
    StwoCairoQm31 e109 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e110 = stwo_qm31_mul(e108, e109);
    StwoCairoQm31 e111 = stwo_qm31_add(e107, e110);
    StwoCairoQm31 e112 = { b6, b199, b199, b199 };
    StwoCairoQm31 e113 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e114 = stwo_qm31_mul(e112, e113);
    StwoCairoQm31 e115 = stwo_qm31_add(e111, e114);
    StwoCairoQm31 e116 = stwo_qm31_sub(e115, e60);
    StwoCairoQm31 e117 = { b213, b199, b199, b199 };
    StwoCairoQm31 e118 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e119 = { b214, b199, b199, b199 };
    StwoCairoQm31 e120 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e121 = stwo_qm31_mul(e119, e120);
    StwoCairoQm31 e122 = stwo_qm31_add(e118, e121);
    StwoCairoQm31 e123 = { b7, b199, b199, b199 };
    StwoCairoQm31 e124 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e125 = stwo_qm31_mul(e123, e124);
    StwoCairoQm31 e126 = stwo_qm31_add(e122, e125);
    StwoCairoQm31 e127 = stwo_qm31_sub(e126, e60);
    StwoCairoQm31 e128 = { b216, b199, b199, b199 };
    StwoCairoQm31 e129 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e130 = { b217, b199, b199, b199 };
    StwoCairoQm31 e131 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e132 = stwo_qm31_mul(e130, e131);
    StwoCairoQm31 e133 = stwo_qm31_add(e129, e132);
    StwoCairoQm31 e134 = { b8, b199, b199, b199 };
    StwoCairoQm31 e135 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e136 = stwo_qm31_mul(e134, e135);
    StwoCairoQm31 e137 = stwo_qm31_add(e133, e136);
    StwoCairoQm31 e138 = stwo_qm31_sub(e137, e60);
    StwoCairoQm31 e139 = { b219, b199, b199, b199 };
    StwoCairoQm31 e140 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e141 = { b220, b199, b199, b199 };
    StwoCairoQm31 e142 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e143 = stwo_qm31_mul(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_add(e140, e143);
    StwoCairoQm31 e145 = { b9, b199, b199, b199 };
    StwoCairoQm31 e146 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e147 = stwo_qm31_mul(e145, e146);
    StwoCairoQm31 e148 = stwo_qm31_add(e144, e147);
    StwoCairoQm31 e149 = stwo_qm31_sub(e148, e60);
    StwoCairoQm31 e150 = { b222, b199, b199, b199 };
    StwoCairoQm31 e151 = { 27u, 0u, 0u, 0u };
    StwoCairoQm31 e152 = { b223, b199, b199, b199 };
    StwoCairoQm31 e153 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e154 = stwo_qm31_mul(e152, e153);
    StwoCairoQm31 e155 = stwo_qm31_add(e151, e154);
    StwoCairoQm31 e156 = { b6, b199, b199, b199 };
    StwoCairoQm31 e157 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e158 = stwo_qm31_mul(e156, e157);
    StwoCairoQm31 e159 = stwo_qm31_add(e155, e158);
    StwoCairoQm31 e160 = stwo_qm31_sub(e159, e60);
    StwoCairoQm31 e161 = { b225, b199, b199, b199 };
    StwoCairoQm31 e162 = { 27u, 0u, 0u, 0u };
    StwoCairoQm31 e163 = { b226, b199, b199, b199 };
    StwoCairoQm31 e164 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e165 = stwo_qm31_mul(e163, e164);
    StwoCairoQm31 e166 = stwo_qm31_add(e162, e165);
    StwoCairoQm31 e167 = { b7, b199, b199, b199 };
    StwoCairoQm31 e168 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e169 = stwo_qm31_mul(e167, e168);
    StwoCairoQm31 e170 = stwo_qm31_add(e166, e169);
    StwoCairoQm31 e171 = stwo_qm31_sub(e170, e60);
    StwoCairoQm31 e172 = { b228, b199, b199, b199 };
    StwoCairoQm31 e173 = { 27u, 0u, 0u, 0u };
    StwoCairoQm31 e174 = { b229, b199, b199, b199 };
    StwoCairoQm31 e175 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e176 = stwo_qm31_mul(e174, e175);
    StwoCairoQm31 e177 = stwo_qm31_add(e173, e176);
    StwoCairoQm31 e178 = { b8, b199, b199, b199 };
    StwoCairoQm31 e179 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e180 = stwo_qm31_mul(e178, e179);
    StwoCairoQm31 e181 = stwo_qm31_add(e177, e180);
    StwoCairoQm31 e182 = stwo_qm31_sub(e181, e60);
    StwoCairoQm31 e183 = { b231, b199, b199, b199 };
    StwoCairoQm31 e184 = { 27u, 0u, 0u, 0u };
    StwoCairoQm31 e185 = { b232, b199, b199, b199 };
    StwoCairoQm31 e186 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e187 = stwo_qm31_mul(e185, e186);
    StwoCairoQm31 e188 = stwo_qm31_add(e184, e187);
    StwoCairoQm31 e189 = { b9, b199, b199, b199 };
    StwoCairoQm31 e190 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e191 = stwo_qm31_mul(e189, e190);
    StwoCairoQm31 e192 = stwo_qm31_add(e188, e191);
    StwoCairoQm31 e193 = stwo_qm31_sub(e192, e60);
    StwoCairoQm31 e194 = { b28, b199, b199, b199 };
    StwoCairoQm31 e195 = { 30u, 0u, 0u, 0u };
    StwoCairoQm31 e196 = { b4, b199, b199, b199 };
    StwoCairoQm31 e197 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e198 = stwo_qm31_mul(e196, e197);
    StwoCairoQm31 e199 = stwo_qm31_add(e195, e198);
    StwoCairoQm31 e200 = { b31, b199, b199, b199 };
    StwoCairoQm31 e201 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e202 = stwo_qm31_mul(e200, e201);
    StwoCairoQm31 e203 = stwo_qm31_add(e199, e202);
    StwoCairoQm31 e204 = { b235, b199, b199, b199 };
    StwoCairoQm31 e205 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e206 = stwo_qm31_mul(e204, e205);
    StwoCairoQm31 e207 = stwo_qm31_add(e203, e206);
    StwoCairoQm31 e208 = { b237, b199, b199, b199 };
    StwoCairoQm31 e209 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e210 = stwo_qm31_mul(e208, e209);
    StwoCairoQm31 e211 = stwo_qm31_add(e207, e210);
    StwoCairoQm31 e212 = stwo_qm31_sub(e211, e60);
    StwoCairoQm31 e213 = { b238, b199, b199, b199 };
    StwoCairoQm31 e214 = { 31u, 0u, 0u, 0u };
    StwoCairoQm31 e215 = { b239, b199, b199, b199 };
    StwoCairoQm31 e216 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e217 = stwo_qm31_mul(e215, e216);
    StwoCairoQm31 e218 = stwo_qm31_add(e214, e217);
    StwoCairoQm31 e219 = stwo_qm31_sub(e218, e60);
    StwoCairoQm31 e220 = { b36, b37, b38, b39 };
    StwoCairoQm31 e221 = { b40, b41, b42, b43 };
    StwoCairoQm31 e222 = { b44, b45, b46, b47 };
    StwoCairoQm31 e223 = { b48, b49, b50, b51 };
    StwoCairoQm31 e224 = { b52, b53, b54, b55 };
    StwoCairoQm31 e225 = { b56, b57, b58, b59 };
    StwoCairoQm31 e226 = { b61, b63, b65, b67 };
    StwoCairoQm31 e227 = { b60, b62, b64, b66 };
    StwoCairoQm31 e228 = stwo_qm31_mul(e62, e83);
    StwoCairoQm31 e229 = stwo_qm31_mul(e73, e72);
    StwoCairoQm31 e230 = stwo_qm31_add(e228, e229);
    StwoCairoQm31 e231 = stwo_qm31_mul(e72, e83);
    StwoCairoQm31 e232 = stwo_qm31_mul(e220, e231);
    StwoCairoQm31 e233 = stwo_qm31_sub(e232, e230);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e233, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 60u) * 4u)));
    StwoCairoQm31 e234 = stwo_qm31_mul(e84, e105);
    StwoCairoQm31 e235 = stwo_qm31_mul(e95, e94);
    StwoCairoQm31 e236 = stwo_qm31_add(e234, e235);
    StwoCairoQm31 e237 = stwo_qm31_mul(e94, e105);
    StwoCairoQm31 e238 = stwo_qm31_sub(e221, e220);
    StwoCairoQm31 e239 = stwo_qm31_mul(e238, e237);
    StwoCairoQm31 e240 = stwo_qm31_sub(e239, e236);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e240, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 61u) * 4u)));
    StwoCairoQm31 e241 = stwo_qm31_mul(e106, e127);
    StwoCairoQm31 e242 = stwo_qm31_mul(e117, e116);
    StwoCairoQm31 e243 = stwo_qm31_add(e241, e242);
    StwoCairoQm31 e244 = stwo_qm31_mul(e116, e127);
    StwoCairoQm31 e245 = stwo_qm31_sub(e222, e221);
    StwoCairoQm31 e246 = stwo_qm31_mul(e245, e244);
    StwoCairoQm31 e247 = stwo_qm31_sub(e246, e243);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e247, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 62u) * 4u)));
    StwoCairoQm31 e248 = stwo_qm31_mul(e128, e149);
    StwoCairoQm31 e249 = stwo_qm31_mul(e139, e138);
    StwoCairoQm31 e250 = stwo_qm31_add(e248, e249);
    StwoCairoQm31 e251 = stwo_qm31_mul(e138, e149);
    StwoCairoQm31 e252 = stwo_qm31_sub(e223, e222);
    StwoCairoQm31 e253 = stwo_qm31_mul(e252, e251);
    StwoCairoQm31 e254 = stwo_qm31_sub(e253, e250);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e254, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 63u) * 4u)));
    StwoCairoQm31 e255 = stwo_qm31_mul(e150, e171);
    StwoCairoQm31 e256 = stwo_qm31_mul(e161, e160);
    StwoCairoQm31 e257 = stwo_qm31_add(e255, e256);
    StwoCairoQm31 e258 = stwo_qm31_mul(e160, e171);
    StwoCairoQm31 e259 = stwo_qm31_sub(e224, e223);
    StwoCairoQm31 e260 = stwo_qm31_mul(e259, e258);
    StwoCairoQm31 e261 = stwo_qm31_sub(e260, e257);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e261, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 64u) * 4u)));
    StwoCairoQm31 e262 = stwo_qm31_mul(e172, e193);
    StwoCairoQm31 e263 = stwo_qm31_mul(e183, e182);
    StwoCairoQm31 e264 = stwo_qm31_add(e262, e263);
    StwoCairoQm31 e265 = stwo_qm31_mul(e182, e193);
    StwoCairoQm31 e266 = stwo_qm31_sub(e225, e224);
    StwoCairoQm31 e267 = stwo_qm31_mul(e266, e265);
    StwoCairoQm31 e268 = stwo_qm31_sub(e267, e264);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e268, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 65u) * 4u)));
    StwoCairoQm31 e269 = stwo_qm31_mul(e194, e219);
    StwoCairoQm31 e270 = stwo_qm31_mul(e213, e212);
    StwoCairoQm31 e271 = stwo_qm31_add(e269, e270);
    StwoCairoQm31 e272 = stwo_qm31_mul(e212, e219);
    StwoCairoQm31 e273 = stwo_qm31_sub(e226, e227);
    StwoCairoQm31 e274 = stwo_qm31_sub(e273, e225);
    StwoCairoQm31 e275 = stwo_qm31_add(e274, e61);
    StwoCairoQm31 e276 = stwo_qm31_mul(e275, e272);
    StwoCairoQm31 e277 = stwo_qm31_sub(e276, e271);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e277, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 66u) * 4u)));
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
