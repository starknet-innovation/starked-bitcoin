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
stwo_cairo_cuda_eval_v6_e62b4326b27d5f08(
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
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 15u, row, -1);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 17u, row, -1);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 18u, row, -1);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 18u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 19u, row, -1);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 19u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 20u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 0u, 2u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 0u, 3u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 0u, 4u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 0u, 5u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 12u, row, -1);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 2u, 13u, row, -1);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 14u, row, -1);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 15u, row, -1);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b58 = arena[args->base_params + 0u];
    unsigned b59 = stwo_m31_sub(b1, b58);
    unsigned b60 = stwo_m31_mul(b1, b59);
    unsigned b61 = stwo_m31_sub(b19, b58);
    unsigned b62 = stwo_m31_mul(b19, b61);
    unsigned b63 = stwo_m31_sub(b24, b58);
    unsigned b64 = stwo_m31_mul(b24, b63);
    unsigned b65 = stwo_m31_sub(b30, b58);
    unsigned b66 = stwo_m31_mul(b30, b65);
    unsigned b67 = stwo_m31_sub(b31, b58);
    unsigned b68 = stwo_m31_mul(b31, b67);
    unsigned b69 = stwo_m31_sub(b11, b58);
    unsigned b70 = stwo_m31_mul(b11, b69);
    unsigned b71 = stwo_m31_sub(b12, b58);
    unsigned b72 = stwo_m31_mul(b12, b71);
    unsigned b73 = stwo_m31_sub(b13, b58);
    unsigned b74 = stwo_m31_mul(b13, b73);
    unsigned b75 = stwo_m31_sub(b15, b58);
    unsigned b76 = stwo_m31_mul(b15, b75);
    unsigned b77 = stwo_m31_sub(b58, b1);
    unsigned b78 = stwo_m31_mul(b32, b77);
    unsigned b79 = stwo_m31_sub(b58, b33);
    unsigned b80 = stwo_m31_mul(b79, b1);
    unsigned b81 = stwo_m31_sub(b58, b32);
    unsigned b82 = stwo_m31_sub(b58, b0);
    unsigned b83 = stwo_m31_mul(b1, b82);
    unsigned b84 = stwo_m31_mul(b81, b83);
    unsigned b85 = stwo_m31_sub(b58, b24);
    unsigned b86 = stwo_m31_mul(b32, b85);
    unsigned b87 = stwo_m31_sub(b58, b35);
    unsigned b88 = stwo_m31_mul(b24, b87);
    unsigned b89 = stwo_m31_mul(b24, b77);
    unsigned b90 = stwo_m31_sub(b24, b22);
    unsigned b91 = stwo_m31_mul(b1, b90);
    unsigned b92 = stwo_m31_mul(b81, b91);
    unsigned b93 = stwo_m31_mul(b1, b85);
    unsigned b94 = stwo_m31_mul(b81, b93);
    unsigned b95 = stwo_m31_sub(b21, b94);
    unsigned b96 = stwo_m31_mul(b36, b19);
    unsigned b97 = stwo_m31_sub(b23, b96);
    unsigned b98 = stwo_m31_mul(b19, b77);
    unsigned b99 = stwo_m31_sub(b58, b2);
    unsigned b100 = stwo_m31_sub(b58, b23);
    unsigned b101 = stwo_m31_mul(b99, b100);
    unsigned b102 = stwo_m31_mul(b1, b101);
    unsigned b103 = stwo_m31_mul(b32, b4);
    unsigned b104 = stwo_m31_sub(b4, b3);
    unsigned b105 = stwo_m31_sub(b104, b58);
    unsigned b106 = stwo_m31_mul(b24, b105);
    unsigned b107 = stwo_m31_mul(b81, b106);
    unsigned b108 = stwo_m31_mul(b21, b104);
    unsigned b109 = stwo_m31_sub(b26, b25);
    unsigned b110 = stwo_m31_mul(b21, b109);
    unsigned b111 = stwo_m31_sub(b28, b27);
    unsigned b112 = stwo_m31_mul(b21, b111);
    unsigned b113 = stwo_m31_mul(b24, b6);
    unsigned b114 = stwo_m31_sub(b6, b5);
    unsigned b115 = stwo_m31_sub(b114, b58);
    unsigned b116 = stwo_m31_mul(b21, b115);
    unsigned b117 = stwo_m31_mul(b35, b116);
    unsigned b118 = stwo_m31_mul(b21, b114);
    unsigned b119 = stwo_m31_mul(b87, b118);
    unsigned b120 = stwo_m31_mul(b35, b24);
    unsigned b121 = stwo_m31_mul(b87, b29);
    unsigned b122 = stwo_m31_add(b120, b121);
    unsigned b123 = stwo_m31_sub(b30, b122);
    unsigned b124 = stwo_m31_mul(b30, b37);
    unsigned b125 = stwo_m31_sub(b31, b124);
    unsigned b126 = stwo_m31_mul(b21, b16);
    unsigned b127 = stwo_m31_add(b11, b12);
    unsigned b128 = stwo_m31_add(b13, b15);
    unsigned b129 = stwo_m31_add(b127, b128);
    unsigned b130 = stwo_m31_add(b126, b129);
    unsigned b131 = stwo_m31_sub(b17, b130);
    unsigned b132 = stwo_m31_sub(b58, b14);
    unsigned b133 = stwo_m31_mul(b11, b132);
    unsigned b134 = stwo_m31_mul(b21, b133);
    unsigned b135 = stwo_m31_sub(b58, b11);
    unsigned b136 = stwo_m31_mul(b35, b135);
    unsigned b137 = stwo_m31_mul(b1, b136);
    unsigned b138 = stwo_m31_sub(b19, b18);
    unsigned b139 = stwo_m31_mul(b21, b138);
    unsigned b140 = stwo_m31_mul(b87, b139);
    unsigned b141 = stwo_m31_sub(b17, b28);
    unsigned b142 = stwo_m31_mul(b23, b141);
    unsigned b143 = stwo_m31_mul(b19, b28);
    unsigned b144 = stwo_m31_sub(b58, b19);
    unsigned b145 = arena[args->base_params + 1u];
    unsigned b146 = stwo_m31_mul(b145, b6);
    unsigned b147 = stwo_m31_add(b146, b145);
    unsigned b148 = stwo_m31_mul(b144, b147);
    unsigned b149 = stwo_m31_add(b143, b148);
    unsigned b150 = stwo_m31_sub(b20, b149);
    unsigned b151 = stwo_m31_mul(b7, b135);
    unsigned b152 = stwo_m31_sub(b58, b12);
    unsigned b153 = stwo_m31_mul(b8, b152);
    unsigned b154 = stwo_m31_sub(b58, b13);
    unsigned b155 = stwo_m31_mul(b9, b154);
    unsigned b156 = stwo_m31_sub(b58, b15);
    unsigned b157 = stwo_m31_mul(b10, b156);
    unsigned b158 = stwo_m31_mul(b11, b77);
    unsigned b159 = stwo_m31_mul(b12, b77);
    unsigned b160 = stwo_m31_mul(b13, b77);
    unsigned b161 = stwo_m31_mul(b15, b77);
    unsigned b162 = stwo_m31_mul(b12, b135);
    unsigned b163 = stwo_m31_mul(b13, b152);
    unsigned b164 = stwo_m31_mul(b15, b154);
    unsigned b165 = stwo_m31_neg(b31);
    unsigned b166 = arena[args->base_params + 2u];
    unsigned b167 = stwo_m31_mul(b166, b8);
    unsigned b168 = stwo_m31_add(b7, b167);
    unsigned b169 = stwo_m31_mul(b166, b10);
    unsigned b170 = stwo_m31_add(b9, b169);
    unsigned b171 = stwo_m31_neg(b24);
    unsigned b172 = arena[args->base_params + 3u];
    unsigned b173 = stwo_m31_sub(b28, b172);
    unsigned b174 = stwo_m31_sub(b58, b31);
    unsigned b175 = stwo_m31_mul(b11, b174);
    unsigned b176 = stwo_m31_neg(b175);
    unsigned b177 = stwo_m31_add(b26, b146);
    unsigned b178 = arena[args->base_params + 4u];
    unsigned b179 = stwo_m31_mul(b178, b34);
    unsigned b180 = arena[args->base_params + 5u];
    unsigned b181 = stwo_m31_add(b179, b180);
    unsigned b182 = stwo_m31_add(b177, b181);
    unsigned b183 = arena[args->base_params + 6u];
    unsigned b184 = stwo_m31_sub(b182, b183);
    unsigned b185 = stwo_m31_mul(b12, b174);
    unsigned b186 = stwo_m31_neg(b185);
    unsigned b187 = stwo_m31_add(b179, b58);
    unsigned b188 = stwo_m31_add(b177, b187);
    unsigned b189 = stwo_m31_sub(b188, b183);
    unsigned b190 = stwo_m31_mul(b13, b174);
    unsigned b191 = stwo_m31_neg(b190);
    unsigned b192 = arena[args->base_params + 7u];
    unsigned b193 = stwo_m31_add(b179, b192);
    unsigned b194 = stwo_m31_add(b177, b193);
    unsigned b195 = stwo_m31_sub(b194, b183);
    unsigned b196 = stwo_m31_mul(b15, b174);
    unsigned b197 = stwo_m31_neg(b196);
    unsigned b198 = arena[args->base_params + 8u];
    unsigned b199 = stwo_m31_add(b179, b198);
    unsigned b200 = stwo_m31_add(b177, b199);
    unsigned b201 = stwo_m31_sub(b200, b183);
    unsigned b202 = stwo_m31_mul(b1, b35);
    StwoCairoQm31 e0 = { b60, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b62, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b64, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b66, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b68, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b70, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b72, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b74, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b76, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b78, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b80, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b84, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b86, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b88, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b89, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b92, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b95, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b97, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b98, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b102, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b103, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b107, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b108, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b110, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b112, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b113, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b117, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b119, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b123, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b125, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b131, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b134, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b137, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b140, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b142, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b150, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b151, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b153, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b155, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b157, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b158, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b159, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b160, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b161, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b162, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b163, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b164, b180, b180, b180 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e49 = { b165, b180, b180, b180 };
    StwoCairoQm31 e50 = { 36u, 0u, 0u, 0u };
    StwoCairoQm31 e51 = { b4, b180, b180, b180 };
    StwoCairoQm31 e52 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e53 = stwo_qm31_mul(e51, e52);
    StwoCairoQm31 e54 = stwo_qm31_add(e50, e53);
    StwoCairoQm31 e55 = { b34, b180, b180, b180 };
    StwoCairoQm31 e56 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e57 = stwo_qm31_mul(e55, e56);
    StwoCairoQm31 e58 = stwo_qm31_add(e54, e57);
    StwoCairoQm31 e59 = { b168, b180, b180, b180 };
    StwoCairoQm31 e60 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e61 = stwo_qm31_mul(e59, e60);
    StwoCairoQm31 e62 = stwo_qm31_add(e58, e61);
    StwoCairoQm31 e63 = { b170, b180, b180, b180 };
    StwoCairoQm31 e64 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e65 = stwo_qm31_mul(e63, e64);
    StwoCairoQm31 e66 = stwo_qm31_add(e62, e65);
    StwoCairoQm31 e67 = stwo_qm31_sub(e66, e47);
    StwoCairoQm31 e68 = { b171, b180, b180, b180 };
    StwoCairoQm31 e69 = { 32u, 0u, 0u, 0u };
    StwoCairoQm31 e70 = { b4, b180, b180, b180 };
    StwoCairoQm31 e71 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e72 = stwo_qm31_mul(e70, e71);
    StwoCairoQm31 e73 = stwo_qm31_add(e69, e72);
    StwoCairoQm31 e74 = { b26, b180, b180, b180 };
    StwoCairoQm31 e75 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e76 = stwo_qm31_mul(e74, e75);
    StwoCairoQm31 e77 = stwo_qm31_add(e73, e76);
    StwoCairoQm31 e78 = { b173, b180, b180, b180 };
    StwoCairoQm31 e79 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e80 = stwo_qm31_mul(e78, e79);
    StwoCairoQm31 e81 = stwo_qm31_add(e77, e80);
    StwoCairoQm31 e82 = stwo_qm31_sub(e81, e47);
    StwoCairoQm31 e83 = { b176, b180, b180, b180 };
    StwoCairoQm31 e84 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e85 = { b184, b180, b180, b180 };
    StwoCairoQm31 e86 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e87 = stwo_qm31_mul(e85, e86);
    StwoCairoQm31 e88 = stwo_qm31_add(e84, e87);
    StwoCairoQm31 e89 = { b7, b180, b180, b180 };
    StwoCairoQm31 e90 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e91 = stwo_qm31_mul(e89, e90);
    StwoCairoQm31 e92 = stwo_qm31_add(e88, e91);
    StwoCairoQm31 e93 = stwo_qm31_sub(e92, e47);
    StwoCairoQm31 e94 = { b186, b180, b180, b180 };
    StwoCairoQm31 e95 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e96 = { b189, b180, b180, b180 };
    StwoCairoQm31 e97 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e98 = stwo_qm31_mul(e96, e97);
    StwoCairoQm31 e99 = stwo_qm31_add(e95, e98);
    StwoCairoQm31 e100 = { b8, b180, b180, b180 };
    StwoCairoQm31 e101 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e102 = stwo_qm31_mul(e100, e101);
    StwoCairoQm31 e103 = stwo_qm31_add(e99, e102);
    StwoCairoQm31 e104 = stwo_qm31_sub(e103, e47);
    StwoCairoQm31 e105 = { b191, b180, b180, b180 };
    StwoCairoQm31 e106 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e107 = { b195, b180, b180, b180 };
    StwoCairoQm31 e108 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e109 = stwo_qm31_mul(e107, e108);
    StwoCairoQm31 e110 = stwo_qm31_add(e106, e109);
    StwoCairoQm31 e111 = { b9, b180, b180, b180 };
    StwoCairoQm31 e112 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e113 = stwo_qm31_mul(e111, e112);
    StwoCairoQm31 e114 = stwo_qm31_add(e110, e113);
    StwoCairoQm31 e115 = stwo_qm31_sub(e114, e47);
    StwoCairoQm31 e116 = { b197, b180, b180, b180 };
    StwoCairoQm31 e117 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e118 = { b201, b180, b180, b180 };
    StwoCairoQm31 e119 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e120 = stwo_qm31_mul(e118, e119);
    StwoCairoQm31 e121 = stwo_qm31_add(e117, e120);
    StwoCairoQm31 e122 = { b10, b180, b180, b180 };
    StwoCairoQm31 e123 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e124 = stwo_qm31_mul(e122, e123);
    StwoCairoQm31 e125 = stwo_qm31_add(e121, e124);
    StwoCairoQm31 e126 = stwo_qm31_sub(e125, e47);
    StwoCairoQm31 e127 = { b1, b180, b180, b180 };
    StwoCairoQm31 e128 = { 37u, 0u, 0u, 0u };
    StwoCairoQm31 e129 = { b4, b180, b180, b180 };
    StwoCairoQm31 e130 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e131 = stwo_qm31_mul(e129, e130);
    StwoCairoQm31 e132 = stwo_qm31_add(e128, e131);
    StwoCairoQm31 e133 = { b6, b180, b180, b180 };
    StwoCairoQm31 e134 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e135 = stwo_qm31_mul(e133, e134);
    StwoCairoQm31 e136 = stwo_qm31_add(e132, e135);
    StwoCairoQm31 e137 = { b34, b180, b180, b180 };
    StwoCairoQm31 e138 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e139 = stwo_qm31_mul(e137, e138);
    StwoCairoQm31 e140 = stwo_qm31_add(e136, e139);
    StwoCairoQm31 e141 = { b168, b180, b180, b180 };
    StwoCairoQm31 e142 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e143 = stwo_qm31_mul(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_add(e140, e143);
    StwoCairoQm31 e145 = { b170, b180, b180, b180 };
    StwoCairoQm31 e146 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e147 = stwo_qm31_mul(e145, e146);
    StwoCairoQm31 e148 = stwo_qm31_add(e144, e147);
    StwoCairoQm31 e149 = stwo_qm31_sub(e148, e47);
    StwoCairoQm31 e150 = { b202, b180, b180, b180 };
    StwoCairoQm31 e151 = { 38u, 0u, 0u, 0u };
    StwoCairoQm31 e152 = { b4, b180, b180, b180 };
    StwoCairoQm31 e153 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e154 = stwo_qm31_mul(e152, e153);
    StwoCairoQm31 e155 = stwo_qm31_add(e151, e154);
    StwoCairoQm31 e156 = { b6, b180, b180, b180 };
    StwoCairoQm31 e157 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e158 = stwo_qm31_mul(e156, e157);
    StwoCairoQm31 e159 = stwo_qm31_add(e155, e158);
    StwoCairoQm31 e160 = { b19, b180, b180, b180 };
    StwoCairoQm31 e161 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e162 = stwo_qm31_mul(e160, e161);
    StwoCairoQm31 e163 = stwo_qm31_add(e159, e162);
    StwoCairoQm31 e164 = { b20, b180, b180, b180 };
    StwoCairoQm31 e165 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e166 = stwo_qm31_mul(e164, e165);
    StwoCairoQm31 e167 = stwo_qm31_add(e163, e166);
    StwoCairoQm31 e168 = stwo_qm31_sub(e167, e47);
    StwoCairoQm31 e169 = { b38, b39, b40, b41 };
    StwoCairoQm31 e170 = { b42, b43, b44, b45 };
    StwoCairoQm31 e171 = { b46, b47, b48, b49 };
    StwoCairoQm31 e172 = { b51, b53, b55, b57 };
    StwoCairoQm31 e173 = { b50, b52, b54, b56 };
    StwoCairoQm31 e174 = stwo_qm31_mul(e49, e82);
    StwoCairoQm31 e175 = stwo_qm31_mul(e68, e67);
    StwoCairoQm31 e176 = stwo_qm31_add(e174, e175);
    StwoCairoQm31 e177 = stwo_qm31_mul(e67, e82);
    StwoCairoQm31 e178 = stwo_qm31_mul(e169, e177);
    StwoCairoQm31 e179 = stwo_qm31_sub(e178, e176);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e179, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e180 = stwo_qm31_mul(e83, e104);
    StwoCairoQm31 e181 = stwo_qm31_mul(e94, e93);
    StwoCairoQm31 e182 = stwo_qm31_add(e180, e181);
    StwoCairoQm31 e183 = stwo_qm31_mul(e93, e104);
    StwoCairoQm31 e184 = stwo_qm31_sub(e170, e169);
    StwoCairoQm31 e185 = stwo_qm31_mul(e184, e183);
    StwoCairoQm31 e186 = stwo_qm31_sub(e185, e182);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e186, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e187 = stwo_qm31_mul(e105, e126);
    StwoCairoQm31 e188 = stwo_qm31_mul(e116, e115);
    StwoCairoQm31 e189 = stwo_qm31_add(e187, e188);
    StwoCairoQm31 e190 = stwo_qm31_mul(e115, e126);
    StwoCairoQm31 e191 = stwo_qm31_sub(e171, e170);
    StwoCairoQm31 e192 = stwo_qm31_mul(e191, e190);
    StwoCairoQm31 e193 = stwo_qm31_sub(e192, e189);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e193, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e194 = stwo_qm31_mul(e127, e168);
    StwoCairoQm31 e195 = stwo_qm31_mul(e150, e149);
    StwoCairoQm31 e196 = stwo_qm31_add(e194, e195);
    StwoCairoQm31 e197 = stwo_qm31_mul(e149, e168);
    StwoCairoQm31 e198 = stwo_qm31_sub(e172, e173);
    StwoCairoQm31 e199 = stwo_qm31_sub(e198, e171);
    StwoCairoQm31 e200 = stwo_qm31_add(e199, e48);
    StwoCairoQm31 e201 = stwo_qm31_mul(e200, e197);
    StwoCairoQm31 e202 = stwo_qm31_sub(e201, e196);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e202, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
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
