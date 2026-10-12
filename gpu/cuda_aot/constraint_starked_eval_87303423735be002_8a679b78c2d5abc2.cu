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
stwo_cairo_cuda_eval_v6_87303423735be002(
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
    unsigned b35 = stwo_trace_value(arena, *args, 1u, 25u, row, -1);
    unsigned b36 = stwo_trace_value(arena, *args, 1u, 25u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 1u, 26u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 2u, 4u, row, -1);
    unsigned b45 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 2u, 5u, row, -1);
    unsigned b47 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 2u, 6u, row, -1);
    unsigned b49 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 7u, row, -1);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b52 = arena[args->base_params + 0u];
    unsigned b53 = stwo_m31_sub(b1, b52);
    unsigned b54 = stwo_m31_mul(b1, b53);
    unsigned b55 = stwo_m31_sub(b2, b52);
    unsigned b56 = stwo_m31_mul(b2, b55);
    unsigned b57 = stwo_m31_sub(b3, b52);
    unsigned b58 = stwo_m31_mul(b3, b57);
    unsigned b59 = stwo_m31_sub(b13, b52);
    unsigned b60 = stwo_m31_mul(b13, b59);
    unsigned b61 = stwo_m31_sub(b19, b52);
    unsigned b62 = stwo_m31_mul(b19, b61);
    unsigned b63 = stwo_m31_sub(b36, b52);
    unsigned b64 = stwo_m31_mul(b36, b63);
    unsigned b65 = stwo_m31_sub(b52, b38);
    unsigned b66 = stwo_m31_sub(b36, b35);
    unsigned b67 = stwo_m31_mul(b65, b66);
    unsigned b68 = stwo_m31_mul(b1, b2);
    unsigned b69 = stwo_m31_add(b1, b2);
    unsigned b70 = stwo_m31_sub(b69, b36);
    unsigned b71 = stwo_m31_mul(b38, b70);
    unsigned b72 = stwo_m31_sub(b52, b27);
    unsigned b73 = stwo_m31_mul(b0, b72);
    unsigned b74 = stwo_m31_sub(b1, b73);
    unsigned b75 = stwo_m31_mul(b65, b74);
    unsigned b76 = stwo_m31_mul(b0, b27);
    unsigned b77 = stwo_m31_sub(b2, b76);
    unsigned b78 = stwo_m31_mul(b65, b77);
    unsigned b79 = arena[args->base_params + 1u];
    unsigned b80 = stwo_m31_sub(b79, b52);
    unsigned b81 = stwo_m31_mul(b2, b80);
    unsigned b82 = stwo_m31_mul(b38, b81);
    unsigned b83 = stwo_m31_sub(b52, b39);
    unsigned b84 = stwo_m31_mul(b83, b1);
    unsigned b85 = stwo_m31_sub(b8, b10);
    unsigned b86 = stwo_m31_add(b85, b52);
    unsigned b87 = stwo_m31_mul(b5, b86);
    unsigned b88 = stwo_m31_sub(b52, b5);
    unsigned b89 = stwo_m31_mul(b86, b6);
    unsigned b90 = stwo_m31_sub(b89, b52);
    unsigned b91 = stwo_m31_mul(b88, b90);
    unsigned b92 = stwo_m31_sub(b10, b52);
    unsigned b93 = stwo_m31_mul(b25, b92);
    unsigned b94 = stwo_m31_sub(b52, b25);
    unsigned b95 = stwo_m31_mul(b92, b26);
    unsigned b96 = stwo_m31_sub(b95, b52);
    unsigned b97 = stwo_m31_mul(b94, b96);
    unsigned b98 = stwo_m31_mul(b5, b25);
    unsigned b99 = stwo_m31_sub(b28, b98);
    unsigned b100 = stwo_m31_sub(b12, b52);
    unsigned b101 = stwo_m31_mul(b100, b29);
    unsigned b102 = stwo_m31_sub(b101, b52);
    unsigned b103 = stwo_m31_mul(b1, b102);
    unsigned b104 = arena[args->base_params + 2u];
    unsigned b105 = stwo_m31_mul(b104, b10);
    unsigned b106 = stwo_m31_add(b12, b13);
    unsigned b107 = stwo_m31_sub(b105, b106);
    unsigned b108 = stwo_m31_mul(b1, b107);
    unsigned b109 = stwo_m31_mul(b38, b21);
    unsigned b110 = stwo_m31_mul(b38, b57);
    unsigned b111 = stwo_m31_mul(b38, b61);
    unsigned b112 = stwo_m31_mul(b38, b15);
    unsigned b113 = stwo_m31_sub(b12, b79);
    unsigned b114 = stwo_m31_mul(b38, b113);
    unsigned b115 = stwo_m31_sub(b21, b20);
    unsigned b116 = stwo_m31_sub(b115, b52);
    unsigned b117 = stwo_m31_mul(b65, b116);
    unsigned b118 = stwo_m31_sub(b3, b4);
    unsigned b119 = stwo_m31_mul(b1, b118);
    unsigned b120 = stwo_m31_mul(b65, b119);
    unsigned b121 = stwo_m31_mul(b3, b8);
    unsigned b122 = stwo_m31_sub(b52, b3);
    unsigned b123 = stwo_m31_mul(b1, b122);
    unsigned b124 = stwo_m31_sub(b33, b123);
    unsigned b125 = stwo_m31_mul(b1, b3);
    unsigned b126 = stwo_m31_sub(b34, b125);
    unsigned b127 = stwo_m31_sub(b8, b7);
    unsigned b128 = stwo_m31_sub(b127, b52);
    unsigned b129 = stwo_m31_mul(b33, b128);
    unsigned b130 = stwo_m31_sub(b10, b9);
    unsigned b131 = stwo_m31_mul(b33, b130);
    unsigned b132 = stwo_m31_sub(b12, b11);
    unsigned b133 = stwo_m31_mul(b33, b132);
    unsigned b134 = stwo_m31_sub(b15, b14);
    unsigned b135 = stwo_m31_mul(b33, b134);
    unsigned b136 = stwo_m31_sub(b17, b16);
    unsigned b137 = stwo_m31_mul(b33, b136);
    unsigned b138 = stwo_m31_sub(b19, b18);
    unsigned b139 = stwo_m31_mul(b33, b138);
    unsigned b140 = stwo_m31_sub(b12, b9);
    unsigned b141 = stwo_m31_mul(b34, b140);
    unsigned b142 = stwo_m31_mul(b65, b141);
    unsigned b143 = stwo_m31_sub(b15, b21);
    unsigned b144 = stwo_m31_mul(b34, b143);
    unsigned b145 = stwo_m31_mul(b65, b144);
    unsigned b146 = stwo_m31_sub(b17, b14);
    unsigned b147 = stwo_m31_mul(b34, b146);
    unsigned b148 = stwo_m31_mul(b65, b147);
    unsigned b149 = stwo_m31_mul(b34, b19);
    unsigned b150 = stwo_m31_mul(b65, b149);
    unsigned b151 = stwo_m31_mul(b13, b5);
    unsigned b152 = stwo_m31_sub(b24, b151);
    unsigned b153 = arena[args->base_params + 3u];
    unsigned b154 = stwo_m31_mul(b153, b8);
    unsigned b155 = stwo_m31_add(b154, b104);
    unsigned b156 = stwo_m31_mul(b19, b155);
    unsigned b157 = stwo_m31_sub(b52, b19);
    unsigned b158 = arena[args->base_params + 4u];
    unsigned b159 = stwo_m31_add(b158, b17);
    unsigned b160 = stwo_m31_mul(b104, b8);
    unsigned b161 = stwo_m31_add(b159, b160);
    unsigned b162 = stwo_m31_mul(b157, b161);
    unsigned b163 = stwo_m31_add(b156, b162);
    unsigned b164 = stwo_m31_sub(b37, b163);
    unsigned b165 = stwo_m31_sub(b52, b2);
    unsigned b166 = arena[args->base_params + 5u];
    unsigned b167 = stwo_m31_mul(b38, b166);
    unsigned b168 = stwo_m31_add(b37, b167);
    unsigned b169 = stwo_m31_sub(b22, b168);
    unsigned b170 = stwo_m31_mul(b165, b169);
    unsigned b171 = stwo_m31_sub(b52, b24);
    unsigned b172 = stwo_m31_add(b19, b52);
    unsigned b173 = stwo_m31_mul(b171, b172);
    unsigned b174 = stwo_m31_add(b37, b173);
    unsigned b175 = stwo_m31_sub(b23, b174);
    unsigned b176 = stwo_m31_mul(b165, b175);
    unsigned b177 = stwo_m31_sub(b22, b32);
    unsigned b178 = stwo_m31_mul(b2, b177);
    unsigned b179 = arena[args->base_params + 6u];
    unsigned b180 = stwo_m31_sub(b23, b179);
    unsigned b181 = stwo_m31_mul(b2, b180);
    unsigned b182 = stwo_m31_add(b32, b52);
    unsigned b183 = stwo_m31_add(b158, b21);
    unsigned b184 = stwo_m31_sub(b182, b183);
    unsigned b185 = stwo_m31_mul(b2, b184);
    unsigned b186 = stwo_m31_mul(b65, b185);
    unsigned b187 = arena[args->base_params + 7u];
    unsigned b188 = stwo_m31_sub(b32, b187);
    unsigned b189 = stwo_m31_mul(b2, b188);
    unsigned b190 = stwo_m31_mul(b38, b189);
    unsigned b191 = stwo_m31_mul(b69, b30);
    unsigned b192 = stwo_m31_mul(b69, b31);
    unsigned b193 = arena[args->base_params + 8u];
    unsigned b194 = arena[args->base_params + 9u];
    StwoCairoQm31 e0 = { b54, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b56, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b58, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b60, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b62, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b64, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b67, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b68, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b71, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b75, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b78, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b82, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b84, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b87, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b91, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b93, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b97, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b99, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b103, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b108, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b109, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b110, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b111, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b112, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b114, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b117, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b120, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b121, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b124, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b126, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b129, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b131, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b133, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b135, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b137, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b139, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b142, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b145, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b148, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b150, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b152, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b164, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b170, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b176, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b178, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b181, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b186, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b190, b194, b194, b194 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e49 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e50 = { b191, b194, b194, b194 };
    StwoCairoQm31 e51 = { 8u, 0u, 0u, 0u };
    StwoCairoQm31 e52 = { b183, b194, b194, b194 };
    StwoCairoQm31 e53 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e54 = stwo_qm31_mul(e52, e53);
    StwoCairoQm31 e55 = stwo_qm31_add(e51, e54);
    StwoCairoQm31 e56 = { b22, b194, b194, b194 };
    StwoCairoQm31 e57 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e58 = stwo_qm31_mul(e56, e57);
    StwoCairoQm31 e59 = stwo_qm31_add(e55, e58);
    StwoCairoQm31 e60 = { b23, b194, b194, b194 };
    StwoCairoQm31 e61 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e62 = stwo_qm31_mul(e60, e61);
    StwoCairoQm31 e63 = stwo_qm31_add(e59, e62);
    StwoCairoQm31 e64 = { b52, b194, b194, b194 };
    StwoCairoQm31 e65 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e66 = stwo_qm31_mul(e64, e65);
    StwoCairoQm31 e67 = stwo_qm31_add(e63, e66);
    StwoCairoQm31 e68 = stwo_qm31_sub(e67, e48);
    StwoCairoQm31 e69 = { b192, b194, b194, b194 };
    StwoCairoQm31 e70 = { 6u, 0u, 0u, 0u };
    StwoCairoQm31 e71 = { b183, b194, b194, b194 };
    StwoCairoQm31 e72 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e73 = stwo_qm31_mul(e71, e72);
    StwoCairoQm31 e74 = stwo_qm31_add(e70, e73);
    StwoCairoQm31 e75 = { b193, b194, b194, b194 };
    StwoCairoQm31 e76 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e77 = stwo_qm31_mul(e75, e76);
    StwoCairoQm31 e78 = stwo_qm31_add(e74, e77);
    StwoCairoQm31 e79 = stwo_qm31_sub(e78, e48);
    StwoCairoQm31 e80 = { b2, b194, b194, b194 };
    StwoCairoQm31 e81 = { 16u, 0u, 0u, 0u };
    StwoCairoQm31 e82 = { b183, b194, b194, b194 };
    StwoCairoQm31 e83 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e84 = stwo_qm31_mul(e82, e83);
    StwoCairoQm31 e85 = stwo_qm31_add(e81, e84);
    StwoCairoQm31 e86 = stwo_qm31_sub(e85, e48);
    StwoCairoQm31 e87 = { b40, b41, b42, b43 };
    StwoCairoQm31 e88 = { b45, b47, b49, b51 };
    StwoCairoQm31 e89 = { b44, b46, b48, b50 };
    StwoCairoQm31 e90 = stwo_qm31_mul(e50, e79);
    StwoCairoQm31 e91 = stwo_qm31_mul(e69, e68);
    StwoCairoQm31 e92 = stwo_qm31_add(e90, e91);
    StwoCairoQm31 e93 = stwo_qm31_mul(e68, e79);
    StwoCairoQm31 e94 = stwo_qm31_mul(e87, e93);
    StwoCairoQm31 e95 = stwo_qm31_sub(e94, e92);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e95, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e96 = stwo_qm31_sub(e88, e89);
    StwoCairoQm31 e97 = stwo_qm31_sub(e96, e87);
    StwoCairoQm31 e98 = stwo_qm31_add(e97, e49);
    StwoCairoQm31 e99 = stwo_qm31_mul(e98, e86);
    StwoCairoQm31 e100 = stwo_qm31_sub(e99, e80);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e100, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
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
