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
stwo_cairo_cuda_eval_v6_7020fe4d93afbe09(
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
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 5u, row, 1);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 6u, row, -1);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 7u, row, -1);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 9u, row, -1);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 13u, row, -1);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 2u, 4u, row, -1);
    unsigned b34 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 2u, 5u, row, -1);
    unsigned b36 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 2u, 6u, row, -1);
    unsigned b38 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 2u, 7u, row, -1);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b41 = arena[args->base_params + 0u];
    unsigned b42 = stwo_m31_sub(b1, b41);
    unsigned b43 = stwo_m31_mul(b1, b42);
    unsigned b44 = stwo_m31_sub(b4, b41);
    unsigned b45 = stwo_m31_mul(b4, b44);
    unsigned b46 = stwo_m31_sub(b10, b41);
    unsigned b47 = stwo_m31_mul(b10, b46);
    unsigned b48 = stwo_m31_sub(b13, b41);
    unsigned b49 = stwo_m31_mul(b13, b48);
    unsigned b50 = stwo_m31_sub(b41, b1);
    unsigned b51 = stwo_m31_mul(b10, b50);
    unsigned b52 = stwo_m31_mul(b13, b50);
    unsigned b53 = stwo_m31_sub(b41, b10);
    unsigned b54 = stwo_m31_mul(b1, b53);
    unsigned b55 = stwo_m31_mul(b27, b54);
    unsigned b56 = stwo_m31_sub(b41, b0);
    unsigned b57 = stwo_m31_mul(b54, b56);
    unsigned b58 = stwo_m31_mul(b54, b12);
    unsigned b59 = stwo_m31_sub(b4, b3);
    unsigned b60 = stwo_m31_mul(b54, b59);
    unsigned b61 = stwo_m31_sub(b6, b5);
    unsigned b62 = stwo_m31_mul(b54, b61);
    unsigned b63 = stwo_m31_sub(b8, b7);
    unsigned b64 = stwo_m31_sub(b63, b41);
    unsigned b65 = stwo_m31_mul(b54, b64);
    unsigned b66 = stwo_m31_sub(b15, b14);
    unsigned b67 = stwo_m31_add(b66, b41);
    unsigned b68 = stwo_m31_mul(b54, b67);
    unsigned b69 = stwo_m31_sub(b18, b17);
    unsigned b70 = stwo_m31_mul(b54, b69);
    unsigned b71 = stwo_m31_sub(b18, b15);
    unsigned b72 = stwo_m31_mul(b10, b71);
    unsigned b73 = stwo_m31_sub(b15, b41);
    unsigned b74 = stwo_m31_mul(b13, b73);
    unsigned b75 = stwo_m31_sub(b1, b13);
    unsigned b76 = stwo_m31_mul(b73, b16);
    unsigned b77 = stwo_m31_sub(b76, b41);
    unsigned b78 = stwo_m31_mul(b75, b77);
    unsigned b79 = stwo_m31_sub(b41, b28);
    unsigned b80 = stwo_m31_mul(b79, b75);
    unsigned b81 = stwo_m31_sub(b41, b2);
    unsigned b82 = stwo_m31_mul(b75, b81);
    unsigned b83 = stwo_m31_mul(b75, b11);
    unsigned b84 = stwo_m31_sub(b20, b9);
    unsigned b85 = stwo_m31_mul(b10, b84);
    unsigned b86 = arena[args->base_params + 1u];
    unsigned b87 = stwo_m31_sub(b22, b86);
    unsigned b88 = stwo_m31_mul(b10, b87);
    unsigned b89 = stwo_m31_sub(b24, b86);
    unsigned b90 = stwo_m31_mul(b10, b89);
    unsigned b91 = stwo_m31_sub(b26, b86);
    unsigned b92 = stwo_m31_mul(b10, b91);
    unsigned b93 = arena[args->base_params + 2u];
    unsigned b94 = stwo_m31_mul(b19, b93);
    unsigned b95 = arena[args->base_params + 3u];
    unsigned b96 = stwo_m31_mul(b21, b95);
    unsigned b97 = stwo_m31_sub(b94, b96);
    unsigned b98 = arena[args->base_params + 4u];
    unsigned b99 = arena[args->base_params + 5u];
    unsigned b100 = stwo_m31_mul(b23, b99);
    unsigned b101 = arena[args->base_params + 6u];
    unsigned b102 = stwo_m31_mul(b25, b101);
    unsigned b103 = stwo_m31_sub(b100, b102);
    unsigned b104 = stwo_m31_mul(b98, b103);
    unsigned b105 = stwo_m31_mul(b23, b101);
    unsigned b106 = stwo_m31_mul(b25, b99);
    unsigned b107 = stwo_m31_add(b105, b106);
    unsigned b108 = stwo_m31_mul(b41, b107);
    unsigned b109 = stwo_m31_sub(b104, b108);
    unsigned b110 = stwo_m31_add(b97, b109);
    unsigned b111 = stwo_m31_add(b110, b9);
    unsigned b112 = stwo_m31_sub(b20, b111);
    unsigned b113 = stwo_m31_mul(b54, b112);
    unsigned b114 = stwo_m31_mul(b19, b95);
    unsigned b115 = stwo_m31_mul(b21, b93);
    unsigned b116 = stwo_m31_add(b114, b115);
    unsigned b117 = stwo_m31_mul(b98, b107);
    unsigned b118 = stwo_m31_mul(b41, b103);
    unsigned b119 = stwo_m31_add(b117, b118);
    unsigned b120 = stwo_m31_add(b116, b119);
    unsigned b121 = stwo_m31_add(b120, b86);
    unsigned b122 = stwo_m31_sub(b22, b121);
    unsigned b123 = stwo_m31_mul(b54, b122);
    unsigned b124 = stwo_m31_mul(b19, b99);
    unsigned b125 = stwo_m31_mul(b21, b101);
    unsigned b126 = stwo_m31_sub(b124, b125);
    unsigned b127 = stwo_m31_mul(b23, b93);
    unsigned b128 = stwo_m31_mul(b25, b95);
    unsigned b129 = stwo_m31_sub(b127, b128);
    unsigned b130 = stwo_m31_add(b126, b129);
    unsigned b131 = stwo_m31_add(b130, b86);
    unsigned b132 = stwo_m31_sub(b24, b131);
    unsigned b133 = stwo_m31_mul(b54, b132);
    unsigned b134 = stwo_m31_mul(b19, b101);
    unsigned b135 = stwo_m31_mul(b21, b99);
    unsigned b136 = stwo_m31_add(b134, b135);
    unsigned b137 = stwo_m31_mul(b23, b95);
    unsigned b138 = stwo_m31_mul(b25, b93);
    unsigned b139 = stwo_m31_add(b137, b138);
    unsigned b140 = stwo_m31_add(b136, b139);
    unsigned b141 = stwo_m31_add(b140, b86);
    unsigned b142 = stwo_m31_sub(b26, b141);
    unsigned b143 = stwo_m31_mul(b54, b142);
    unsigned b144 = stwo_m31_sub(b41, b4);
    unsigned b145 = stwo_m31_mul(b1, b144);
    unsigned b146 = stwo_m31_neg(b145);
    unsigned b147 = stwo_m31_mul(b1, b4);
    unsigned b148 = stwo_m31_neg(b147);
    unsigned b149 = stwo_m31_neg(b10);
    StwoCairoQm31 e0 = { b43, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b45, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b47, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b49, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b51, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b52, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b55, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b57, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b58, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b60, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b62, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b65, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b68, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b70, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b72, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b74, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b78, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b80, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b82, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b83, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b85, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b88, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b90, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b92, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b113, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b123, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b133, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b143, b86, b86, b86 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e29 = stwo_load_qm31(arena, args->ext_params + 8u * 4u);
    StwoCairoQm31 e30 = { b146, b86, b86, b86 };
    StwoCairoQm31 e31 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e32 = { b8, b86, b86, b86 };
    StwoCairoQm31 e33 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e34 = stwo_qm31_mul(e32, e33);
    StwoCairoQm31 e35 = stwo_qm31_add(e31, e34);
    StwoCairoQm31 e36 = { b9, b86, b86, b86 };
    StwoCairoQm31 e37 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e38 = stwo_qm31_mul(e36, e37);
    StwoCairoQm31 e39 = stwo_qm31_add(e35, e38);
    StwoCairoQm31 e40 = stwo_qm31_sub(e39, e28);
    StwoCairoQm31 e41 = { b148, b86, b86, b86 };
    StwoCairoQm31 e42 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e43 = { b8, b86, b86, b86 };
    StwoCairoQm31 e44 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e45 = stwo_qm31_mul(e43, e44);
    StwoCairoQm31 e46 = stwo_qm31_add(e42, e45);
    StwoCairoQm31 e47 = { b9, b86, b86, b86 };
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e49 = stwo_qm31_mul(e47, e48);
    StwoCairoQm31 e50 = stwo_qm31_add(e46, e49);
    StwoCairoQm31 e51 = stwo_qm31_sub(e50, e28);
    StwoCairoQm31 e52 = { b149, b86, b86, b86 };
    StwoCairoQm31 e53 = { 21u, 0u, 0u, 0u };
    StwoCairoQm31 e54 = { b4, b86, b86, b86 };
    StwoCairoQm31 e55 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e56 = stwo_qm31_mul(e54, e55);
    StwoCairoQm31 e57 = stwo_qm31_add(e53, e56);
    StwoCairoQm31 e58 = { b6, b86, b86, b86 };
    StwoCairoQm31 e59 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e60 = stwo_qm31_mul(e58, e59);
    StwoCairoQm31 e61 = stwo_qm31_add(e57, e60);
    StwoCairoQm31 e62 = { b8, b86, b86, b86 };
    StwoCairoQm31 e63 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e64 = stwo_qm31_mul(e62, e63);
    StwoCairoQm31 e65 = stwo_qm31_add(e61, e64);
    StwoCairoQm31 e66 = { b15, b86, b86, b86 };
    StwoCairoQm31 e67 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e68 = stwo_qm31_mul(e66, e67);
    StwoCairoQm31 e69 = stwo_qm31_add(e65, e68);
    StwoCairoQm31 e70 = stwo_qm31_sub(e69, e28);
    StwoCairoQm31 e71 = { b13, b86, b86, b86 };
    StwoCairoQm31 e72 = { 22u, 0u, 0u, 0u };
    StwoCairoQm31 e73 = { b4, b86, b86, b86 };
    StwoCairoQm31 e74 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e75 = stwo_qm31_mul(e73, e74);
    StwoCairoQm31 e76 = stwo_qm31_add(e72, e75);
    StwoCairoQm31 e77 = { b6, b86, b86, b86 };
    StwoCairoQm31 e78 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e79 = stwo_qm31_mul(e77, e78);
    StwoCairoQm31 e80 = stwo_qm31_add(e76, e79);
    StwoCairoQm31 e81 = { b18, b86, b86, b86 };
    StwoCairoQm31 e82 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e83 = stwo_qm31_mul(e81, e82);
    StwoCairoQm31 e84 = stwo_qm31_add(e80, e83);
    StwoCairoQm31 e85 = { b20, b86, b86, b86 };
    StwoCairoQm31 e86 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e87 = stwo_qm31_mul(e85, e86);
    StwoCairoQm31 e88 = stwo_qm31_add(e84, e87);
    StwoCairoQm31 e89 = { b22, b86, b86, b86 };
    StwoCairoQm31 e90 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e91 = stwo_qm31_mul(e89, e90);
    StwoCairoQm31 e92 = stwo_qm31_add(e88, e91);
    StwoCairoQm31 e93 = { b24, b86, b86, b86 };
    StwoCairoQm31 e94 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e95 = stwo_qm31_mul(e93, e94);
    StwoCairoQm31 e96 = stwo_qm31_add(e92, e95);
    StwoCairoQm31 e97 = { b26, b86, b86, b86 };
    StwoCairoQm31 e98 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e99 = stwo_qm31_mul(e97, e98);
    StwoCairoQm31 e100 = stwo_qm31_add(e96, e99);
    StwoCairoQm31 e101 = stwo_qm31_sub(e100, e28);
    StwoCairoQm31 e102 = { b29, b30, b31, b32 };
    StwoCairoQm31 e103 = { b34, b36, b38, b40 };
    StwoCairoQm31 e104 = { b33, b35, b37, b39 };
    StwoCairoQm31 e105 = stwo_qm31_mul(e30, e51);
    StwoCairoQm31 e106 = stwo_qm31_mul(e41, e40);
    StwoCairoQm31 e107 = stwo_qm31_add(e105, e106);
    StwoCairoQm31 e108 = stwo_qm31_mul(e40, e51);
    StwoCairoQm31 e109 = stwo_qm31_mul(e102, e108);
    StwoCairoQm31 e110 = stwo_qm31_sub(e109, e107);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e110, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e111 = stwo_qm31_mul(e52, e101);
    StwoCairoQm31 e112 = stwo_qm31_mul(e71, e70);
    StwoCairoQm31 e113 = stwo_qm31_add(e111, e112);
    StwoCairoQm31 e114 = stwo_qm31_mul(e70, e101);
    StwoCairoQm31 e115 = stwo_qm31_sub(e103, e104);
    StwoCairoQm31 e116 = stwo_qm31_sub(e115, e102);
    StwoCairoQm31 e117 = stwo_qm31_add(e116, e29);
    StwoCairoQm31 e118 = stwo_qm31_mul(e117, e114);
    StwoCairoQm31 e119 = stwo_qm31_sub(e118, e113);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e119, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
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
