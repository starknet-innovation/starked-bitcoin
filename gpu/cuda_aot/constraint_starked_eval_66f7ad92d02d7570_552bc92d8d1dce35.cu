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
stwo_cairo_cuda_eval_v6_66f7ad92d02d7570(
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
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b24 = stwo_trace_value(arena, *args, 0u, 2u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 0u, 3u, row, 0);
    unsigned b26 = stwo_trace_value(arena, *args, 0u, 4u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 2u, 8u, row, -1);
    unsigned b36 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 2u, 9u, row, -1);
    unsigned b38 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 2u, 10u, row, -1);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 11u, row, -1);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b43 = arena[args->base_params + 0u];
    unsigned b44 = stwo_m31_sub(b1, b43);
    unsigned b45 = stwo_m31_mul(b1, b44);
    unsigned b46 = stwo_m31_sub(b18, b43);
    unsigned b47 = stwo_m31_mul(b18, b46);
    unsigned b48 = stwo_m31_sub(b10, b43);
    unsigned b49 = stwo_m31_mul(b10, b48);
    unsigned b50 = stwo_m31_sub(b11, b43);
    unsigned b51 = stwo_m31_mul(b11, b50);
    unsigned b52 = stwo_m31_sub(b12, b43);
    unsigned b53 = stwo_m31_mul(b12, b52);
    unsigned b54 = stwo_m31_sub(b14, b43);
    unsigned b55 = stwo_m31_mul(b14, b54);
    unsigned b56 = stwo_m31_sub(b43, b1);
    unsigned b57 = stwo_m31_mul(b22, b56);
    unsigned b58 = stwo_m31_mul(b22, b4);
    unsigned b59 = stwo_m31_sub(b43, b23);
    unsigned b60 = stwo_m31_mul(b59, b1);
    unsigned b61 = stwo_m31_sub(b43, b22);
    unsigned b62 = stwo_m31_sub(b43, b0);
    unsigned b63 = stwo_m31_mul(b1, b62);
    unsigned b64 = stwo_m31_mul(b61, b63);
    unsigned b65 = stwo_m31_mul(b61, b1);
    unsigned b66 = stwo_m31_sub(b20, b65);
    unsigned b67 = stwo_m31_add(b3, b43);
    unsigned b68 = stwo_m31_mul(b20, b67);
    unsigned b69 = stwo_m31_sub(b4, b68);
    unsigned b70 = stwo_m31_mul(b25, b69);
    unsigned b71 = stwo_m31_sub(b43, b25);
    unsigned b72 = stwo_m31_sub(b4, b3);
    unsigned b73 = stwo_m31_mul(b71, b72);
    unsigned b74 = arena[args->base_params + 1u];
    unsigned b75 = stwo_m31_mul(b74, b4);
    unsigned b76 = arena[args->base_params + 2u];
    unsigned b77 = stwo_m31_mul(b76, b24);
    unsigned b78 = stwo_m31_add(b75, b77);
    unsigned b79 = stwo_m31_sub(b5, b78);
    unsigned b80 = stwo_m31_mul(b20, b15);
    unsigned b81 = stwo_m31_add(b10, b11);
    unsigned b82 = stwo_m31_add(b12, b14);
    unsigned b83 = stwo_m31_add(b81, b82);
    unsigned b84 = stwo_m31_add(b80, b83);
    unsigned b85 = stwo_m31_sub(b16, b84);
    unsigned b86 = stwo_m31_sub(b43, b13);
    unsigned b87 = stwo_m31_mul(b10, b86);
    unsigned b88 = stwo_m31_mul(b20, b87);
    unsigned b89 = stwo_m31_sub(b43, b10);
    unsigned b90 = stwo_m31_mul(b89, b4);
    unsigned b91 = stwo_m31_mul(b25, b90);
    unsigned b92 = stwo_m31_sub(b1, b2);
    unsigned b93 = stwo_m31_mul(b23, b92);
    unsigned b94 = stwo_m31_sub(b21, b93);
    unsigned b95 = stwo_m31_sub(b43, b26);
    unsigned b96 = stwo_m31_mul(b95, b21);
    unsigned b97 = stwo_m31_sub(b18, b21);
    unsigned b98 = stwo_m31_mul(b26, b97);
    unsigned b99 = stwo_m31_sub(b18, b17);
    unsigned b100 = stwo_m31_mul(b71, b99);
    unsigned b101 = arena[args->base_params + 3u];
    unsigned b102 = stwo_m31_sub(b16, b101);
    unsigned b103 = stwo_m31_mul(b21, b102);
    unsigned b104 = stwo_m31_mul(b18, b101);
    unsigned b105 = stwo_m31_sub(b43, b18);
    unsigned b106 = stwo_m31_add(b75, b74);
    unsigned b107 = stwo_m31_mul(b105, b106);
    unsigned b108 = stwo_m31_add(b104, b107);
    unsigned b109 = stwo_m31_sub(b19, b108);
    unsigned b110 = stwo_m31_mul(b6, b89);
    unsigned b111 = stwo_m31_sub(b43, b11);
    unsigned b112 = stwo_m31_mul(b7, b111);
    unsigned b113 = stwo_m31_sub(b43, b12);
    unsigned b114 = stwo_m31_mul(b8, b113);
    unsigned b115 = stwo_m31_sub(b43, b14);
    unsigned b116 = stwo_m31_mul(b9, b115);
    unsigned b117 = stwo_m31_mul(b10, b56);
    unsigned b118 = stwo_m31_mul(b11, b56);
    unsigned b119 = stwo_m31_mul(b12, b56);
    unsigned b120 = stwo_m31_mul(b14, b56);
    unsigned b121 = stwo_m31_mul(b11, b89);
    unsigned b122 = stwo_m31_mul(b12, b111);
    unsigned b123 = stwo_m31_mul(b14, b113);
    unsigned b124 = stwo_m31_neg(b10);
    unsigned b125 = arena[args->base_params + 4u];
    unsigned b126 = stwo_m31_add(b5, b125);
    unsigned b127 = stwo_m31_neg(b11);
    unsigned b128 = stwo_m31_add(b5, b43);
    unsigned b129 = stwo_m31_neg(b12);
    unsigned b130 = arena[args->base_params + 5u];
    unsigned b131 = stwo_m31_add(b5, b130);
    unsigned b132 = stwo_m31_neg(b14);
    unsigned b133 = arena[args->base_params + 6u];
    unsigned b134 = stwo_m31_add(b5, b133);
    unsigned b135 = arena[args->base_params + 7u];
    unsigned b136 = stwo_m31_mul(b135, b7);
    unsigned b137 = stwo_m31_add(b6, b136);
    unsigned b138 = stwo_m31_mul(b135, b9);
    unsigned b139 = stwo_m31_add(b8, b138);
    unsigned b140 = stwo_m31_mul(b1, b25);
    StwoCairoQm31 e0 = { b45, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b47, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b49, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b51, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b53, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b55, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b57, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b58, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b60, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b64, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b66, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b70, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b73, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b79, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b85, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b88, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b91, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b94, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b96, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b98, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b100, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b103, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b109, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b110, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b112, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b114, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b116, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b117, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b118, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b119, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b120, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b121, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b122, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b123, b125, b125, b125 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e35 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e36 = { b124, b125, b125, b125 };
    StwoCairoQm31 e37 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e38 = { b126, b125, b125, b125 };
    StwoCairoQm31 e39 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e40 = stwo_qm31_mul(e38, e39);
    StwoCairoQm31 e41 = stwo_qm31_add(e37, e40);
    StwoCairoQm31 e42 = { b6, b125, b125, b125 };
    StwoCairoQm31 e43 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e44 = stwo_qm31_mul(e42, e43);
    StwoCairoQm31 e45 = stwo_qm31_add(e41, e44);
    StwoCairoQm31 e46 = stwo_qm31_sub(e45, e34);
    StwoCairoQm31 e47 = { b127, b125, b125, b125 };
    StwoCairoQm31 e48 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e49 = { b128, b125, b125, b125 };
    StwoCairoQm31 e50 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e51 = stwo_qm31_mul(e49, e50);
    StwoCairoQm31 e52 = stwo_qm31_add(e48, e51);
    StwoCairoQm31 e53 = { b7, b125, b125, b125 };
    StwoCairoQm31 e54 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e55 = stwo_qm31_mul(e53, e54);
    StwoCairoQm31 e56 = stwo_qm31_add(e52, e55);
    StwoCairoQm31 e57 = stwo_qm31_sub(e56, e34);
    StwoCairoQm31 e58 = { b129, b125, b125, b125 };
    StwoCairoQm31 e59 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e60 = { b131, b125, b125, b125 };
    StwoCairoQm31 e61 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e62 = stwo_qm31_mul(e60, e61);
    StwoCairoQm31 e63 = stwo_qm31_add(e59, e62);
    StwoCairoQm31 e64 = { b8, b125, b125, b125 };
    StwoCairoQm31 e65 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e66 = stwo_qm31_mul(e64, e65);
    StwoCairoQm31 e67 = stwo_qm31_add(e63, e66);
    StwoCairoQm31 e68 = stwo_qm31_sub(e67, e34);
    StwoCairoQm31 e69 = { b132, b125, b125, b125 };
    StwoCairoQm31 e70 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e71 = { b134, b125, b125, b125 };
    StwoCairoQm31 e72 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e73 = stwo_qm31_mul(e71, e72);
    StwoCairoQm31 e74 = stwo_qm31_add(e70, e73);
    StwoCairoQm31 e75 = { b9, b125, b125, b125 };
    StwoCairoQm31 e76 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e77 = stwo_qm31_mul(e75, e76);
    StwoCairoQm31 e78 = stwo_qm31_add(e74, e77);
    StwoCairoQm31 e79 = stwo_qm31_sub(e78, e34);
    StwoCairoQm31 e80 = { b1, b125, b125, b125 };
    StwoCairoQm31 e81 = { 18u, 0u, 0u, 0u };
    StwoCairoQm31 e82 = { b4, b125, b125, b125 };
    StwoCairoQm31 e83 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e84 = stwo_qm31_mul(e82, e83);
    StwoCairoQm31 e85 = stwo_qm31_add(e81, e84);
    StwoCairoQm31 e86 = { b24, b125, b125, b125 };
    StwoCairoQm31 e87 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e88 = stwo_qm31_mul(e86, e87);
    StwoCairoQm31 e89 = stwo_qm31_add(e85, e88);
    StwoCairoQm31 e90 = { b137, b125, b125, b125 };
    StwoCairoQm31 e91 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e92 = stwo_qm31_mul(e90, e91);
    StwoCairoQm31 e93 = stwo_qm31_add(e89, e92);
    StwoCairoQm31 e94 = { b139, b125, b125, b125 };
    StwoCairoQm31 e95 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e96 = stwo_qm31_mul(e94, e95);
    StwoCairoQm31 e97 = stwo_qm31_add(e93, e96);
    StwoCairoQm31 e98 = stwo_qm31_sub(e97, e34);
    StwoCairoQm31 e99 = { b140, b125, b125, b125 };
    StwoCairoQm31 e100 = { 19u, 0u, 0u, 0u };
    StwoCairoQm31 e101 = { b4, b125, b125, b125 };
    StwoCairoQm31 e102 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e103 = stwo_qm31_mul(e101, e102);
    StwoCairoQm31 e104 = stwo_qm31_add(e100, e103);
    StwoCairoQm31 e105 = { b18, b125, b125, b125 };
    StwoCairoQm31 e106 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e107 = stwo_qm31_mul(e105, e106);
    StwoCairoQm31 e108 = stwo_qm31_add(e104, e107);
    StwoCairoQm31 e109 = { b19, b125, b125, b125 };
    StwoCairoQm31 e110 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e111 = stwo_qm31_mul(e109, e110);
    StwoCairoQm31 e112 = stwo_qm31_add(e108, e111);
    StwoCairoQm31 e113 = stwo_qm31_sub(e112, e34);
    StwoCairoQm31 e114 = { b27, b28, b29, b30 };
    StwoCairoQm31 e115 = { b31, b32, b33, b34 };
    StwoCairoQm31 e116 = { b36, b38, b40, b42 };
    StwoCairoQm31 e117 = { b35, b37, b39, b41 };
    StwoCairoQm31 e118 = stwo_qm31_mul(e36, e57);
    StwoCairoQm31 e119 = stwo_qm31_mul(e47, e46);
    StwoCairoQm31 e120 = stwo_qm31_add(e118, e119);
    StwoCairoQm31 e121 = stwo_qm31_mul(e46, e57);
    StwoCairoQm31 e122 = stwo_qm31_mul(e114, e121);
    StwoCairoQm31 e123 = stwo_qm31_sub(e122, e120);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e123, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e124 = stwo_qm31_mul(e58, e79);
    StwoCairoQm31 e125 = stwo_qm31_mul(e69, e68);
    StwoCairoQm31 e126 = stwo_qm31_add(e124, e125);
    StwoCairoQm31 e127 = stwo_qm31_mul(e68, e79);
    StwoCairoQm31 e128 = stwo_qm31_sub(e115, e114);
    StwoCairoQm31 e129 = stwo_qm31_mul(e128, e127);
    StwoCairoQm31 e130 = stwo_qm31_sub(e129, e126);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e130, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e131 = stwo_qm31_mul(e80, e113);
    StwoCairoQm31 e132 = stwo_qm31_mul(e99, e98);
    StwoCairoQm31 e133 = stwo_qm31_add(e131, e132);
    StwoCairoQm31 e134 = stwo_qm31_mul(e98, e113);
    StwoCairoQm31 e135 = stwo_qm31_sub(e116, e117);
    StwoCairoQm31 e136 = stwo_qm31_sub(e135, e115);
    StwoCairoQm31 e137 = stwo_qm31_add(e136, e35);
    StwoCairoQm31 e138 = stwo_qm31_mul(e137, e134);
    StwoCairoQm31 e139 = stwo_qm31_sub(e138, e133);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e139, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
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
