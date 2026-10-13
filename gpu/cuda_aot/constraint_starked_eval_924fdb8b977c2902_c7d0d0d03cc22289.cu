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
stwo_cairo_cuda_eval_v6_924fdb8b977c2902(
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
    unsigned b26 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b28 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b30 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b34 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 2u, 16u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 2u, 17u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 2u, 18u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 2u, 19u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 2u, 20u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 2u, 21u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 22u, row, 0);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 23u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 2u, 24u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 25u, row, 0);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 26u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 27u, row, 0);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 28u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 29u, row, 0);
    unsigned b58 = stwo_trace_value(arena, *args, 2u, 30u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 2u, 31u, row, 0);
    unsigned b60 = stwo_trace_value(arena, *args, 2u, 32u, row, 0);
    unsigned b61 = stwo_trace_value(arena, *args, 2u, 33u, row, 0);
    unsigned b62 = stwo_trace_value(arena, *args, 2u, 34u, row, 0);
    unsigned b63 = stwo_trace_value(arena, *args, 2u, 35u, row, 0);
    unsigned b64 = stwo_trace_value(arena, *args, 2u, 36u, row, -1);
    unsigned b65 = stwo_trace_value(arena, *args, 2u, 36u, row, 0);
    unsigned b66 = stwo_trace_value(arena, *args, 2u, 37u, row, -1);
    unsigned b67 = stwo_trace_value(arena, *args, 2u, 37u, row, 0);
    unsigned b68 = stwo_trace_value(arena, *args, 2u, 38u, row, -1);
    unsigned b69 = stwo_trace_value(arena, *args, 2u, 38u, row, 0);
    unsigned b70 = stwo_trace_value(arena, *args, 2u, 39u, row, -1);
    unsigned b71 = stwo_trace_value(arena, *args, 2u, 39u, row, 0);
    unsigned b72 = arena[args->base_params + 0u];
    unsigned b73 = stwo_m31_sub(b1, b72);
    unsigned b74 = stwo_m31_mul(b1, b73);
    unsigned b75 = stwo_m31_sub(b72, b26);
    unsigned b76 = stwo_m31_sub(b72, b0);
    unsigned b77 = stwo_m31_mul(b1, b76);
    unsigned b78 = stwo_m31_mul(b75, b77);
    unsigned b79 = stwo_m31_sub(b72, b27);
    unsigned b80 = stwo_m31_mul(b79, b1);
    unsigned b81 = stwo_m31_mul(b26, b4);
    unsigned b82 = stwo_m31_sub(b4, b3);
    unsigned b83 = stwo_m31_sub(b82, b72);
    unsigned b84 = stwo_m31_mul(b1, b83);
    unsigned b85 = stwo_m31_mul(b75, b84);
    unsigned b86 = stwo_m31_sub(b6, b72);
    unsigned b87 = stwo_m31_mul(b26, b86);
    unsigned b88 = arena[args->base_params + 1u];
    unsigned b89 = stwo_m31_add(b5, b88);
    unsigned b90 = stwo_m31_add(b89, b7);
    unsigned b91 = stwo_m31_sub(b6, b90);
    unsigned b92 = stwo_m31_mul(b1, b91);
    unsigned b93 = stwo_m31_mul(b75, b92);
    unsigned b94 = stwo_m31_sub(b1, b2);
    unsigned b95 = stwo_m31_mul(b27, b94);
    unsigned b96 = stwo_m31_add(b6, b88);
    unsigned b97 = stwo_m31_add(b96, b8);
    unsigned b98 = arena[args->base_params + 2u];
    unsigned b99 = stwo_m31_sub(b97, b98);
    unsigned b100 = stwo_m31_mul(b95, b99);
    unsigned b101 = stwo_m31_sub(b72, b1);
    unsigned b102 = stwo_m31_sub(b98, b72);
    unsigned b103 = stwo_m31_mul(b101, b102);
    unsigned b104 = stwo_m31_mul(b26, b103);
    unsigned b105 = arena[args->base_params + 3u];
    unsigned b106 = stwo_m31_mul(b105, b25);
    unsigned b107 = stwo_m31_add(b24, b106);
    unsigned b108 = stwo_m31_sub(b8, b107);
    unsigned b109 = stwo_m31_mul(b1, b108);
    unsigned b110 = stwo_m31_neg(b26);
    unsigned b111 = arena[args->base_params + 4u];
    unsigned b112 = stwo_m31_neg(b1);
    unsigned b113 = stwo_m31_add(b6, b111);
    unsigned b114 = stwo_m31_add(b6, b72);
    unsigned b115 = arena[args->base_params + 5u];
    unsigned b116 = stwo_m31_add(b6, b115);
    unsigned b117 = arena[args->base_params + 6u];
    unsigned b118 = stwo_m31_add(b6, b117);
    unsigned b119 = arena[args->base_params + 7u];
    unsigned b120 = stwo_m31_add(b6, b119);
    unsigned b121 = arena[args->base_params + 8u];
    unsigned b122 = stwo_m31_add(b6, b121);
    unsigned b123 = arena[args->base_params + 9u];
    unsigned b124 = stwo_m31_add(b6, b123);
    unsigned b125 = arena[args->base_params + 10u];
    unsigned b126 = stwo_m31_add(b6, b125);
    unsigned b127 = arena[args->base_params + 11u];
    unsigned b128 = stwo_m31_add(b6, b127);
    unsigned b129 = arena[args->base_params + 12u];
    unsigned b130 = stwo_m31_add(b6, b129);
    unsigned b131 = arena[args->base_params + 13u];
    unsigned b132 = stwo_m31_add(b6, b131);
    unsigned b133 = arena[args->base_params + 14u];
    unsigned b134 = stwo_m31_add(b6, b133);
    unsigned b135 = arena[args->base_params + 15u];
    unsigned b136 = stwo_m31_add(b6, b135);
    unsigned b137 = arena[args->base_params + 16u];
    unsigned b138 = stwo_m31_add(b6, b137);
    unsigned b139 = arena[args->base_params + 17u];
    unsigned b140 = stwo_m31_add(b6, b139);
    unsigned b141 = arena[args->base_params + 18u];
    unsigned b142 = stwo_m31_add(b6, b141);
    unsigned b143 = stwo_m31_mul(b105, b10);
    unsigned b144 = stwo_m31_add(b9, b143);
    unsigned b145 = stwo_m31_mul(b105, b12);
    unsigned b146 = stwo_m31_add(b11, b145);
    unsigned b147 = stwo_m31_mul(b105, b14);
    unsigned b148 = stwo_m31_add(b13, b147);
    unsigned b149 = arena[args->base_params + 19u];
    unsigned b150 = stwo_m31_mul(b149, b15);
    unsigned b151 = stwo_m31_add(b148, b150);
    unsigned b152 = stwo_m31_mul(b105, b17);
    unsigned b153 = stwo_m31_add(b16, b152);
    unsigned b154 = stwo_m31_mul(b149, b18);
    unsigned b155 = stwo_m31_add(b153, b154);
    unsigned b156 = arena[args->base_params + 20u];
    unsigned b157 = stwo_m31_mul(b156, b19);
    unsigned b158 = stwo_m31_add(b155, b157);
    unsigned b159 = stwo_m31_mul(b105, b22);
    unsigned b160 = stwo_m31_add(b21, b159);
    unsigned b161 = stwo_m31_mul(b149, b23);
    unsigned b162 = stwo_m31_add(b160, b161);
    StwoCairoQm31 e0 = { b74, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b78, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b80, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b81, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b85, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b87, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b93, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b100, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b104, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b109, b111, b111, b111 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e11 = stwo_load_qm31(arena, args->ext_params + 7u * 4u);
    StwoCairoQm31 e12 = { b110, b111, b111, b111 };
    StwoCairoQm31 e13 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e14 = { b111, b111, b111, b111 };
    StwoCairoQm31 e15 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e16 = stwo_qm31_mul(e14, e15);
    StwoCairoQm31 e17 = stwo_qm31_add(e13, e16);
    StwoCairoQm31 e18 = { b72, b111, b111, b111 };
    StwoCairoQm31 e19 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e20 = stwo_qm31_mul(e18, e19);
    StwoCairoQm31 e21 = stwo_qm31_add(e17, e20);
    StwoCairoQm31 e22 = stwo_qm31_sub(e21, e10);
    StwoCairoQm31 e23 = { b112, b111, b111, b111 };
    StwoCairoQm31 e24 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e25 = { b113, b111, b111, b111 };
    StwoCairoQm31 e26 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e27 = stwo_qm31_mul(e25, e26);
    StwoCairoQm31 e28 = stwo_qm31_add(e24, e27);
    StwoCairoQm31 e29 = { b9, b111, b111, b111 };
    StwoCairoQm31 e30 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e31 = stwo_qm31_mul(e29, e30);
    StwoCairoQm31 e32 = stwo_qm31_add(e28, e31);
    StwoCairoQm31 e33 = stwo_qm31_sub(e32, e10);
    StwoCairoQm31 e34 = { b112, b111, b111, b111 };
    StwoCairoQm31 e35 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e36 = { b114, b111, b111, b111 };
    StwoCairoQm31 e37 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e38 = stwo_qm31_mul(e36, e37);
    StwoCairoQm31 e39 = stwo_qm31_add(e35, e38);
    StwoCairoQm31 e40 = { b10, b111, b111, b111 };
    StwoCairoQm31 e41 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e42 = stwo_qm31_mul(e40, e41);
    StwoCairoQm31 e43 = stwo_qm31_add(e39, e42);
    StwoCairoQm31 e44 = stwo_qm31_sub(e43, e10);
    StwoCairoQm31 e45 = { b112, b111, b111, b111 };
    StwoCairoQm31 e46 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e47 = { b116, b111, b111, b111 };
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e49 = stwo_qm31_mul(e47, e48);
    StwoCairoQm31 e50 = stwo_qm31_add(e46, e49);
    StwoCairoQm31 e51 = { b11, b111, b111, b111 };
    StwoCairoQm31 e52 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e53 = stwo_qm31_mul(e51, e52);
    StwoCairoQm31 e54 = stwo_qm31_add(e50, e53);
    StwoCairoQm31 e55 = stwo_qm31_sub(e54, e10);
    StwoCairoQm31 e56 = { b112, b111, b111, b111 };
    StwoCairoQm31 e57 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e58 = { b118, b111, b111, b111 };
    StwoCairoQm31 e59 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e60 = stwo_qm31_mul(e58, e59);
    StwoCairoQm31 e61 = stwo_qm31_add(e57, e60);
    StwoCairoQm31 e62 = { b12, b111, b111, b111 };
    StwoCairoQm31 e63 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e64 = stwo_qm31_mul(e62, e63);
    StwoCairoQm31 e65 = stwo_qm31_add(e61, e64);
    StwoCairoQm31 e66 = stwo_qm31_sub(e65, e10);
    StwoCairoQm31 e67 = { b112, b111, b111, b111 };
    StwoCairoQm31 e68 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e69 = { b96, b111, b111, b111 };
    StwoCairoQm31 e70 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e71 = stwo_qm31_mul(e69, e70);
    StwoCairoQm31 e72 = stwo_qm31_add(e68, e71);
    StwoCairoQm31 e73 = { b13, b111, b111, b111 };
    StwoCairoQm31 e74 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e75 = stwo_qm31_mul(e73, e74);
    StwoCairoQm31 e76 = stwo_qm31_add(e72, e75);
    StwoCairoQm31 e77 = stwo_qm31_sub(e76, e10);
    StwoCairoQm31 e78 = { b112, b111, b111, b111 };
    StwoCairoQm31 e79 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e80 = { b120, b111, b111, b111 };
    StwoCairoQm31 e81 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e82 = stwo_qm31_mul(e80, e81);
    StwoCairoQm31 e83 = stwo_qm31_add(e79, e82);
    StwoCairoQm31 e84 = { b14, b111, b111, b111 };
    StwoCairoQm31 e85 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e86 = stwo_qm31_mul(e84, e85);
    StwoCairoQm31 e87 = stwo_qm31_add(e83, e86);
    StwoCairoQm31 e88 = stwo_qm31_sub(e87, e10);
    StwoCairoQm31 e89 = { b112, b111, b111, b111 };
    StwoCairoQm31 e90 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e91 = { b122, b111, b111, b111 };
    StwoCairoQm31 e92 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e93 = stwo_qm31_mul(e91, e92);
    StwoCairoQm31 e94 = stwo_qm31_add(e90, e93);
    StwoCairoQm31 e95 = { b15, b111, b111, b111 };
    StwoCairoQm31 e96 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e97 = stwo_qm31_mul(e95, e96);
    StwoCairoQm31 e98 = stwo_qm31_add(e94, e97);
    StwoCairoQm31 e99 = stwo_qm31_sub(e98, e10);
    StwoCairoQm31 e100 = { b112, b111, b111, b111 };
    StwoCairoQm31 e101 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e102 = { b124, b111, b111, b111 };
    StwoCairoQm31 e103 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e104 = stwo_qm31_mul(e102, e103);
    StwoCairoQm31 e105 = stwo_qm31_add(e101, e104);
    StwoCairoQm31 e106 = { b16, b111, b111, b111 };
    StwoCairoQm31 e107 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e108 = stwo_qm31_mul(e106, e107);
    StwoCairoQm31 e109 = stwo_qm31_add(e105, e108);
    StwoCairoQm31 e110 = stwo_qm31_sub(e109, e10);
    StwoCairoQm31 e111 = { b112, b111, b111, b111 };
    StwoCairoQm31 e112 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e113 = { b126, b111, b111, b111 };
    StwoCairoQm31 e114 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e115 = stwo_qm31_mul(e113, e114);
    StwoCairoQm31 e116 = stwo_qm31_add(e112, e115);
    StwoCairoQm31 e117 = { b17, b111, b111, b111 };
    StwoCairoQm31 e118 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e119 = stwo_qm31_mul(e117, e118);
    StwoCairoQm31 e120 = stwo_qm31_add(e116, e119);
    StwoCairoQm31 e121 = stwo_qm31_sub(e120, e10);
    StwoCairoQm31 e122 = { b112, b111, b111, b111 };
    StwoCairoQm31 e123 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e124 = { b128, b111, b111, b111 };
    StwoCairoQm31 e125 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e126 = stwo_qm31_mul(e124, e125);
    StwoCairoQm31 e127 = stwo_qm31_add(e123, e126);
    StwoCairoQm31 e128 = { b18, b111, b111, b111 };
    StwoCairoQm31 e129 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e130 = stwo_qm31_mul(e128, e129);
    StwoCairoQm31 e131 = stwo_qm31_add(e127, e130);
    StwoCairoQm31 e132 = stwo_qm31_sub(e131, e10);
    StwoCairoQm31 e133 = { b112, b111, b111, b111 };
    StwoCairoQm31 e134 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e135 = { b130, b111, b111, b111 };
    StwoCairoQm31 e136 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e137 = stwo_qm31_mul(e135, e136);
    StwoCairoQm31 e138 = stwo_qm31_add(e134, e137);
    StwoCairoQm31 e139 = { b19, b111, b111, b111 };
    StwoCairoQm31 e140 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e141 = stwo_qm31_mul(e139, e140);
    StwoCairoQm31 e142 = stwo_qm31_add(e138, e141);
    StwoCairoQm31 e143 = stwo_qm31_sub(e142, e10);
    StwoCairoQm31 e144 = { b112, b111, b111, b111 };
    StwoCairoQm31 e145 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e146 = { b132, b111, b111, b111 };
    StwoCairoQm31 e147 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e148 = stwo_qm31_mul(e146, e147);
    StwoCairoQm31 e149 = stwo_qm31_add(e145, e148);
    StwoCairoQm31 e150 = { b20, b111, b111, b111 };
    StwoCairoQm31 e151 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e152 = stwo_qm31_mul(e150, e151);
    StwoCairoQm31 e153 = stwo_qm31_add(e149, e152);
    StwoCairoQm31 e154 = stwo_qm31_sub(e153, e10);
    StwoCairoQm31 e155 = { b112, b111, b111, b111 };
    StwoCairoQm31 e156 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e157 = { b134, b111, b111, b111 };
    StwoCairoQm31 e158 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e159 = stwo_qm31_mul(e157, e158);
    StwoCairoQm31 e160 = stwo_qm31_add(e156, e159);
    StwoCairoQm31 e161 = { b21, b111, b111, b111 };
    StwoCairoQm31 e162 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e163 = stwo_qm31_mul(e161, e162);
    StwoCairoQm31 e164 = stwo_qm31_add(e160, e163);
    StwoCairoQm31 e165 = stwo_qm31_sub(e164, e10);
    StwoCairoQm31 e166 = { b112, b111, b111, b111 };
    StwoCairoQm31 e167 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e168 = { b136, b111, b111, b111 };
    StwoCairoQm31 e169 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e170 = stwo_qm31_mul(e168, e169);
    StwoCairoQm31 e171 = stwo_qm31_add(e167, e170);
    StwoCairoQm31 e172 = { b22, b111, b111, b111 };
    StwoCairoQm31 e173 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e174 = stwo_qm31_mul(e172, e173);
    StwoCairoQm31 e175 = stwo_qm31_add(e171, e174);
    StwoCairoQm31 e176 = stwo_qm31_sub(e175, e10);
    StwoCairoQm31 e177 = { b112, b111, b111, b111 };
    StwoCairoQm31 e178 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e179 = { b138, b111, b111, b111 };
    StwoCairoQm31 e180 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e181 = stwo_qm31_mul(e179, e180);
    StwoCairoQm31 e182 = stwo_qm31_add(e178, e181);
    StwoCairoQm31 e183 = { b23, b111, b111, b111 };
    StwoCairoQm31 e184 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e185 = stwo_qm31_mul(e183, e184);
    StwoCairoQm31 e186 = stwo_qm31_add(e182, e185);
    StwoCairoQm31 e187 = stwo_qm31_sub(e186, e10);
    StwoCairoQm31 e188 = { b112, b111, b111, b111 };
    StwoCairoQm31 e189 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e190 = { b140, b111, b111, b111 };
    StwoCairoQm31 e191 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e192 = stwo_qm31_mul(e190, e191);
    StwoCairoQm31 e193 = stwo_qm31_add(e189, e192);
    StwoCairoQm31 e194 = { b24, b111, b111, b111 };
    StwoCairoQm31 e195 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e196 = stwo_qm31_mul(e194, e195);
    StwoCairoQm31 e197 = stwo_qm31_add(e193, e196);
    StwoCairoQm31 e198 = stwo_qm31_sub(e197, e10);
    StwoCairoQm31 e199 = { b112, b111, b111, b111 };
    StwoCairoQm31 e200 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e201 = { b142, b111, b111, b111 };
    StwoCairoQm31 e202 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e203 = stwo_qm31_mul(e201, e202);
    StwoCairoQm31 e204 = stwo_qm31_add(e200, e203);
    StwoCairoQm31 e205 = { b25, b111, b111, b111 };
    StwoCairoQm31 e206 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e207 = stwo_qm31_mul(e205, e206);
    StwoCairoQm31 e208 = stwo_qm31_add(e204, e207);
    StwoCairoQm31 e209 = stwo_qm31_sub(e208, e10);
    StwoCairoQm31 e210 = { b1, b111, b111, b111 };
    StwoCairoQm31 e211 = { 21u, 0u, 0u, 0u };
    StwoCairoQm31 e212 = { b72, b111, b111, b111 };
    StwoCairoQm31 e213 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e214 = stwo_qm31_mul(e212, e213);
    StwoCairoQm31 e215 = stwo_qm31_add(e211, e214);
    StwoCairoQm31 e216 = { b4, b111, b111, b111 };
    StwoCairoQm31 e217 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e218 = stwo_qm31_mul(e216, e217);
    StwoCairoQm31 e219 = stwo_qm31_add(e215, e218);
    StwoCairoQm31 e220 = { b96, b111, b111, b111 };
    StwoCairoQm31 e221 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e222 = stwo_qm31_mul(e220, e221);
    StwoCairoQm31 e223 = stwo_qm31_add(e219, e222);
    StwoCairoQm31 e224 = { b8, b111, b111, b111 };
    StwoCairoQm31 e225 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e226 = stwo_qm31_mul(e224, e225);
    StwoCairoQm31 e227 = stwo_qm31_add(e223, e226);
    StwoCairoQm31 e228 = stwo_qm31_sub(e227, e10);
    StwoCairoQm31 e229 = { b1, b111, b111, b111 };
    StwoCairoQm31 e230 = { 23u, 0u, 0u, 0u };
    StwoCairoQm31 e231 = { b4, b111, b111, b111 };
    StwoCairoQm31 e232 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e233 = stwo_qm31_mul(e231, e232);
    StwoCairoQm31 e234 = stwo_qm31_add(e230, e233);
    StwoCairoQm31 e235 = { b144, b111, b111, b111 };
    StwoCairoQm31 e236 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e237 = stwo_qm31_mul(e235, e236);
    StwoCairoQm31 e238 = stwo_qm31_add(e234, e237);
    StwoCairoQm31 e239 = { b146, b111, b111, b111 };
    StwoCairoQm31 e240 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e241 = stwo_qm31_mul(e239, e240);
    StwoCairoQm31 e242 = stwo_qm31_add(e238, e241);
    StwoCairoQm31 e243 = { b151, b111, b111, b111 };
    StwoCairoQm31 e244 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e245 = stwo_qm31_mul(e243, e244);
    StwoCairoQm31 e246 = stwo_qm31_add(e242, e245);
    StwoCairoQm31 e247 = { b158, b111, b111, b111 };
    StwoCairoQm31 e248 = stwo_load_qm31(arena, args->ext_params + 5u * 4u);
    StwoCairoQm31 e249 = stwo_qm31_mul(e247, e248);
    StwoCairoQm31 e250 = stwo_qm31_add(e246, e249);
    StwoCairoQm31 e251 = { b162, b111, b111, b111 };
    StwoCairoQm31 e252 = stwo_load_qm31(arena, args->ext_params + 6u * 4u);
    StwoCairoQm31 e253 = stwo_qm31_mul(e251, e252);
    StwoCairoQm31 e254 = stwo_qm31_add(e250, e253);
    StwoCairoQm31 e255 = stwo_qm31_sub(e254, e10);
    StwoCairoQm31 e256 = { b28, b29, b30, b31 };
    StwoCairoQm31 e257 = { b32, b33, b34, b35 };
    StwoCairoQm31 e258 = { b36, b37, b38, b39 };
    StwoCairoQm31 e259 = { b40, b41, b42, b43 };
    StwoCairoQm31 e260 = { b44, b45, b46, b47 };
    StwoCairoQm31 e261 = { b48, b49, b50, b51 };
    StwoCairoQm31 e262 = { b52, b53, b54, b55 };
    StwoCairoQm31 e263 = { b56, b57, b58, b59 };
    StwoCairoQm31 e264 = { b60, b61, b62, b63 };
    StwoCairoQm31 e265 = { b65, b67, b69, b71 };
    StwoCairoQm31 e266 = { b64, b66, b68, b70 };
    StwoCairoQm31 e267 = stwo_qm31_mul(e12, e33);
    StwoCairoQm31 e268 = stwo_qm31_mul(e23, e22);
    StwoCairoQm31 e269 = stwo_qm31_add(e267, e268);
    StwoCairoQm31 e270 = stwo_qm31_mul(e22, e33);
    StwoCairoQm31 e271 = stwo_qm31_mul(e256, e270);
    StwoCairoQm31 e272 = stwo_qm31_sub(e271, e269);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e272, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e273 = stwo_qm31_mul(e34, e55);
    StwoCairoQm31 e274 = stwo_qm31_mul(e45, e44);
    StwoCairoQm31 e275 = stwo_qm31_add(e273, e274);
    StwoCairoQm31 e276 = stwo_qm31_mul(e44, e55);
    StwoCairoQm31 e277 = stwo_qm31_sub(e257, e256);
    StwoCairoQm31 e278 = stwo_qm31_mul(e277, e276);
    StwoCairoQm31 e279 = stwo_qm31_sub(e278, e275);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e279, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e280 = stwo_qm31_mul(e56, e77);
    StwoCairoQm31 e281 = stwo_qm31_mul(e67, e66);
    StwoCairoQm31 e282 = stwo_qm31_add(e280, e281);
    StwoCairoQm31 e283 = stwo_qm31_mul(e66, e77);
    StwoCairoQm31 e284 = stwo_qm31_sub(e258, e257);
    StwoCairoQm31 e285 = stwo_qm31_mul(e284, e283);
    StwoCairoQm31 e286 = stwo_qm31_sub(e285, e282);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e286, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e287 = stwo_qm31_mul(e78, e99);
    StwoCairoQm31 e288 = stwo_qm31_mul(e89, e88);
    StwoCairoQm31 e289 = stwo_qm31_add(e287, e288);
    StwoCairoQm31 e290 = stwo_qm31_mul(e88, e99);
    StwoCairoQm31 e291 = stwo_qm31_sub(e259, e258);
    StwoCairoQm31 e292 = stwo_qm31_mul(e291, e290);
    StwoCairoQm31 e293 = stwo_qm31_sub(e292, e289);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e293, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e294 = stwo_qm31_mul(e100, e121);
    StwoCairoQm31 e295 = stwo_qm31_mul(e111, e110);
    StwoCairoQm31 e296 = stwo_qm31_add(e294, e295);
    StwoCairoQm31 e297 = stwo_qm31_mul(e110, e121);
    StwoCairoQm31 e298 = stwo_qm31_sub(e260, e259);
    StwoCairoQm31 e299 = stwo_qm31_mul(e298, e297);
    StwoCairoQm31 e300 = stwo_qm31_sub(e299, e296);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e300, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e301 = stwo_qm31_mul(e122, e143);
    StwoCairoQm31 e302 = stwo_qm31_mul(e133, e132);
    StwoCairoQm31 e303 = stwo_qm31_add(e301, e302);
    StwoCairoQm31 e304 = stwo_qm31_mul(e132, e143);
    StwoCairoQm31 e305 = stwo_qm31_sub(e261, e260);
    StwoCairoQm31 e306 = stwo_qm31_mul(e305, e304);
    StwoCairoQm31 e307 = stwo_qm31_sub(e306, e303);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e307, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e308 = stwo_qm31_mul(e144, e165);
    StwoCairoQm31 e309 = stwo_qm31_mul(e155, e154);
    StwoCairoQm31 e310 = stwo_qm31_add(e308, e309);
    StwoCairoQm31 e311 = stwo_qm31_mul(e154, e165);
    StwoCairoQm31 e312 = stwo_qm31_sub(e262, e261);
    StwoCairoQm31 e313 = stwo_qm31_mul(e312, e311);
    StwoCairoQm31 e314 = stwo_qm31_sub(e313, e310);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e314, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e315 = stwo_qm31_mul(e166, e187);
    StwoCairoQm31 e316 = stwo_qm31_mul(e177, e176);
    StwoCairoQm31 e317 = stwo_qm31_add(e315, e316);
    StwoCairoQm31 e318 = stwo_qm31_mul(e176, e187);
    StwoCairoQm31 e319 = stwo_qm31_sub(e263, e262);
    StwoCairoQm31 e320 = stwo_qm31_mul(e319, e318);
    StwoCairoQm31 e321 = stwo_qm31_sub(e320, e317);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e321, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e322 = stwo_qm31_mul(e188, e209);
    StwoCairoQm31 e323 = stwo_qm31_mul(e199, e198);
    StwoCairoQm31 e324 = stwo_qm31_add(e322, e323);
    StwoCairoQm31 e325 = stwo_qm31_mul(e198, e209);
    StwoCairoQm31 e326 = stwo_qm31_sub(e264, e263);
    StwoCairoQm31 e327 = stwo_qm31_mul(e326, e325);
    StwoCairoQm31 e328 = stwo_qm31_sub(e327, e324);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e328, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e329 = stwo_qm31_mul(e210, e255);
    StwoCairoQm31 e330 = stwo_qm31_mul(e229, e228);
    StwoCairoQm31 e331 = stwo_qm31_add(e329, e330);
    StwoCairoQm31 e332 = stwo_qm31_mul(e228, e255);
    StwoCairoQm31 e333 = stwo_qm31_sub(e265, e266);
    StwoCairoQm31 e334 = stwo_qm31_sub(e333, e264);
    StwoCairoQm31 e335 = stwo_qm31_add(e334, e11);
    StwoCairoQm31 e336 = stwo_qm31_mul(e335, e332);
    StwoCairoQm31 e337 = stwo_qm31_sub(e336, e331);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e337, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
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
