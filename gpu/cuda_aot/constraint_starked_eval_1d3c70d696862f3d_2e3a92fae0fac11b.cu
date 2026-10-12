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
stwo_cairo_cuda_eval_v6_1d3c70d696862f3d(
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
    unsigned b4 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b15 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 2u, 0u, row, -1);
    unsigned b17 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 2u, 1u, row, -1);
    unsigned b19 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b20 = stwo_trace_value(arena, *args, 2u, 2u, row, -1);
    unsigned b21 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b22 = stwo_trace_value(arena, *args, 2u, 3u, row, -1);
    unsigned b23 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b24 = stwo_m31_mul(b14, b1);
    unsigned b25 = arena[args->base_params + 0u];
    unsigned b26 = stwo_m31_sub(b25, b14);
    unsigned b27 = stwo_m31_sub(b1, b0);
    unsigned b28 = stwo_m31_sub(b27, b25);
    unsigned b29 = stwo_m31_mul(b26, b28);
    unsigned b30 = arena[args->base_params + 1u];
    unsigned b31 = stwo_m31_mul(b25, b3);
    unsigned b32 = stwo_m31_add(b30, b31);
    unsigned b33 = arena[args->base_params + 2u];
    unsigned b34 = stwo_m31_mul(b33, b4);
    unsigned b35 = stwo_m31_add(b32, b34);
    unsigned b36 = arena[args->base_params + 3u];
    unsigned b37 = stwo_m31_mul(b36, b5);
    unsigned b38 = stwo_m31_add(b35, b37);
    unsigned b39 = arena[args->base_params + 4u];
    unsigned b40 = stwo_m31_mul(b39, b6);
    unsigned b41 = stwo_m31_add(b38, b40);
    unsigned b42 = arena[args->base_params + 5u];
    unsigned b43 = stwo_m31_mul(b42, b7);
    unsigned b44 = stwo_m31_add(b41, b43);
    unsigned b45 = arena[args->base_params + 6u];
    unsigned b46 = stwo_m31_mul(b45, b8);
    unsigned b47 = stwo_m31_add(b44, b46);
    unsigned b48 = arena[args->base_params + 7u];
    unsigned b49 = stwo_m31_mul(b48, b9);
    unsigned b50 = stwo_m31_add(b47, b49);
    unsigned b51 = arena[args->base_params + 8u];
    unsigned b52 = stwo_m31_mul(b51, b10);
    unsigned b53 = stwo_m31_add(b50, b52);
    unsigned b54 = stwo_m31_sub(b2, b53);
    unsigned b55 = stwo_m31_sub(b12, b25);
    unsigned b56 = stwo_m31_mul(b12, b55);
    unsigned b57 = stwo_m31_sub(b25, b12);
    unsigned b58 = stwo_m31_mul(b14, b57);
    unsigned b59 = stwo_m31_sub(b25, b11);
    unsigned b60 = stwo_m31_mul(b12, b59);
    unsigned b61 = stwo_m31_mul(b26, b60);
    unsigned b62 = stwo_m31_sub(b11, b12);
    unsigned b63 = arena[args->base_params + 9u];
    unsigned b64 = stwo_m31_sub(b1, b63);
    unsigned b65 = stwo_m31_mul(b62, b64);
    unsigned b66 = stwo_m31_mul(b26, b65);
    unsigned b67 = stwo_m31_sub(b25, b15);
    unsigned b68 = stwo_m31_add(b1, b25);
    unsigned b69 = stwo_m31_sub(b68, b63);
    unsigned b70 = stwo_m31_mul(b12, b69);
    unsigned b71 = stwo_m31_mul(b67, b70);
    unsigned b72 = stwo_m31_sub(b3, b25);
    unsigned b73 = stwo_m31_mul(b3, b72);
    unsigned b74 = stwo_m31_sub(b4, b25);
    unsigned b75 = stwo_m31_mul(b4, b74);
    unsigned b76 = stwo_m31_sub(b5, b25);
    unsigned b77 = stwo_m31_mul(b5, b76);
    unsigned b78 = stwo_m31_sub(b6, b25);
    unsigned b79 = stwo_m31_mul(b6, b78);
    unsigned b80 = stwo_m31_sub(b7, b25);
    unsigned b81 = stwo_m31_mul(b7, b80);
    unsigned b82 = stwo_m31_sub(b8, b25);
    unsigned b83 = stwo_m31_mul(b8, b82);
    unsigned b84 = stwo_m31_sub(b9, b25);
    unsigned b85 = stwo_m31_mul(b9, b84);
    unsigned b86 = stwo_m31_sub(b10, b25);
    unsigned b87 = stwo_m31_mul(b10, b86);
    unsigned b88 = stwo_m31_mul(b12, b13);
    StwoCairoQm31 e0 = { b24, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b29, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b54, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b56, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b58, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b61, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b66, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b71, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b73, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b75, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b77, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b79, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b81, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b83, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b85, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b87, b30, b30, b30 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e17 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e18 = { b88, b30, b30, b30 };
    StwoCairoQm31 e19 = { 17u, 0u, 0u, 0u };
    StwoCairoQm31 e20 = { b1, b30, b30, b30 };
    StwoCairoQm31 e21 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e22 = stwo_qm31_mul(e20, e21);
    StwoCairoQm31 e23 = stwo_qm31_add(e19, e22);
    StwoCairoQm31 e24 = { b2, b30, b30, b30 };
    StwoCairoQm31 e25 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e26 = stwo_qm31_mul(e24, e25);
    StwoCairoQm31 e27 = stwo_qm31_add(e23, e26);
    StwoCairoQm31 e28 = stwo_qm31_sub(e27, e16);
    StwoCairoQm31 e29 = { b17, b19, b21, b23 };
    StwoCairoQm31 e30 = { b16, b18, b20, b22 };
    StwoCairoQm31 e31 = stwo_qm31_sub(e29, e30);
    StwoCairoQm31 e32 = stwo_qm31_add(e31, e17);
    StwoCairoQm31 e33 = stwo_qm31_mul(e32, e28);
    StwoCairoQm31 e34 = stwo_qm31_sub(e33, e18);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
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
