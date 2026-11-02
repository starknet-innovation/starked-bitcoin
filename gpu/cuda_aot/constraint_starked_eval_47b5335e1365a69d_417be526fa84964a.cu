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
stwo_cairo_cuda_eval_v6_47b5335e1365a69d(
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
    unsigned b5 = stwo_trace_value(arena, *args, 1u, 2u, row, -3);
    unsigned b6 = stwo_trace_value(arena, *args, 1u, 2u, row, -2);
    unsigned b7 = stwo_trace_value(arena, *args, 1u, 2u, row, -1);
    unsigned b8 = stwo_trace_value(arena, *args, 1u, 2u, row, 0);
    unsigned b9 = stwo_trace_value(arena, *args, 1u, 3u, row, -1);
    unsigned b10 = stwo_trace_value(arena, *args, 1u, 3u, row, 0);
    unsigned b11 = stwo_trace_value(arena, *args, 1u, 4u, row, 0);
    unsigned b12 = stwo_trace_value(arena, *args, 1u, 4u, row, 1);
    unsigned b13 = stwo_trace_value(arena, *args, 1u, 5u, row, 0);
    unsigned b14 = stwo_trace_value(arena, *args, 1u, 5u, row, 1);
    unsigned b15 = stwo_trace_value(arena, *args, 1u, 6u, row, 0);
    unsigned b16 = stwo_trace_value(arena, *args, 1u, 6u, row, 1);
    unsigned b17 = stwo_trace_value(arena, *args, 1u, 7u, row, 0);
    unsigned b18 = stwo_trace_value(arena, *args, 1u, 8u, row, 0);
    unsigned b19 = stwo_trace_value(arena, *args, 1u, 9u, row, -1);
    unsigned b20 = stwo_trace_value(arena, *args, 1u, 9u, row, 0);
    unsigned b21 = stwo_trace_value(arena, *args, 1u, 10u, row, -1);
    unsigned b22 = stwo_trace_value(arena, *args, 1u, 10u, row, 0);
    unsigned b23 = stwo_trace_value(arena, *args, 1u, 11u, row, -1);
    unsigned b24 = stwo_trace_value(arena, *args, 1u, 11u, row, 0);
    unsigned b25 = stwo_trace_value(arena, *args, 1u, 12u, row, -1);
    unsigned b26 = stwo_trace_value(arena, *args, 1u, 12u, row, 0);
    unsigned b27 = stwo_trace_value(arena, *args, 1u, 13u, row, -1);
    unsigned b28 = stwo_trace_value(arena, *args, 1u, 13u, row, 0);
    unsigned b29 = stwo_trace_value(arena, *args, 1u, 14u, row, -1);
    unsigned b30 = stwo_trace_value(arena, *args, 1u, 14u, row, 0);
    unsigned b31 = stwo_trace_value(arena, *args, 1u, 15u, row, 0);
    unsigned b32 = stwo_trace_value(arena, *args, 1u, 16u, row, 0);
    unsigned b33 = stwo_trace_value(arena, *args, 1u, 17u, row, -1);
    unsigned b34 = stwo_trace_value(arena, *args, 1u, 17u, row, 0);
    unsigned b35 = stwo_trace_value(arena, *args, 0u, 0u, row, 0);
    unsigned b36 = stwo_trace_value(arena, *args, 0u, 1u, row, 0);
    unsigned b37 = stwo_trace_value(arena, *args, 0u, 2u, row, 0);
    unsigned b38 = stwo_trace_value(arena, *args, 0u, 3u, row, 0);
    unsigned b39 = stwo_trace_value(arena, *args, 0u, 4u, row, 0);
    unsigned b40 = stwo_trace_value(arena, *args, 0u, 5u, row, 0);
    unsigned b41 = stwo_trace_value(arena, *args, 2u, 0u, row, 0);
    unsigned b42 = stwo_trace_value(arena, *args, 2u, 1u, row, 0);
    unsigned b43 = stwo_trace_value(arena, *args, 2u, 2u, row, 0);
    unsigned b44 = stwo_trace_value(arena, *args, 2u, 3u, row, 0);
    unsigned b45 = stwo_trace_value(arena, *args, 2u, 4u, row, 0);
    unsigned b46 = stwo_trace_value(arena, *args, 2u, 5u, row, 0);
    unsigned b47 = stwo_trace_value(arena, *args, 2u, 6u, row, 0);
    unsigned b48 = stwo_trace_value(arena, *args, 2u, 7u, row, 0);
    unsigned b49 = stwo_trace_value(arena, *args, 2u, 8u, row, 0);
    unsigned b50 = stwo_trace_value(arena, *args, 2u, 9u, row, 0);
    unsigned b51 = stwo_trace_value(arena, *args, 2u, 10u, row, 0);
    unsigned b52 = stwo_trace_value(arena, *args, 2u, 11u, row, 0);
    unsigned b53 = stwo_trace_value(arena, *args, 2u, 12u, row, -1);
    unsigned b54 = stwo_trace_value(arena, *args, 2u, 12u, row, 0);
    unsigned b55 = stwo_trace_value(arena, *args, 2u, 13u, row, -1);
    unsigned b56 = stwo_trace_value(arena, *args, 2u, 13u, row, 0);
    unsigned b57 = stwo_trace_value(arena, *args, 2u, 14u, row, -1);
    unsigned b58 = stwo_trace_value(arena, *args, 2u, 14u, row, 0);
    unsigned b59 = stwo_trace_value(arena, *args, 2u, 15u, row, -1);
    unsigned b60 = stwo_trace_value(arena, *args, 2u, 15u, row, 0);
    unsigned b61 = arena[args->base_params + 0u];
    unsigned b62 = stwo_m31_sub(b1, b61);
    unsigned b63 = stwo_m31_mul(b1, b62);
    unsigned b64 = stwo_m31_sub(b10, b61);
    unsigned b65 = stwo_m31_mul(b10, b64);
    unsigned b66 = stwo_m31_sub(b11, b61);
    unsigned b67 = stwo_m31_mul(b11, b66);
    unsigned b68 = stwo_m31_sub(b13, b61);
    unsigned b69 = stwo_m31_mul(b13, b68);
    unsigned b70 = stwo_m31_sub(b15, b61);
    unsigned b71 = stwo_m31_mul(b15, b70);
    unsigned b72 = stwo_m31_sub(b17, b61);
    unsigned b73 = stwo_m31_mul(b17, b72);
    unsigned b74 = stwo_m31_sub(b20, b61);
    unsigned b75 = stwo_m31_mul(b20, b74);
    unsigned b76 = stwo_m31_sub(b30, b61);
    unsigned b77 = stwo_m31_mul(b30, b76);
    unsigned b78 = stwo_m31_add(b11, b13);
    unsigned b79 = stwo_m31_add(b78, b15);
    unsigned b80 = stwo_m31_add(b10, b79);
    unsigned b81 = stwo_m31_sub(b1, b80);
    unsigned b82 = stwo_m31_sub(b61, b1);
    unsigned b83 = stwo_m31_mul(b35, b82);
    unsigned b84 = stwo_m31_sub(b61, b36);
    unsigned b85 = stwo_m31_mul(b84, b1);
    unsigned b86 = stwo_m31_sub(b61, b35);
    unsigned b87 = stwo_m31_sub(b61, b0);
    unsigned b88 = stwo_m31_mul(b1, b87);
    unsigned b89 = stwo_m31_mul(b86, b88);
    unsigned b90 = stwo_m31_mul(b35, b4);
    unsigned b91 = stwo_m31_sub(b4, b3);
    unsigned b92 = stwo_m31_sub(b91, b61);
    unsigned b93 = stwo_m31_mul(b86, b92);
    unsigned b94 = stwo_m31_sub(b61, b9);
    unsigned b95 = stwo_m31_mul(b10, b94);
    unsigned b96 = stwo_m31_mul(b86, b95);
    unsigned b97 = stwo_m31_sub(b61, b10);
    unsigned b98 = arena[args->base_params + 1u];
    unsigned b99 = stwo_m31_mul(b97, b98);
    unsigned b100 = stwo_m31_mul(b35, b99);
    unsigned b101 = stwo_m31_sub(b9, b10);
    unsigned b102 = stwo_m31_sub(b4, b98);
    unsigned b103 = stwo_m31_mul(b101, b102);
    unsigned b104 = stwo_m31_mul(b86, b103);
    unsigned b105 = stwo_m31_mul(b35, b97);
    unsigned b106 = stwo_m31_mul(b9, b97);
    unsigned b107 = stwo_m31_mul(b86, b106);
    unsigned b108 = stwo_m31_add(b105, b107);
    unsigned b109 = stwo_m31_sub(b18, b108);
    unsigned b110 = stwo_m31_mul(b19, b1);
    unsigned b111 = stwo_m31_mul(b86, b110);
    unsigned b112 = stwo_m31_add(b18, b111);
    unsigned b113 = stwo_m31_sub(b17, b112);
    unsigned b114 = stwo_m31_sub(b61, b11);
    unsigned b115 = stwo_m31_mul(b17, b114);
    unsigned b116 = stwo_m31_mul(b17, b24);
    unsigned b117 = stwo_m31_mul(b18, b22);
    unsigned b118 = stwo_m31_sub(b17, b18);
    unsigned b119 = stwo_m31_sub(b22, b21);
    unsigned b120 = stwo_m31_sub(b119, b61);
    unsigned b121 = stwo_m31_mul(b118, b120);
    unsigned b122 = stwo_m31_sub(b79, b17);
    unsigned b123 = stwo_m31_mul(b122, b119);
    unsigned b124 = stwo_m31_sub(b26, b25);
    unsigned b125 = stwo_m31_mul(b122, b124);
    unsigned b126 = stwo_m31_sub(b28, b27);
    unsigned b127 = stwo_m31_mul(b122, b126);
    unsigned b128 = stwo_m31_sub(b24, b23);
    unsigned b129 = stwo_m31_sub(b128, b61);
    unsigned b130 = stwo_m31_mul(b122, b129);
    unsigned b131 = stwo_m31_add(b12, b14);
    unsigned b132 = stwo_m31_sub(b61, b131);
    unsigned b133 = stwo_m31_mul(b11, b132);
    unsigned b134 = arena[args->base_params + 2u];
    unsigned b135 = stwo_m31_sub(b24, b134);
    unsigned b136 = stwo_m31_mul(b14, b135);
    unsigned b137 = stwo_m31_mul(b11, b136);
    unsigned b138 = stwo_m31_add(b14, b16);
    unsigned b139 = stwo_m31_sub(b61, b138);
    unsigned b140 = stwo_m31_mul(b13, b139);
    unsigned b141 = arena[args->base_params + 3u];
    unsigned b142 = stwo_m31_sub(b24, b141);
    unsigned b143 = stwo_m31_mul(b16, b142);
    unsigned b144 = stwo_m31_mul(b13, b143);
    unsigned b145 = stwo_m31_sub(b61, b20);
    unsigned b146 = stwo_m31_sub(b61, b16);
    unsigned b147 = stwo_m31_mul(b145, b146);
    unsigned b148 = stwo_m31_mul(b15, b147);
    unsigned b149 = stwo_m31_sub(b61, b15);
    unsigned b150 = stwo_m31_mul(b20, b149);
    unsigned b151 = stwo_m31_add(b141, b28);
    unsigned b152 = stwo_m31_sub(b24, b151);
    unsigned b153 = stwo_m31_mul(b20, b152);
    unsigned b154 = stwo_m31_sub(b61, b2);
    unsigned b155 = stwo_m31_mul(b1, b154);
    unsigned b156 = stwo_m31_sub(b32, b155);
    unsigned b157 = stwo_m31_mul(b32, b145);
    unsigned b158 = stwo_m31_mul(b30, b82);
    unsigned b159 = stwo_m31_mul(b35, b30);
    unsigned b160 = stwo_m31_sub(b61, b30);
    unsigned b161 = stwo_m31_mul(b29, b160);
    unsigned b162 = stwo_m31_mul(b1, b161);
    unsigned b163 = stwo_m31_sub(b61, b29);
    unsigned b164 = stwo_m31_sub(b61, b38);
    unsigned b165 = stwo_m31_mul(b163, b164);
    unsigned b166 = stwo_m31_mul(b30, b165);
    unsigned b167 = stwo_m31_mul(b30, b39);
    unsigned b168 = stwo_m31_mul(b1, b160);
    unsigned b169 = stwo_m31_sub(b31, b168);
    unsigned b170 = stwo_m31_sub(b61, b39);
    unsigned b171 = stwo_m31_mul(b170, b154);
    unsigned b172 = stwo_m31_mul(b31, b171);
    unsigned b173 = stwo_m31_mul(b35, b34);
    unsigned b174 = stwo_m31_sub(b34, b33);
    unsigned b175 = stwo_m31_sub(b174, b38);
    unsigned b176 = stwo_m31_mul(b86, b175);
    unsigned b177 = arena[args->base_params + 4u];
    unsigned b178 = stwo_m31_add(b40, b61);
    unsigned b179 = stwo_m31_mul(b30, b178);
    unsigned b180 = stwo_m31_sub(b177, b179);
    unsigned b181 = stwo_m31_mul(b32, b180);
    unsigned b182 = arena[args->base_params + 5u];
    unsigned b183 = arena[args->base_params + 6u];
    unsigned b184 = stwo_m31_sub(b182, b183);
    unsigned b185 = stwo_m31_add(b34, b61);
    unsigned b186 = stwo_m31_sub(b185, b30);
    unsigned b187 = stwo_m31_sub(b184, b186);
    unsigned b188 = stwo_m31_mul(b32, b187);
    unsigned b189 = stwo_m31_add(b22, b61);
    unsigned b190 = arena[args->base_params + 7u];
    unsigned b191 = arena[args->base_params + 8u];
    unsigned b192 = stwo_m31_sub(b190, b191);
    unsigned b193 = stwo_m31_sub(b189, b192);
    unsigned b194 = stwo_m31_mul(b32, b193);
    unsigned b195 = stwo_m31_neg(b10);
    unsigned b196 = stwo_m31_neg(b11);
    unsigned b197 = stwo_m31_add(b26, b24);
    unsigned b198 = stwo_m31_neg(b13);
    unsigned b199 = arena[args->base_params + 9u];
    unsigned b200 = stwo_m31_sub(b24, b199);
    unsigned b201 = stwo_m31_neg(b15);
    unsigned b202 = arena[args->base_params + 10u];
    unsigned b203 = stwo_m31_add(b197, b202);
    unsigned b204 = stwo_m31_neg(b17);
    unsigned b205 = stwo_m31_neg(b30);
    unsigned b206 = stwo_m31_mul(b31, b37);
    unsigned b207 = arena[args->base_params + 11u];
    unsigned b208 = stwo_m31_sub(b4, b207);
    unsigned b209 = arena[args->base_params + 12u];
    unsigned b210 = stwo_m31_mul(b209, b7);
    unsigned b211 = stwo_m31_add(b210, b8);
    unsigned b212 = stwo_m31_mul(b209, b5);
    unsigned b213 = stwo_m31_add(b212, b6);
    unsigned b214 = stwo_m31_neg(b35);
    unsigned b215 = stwo_m31_sub(b184, b61);
    unsigned b216 = arena[args->base_params + 13u];
    StwoCairoQm31 e0 = { b63, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e0, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 0u) * 4u)));
    StwoCairoQm31 e1 = { b65, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e1, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 1u) * 4u)));
    StwoCairoQm31 e2 = { b67, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e2, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 2u) * 4u)));
    StwoCairoQm31 e3 = { b69, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e3, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 3u) * 4u)));
    StwoCairoQm31 e4 = { b71, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e4, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 4u) * 4u)));
    StwoCairoQm31 e5 = { b73, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e5, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 5u) * 4u)));
    StwoCairoQm31 e6 = { b75, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e6, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 6u) * 4u)));
    StwoCairoQm31 e7 = { b77, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e7, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 7u) * 4u)));
    StwoCairoQm31 e8 = { b81, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e8, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 8u) * 4u)));
    StwoCairoQm31 e9 = { b83, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e9, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 9u) * 4u)));
    StwoCairoQm31 e10 = { b85, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e10, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 10u) * 4u)));
    StwoCairoQm31 e11 = { b89, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e11, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 11u) * 4u)));
    StwoCairoQm31 e12 = { b90, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e12, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 12u) * 4u)));
    StwoCairoQm31 e13 = { b93, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e13, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 13u) * 4u)));
    StwoCairoQm31 e14 = { b96, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e14, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 14u) * 4u)));
    StwoCairoQm31 e15 = { b100, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e15, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 15u) * 4u)));
    StwoCairoQm31 e16 = { b104, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e16, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 16u) * 4u)));
    StwoCairoQm31 e17 = { b109, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e17, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 17u) * 4u)));
    StwoCairoQm31 e18 = { b113, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e18, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 18u) * 4u)));
    StwoCairoQm31 e19 = { b115, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e19, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 19u) * 4u)));
    StwoCairoQm31 e20 = { b116, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e20, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 20u) * 4u)));
    StwoCairoQm31 e21 = { b117, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e21, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 21u) * 4u)));
    StwoCairoQm31 e22 = { b121, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e22, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 22u) * 4u)));
    StwoCairoQm31 e23 = { b123, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e23, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 23u) * 4u)));
    StwoCairoQm31 e24 = { b125, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e24, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 24u) * 4u)));
    StwoCairoQm31 e25 = { b127, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e25, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 25u) * 4u)));
    StwoCairoQm31 e26 = { b130, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e26, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 26u) * 4u)));
    StwoCairoQm31 e27 = { b133, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e27, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 27u) * 4u)));
    StwoCairoQm31 e28 = { b137, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e28, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 28u) * 4u)));
    StwoCairoQm31 e29 = { b140, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e29, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 29u) * 4u)));
    StwoCairoQm31 e30 = { b144, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e30, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 30u) * 4u)));
    StwoCairoQm31 e31 = { b148, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e31, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 31u) * 4u)));
    StwoCairoQm31 e32 = { b150, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e32, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 32u) * 4u)));
    StwoCairoQm31 e33 = { b153, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e33, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 33u) * 4u)));
    StwoCairoQm31 e34 = { b156, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e34, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 34u) * 4u)));
    StwoCairoQm31 e35 = { b157, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e35, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 35u) * 4u)));
    StwoCairoQm31 e36 = { b158, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e36, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 36u) * 4u)));
    StwoCairoQm31 e37 = { b159, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e37, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 37u) * 4u)));
    StwoCairoQm31 e38 = { b162, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e38, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 38u) * 4u)));
    StwoCairoQm31 e39 = { b166, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e39, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 39u) * 4u)));
    StwoCairoQm31 e40 = { b167, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e40, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 40u) * 4u)));
    StwoCairoQm31 e41 = { b169, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e41, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 41u) * 4u)));
    StwoCairoQm31 e42 = { b172, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e42, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 42u) * 4u)));
    StwoCairoQm31 e43 = { b173, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e43, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 43u) * 4u)));
    StwoCairoQm31 e44 = { b176, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e44, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 44u) * 4u)));
    StwoCairoQm31 e45 = { b181, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e45, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 45u) * 4u)));
    StwoCairoQm31 e46 = { b188, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e46, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 46u) * 4u)));
    StwoCairoQm31 e47 = { b194, b216, b216, b216 };
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e47, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 47u) * 4u)));
    StwoCairoQm31 e48 = stwo_load_qm31(arena, args->ext_params + 0u * 4u);
    StwoCairoQm31 e49 = stwo_load_qm31(arena, args->ext_params + 4u * 4u);
    StwoCairoQm31 e50 = { b195, b216, b216, b216 };
    StwoCairoQm31 e51 = { 28u, 0u, 0u, 0u };
    StwoCairoQm31 e52 = { b4, b216, b216, b216 };
    StwoCairoQm31 e53 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e54 = stwo_qm31_mul(e52, e53);
    StwoCairoQm31 e55 = stwo_qm31_add(e51, e54);
    StwoCairoQm31 e56 = { b8, b216, b216, b216 };
    StwoCairoQm31 e57 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e58 = stwo_qm31_mul(e56, e57);
    StwoCairoQm31 e59 = stwo_qm31_add(e55, e58);
    StwoCairoQm31 e60 = stwo_qm31_sub(e59, e48);
    StwoCairoQm31 e61 = { b196, b216, b216, b216 };
    StwoCairoQm31 e62 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e63 = { b197, b216, b216, b216 };
    StwoCairoQm31 e64 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e65 = stwo_qm31_mul(e63, e64);
    StwoCairoQm31 e66 = stwo_qm31_add(e62, e65);
    StwoCairoQm31 e67 = { b8, b216, b216, b216 };
    StwoCairoQm31 e68 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e69 = stwo_qm31_mul(e67, e68);
    StwoCairoQm31 e70 = stwo_qm31_add(e66, e69);
    StwoCairoQm31 e71 = stwo_qm31_sub(e70, e48);
    StwoCairoQm31 e72 = { b198, b216, b216, b216 };
    StwoCairoQm31 e73 = { 33u, 0u, 0u, 0u };
    StwoCairoQm31 e74 = { b22, b216, b216, b216 };
    StwoCairoQm31 e75 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e76 = stwo_qm31_mul(e74, e75);
    StwoCairoQm31 e77 = stwo_qm31_add(e73, e76);
    StwoCairoQm31 e78 = { b200, b216, b216, b216 };
    StwoCairoQm31 e79 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e80 = stwo_qm31_mul(e78, e79);
    StwoCairoQm31 e81 = stwo_qm31_add(e77, e80);
    StwoCairoQm31 e82 = { b8, b216, b216, b216 };
    StwoCairoQm31 e83 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e84 = stwo_qm31_mul(e82, e83);
    StwoCairoQm31 e85 = stwo_qm31_add(e81, e84);
    StwoCairoQm31 e86 = stwo_qm31_sub(e85, e48);
    StwoCairoQm31 e87 = { b201, b216, b216, b216 };
    StwoCairoQm31 e88 = { 3u, 0u, 0u, 0u };
    StwoCairoQm31 e89 = { b203, b216, b216, b216 };
    StwoCairoQm31 e90 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e91 = stwo_qm31_mul(e89, e90);
    StwoCairoQm31 e92 = stwo_qm31_add(e88, e91);
    StwoCairoQm31 e93 = { b8, b216, b216, b216 };
    StwoCairoQm31 e94 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e95 = stwo_qm31_mul(e93, e94);
    StwoCairoQm31 e96 = stwo_qm31_add(e92, e95);
    StwoCairoQm31 e97 = stwo_qm31_sub(e96, e48);
    StwoCairoQm31 e98 = { b204, b216, b216, b216 };
    StwoCairoQm31 e99 = { 32u, 0u, 0u, 0u };
    StwoCairoQm31 e100 = { b22, b216, b216, b216 };
    StwoCairoQm31 e101 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e102 = stwo_qm31_mul(e100, e101);
    StwoCairoQm31 e103 = stwo_qm31_add(e99, e102);
    StwoCairoQm31 e104 = { b26, b216, b216, b216 };
    StwoCairoQm31 e105 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e106 = stwo_qm31_mul(e104, e105);
    StwoCairoQm31 e107 = stwo_qm31_add(e103, e106);
    StwoCairoQm31 e108 = { b28, b216, b216, b216 };
    StwoCairoQm31 e109 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e110 = stwo_qm31_mul(e108, e109);
    StwoCairoQm31 e111 = stwo_qm31_add(e107, e110);
    StwoCairoQm31 e112 = stwo_qm31_sub(e111, e48);
    StwoCairoQm31 e113 = { b205, b216, b216, b216 };
    StwoCairoQm31 e114 = { 29u, 0u, 0u, 0u };
    StwoCairoQm31 e115 = { b40, b216, b216, b216 };
    StwoCairoQm31 e116 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e117 = stwo_qm31_mul(e115, e116);
    StwoCairoQm31 e118 = stwo_qm31_add(e114, e117);
    StwoCairoQm31 e119 = { b8, b216, b216, b216 };
    StwoCairoQm31 e120 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e121 = stwo_qm31_mul(e119, e120);
    StwoCairoQm31 e122 = stwo_qm31_add(e118, e121);
    StwoCairoQm31 e123 = stwo_qm31_sub(e122, e48);
    StwoCairoQm31 e124 = { b206, b216, b216, b216 };
    StwoCairoQm31 e125 = { 34u, 0u, 0u, 0u };
    StwoCairoQm31 e126 = { b208, b216, b216, b216 };
    StwoCairoQm31 e127 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e128 = stwo_qm31_mul(e126, e127);
    StwoCairoQm31 e129 = stwo_qm31_add(e125, e128);
    StwoCairoQm31 e130 = { b211, b216, b216, b216 };
    StwoCairoQm31 e131 = stwo_load_qm31(arena, args->ext_params + 2u * 4u);
    StwoCairoQm31 e132 = stwo_qm31_mul(e130, e131);
    StwoCairoQm31 e133 = stwo_qm31_add(e129, e132);
    StwoCairoQm31 e134 = { b213, b216, b216, b216 };
    StwoCairoQm31 e135 = stwo_load_qm31(arena, args->ext_params + 3u * 4u);
    StwoCairoQm31 e136 = stwo_qm31_mul(e134, e135);
    StwoCairoQm31 e137 = stwo_qm31_add(e133, e136);
    StwoCairoQm31 e138 = stwo_qm31_sub(e137, e48);
    StwoCairoQm31 e139 = { b214, b216, b216, b216 };
    StwoCairoQm31 e140 = { 35u, 0u, 0u, 0u };
    StwoCairoQm31 e141 = { b215, b216, b216, b216 };
    StwoCairoQm31 e142 = stwo_load_qm31(arena, args->ext_params + 1u * 4u);
    StwoCairoQm31 e143 = stwo_qm31_mul(e141, e142);
    StwoCairoQm31 e144 = stwo_qm31_add(e140, e143);
    StwoCairoQm31 e145 = stwo_qm31_sub(e144, e48);
    StwoCairoQm31 e146 = { b41, b42, b43, b44 };
    StwoCairoQm31 e147 = { b45, b46, b47, b48 };
    StwoCairoQm31 e148 = { b49, b50, b51, b52 };
    StwoCairoQm31 e149 = { b54, b56, b58, b60 };
    StwoCairoQm31 e150 = { b53, b55, b57, b59 };
    StwoCairoQm31 e151 = stwo_qm31_mul(e50, e71);
    StwoCairoQm31 e152 = stwo_qm31_mul(e61, e60);
    StwoCairoQm31 e153 = stwo_qm31_add(e151, e152);
    StwoCairoQm31 e154 = stwo_qm31_mul(e60, e71);
    StwoCairoQm31 e155 = stwo_qm31_mul(e146, e154);
    StwoCairoQm31 e156 = stwo_qm31_sub(e155, e153);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e156, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 48u) * 4u)));
    StwoCairoQm31 e157 = stwo_qm31_mul(e72, e97);
    StwoCairoQm31 e158 = stwo_qm31_mul(e87, e86);
    StwoCairoQm31 e159 = stwo_qm31_add(e157, e158);
    StwoCairoQm31 e160 = stwo_qm31_mul(e86, e97);
    StwoCairoQm31 e161 = stwo_qm31_sub(e147, e146);
    StwoCairoQm31 e162 = stwo_qm31_mul(e161, e160);
    StwoCairoQm31 e163 = stwo_qm31_sub(e162, e159);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e163, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 49u) * 4u)));
    StwoCairoQm31 e164 = stwo_qm31_mul(e98, e123);
    StwoCairoQm31 e165 = stwo_qm31_mul(e113, e112);
    StwoCairoQm31 e166 = stwo_qm31_add(e164, e165);
    StwoCairoQm31 e167 = stwo_qm31_mul(e112, e123);
    StwoCairoQm31 e168 = stwo_qm31_sub(e148, e147);
    StwoCairoQm31 e169 = stwo_qm31_mul(e168, e167);
    StwoCairoQm31 e170 = stwo_qm31_sub(e169, e166);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e170, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 50u) * 4u)));
    StwoCairoQm31 e171 = stwo_qm31_mul(e124, e145);
    StwoCairoQm31 e172 = stwo_qm31_mul(e139, e138);
    StwoCairoQm31 e173 = stwo_qm31_add(e171, e172);
    StwoCairoQm31 e174 = stwo_qm31_mul(e138, e145);
    StwoCairoQm31 e175 = stwo_qm31_sub(e149, e150);
    StwoCairoQm31 e176 = stwo_qm31_sub(e175, e148);
    StwoCairoQm31 e177 = stwo_qm31_add(e176, e49);
    StwoCairoQm31 e178 = stwo_qm31_mul(e177, e174);
    StwoCairoQm31 e179 = stwo_qm31_sub(e178, e173);
    part_acc = stwo_qm31_add(part_acc, stwo_qm31_mul(e179, stwo_load_qm31(arena, args->random_coeffs + (args->rc_base + 51u) * 4u)));
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
