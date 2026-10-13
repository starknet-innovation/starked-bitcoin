// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): preprocessed columns.
// Column first + blockIdx.y (desc[8 c..]: kind, k, values offset, period, address lo, hi),
// row i < 2^log in natural order: ir.PreCol.at(i, 2^log). Kinds: 0 is_first, 1 not_last,
// 2 periodic (values[off + i % period]), 3 row_lt (i < k), 4 row_ge_end (i + k >= n).
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }

extern "C" __global__ void __launch_bounds__(256) starked_witness_pre_v1_34475ffbc38611b1(
    const unsigned *desc, const unsigned *values, unsigned first, unsigned log_size, unsigned columns) {
    const unsigned rows = 1u << log_size;
    const unsigned i = blockIdx.x * blockDim.x + threadIdx.x;
    const unsigned c = blockIdx.y;
    if (i >= rows || c >= columns) return;
    const unsigned *d = desc + (u64)(first + c) * 8u;
    const unsigned k = d[1];
    unsigned v = 0u;
    switch (d[0]) {
    case 0u: v = i == 0u ? 1u : 0u; break;
    case 1u: v = i + 1u < rows ? 1u : 0u; break;
    case 2u: v = values[d[2] + i % d[3]]; break;
    case 3u: v = i < k ? 1u : 0u; break;
    default: v = (u64)i + (u64)k >= (u64)rows ? 1u : 0u; break;
    }
    ((unsigned *)(((u64)d[5] << 32u) | (u64)d[4]))[i] = v;
}
