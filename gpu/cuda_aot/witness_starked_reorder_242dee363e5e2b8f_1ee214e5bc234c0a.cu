// starked-bitcoin natural -> storage reorder v1 (src/gpu/cuda/reorder.zig).
// storage[c * 2^log + s] = natural[c * 2^log + natural_row(s)]: storage row s is the
// bit-reversed circle-domain index of natural (coset-order) row natural_row(s).
typedef unsigned long long u64;
extern "C" __global__ void __launch_bounds__(256) starked_reorder_v1_242dee363e5e2b8f(
    const unsigned *natural, unsigned *storage, unsigned log_size, unsigned columns) {
    const unsigned rows = 1u << log_size;
    const unsigned s = blockIdx.x * blockDim.x + threadIdx.x;
    const unsigned c = blockIdx.y;
    if (s >= rows || c >= columns) return;
    // One row (log 0) is its own image; else circle c < n/2 is natural 2c, c >= n/2 is 2(n - c) - 1.
    const unsigned circle = log_size == 0u ? 0u : __brev(s) >> (32u - log_size);
    const unsigned i = log_size == 0u ? 0u : circle < (rows >> 1u) ? circle << 1u : ((rows - circle) << 1u) - 1u;
    const u64 base = (u64)c << log_size;
    storage[base + s] = natural[base + i];
}
