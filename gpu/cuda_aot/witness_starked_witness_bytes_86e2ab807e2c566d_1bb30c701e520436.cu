// starked-bitcoin device witness v1 (src/gpu/cuda/witness.zig): block_bytes columns.
// Row r: POS = r; for r < len its byte raw[r], the byte's bits, ACTIVE and MULT = mults[r]
// (the reads of position r); zero past the block (block/bytes.zig generate).
typedef unsigned long long u64;
__device__ __forceinline__ unsigned starked_rotr(unsigned x, unsigned n) { return (x >> n) | (x << (32u - n)); }

extern "C" __global__ void __launch_bounds__(256) starked_witness_bytes_v1_86e2ab807e2c566d(
    const unsigned *raw, const unsigned *mults, unsigned len, const u64 *columns, unsigned rows) {
    const unsigned r = blockIdx.x * blockDim.x + threadIdx.x;
    if (r >= rows) return;
#define PUT(c, v) (((unsigned *)columns[(c)])[r] = (v))
    const unsigned active = r < len ? 1u : 0u;
    const unsigned b = active ? (raw[r >> 2u] >> (8u * (r & 3u))) & 0xffu : 0u;
    PUT(0u, r);
    PUT(1u, b);
    for (unsigned i = 0; i < 8u; ++i) PUT(2u + i, (b >> i) & 1u);
    PUT(10u, active);
    PUT(11u, active ? mults[r] : 0u);
#undef PUT
}
