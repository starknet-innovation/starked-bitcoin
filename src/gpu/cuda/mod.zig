//! Resident CUDA prover for the block system (GPU plan step 3; docs/design/gpu-cuda.md).
//!
//! stwo-zig's resident circuit-recursion CUDA pipeline (`integrations/circuit_cuda`) re-targeted
//! at our STWZEVA-lowered block system: its generic stages are imported as modules, and only the
//! circuit-specific pieces (geometry, transcript prefix, memory plan, ingress, terminal decode) are
//! replaced here. Built only with `-Dcuda=true`.

pub const circuit_cuda = @import("stwo_circuit_cuda_integration");
pub const catalog = @import("catalog.zig");
pub const plan = @import("plan.zig");
pub const transcript = @import("transcript.zig");

test {
    _ = catalog;
    _ = plan;
    _ = transcript;
    _ = @import("cpu_parity_test.zig");
}
