//! Resident CUDA prover for the block system (GPU plan step 3; docs/design/gpu-cuda.md).
//!
//! stwo-zig's resident circuit-recursion CUDA pipeline (`integrations/circuit_cuda`) re-targeted
//! at our STWZEVA-lowered block system: its generic stages are imported as modules, and only the
//! circuit-specific pieces are replaced or adapted here. Built only with `-Dcuda=true`.
//!
//! - `catalog`: one AOT constraint kernel per AIR (`gpu/cuda_aot/`).
//! - `plan`: geometry and stage plans (with forks `topology`, `masks`).
//! - `transcript`: our prefix; host sink, device sink, host model of the device.
//! - `memory`: the arena's slots and views; `composition_controller` (fork); `terminal`.
//! - `reorder`: the natural → storage reorder of trees 0–1 (`.trace_generation`).
//! - `logup`: device LogUp (generated fraction kernels, stwo-zig's relation completion).
//! - `pipeline`, `prover`: the device schedule and the prover.

pub const circuit_cuda = @import("stwo_circuit_cuda_integration");
pub const catalog = @import("catalog.zig");
pub const plan = @import("plan.zig");
pub const topology = @import("topology.zig");
pub const masks = @import("masks.zig");
pub const transcript = @import("transcript.zig");
pub const memory = @import("memory.zig");
pub const composition_controller = @import("composition_controller.zig");
pub const terminal = @import("terminal.zig");
pub const pipeline = @import("pipeline.zig");
pub const logup = @import("logup.zig");
pub const reorder = @import("reorder.zig");
pub const prover = @import("prover.zig");

test {
    _ = catalog;
    _ = plan;
    _ = transcript;
    _ = terminal;
    _ = prover;
    _ = logup;
    _ = @import("logup_test.zig");
    _ = @import("reorder_test.zig");
    _ = @import("cpu_parity_test.zig");
    _ = @import("arena_test.zig");
}
