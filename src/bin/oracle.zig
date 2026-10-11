//! `oracle`: VL-ORACLE, the native verifier as oracle for the in-circuit plain verifier
//! (`recursion/fuzz.zig`). Mutates native proof scalars one at a time, FRI included, and requires the
//! native verifier and the circuit to agree (or, for sites the circuit takes from the capture, the
//! native verifier to reject). `REC_FUZZ_BUDGET=<n>` sets the sample size per proof (default 150);
//! `REC_FUZZ_ALL=1` mutates every site. Exits nonzero on any disagreement.
//!
//!   zig build oracle -Doptimize=ReleaseFast

const std = @import("std");
const sb = @import("starked_bitcoin");

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    const fuzz = sb.recursion.fuzz;
    const budget = fuzz.sampleBudget();
    const bad = try fuzz.oracleLogupSystem(gpa, budget, false) + try fuzz.oracleSegment(gpa, budget, false);
    if (bad != 0) {
        std.debug.print("VL-ORACLE: {d} disagreements\n", .{bad});
        std.process.exit(1);
    }
    std.debug.print("VL-ORACLE: native verifier and circuit agree on every mutation\n", .{});
}
