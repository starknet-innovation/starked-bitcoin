//! `blockleaf [test|prod] [prove]`: BLOCK-REC measurement. A block-170 proof verified by the plain
//! in-circuit verifier; prints the circuit's size and validity, and with `prove` proves it.
//!
//!   zig build blockleaf -Doptimize=ReleaseFast -- test prove

const std = @import("std");
const sb = @import("starked_bitcoin");

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    var weak = true;
    var prove = false;
    for (args[1..]) |x| {
        if (std.mem.eql(u8, x, "prod")) weak = false;
        if (std.mem.eql(u8, x, "prove")) prove = true;
    }
    try sb.recursion.block_leaf.measure(gpa, weak, prove);
}
