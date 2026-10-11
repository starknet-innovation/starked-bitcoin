//! `blockrec <epoch dir> <h>`: BLOCK-REC demo. The block proofs at heights `h` and `h + 1` (from
//! `prove-epoch`) as two block leaves and one block node, each proved and verified.
//!
//!   zig build blockrec -Doptimize=ReleaseFast -- data/epoch 0

const std = @import("std");
const sb = @import("starked_bitcoin");

pub fn main() !void {
    var gpa_state = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len < 3) return error.Usage;
    try sb.recursion.block_rec.demo(gpa, args[1], try std.fmt.parseInt(u32, args[2], 10));
}
