//! `blockpack <epoch dir> <from> <k>... [prove]`: leaf-packing spike. k consecutive block proofs
//! (from `prove-epoch`) verified in one circuit; prints its size, and with `prove` proves it.
//!
//!   zig build -Doptimize=ReleaseFast && zig-out/bin/blockpack data/epoch-pack 0 1 2 4 prove

const std = @import("std");
const sb = @import("starked_bitcoin");

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    if (args.len < 4) return error.Usage;
    var ks: std.ArrayList(usize) = .empty;
    defer ks.deinit(gpa);
    var prove = false;
    for (args[3..]) |x| {
        if (std.mem.eql(u8, x, "prove")) prove = true else try ks.append(gpa, try std.fmt.parseInt(usize, x, 10));
    }
    try sb.recursion.block_pack.measure(gpa, args[1], try std.fmt.parseInt(u32, args[2], 10), ks.items, prove);
}
