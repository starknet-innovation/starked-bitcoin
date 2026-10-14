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
    if (args.len < 3) return error.Usage;
    if (std.mem.eql(u8, args[1], "widenode")) {
        // blockpack widenode <dir> <from> <a> [prove]
        const prove_node = args.len > 5 and std.mem.eql(u8, args[5], "prove");
        return sb.recursion.block_node_k.demo(gpa, args[2], try std.fmt.parseInt(u32, args[3], 10), try std.fmt.parseInt(u32, args[4], 10), prove_node);
    }
    if (std.mem.eql(u8, args[1], "shapes")) return sb.recursion.block_pack.shapes(gpa, args[2], try std.fmt.parseInt(u32, args[3], 10));
    if (std.mem.eql(u8, args[1], "nodecost")) {
        // blockpack nodecost <dir> <from> <fold> <k...>
        var ks2: std.ArrayList(usize) = .empty;
        defer ks2.deinit(gpa);
        for (args[5..]) |x| try ks2.append(gpa, try std.fmt.parseInt(usize, x, 10));
        return sb.recursion.block_pack.nodeCost(gpa, args[2], try std.fmt.parseInt(u32, args[3], 10), ks2.items, try std.fmt.parseInt(u32, args[4], 10));
    }
    var ks: std.ArrayList(usize) = .empty;
    defer ks.deinit(gpa);
    var prove = false;
    for (args[3..]) |x| {
        if (std.mem.eql(u8, x, "prove")) prove = true else try ks.append(gpa, try std.fmt.parseInt(usize, x, 10));
    }
    try sb.recursion.block_pack.measure(gpa, args[1], try std.fmt.parseInt(u32, args[2], 10), ks.items, prove);
}
