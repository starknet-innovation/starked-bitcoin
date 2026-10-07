//! Splitting a header file (headers by height from genesis) into chained segments.

const std = @import("std");
const H = @import("header_chain.zig");
const R = @import("retarget.zig");
const work = @import("work.zig");

fn word(h: *const H.Header, t: usize) u32 {
    return std.mem.readInt(u32, h[4 * t ..][0..4], .big);
}

/// Chainwork of `all[0..h0]`.
pub fn workBefore(all: []const H.Header, h0: usize) u256 {
    var w: u256 = 0;
    for (all[0..h0]) |*h| w += work.blockProof(R.compactValue(R.le(word(h, 18))));
    return w;
}

/// Start state of the segment beginning at height `h0`, given the chainwork `w` before it.
pub fn startAt(all: []const H.Header, h0: usize, w: u256) H.ChainStart {
    if (h0 == 0) return H.genesis_start;
    var prev: [11]u32 = undefined;
    const k = @min(h0, 11);
    for (0..k) |i| prev[i] = word(&all[h0 - 1 - i], 17);
    const p = (h0 - 1) - (h0 - 1) % 2016;
    return .{
        .height = @intCast(h0),
        .prev_nbits_word = word(&all[h0 - 1], 18),
        .prev_pst_word = word(&all[p], 17),
        .window = H.windowFrom(prev[0..k]),
        .work = w,
    };
}
