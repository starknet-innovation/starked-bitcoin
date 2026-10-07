//! Witness for the chainwork constraints (lean/StarkedAir/Gadgets/Work.lean): rows 241..253 of
//! a header. Per header `q = ⌊2^256 / (T + 1)⌋` (Core `GetBlockProof`), enforced as
//! `R = q·mant`, `R·256^s + q + ρ = 2^256`, `ρ + σ = T`, and the running chainwork `W += q`.
//! Every carry is computed by replaying the exact column equation the AIR checks.

const std = @import("std");

/// Raw words for rows 241..253 (index 0 = row 241), columns a, e, w.
pub const Scratch = struct {
    a: [13]u32 = [_]u32{0} ** 13,
    e: [13]u32 = [_]u32{0} ** 13,
    w: [13]u32 = [_]u32{0} ** 13,
    /// Chainwork after this header.
    work: u256 = 0,
};

/// `GetBlockProof` for a valid target `t` (Core's formula over 256-bit integers).
pub fn blockProof(t: u256) u256 {
    return (~t) / (t + 1) + 1;
}

const Col = enum { a, e, w };
const Slot = struct { row: usize, col: Col };

fn put(s: *Scratch, slot: Slot, value: u32, shift: u5, width: u6) void {
    const mask: u32 = if (width == 32) 0xffffffff else (@as(u32, 1) << @intCast(width)) - 1;
    const v = (value & mask) << shift;
    const i = slot.row - 241;
    switch (slot.col) {
        .a => s.a[i] |= v,
        .e => s.e[i] |= v,
        .w => s.w[i] |= v,
    }
}

fn putFields(s: *Scratch, slots: []const Slot, width: u6, per: usize, fields: []const u32) void {
    for (fields, 0..) |f, i| put(s, slots[i / per], f, @intCast(width * (i % per)), width);
}

const q_slots = [_]Slot{ .{ .row = 241, .col = .a }, .{ .row = 241, .col = .e }, .{ .row = 241, .col = .w }, .{ .row = 242, .col = .a } };
const r_slots = [_]Slot{ .{ .row = 242, .col = .e }, .{ .row = 242, .col = .w }, .{ .row = 243, .col = .a }, .{ .row = 243, .col = .e } };
const rho_slots = [_]Slot{ .{ .row = 243, .col = .w }, .{ .row = 244, .col = .a }, .{ .row = 244, .col = .e }, .{ .row = 244, .col = .w }, .{ .row = 245, .col = .a }, .{ .row = 245, .col = .e }, .{ .row = 245, .col = .w } };
const sig_slots = [_]Slot{ .{ .row = 246, .col = .a }, .{ .row = 246, .col = .e }, .{ .row = 246, .col = .w }, .{ .row = 247, .col = .a }, .{ .row = 247, .col = .e }, .{ .row = 247, .col = .w }, .{ .row = 248, .col = .a } };
const w_slots = [_]Slot{ .{ .row = 248, .col = .e }, .{ .row = 248, .col = .w }, .{ .row = 249, .col = .a }, .{ .row = 249, .col = .e }, .{ .row = 249, .col = .w } };
const pc_slots = [_]Slot{ .{ .row = 250, .col = .a }, .{ .row = 250, .col = .e }, .{ .row = 250, .col = .w }, .{ .row = 251, .col = .a }, .{ .row = 251, .col = .e }, .{ .row = 251, .col = .w } };
const mc_slots = [_]Slot{ .{ .row = 252, .col = .a }, .{ .row = 252, .col = .e }, .{ .row = 252, .col = .w } };

fn bytesOf(comptime n: usize, x: u256) [n]u32 {
    var out: [n]u32 = undefined;
    for (0..n) |i| out[i] = @intCast((x >> @intCast(8 * i)) & 0xff);
    return out;
}

/// `word18` is the raw header word 18 (nBits); `prev` the chainwork before this header.
pub fn scratch(word18: u32, prev: u256) !Scratch {
    const n_size = word18 & 0xff;
    if (n_size < 3 + 16 or n_size > 29) return error.TargetOutOfRange;
    const s: usize = n_size - 3;
    const mant: u32 = (word18 >> 24) | (((word18 >> 16) & 0xff) << 8) | (((word18 >> 8) & 0x7f) << 16);
    const t: u256 = @as(u256, mant) << @intCast(8 * s);
    const q = blockProof(t);
    const r = q * mant;
    const rho = (~t) % (t + 1);
    const sig = t - rho;
    const work = prev + q;
    if (q >> 128 != 0 or r >> 128 != 0 or work >> 160 != 0) return error.WorkOutOfRange;

    const qb = bytesOf(16, q);
    const rb = bytesOf(16, r);
    const rhob = bytesOf(28, rho);
    const sigb = bytesOf(28, sig);
    const mb = [3]u32{ mant & 0xff, (mant >> 8) & 0xff, mant >> 16 };
    var out = Scratch{ .work = work };

    // R = q · mant (columns 0..17).
    var pc: [17]u32 = undefined;
    for (0..18) |k| {
        var sum: u32 = if (k == 0) 0 else pc[k - 1];
        for (0..16) |i| if (i <= k and k - i < 3) {
            sum += qb[i] * mb[k - i];
        };
        const rk: u32 = if (k < 16) rb[k] else 0;
        if (sum < rk or (sum - rk) % 256 != 0) return error.ProductColumn;
        if (k < 17) pc[k] = (sum - rk) / 256 else if (sum != rk) return error.ProductColumn;
    }
    // R · 256^s + q + ρ = 2^256 (columns 0..41).
    var mc: [41]u32 = undefined;
    for (0..42) |k| {
        var sum: u32 = if (k == 0) 0 else mc[k - 1];
        if (k >= s and k - s < 16) sum += rb[k - s];
        if (k < 16) sum += qb[k];
        if (k < 28) sum += rhob[k];
        const target: u32 = @intFromBool(k == 32);
        if (sum < target or (sum - target) % 256 != 0) return error.MainColumn;
        if (k < 41) mc[k] = (sum - target) / 256 else if (sum != target) return error.MainColumn;
    }
    // ρ + σ = T (columns 0..28).
    var ec: [28]u32 = undefined;
    for (0..29) |k| {
        var sum: u32 = if (k == 0) 0 else ec[k - 1];
        if (k < 28) sum += rhob[k] + sigb[k];
        const tk: u32 = if (k >= s and k - s < 3) mb[k - s] else 0;
        if (sum < tk or (sum - tk) % 256 != 0) return error.RemainderColumn;
        if (k < 28) ec[k] = (sum - tk) / 256 else if (sum != tk) return error.RemainderColumn;
    }
    // W = prev + q in 16-bit limbs (0..9).
    var wc: [9]u32 = undefined;
    for (0..10) |l| {
        const pl: u32 = @intCast((prev >> @intCast(16 * l)) & 0xffff);
        const ql: u32 = @intCast((q >> @intCast(16 * l)) & 0xffff);
        const wl: u32 = @intCast((work >> @intCast(16 * l)) & 0xffff);
        const sum = pl + ql + (if (l == 0) 0 else wc[l - 1]);
        if (l < 9) wc[l] = (sum - wl) / 65536 else if (sum != wl) return error.WorkColumn;
    }

    putFields(&out, &q_slots, 8, 4, &qb);
    putFields(&out, &r_slots, 8, 4, &rb);
    putFields(&out, &rho_slots, 8, 4, &rhob);
    putFields(&out, &sig_slots, 8, 4, &sigb);
    putFields(&out, &w_slots, 8, 4, &bytesOf(20, work));
    putFields(&out, &pc_slots, 10, 3, &pc);
    putFields(&out, &mc_slots, 2, 16, &mc);
    putFields(&out, &.{.{ .row = 253, .col = .a }}, 1, 32, &ec);
    putFields(&out, &.{.{ .row = 253, .col = .e }}, 1, 32, &wc);
    return out;
}

test "block proof matches Core's genesis chainwork and a Python reference" {
    try std.testing.expectEqual(@as(u256, 0x100010001), blockProof(@as(u256, 0xffff) << 208));
    // 2^256 // (0xd86a * 2^208 + 1), computed independently.
    const r = blockProof(@as(u256, 0xd86a) << 208);
    try std.testing.expectEqual(@as(u256, 0x7e4c32ec7280) - 32256 * 0x100010001, 64 * r);
}

test "targets below 2^128 are outside the circuit's range" {
    // nSize 0x12 → s = 15.
    try std.testing.expectError(error.TargetOutOfRange, scratch(0xffff0012, 0));
    _ = try scratch(0xffff001d, 0);
}
