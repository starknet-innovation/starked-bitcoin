//! Sigop walker (M3a.5d, D-035): the witness for the `block_walk` component (Lean: `Block/Walk.lean`).
//! One row per byte of each non-empty script, running Core's legacy sigop automaton (`wstep` in
//! `Spec/BlockFlat.lean`): opcodes, `PUSHDATA` length bytes, skipped data bytes, and the data of a push
//! of at least `2^25` bytes, which runs to the end.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;

pub const json = @embedFile("air:block_walk");
pub const N_MAIN = 51;

const ACT = 0;
const FS = 1;
const POS = 2;
const REM = 3;
const B = 4;
const OP = 5;
const LN = 6;
const DT = 7;
const INF = 8;
const PN = 9;
const K1 = 10;
const K2 = 11;
const K4 = 12;
const SG = 13;
const NZP = 14;
const LI0 = 15;
const LK1 = 19;
const LK2 = 20;
const LK4 = 21;
const LACC = 22;
const DR = 23;
const ACC2 = 24;
const ENDC = 25;
const LE = 26;
const LEF = 27;
const TOPF = 28;
const L4 = 29;
const ZA = 30;
const INVA = 31;
const ZD = 32;
const INVD = 33;
const ZR = 34;
const INVR = 35;
const NOP = 36;
const NLN = 37;
const NDT = 38;
const NINF = 39;
const NDR = 40;
const NLACC = 41;
const NLI0 = 42;
const NLK1 = 46;
const NLK2 = 47;
const NLK4 = 48;
const SUMS = 49;
const GC = 50;

pub fn sigW(b: u8) u32 {
    return switch (b) {
        0xac, 0xad => 1,
        0xae, 0xaf => 20,
        else => 0,
    };
}

/// Core's `GetSigOpCount(false)` (reference for tests).
pub fn sigOps(s: []const u8) u32 {
    var pc: usize = 0;
    var n: u32 = 0;
    while (pc < s.len) {
        const o = s[pc];
        pc += 1;
        var push: usize = 0;
        if (o < 0x4c) {
            push = o;
        } else if (o == 0x4c or o == 0x4d or o == 0x4e) {
            const k: usize = if (o == 0x4c) 1 else if (o == 0x4d) 2 else 4;
            if (s.len - pc < k) break;
            var v: usize = 0;
            for (0..k) |i| v |= @as(usize, s[pc + i]) << @intCast(8 * i);
            pc += k;
            push = v;
        }
        if (o <= 0x4e) {
            if (s.len - pc < push) break;
            pc += push;
        }
        n += sigW(o);
    }
    return n;
}

const Kind = enum { op, ln, dt, inf };

const State = struct {
    kind: Kind = .op,
    dr: u64 = 0,
    lk: u8 = 0,
    li: u8 = 0,
    lacc: u64 = 0,
};

pub const Out = struct {
    cols: [][]M31,
    /// Positions read, opcode bytes, range values used.
    reads: []u32,
    opcodes: []u8,
    ranges: []u32,
    sigops: u32,
};

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

fn invOrZero(x: M31) M31 {
    return x.inv() catch M31.zero();
}

pub fn rowsNeeded(scripts: []const [2]u32) usize {
    var n: usize = 0;
    for (scripts) |s| n += s[1];
    return n + 1;
}

pub fn generate(a: std.mem.Allocator, log_size: u32, raw: []const u8, scripts: []const [2]u32) !Out {
    const n = @as(usize, 1) << @intCast(log_size);
    if (rowsNeeded(scripts) > n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    var reads = std.ArrayList(u32).empty;
    var opcodes = std.ArrayList(u8).empty;
    var ranges = std.ArrayList(u32).empty;
    const one = M31.one();
    var r: usize = 0;
    var sums: u32 = 0;
    for (scripts) |sp| {
        var st = State{};
        for (0..sp[1]) |j| {
            const pos: u32 = sp[0] + @as(u32, @intCast(j));
            const b = raw[pos];
            const rem: u32 = sp[1] - @as(u32, @intCast(j));
            cols[ACT][r] = one;
            if (j == 0) cols[FS][r] = one;
            cols[POS][r] = f(pos);
            cols[REM][r] = f(rem);
            cols[B][r] = f(b);
            try reads.append(a, pos);
            cols[ZR][r] = f(@intFromBool(rem == 1));
            cols[INVR][r] = invOrZero(f(rem).sub(one));
            // This row's state.
            var nxt = State{};
            switch (st.kind) {
                .op => {
                    cols[OP][r] = one;
                    try opcodes.append(a, b);
                    const pn: u32 = if (b < 0x4c) b else 0;
                    cols[PN][r] = f(pn);
                    if (b == 0x4c) cols[K1][r] = one;
                    if (b == 0x4d) cols[K2][r] = one;
                    if (b == 0x4e) cols[K4][r] = one;
                    cols[SG][r] = f(sigW(b));
                    sums += sigW(b);
                    const nzp = b >= 1 and b < 0x4c;
                    cols[NZP][r] = f(@intFromBool(nzp));
                    if (nzp) {
                        nxt = .{ .kind = .dt, .dr = pn };
                    } else if (b >= 0x4c and b <= 0x4e) {
                        nxt = .{ .kind = .ln, .lk = if (b == 0x4c) 1 else if (b == 0x4d) 2 else 4, .li = 0, .lacc = 0 };
                    } else nxt = .{ .kind = .op };
                },
                .ln => {
                    cols[LN][r] = one;
                    cols[LI0 + st.li][r] = one;
                    switch (st.lk) {
                        1 => cols[LK1][r] = one,
                        2 => cols[LK2][r] = one,
                        else => cols[LK4][r] = one,
                    }
                    cols[LACC][r] = f(st.lacc);
                    const acc2 = st.lacc + (@as(u64, b) << @intCast(8 * @as(u6, @intCast(st.li))));
                    const end = st.li + 1 == st.lk;
                    if (end) {
                        cols[ENDC][r] = one;
                        cols[LE][r] = one;
                        if (st.lk == 4 and b >= 2) {
                            cols[TOPF][r] = one;
                            try ranges.append(a, b - 2);
                            nxt = .{ .kind = .inf };
                        } else {
                            cols[LEF][r] = one;
                            if (st.lk == 4) cols[L4][r] = one;
                            nxt = if (acc2 == 0) .{ .kind = .op } else .{ .kind = .dt, .dr = acc2 };
                        }
                    } else nxt = .{ .kind = .ln, .lk = st.lk, .li = st.li + 1, .lacc = acc2 };
                    if (!(end and st.lk == 4 and b >= 2)) {
                        cols[ACC2][r] = f(acc2);
                        cols[ZA][r] = f(@intFromBool(acc2 == 0));
                        cols[INVA][r] = invOrZero(f(acc2));
                    } else {
                        // acc2 ≥ 2^25 may exceed the field; the column still holds the field value.
                        const v = M31.fromU64(acc2);
                        cols[ACC2][r] = v;
                        cols[ZA][r] = f(@intFromBool(v.isZero()));
                        cols[INVA][r] = invOrZero(v);
                    }
                },
                .dt => {
                    cols[DT][r] = one;
                    cols[DR][r] = f(st.dr);
                    nxt = if (st.dr == 1) .{ .kind = .op } else .{ .kind = .dt, .dr = st.dr - 1 };
                },
                .inf => {
                    cols[INF][r] = one;
                    nxt = .{ .kind = .inf };
                },
            }
            if (st.kind != .ln) {
                // Defaults for the zero tests on rows where they are unused.
                cols[ZA][r] = f(@intFromBool(cols[ACC2][r].isZero()));
                cols[INVA][r] = invOrZero(cols[ACC2][r]);
            }
            cols[ZD][r] = f(@intFromBool(cols[DR][r].eql(one)));
            cols[INVD][r] = invOrZero(cols[DR][r].sub(one));
            // The next state, as the AIR computes it (also after the script's last byte).
            cols[NOP][r] = f(@intFromBool(nxt.kind == .op));
            cols[NLN][r] = f(@intFromBool(nxt.kind == .ln));
            cols[NDT][r] = f(@intFromBool(nxt.kind == .dt));
            cols[NINF][r] = f(@intFromBool(nxt.kind == .inf));
            if (nxt.kind == .dt) cols[NDR][r] = f(nxt.dr);
            if (nxt.kind == .ln) {
                cols[NLACC][r] = f(nxt.lacc);
                cols[NLI0 + nxt.li][r] = one;
                switch (nxt.lk) {
                    1 => cols[NLK1][r] = one,
                    2 => cols[NLK2][r] = one,
                    else => cols[NLK4][r] = one,
                }
            }
            cols[GC][r] = f(@intFromBool(j != 0));
            cols[SUMS][r] = f(sums);
            st = nxt;
            r += 1;
        }
    }
    // Padding rows: inactive; zero tests on zero values.
    while (r < n) : (r += 1) {
        cols[SUMS][r] = f(sums);
        cols[ZA][r] = one;
        cols[INVD][r] = invOrZero(M31.zero().sub(one));
        cols[INVR][r] = invOrZero(M31.zero().sub(one));
    }
    return .{
        .cols = cols,
        .reads = try reads.toOwnedSlice(a),
        .opcodes = try opcodes.toOwnedSlice(a),
        .ranges = try ranges.toOwnedSlice(a),
        .sigops = sums,
    };
}
