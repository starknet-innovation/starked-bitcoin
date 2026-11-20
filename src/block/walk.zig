//! Sigop walker (M3a.5d, D-035): the witness for the `block_walk` component (Lean: `Block/Walk.lean`).
//! One row per byte of each non-empty script, running Core's legacy sigop automaton (`wstep` in
//! `Spec/BlockFlat.lean`): opcodes, `PUSHDATA` length bytes, skipped data bytes, and the data of a push
//! of at least `2^25` bytes, which runs to the end.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;

pub const json = @embedFile("air:block_walk");
pub const N_MAIN = 71;

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
// CONNECT-RULES step 3 (Lean `Walk.accC`).
const AC = 51;
const W4 = 52;
const HI = 53;
const MS = 54;
const DV = 55;
const HCN = 56;
const ZH = 57;
const INVH = 58;
const PO = 59;
const RS = 60;
const RL = 61;
const ZE = 62;
const INVE = 63;
const EZ = 64;
const PV = 65;
const NPV = 66;
const M1 = 67;
const AN = 68;
const LG = 69;
const SUMA = 70;

/// The opcode table's columns for the accurate count (Lean `Tables.hiN`, `msN`, `dvN`).
pub fn hiN(b: u8) u32 {
    return @intFromBool(b > 0x60);
}
pub fn msN(b: u8) u32 {
    return @intFromBool(b == 0xae or b == 0xaf);
}
pub fn dvN(b: u8) u32 {
    return if (b >= 0x51 and b <= 0x60) b - 0x50 else 20;
}

/// A walked span: a script (`mode` 0, legacy count), or an accurate span of weight 1 (`mode` 1, a
/// witness script) or 4 (`mode` 2, a redeem script).
pub const Span = struct { start: u32, len: u32, mode: u8 = 0 };

/// What the walker outputs for a span besides its counts: `po` (it parses and no opcode is above
/// `OP_16`), and the data of its last operation `(rs, rl)` when a push's data ends exactly with the
/// span (else both 0), as the AIR fixes them.
pub const SpanOut = struct { po: bool, rs: u32, rl: u32 };

pub fn spanOut(raw: []const u8, start: u32, len: u32) SpanOut {
    var st = State{};
    var hi: u32 = 0;
    var out: SpanOut = .{ .po = false, .rs = 0, .rl = 0 };
    for (0..len) |j| {
        const pos = start + @as(u32, @intCast(j));
        const b = raw[pos];
        if (st.kind == .op) hi += hiN(b);
        const nxt = step(st, b);
        const rem = len - @as(u32, @intCast(j));
        if ((st.kind == .op or st.kind == .ln) and nxt.kind == .dt and nxt.dr == rem - 1) out = .{ .po = false, .rs = pos + 1, .rl = rem - 1 };
        st = nxt;
    }
    out.po = hi == 0 and st.kind == .op;
    return out;
}

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
    siga: u32 = 0,
};

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

fn invOrZero(x: M31) M31 {
    return x.inv() catch M31.zero();
}

pub fn rowsNeeded(spans: []const Span) usize {
    var n: usize = 0;
    for (spans) |s| n += s.len;
    return n + 1;
}

/// A walked row's starting state, packed for the device witness (`gpu/cuda/witness.zig`, `walk`):
/// `w0` = position (bits 0–23), kind (24–25: op, ln, dt, inf), `li` (26–27), `lk` code (28–29:
/// 0 none, 1, 2, 3 = 4), first byte of its script (30); `val` = `dr` (dt) or `lacc` (ln); `sums`
/// the running sigop count including this row. The row's columns are a function of the record and
/// its byte (`expand`).
pub const Rec = extern struct { w0: u32, rem: u32, val: u32, sums: u32 };

/// The step 3 state of a walked row (host only so far; the device kernel does not know it yet).
pub const Ext = struct { mode: u8, po: bool, rs: u32, rl: u32, hcn: u32, pv: u32, suma: u32 };

/// The host's sequential pass: one record per walked row, and what the other components read.
pub const Plan = struct {
    recs: []Rec,
    ext: []Ext,
    reads: []u32,
    opcodes: []u8,
    ranges: []u32,
    /// The legacy count of the scripts, and the weighted accurate count of the accurate spans.
    sigops: u32,
    siga: u32,
};

fn lkCode(lk: u8) u32 {
    return switch (lk) {
        0 => 0,
        1 => 1,
        2 => 2,
        else => 3,
    };
}

fn lkOf(code: u32) u8 {
    return switch (code) {
        0 => 0,
        1 => 1,
        2 => 2,
        else => 4,
    };
}

/// The automaton's step from state `st` on byte `b` (`wstep`).
fn step(st: State, b: u8) State {
    return switch (st.kind) {
        .op => if (b >= 1 and b < 0x4c)
            .{ .kind = .dt, .dr = b }
        else if (b >= 0x4c and b <= 0x4e)
            .{ .kind = .ln, .lk = if (b == 0x4c) 1 else if (b == 0x4d) 2 else 4, .li = 0, .lacc = 0 }
        else
            .{ .kind = .op },
        .ln => blk: {
            const acc2 = st.lacc + (@as(u64, b) << @intCast(8 * @as(u6, @intCast(st.li))));
            if (st.li + 1 != st.lk) break :blk .{ .kind = .ln, .lk = st.lk, .li = st.li + 1, .lacc = acc2 };
            if (st.lk == 4 and b >= 2) break :blk .{ .kind = .inf };
            break :blk if (acc2 == 0) .{ .kind = .op } else .{ .kind = .dt, .dr = acc2 };
        },
        .dt => if (st.dr == 1) .{ .kind = .op } else .{ .kind = .dt, .dr = st.dr - 1 },
        .inf => .{ .kind = .inf },
    };
}

pub fn plan(a: std.mem.Allocator, log_size: u32, raw: []const u8, spans: []const Span) !Plan {
    const n = @as(usize, 1) << @intCast(log_size);
    const active = rowsNeeded(spans) - 1;
    if (active + 1 > n) return error.TooManyRows;
    if (raw.len >= 1 << 24) return error.TooManyRows;
    const recs = try a.alloc(Rec, active);
    const ext = try a.alloc(Ext, active);
    const reads = try a.alloc(u32, active);
    var opcodes = std.ArrayList(u8).empty;
    var ranges = std.ArrayList(u32).empty;
    var r: usize = 0;
    var sums: u32 = 0;
    var suma: u32 = 0;
    for (spans) |span| {
        const sp = [2]u32{ span.start, span.len };
        const so = spanOut(raw, span.start, span.len);
        const wgt: u32 = switch (span.mode) {
            0 => 0,
            1 => 1,
            else => 4,
        };
        var st = State{};
        var hcn: u32 = 0;
        var pv: u32 = 20;
        for (0..sp[1]) |j| {
            const pos: u32 = sp[0] + @as(u32, @intCast(j));
            const b = raw[pos];
            reads[r] = pos;
            ext[r] = .{ .mode = span.mode, .po = so.po, .rs = so.rs, .rl = so.rl, .hcn = hcn, .pv = pv, .suma = suma };
            switch (st.kind) {
                .op => {
                    try opcodes.append(a, b);
                    if (span.mode == 0) sums += sigW(b) else suma += wgt * (sigW(b) - 20 * msN(b) + msN(b) * pv);
                    hcn += hiN(b);
                    pv = dvN(b);
                    ext[r].hcn = hcn;
                    ext[r].suma = suma;
                },
                .ln => if (st.li + 1 == st.lk and st.lk == 4 and b >= 2) try ranges.append(a, b - 2),
                else => {},
            }
            const val: u64 = switch (st.kind) {
                .dt => st.dr,
                .ln => st.lacc,
                else => 0,
            };
            if (val >= 1 << 32) return error.TooManyRows;
            recs[r] = .{
                .w0 = pos | @as(u32, @intFromEnum(st.kind)) << 24 | @as(u32, st.li) << 26 | lkCode(st.lk) << 28 | @as(u32, @intFromBool(j == 0)) << 30,
                .rem = sp[1] - @as(u32, @intCast(j)),
                .val = @intCast(val),
                .sums = sums,
            };
            st = step(st, b);
            r += 1;
        }
    }
    return .{ .recs = recs, .ext = ext, .reads = reads, .opcodes = try opcodes.toOwnedSlice(a), .ranges = try ranges.toOwnedSlice(a), .sigops = sums, .siga = suma };
}

/// Main columns in `2^log_size` rows from the plan (the device's `walk` kernel computes the same).
pub fn columns(a: std.mem.Allocator, log_size: u32, raw: []const u8, p: Plan) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (p.recs.len + 1 > n) return error.TooManyRows;
    const cols = try a.alloc([]M31, N_MAIN);
    for (cols) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    const one = M31.one();
    for (p.recs, 0..) |rc, r| {
        const pos = rc.w0 & 0xffffff;
        const st = State{
            .kind = @enumFromInt((rc.w0 >> 24) & 3),
            .li = @intCast((rc.w0 >> 26) & 3),
            .lk = lkOf((rc.w0 >> 28) & 3),
            .dr = if ((rc.w0 >> 24) & 3 == @intFromEnum(Kind.dt)) rc.val else 0,
            .lacc = if ((rc.w0 >> 24) & 3 == @intFromEnum(Kind.ln)) rc.val else 0,
        };
        const b = raw[pos];
        const rem = rc.rem;
        cols[ACT][r] = one;
        if ((rc.w0 >> 30) & 1 == 1) cols[FS][r] = one;
        cols[POS][r] = f(pos);
        cols[REM][r] = f(rem);
        cols[B][r] = f(b);
        cols[ZR][r] = f(@intFromBool(rem == 1));
        cols[INVR][r] = invOrZero(f(rem).sub(one));
        const nxt = step(st, b);
        switch (st.kind) {
            .op => {
                cols[OP][r] = one;
                const pn: u32 = if (b < 0x4c) b else 0;
                cols[PN][r] = f(pn);
                if (b == 0x4c) cols[K1][r] = one;
                if (b == 0x4d) cols[K2][r] = one;
                if (b == 0x4e) cols[K4][r] = one;
                cols[SG][r] = f(sigW(b));
                cols[NZP][r] = f(@intFromBool(b >= 1 and b < 0x4c));
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
                    } else {
                        cols[LEF][r] = one;
                        if (st.lk == 4) cols[L4][r] = one;
                    }
                }
                // acc2 ≥ 2^25 may exceed the field; the column holds the field value.
                const v = M31.fromU64(acc2);
                cols[ACC2][r] = v;
                cols[ZA][r] = f(@intFromBool(v.isZero()));
                cols[INVA][r] = invOrZero(v);
            },
            .dt => {
                cols[DT][r] = one;
                cols[DR][r] = f(st.dr);
            },
            .inf => cols[INF][r] = one,
        }
        if (st.kind != .ln) {
            // Defaults for the zero tests on rows where they are unused.
            cols[ZA][r] = one;
            cols[INVA][r] = M31.zero();
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
        cols[GC][r] = f(@intFromBool((rc.w0 >> 30) & 1 == 0));
        cols[SUMS][r] = f(rc.sums);
        // Step 3.
        const x = p.ext[r];
        const ac: u32 = @intFromBool(x.mode != 0);
        const w4: u32 = @intFromBool(x.mode == 2);
        cols[AC][r] = f(ac);
        cols[W4][r] = f(w4);
        cols[HCN][r] = f(x.hcn);
        cols[ZH][r] = f(@intFromBool(x.hcn == 0));
        cols[INVH][r] = invOrZero(f(x.hcn));
        cols[PO][r] = f(@intFromBool(x.po));
        cols[RS][r] = f(x.rs);
        cols[RL][r] = f(x.rl);
        const e = cols[NDR][r].sub(f(rem)).add(one);
        const ze = e.isZero();
        cols[ZE][r] = f(@intFromBool(ze));
        cols[INVE][r] = invOrZero(e);
        const ent = (st.kind == .op or st.kind == .ln) and nxt.kind == .dt;
        cols[EZ][r] = f(@intFromBool(ent and ze));
        cols[PV][r] = f(x.pv);
        var sg: u32 = 0;
        var ms: u32 = 0;
        if (st.kind == .op) {
            cols[HI][r] = f(hiN(b));
            ms = msN(b);
            sg = sigW(b);
            cols[MS][r] = f(ms);
            cols[DV][r] = f(dvN(b));
            cols[NPV][r] = f(dvN(b));
        } else cols[NPV][r] = f(x.pv);
        const m1 = ms * x.pv;
        cols[M1][r] = f(m1);
        cols[AN][r] = f((ac + 3 * w4) * (sg - 20 * ms + m1));
        cols[LG][r] = f((1 - ac) * sg);
        cols[SUMA][r] = f(x.suma);
    }
    // Padding rows: inactive; zero tests on zero values.
    const inv_m1 = invOrZero(M31.zero().sub(one));
    for (p.recs.len..n) |r| {
        cols[SUMS][r] = f(p.sigops);
        cols[SUMA][r] = f(p.siga);
        cols[ZH][r] = one;
        cols[INVE][r] = one;
        cols[ZA][r] = one;
        cols[INVD][r] = inv_m1;
        cols[INVR][r] = inv_m1;
    }
    return cols;
}

pub fn generate(a: std.mem.Allocator, log_size: u32, raw: []const u8, spans: []const Span) !Out {
    const p = try plan(a, log_size, raw, spans);
    return .{ .cols = try columns(a, log_size, raw, p), .reads = p.reads, .opcodes = p.opcodes, .ranges = p.ranges, .sigops = p.sigops, .siga = p.siga };
}
