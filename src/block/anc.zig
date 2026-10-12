//! Ancestry (D-043 part 3, option A): the witness for the `block_anc` component (Lean: `Block/Anc.lean`).
//! A header chain in the header-chain AIR's layout (one header per 256 rows, SHA256d at rows 0–215):
//! with the CSV bit, periods 0–10 are the block's 11 predecessors (oldest first) and period 11 its own
//! header; later periods are filler headers that only carry the previous hash. Rows 229 and 230 of every
//! period compare the MTP with the header's time; period 0's row 240 holds the two counts' slack.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const spec = @import("../sha256/spec.zig");
const sha = @import("../sha256/witness.zig");
const hc = @import("../btc/header_chain.zig");

pub const json = @embedFile("air:block_anc");
pub const N_MAIN = sha.N_MAIN + 1;
pub const NANC = 11;
pub const PERIOD = hc.PERIOD;
/// Rows the component needs with the CSV bit (12 periods, rounded up to a power of two).
pub const MIN_ROWS_CSV: usize = 4096;

pub const Header = [80]u8;

fn wordAt(h: *const Header, t: usize) u32 {
    return std.mem.readInt(u32, h[4 * t ..][0..4], .big);
}

/// Numeric value of a raw (byte-swapped) time word.
fn num(raw: u32) u32 {
    return @byteSwap(raw);
}

/// Core's median time past of the predecessors' times (the median of the 11 sorted).
pub fn median(anc: *const [NANC]Header) u32 {
    var ts: [NANC]u32 = undefined;
    for (anc, &ts) |*h, *t| t.* = std.mem.readInt(u32, h[68..72], .little);
    std.mem.sort(u32, &ts, {}, std.sort.asc(u32));
    return ts[NANC / 2];
}

/// One comparison row: `a`, `w` raw words, `[num a < num w]`, the difference and the lo carry.
const Cmp = struct { a: u32, e: u32, w: u32, b: u32, c: u32 };

fn cmp(a: u32, w: u32) Cmp {
    const x = num(a);
    const y = num(w);
    const b = x < y;
    const d: u32 = if (b) y - x - 1 else x - y;
    const c: u32 = if (b) ((x & 0xffff) + 1 + (d & 0xffff)) >> 16 else ((y & 0xffff) + (d & 0xffff)) >> 16;
    return .{ .a = a, .e = d, .w = w, .b = @intFromBool(b), .c = c };
}

/// `own` is the block's header; `anc` its 11 predecessors (oldest first) when the CSV bit is set, in which
/// case `mtp` must be their median; otherwise `mtp` is 0.
pub fn generate(a: std.mem.Allocator, log_size: u32, own: *const Header, anc: ?*const [NANC]Header, mtp: u32, force: bool) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    if (n < PERIOD) return error.TooSmall;
    const csv = anc != null;
    if (csv and n < MIN_ROWS_CSV) return error.TooSmall;
    if (csv and median(anc.?) != mtp and !force) return error.MtpMismatch;
    if (!csv and mtp != 0) return error.MtpMismatch;
    const np = n / PERIOD;
    const headers = try a.alloc(Header, np);
    // Periods: the predecessors and the block (CSV), or the block first; then filler headers.
    var first_filler: usize = 1;
    if (anc) |xs| {
        for (xs, 0..) |*h, i| headers[i] = h.*;
        headers[NANC] = own.*;
        first_filler = NANC + 1;
    } else headers[0] = own.*;

    const words = try sha.Words.init(a, n);
    defer words.deinit(a);
    var prev: spec.State = undefined;
    for (0..np) |i| {
        if (i >= first_filler) {
            headers[i] = [_]u8{0} ** 80;
            for (0..8) |k| std.mem.writeInt(u32, headers[i][4 + 4 * k ..][0..4], prev[k], .big);
        }
        // The predecessors must chain to the block.
        if (i > 0 and !force) for (0..8) |k| {
            if (wordAt(&headers[i], 1 + k) != prev[k]) return error.BrokenAncestry;
        };
        const base = i * PERIOD;
        const blocks = spec.HeaderBlocks.fromHeader(&headers[i]);
        const mid = words.place(base, .{ .input = spec.IV, .block = blocks.first });
        const inner = words.place(base + 72, .{ .input = mid, .block = blocks.second });
        prev = words.place(base + 144, .{ .input = spec.IV, .block = spec.digestBlock(inner) });
    }
    // Comparisons (every period) and the counts (period 0).
    const m_raw = @byteSwap(mtp);
    var bits = try a.alloc([2][2]u32, np);
    var above: u32 = 0;
    var below: u32 = 0;
    for (0..np) |i| {
        const base = i * PERIOD;
        const t = wordAt(&headers[i], 17);
        const c1 = cmp(m_raw, t);
        const c2 = cmp(t, m_raw);
        inline for (.{ .{ 229, c1 }, .{ 230, c2 } }) |rc| {
            words.a[base + rc[0]] = rc[1].a;
            words.e[base + rc[0]] = rc[1].e;
            words.w[base + rc[0]] = rc[1].w;
        }
        bits[i] = .{ .{ c1.b, c1.c }, .{ c2.b, c2.c } };
        if (csv and i < NANC) {
            above += c1.b;
            below += c2.b;
        }
    }
    if (csv) {
        if ((above > 5 or below > 5) and !force) return error.MtpMismatch;
        words.a[240] = (5 -% above) & 7;
        words.e[240] = (5 -% below) & 7;
    }
    const sm = try sha.columns(a, words, &hc.role);
    const main = try a.alloc([]M31, N_MAIN);
    @memcpy(main[0..sha.N_MAIN], sm);
    main[sha.N_MAIN] = try a.alloc(M31, n);
    for (main[sha.N_MAIN], 0..) |*x, r| x.* = if (r < PERIOD) M31.one() else M31.zero();
    for (bits, 0..) |bc, i| for (bc, 0..) |x, s| {
        main[sha.CA_LO][i * PERIOD + 229 + s] = M31.fromCanonical(x[0]);
        main[sha.CA_LO + 1][i * PERIOD + 229 + s] = M31.fromCanonical(x[1]);
    };
    return main;
}

// ---------------------------------------------------------------- tests

fn testPubs(own: *const Header, csv: bool, mtp: u32) [41]M31 {
    var p = [_]M31{M31.zero()} ** 41;
    p[3] = M31.fromCanonical(mtp & 0xffff);
    p[5] = M31.fromCanonical(@intFromBool(csv));
    p[7] = M31.fromCanonical(mtp >> 16);
    @memcpy(p[25..41], &@import("system.zig").hashLimbs(own));
    return p;
}

fn violation(a: std.mem.Allocator, air: anytype, log_size: u32, pubs: []const M31, main: [][]M31) !?usize {
    const interp = @import("../air/interp.zig");
    const tr = interp.RowTrace{ .log_size = log_size, .pubs = pubs, .preprocessed = @ptrCast(try air.genPreprocessed(a, log_size)), .main = @ptrCast(main) };
    const v = try interp.firstViolation(a, air, tr) orelse return null;
    std.debug.print("  anc: row {d} violates constraint {d}\n", .{ v.row, v.constraint });
    return v.constraint;
}

test "block anc: block 170's predecessors give its MTP; tampers are rejected" {
    const ir = @import("../air/ir.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, json)).value;
    const own: *const Header = @embedFile("testdata:block_170")[0..80];
    const anc: *const [NANC]Header = @import("checks.zig").ancOf("170");
    const mtp = median(anc);
    try std.testing.expectEqual(@as(u32, 1231715347), mtp);
    const log_size: u32 = 12;
    const pubs = testPubs(own, true, mtp);
    const honest = try generate(a, log_size, own, anc, mtp, false);
    try std.testing.expect(try violation(a, air, log_size, &pubs, honest) == null);
    // A wrong MTP (the next time up or down), forced through.
    for ([_]u32{ mtp + 1, mtp - 1 }) |m| {
        const p = testPubs(own, true, m);
        const w = try generate(a, log_size, own, anc, m, true);
        try std.testing.expect(try violation(a, air, log_size, &p, w) != null);
    }
    // A predecessor that does not chain (one time byte changed), forced through.
    var bad = anc.*;
    bad[3][68] +%= 1;
    try std.testing.expectError(error.BrokenAncestry, generate(a, log_size, own, &bad, median(&bad), false));
    try std.testing.expect(try violation(a, air, log_size, &pubs, try generate(a, log_size, own, &bad, median(&bad), true)) != null);
    // Another block's hash in the public inputs.
    var other = pubs;
    other[25] = other[25].add(M31.one());
    try std.testing.expect(try violation(a, air, log_size, &other, honest) != null);
    // Below the CSV height: limbs 0 accepted, nonzero rejected; and a 2048-row trace cannot claim CSV.
    const off = try generate(a, 11, own, null, 0, false);
    try std.testing.expect(try violation(a, air, 11, &testPubs(own, false, 0), off) == null);
    try std.testing.expect(try violation(a, air, 11, &testPubs(own, false, mtp), off) != null);
    try std.testing.expect(try violation(a, air, 11, &testPubs(own, true, mtp), off) != null);
}

test "block anc: the STWZEVA-composed proof is byte-identical under the production profile" {
    const ir = @import("../air/ir.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, json)).value;
    const own: *const Header = @embedFile("testdata:block_170")[0..80];
    const anc: *const [NANC]Header = @import("checks.zig").ancOf("170");
    const mtp = median(anc);
    const log_size: u32 = 12;
    const pubs = testPubs(own, true, mtp);
    const main = try generate(a, log_size, own, anc, mtp, false);
    const parts = [_]system.Part{.{ .air = &air, .log_size = log_size, .pubs = &pubs }};
    const mains = [_][]const []const M31{@ptrCast(main)};
    // 70 queries, 26-bit PoW, blowup 1, fold step 1.
    const n = try system.checkStwzevaProof(rec.Engine(@import("stwo_cpu_backend").CpuBackend), a, try rec.config(log_size), &parts, &mains, &.{});
    std.debug.print("block_anc (log {d}, production profile): STWZEVA proof byte-identical ({d} bytes)\n", .{ log_size, n });
}
