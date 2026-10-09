//! Block SHA-256 (M3a.3 `BLK-SHA`): the witness for the `block_sha` component (Lean:
//! `Block/Sha.lean`). Per message: one compression per padded 64-byte block, chained, then the
//! second hash of SHA256d over the 32-byte digest. Unused periods are dummies flagged `NILS`.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const sha = @import("../sha256/witness.zig");
const spec = @import("../sha256/spec.zig");
const msg = @import("msg.zig");

pub const json = @embedFile("air:block_sha");
pub const N_MAIN = 132;
const MID = 124;
const BLKI = 125;
const FST = 126;
const DBL = 127;
const NILS = 128;
const USEW = 129;
const CHN = 130;
const YM = 131;

/// The padded message bytes (SHA-256 padding).
pub fn padded(a: std.mem.Allocator, raw: []const u8, m: msg.Message) ![]u8 {
    const dl = m.positions.len;
    const len = (dl + 9 + 63) / 64 * 64;
    const out = try a.alloc(u8, len);
    @memset(out, 0);
    for (m.positions, 0..) |p, j| out[j] = raw[p];
    out[dl] = 0x80;
    std.mem.writeInt(u64, out[len - 8 ..][0..8], 8 * @as(u64, dl), .big);
    return out;
}

pub const Plan = struct {
    compressions: []sha.Compression,
    /// Per compression: message id, block index, first block, second hash.
    meta: []struct { mid: u32, blk: u32, fst: bool, dbl: bool },
    /// Per message: its SHA256d as state words.
    digests: []spec.State,
};

pub fn plan(a: std.mem.Allocator, raw: []const u8, msgs: []const msg.Message) !Plan {
    var comps = std.ArrayList(sha.Compression).empty;
    var meta = std.ArrayList(@typeInfo(@FieldType(Plan, "meta")).pointer.child).empty;
    const digests = try a.alloc(spec.State, msgs.len);
    for (msgs, digests) |m, *dg| {
        const bytes = try padded(a, raw, m);
        var h = spec.IV;
        for (0..bytes.len / 64) |b| {
            var block: spec.Block = undefined;
            for (&block, 0..) |*w, t| w.* = std.mem.readInt(u32, bytes[64 * b + 4 * t ..][0..4], .big);
            try comps.append(a, .{ .input = h, .block = block });
            try meta.append(a, .{ .mid = m.id, .blk = @intCast(b), .fst = b == 0, .dbl = false });
            h = spec.compress(h, block);
        }
        var block2: spec.Block = undefined;
        @memcpy(block2[0..8], &h);
        block2[8] = 0x80000000;
        @memset(block2[9..15], 0);
        block2[15] = 256;
        try comps.append(a, .{ .input = spec.IV, .block = block2 });
        try meta.append(a, .{ .mid = m.id, .blk = @intCast(bytes.len / 64), .fst = false, .dbl = true });
        dg.* = spec.compress(spec.IV, block2);
    }
    return .{ .compressions = try comps.toOwnedSlice(a), .meta = try meta.toOwnedSlice(a), .digests = digests };
}

pub fn periodsNeeded(p: Plan) usize {
    return p.compressions.len;
}

fn f(x: anytype) M31 {
    return M31.fromCanonical(@intCast(x));
}

/// Main columns in `2^log_size` rows.
pub fn generate(a: std.mem.Allocator, log_size: u32, p: Plan) ![][]M31 {
    const n = @as(usize, 1) << @intCast(log_size);
    const w = try sha.generate(a, log_size, p.compressions);
    const cols = try a.alloc([]M31, N_MAIN);
    @memcpy(cols[0..sha.N_MAIN], w.main);
    for (cols[sha.N_MAIN..]) |*c| {
        c.* = try a.alloc(M31, n);
        @memset(c.*, M31.zero());
    }
    const one = M31.one();
    for (0..n) |r| {
        const per = r / sha.PERIOD;
        if (per < p.meta.len) {
            const m = p.meta[per];
            cols[MID][r] = f(m.mid);
            cols[BLKI][r] = f(m.blk);
            if (m.fst) cols[FST][r] = one;
            if (m.dbl) cols[DBL][r] = one;
        } else cols[NILS][r] = one;
        cols[USEW][r] = one.sub(cols[DBL][r]).sub(cols[NILS][r]);
        cols[CHN][r] = one.sub(cols[FST][r]).sub(cols[DBL][r]).sub(cols[NILS][r]);
    }
    _ = YM;
    return cols;
}

/// The digest bytes of a state (big-endian words).
pub fn digestBytes(s: spec.State) [32]u8 {
    var out: [32]u8 = undefined;
    for (s, 0..) |x, i| std.mem.writeInt(u32, out[4 * i ..][0..4], x, .big);
    return out;
}

/// The Merkle root over the txid messages' digests (native check).
pub fn merkleOfDigests(a: std.mem.Allocator, msgs: []const msg.Message, digests: []const spec.State) ![32]u8 {
    const Sha = std.crypto.hash.sha2.Sha256;
    var level = std.ArrayList([32]u8).empty;
    for (msgs, digests) |m, d| if (!m.hdr and !m.wtx) try level.append(a, digestBytes(d));
    while (level.items.len > 1) {
        if (level.items.len % 2 == 1) try level.append(a, level.items[level.items.len - 1]);
        var next = std.ArrayList([32]u8).empty;
        var i: usize = 0;
        while (i < level.items.len) : (i += 2) {
            var buf: [64]u8 = undefined;
            @memcpy(buf[0..32], &level.items[i]);
            @memcpy(buf[32..64], &level.items[i + 1]);
            var h: [32]u8 = undefined;
            Sha.hash(&buf, &h, .{});
            Sha.hash(&h, &h, .{});
            try next.append(a, h);
        }
        level = next;
    }
    return level.items[0];
}

test "block sha: segwit samples satisfy the SHA AIR; digests Merkle-hash to the header root (run with ReleaseFast)" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const fields = @import("fields.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const sha_air = (try ir.Air.parseJson(a, json)).value;
    const samples = [_][]const u8{ @embedFile("testdata:block_481824"), @embedFile("testdata:block_709632") };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const msgs = try msg.messages(a, try msg.txRanges(a, rows));
        const pl = try plan(a, raw, msgs);
        try std.testing.expectEqualSlices(u8, raw[36..68], &try merkleOfDigests(a, msgs, pl.digests));
        const log_size: u32 = std.math.log2_int_ceil(usize, (pl.compressions.len + 1) * sha.PERIOD);
        const sm = try generate(a, log_size, pl);
        const tr = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(try sha_air.genPreprocessed(a, log_size)), .main = @ptrCast(sm) };
        std.debug.print("block of {d} bytes: {d} compressions, log {d}\n", .{ raw.len, pl.compressions.len, log_size });
        if (try interp.firstViolation(a, sha_air, tr)) |v| {
            std.debug.print("  row {d} violates constraint {d}\n", .{ v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
    }
}

test "block sha: (bytes, fields, msg, sha) prove for small blocks; digests are the txids and header hash" {
    const ir = @import("../air/ir.zig");
    const interp = @import("../air/interp.zig");
    const system = @import("../air/system.zig");
    const rec = @import("../air/prove_rec.zig");
    const bytes = @import("bytes.zig");
    const fields = @import("fields.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const sha_air = (try ir.Air.parseJson(a, json)).value;
    const msg_air = (try ir.Air.parseJson(a, msg.json)).value;
    const fields_air = (try ir.Air.parseJson(a, fields.json)).value;
    const bytes_air = (try ir.Air.parseJson(a, bytes.json)).value;
    const samples = [_][]const u8{ @embedFile("testdata:block_0"), @embedFile("testdata:block_170"), @embedFile("testdata:block_91812") };
    for (samples) |raw| {
        const rows = try fields.tokenize(a, raw);
        const txs = try msg.txRanges(a, rows);
        const msgs = try msg.messages(a, txs);
        const pl = try plan(a, raw, msgs);
        const need = @max(msg.rowsNeeded(msgs), raw.len + 1, rows.len + 1, (pl.compressions.len + 1) * sha.PERIOD);
        const log_size: u32 = std.math.log2_int_ceil(usize, need);
        // The digests: the header hash and each txid, as Core computes them.
        var hh: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(raw[0..80], &hh, .{});
        std.crypto.hash.sha2.Sha256.hash(&hh, &hh, .{});
        try std.testing.expectEqualSlices(u8, &hh, &digestBytes(pl.digests[0]));
        try std.testing.expectEqualSlices(u8, raw[36..68], &try merkleOfDigests(a, msgs, pl.digests));
        var reads = std.ArrayList(u32).empty;
        const mm = try msg.generate(a, log_size, raw, msgs, &reads);
        msg.setUses(mm);
        const sm = try generate(a, log_size, pl);
        const tr = interp.RowTrace{ .log_size = log_size, .preprocessed = @ptrCast(try sha_air.genPreprocessed(a, log_size)), .main = @ptrCast(sm) };
        if (try interp.firstViolation(a, sha_air, tr)) |v| {
            std.debug.print("block of {d} bytes: sha row {d} violates constraint {d}\n", .{ raw.len, v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        const fm = try fields.generate(a, log_size, raw, rows);
        fields.setTxUses(fm, rows, 2);
        try reads.appendSlice(a, try fields.reads(a, rows));
        const bm = try bytes.generate(a, log_size, raw, reads.items);
        const pubs = [_]M31{f(raw.len)};
        const parts = [_]system.Part{
            .{ .air = &bytes_air, .log_size = log_size, .pubs = &pubs },
            .{ .air = &fields_air, .log_size = log_size, .pubs = &pubs },
            .{ .air = &msg_air, .log_size = log_size },
            .{ .air = &sha_air, .log_size = log_size },
        };
        const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), log_size);
        const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
        const mains = [_][]const []const M31{ @ptrCast(bm), @ptrCast(fm), @ptrCast(mm), @ptrCast(sm) };
        try system.verifyExt(a, cfg, &parts, &.{}, try system.prove(E, a, cfg, &parts, &mains));
        std.debug.print("block of {d} bytes: {d} messages, {d} compressions, log {d}: proved and verified\n", .{ raw.len, msgs.len, pl.compressions.len, log_size });
    }
}
