//! The block system (M3a.5–6, D-035, D-038): every component of the block proof, at one log size, in
//! the order the Lean statement uses: bytes, fields, messages, SHA, txid tree, tables, sigop walker,
//! context, witness tree, undo bytes, Blake2s message words, Blake2s. `build` computes all witnesses
//! for a raw block (and its undo stream) in its context.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const ir = @import("../air/ir.zig");
const system = @import("../air/system.zig");
const shaw = @import("../sha256/witness.zig");
const bytes = @import("bytes.zig");
const fields = @import("fields.zig");
const msg = @import("msg.zig");
const bsha = @import("sha.zig");
const merkle = @import("merkle.zig");
const checks = @import("checks.zig");
const walk = @import("walk.zig");
const ctxw = @import("ctx.zig");
const wmerkle = @import("wmerkle.zig");
const commit = @import("commit.zig");

pub const N_COMP = 12;
pub const jsons = [N_COMP][]const u8{ bytes.json, fields.json, msg.json, bsha.json, merkle.json, checks.tables_json, walk.json, ctxw.json, wmerkle.json, commit.undo_json, commit.msg_json, commit.b2s_json };
pub const names = [N_COMP][]const u8{ "bytes", "fields", "msg", "sha", "merkle", "tables", "walk", "ctx", "wmerkle", "undo", "b2msg", "b2s" };
/// Public inputs each component's AIR references (a prefix of the block's 41: the eight checks inputs,
/// the undo length, the commitment's 16 limbs, the block hash's 16 limbs).
pub const N_PUB = 41;
pub const PUB_HASH = 25;
pub const n_pubs = [N_COMP]usize{ 1, 7, 0, 0, 2, 0, 0, 41, 2, 9, 9, 25 };

pub const Built = struct {
    log_size: u32,
    pubs: [N_PUB]M31,
    /// The block commitment `blake2s(undo)` (D-038 as amended).
    commitment_words: [8]u32,
    mains: [N_COMP][][]M31,
    ntx: u32,
    sigops: u32,
    weight: u64,
    commitment: bool,
    /// Block positions read by the other components (the byte table's multiplicities).
    reads: []u32,
};

pub fn parseAirs(a: std.mem.Allocator) ![N_COMP]ir.Air {
    var out: [N_COMP]ir.Air = undefined;
    for (&out, jsons) |*x, j| x.* = (try ir.Air.parseJson(a, j)).value;
    return out;
}

/// `build` with an empty undo record (`undo = 0x01`).
pub fn build(a: std.mem.Allocator, raw: []const u8, ctx: checks.Ctx) !Built {
    return buildU(a, raw, &[_]u8{1}, ctx);
}

pub fn buildU(a: std.mem.Allocator, raw: []const u8, undo: []const u8, ctx: checks.Ctx) !Built {
    const rows = try fields.tokenize(a, raw);
    const ntx: u32 = @intCast(rows[0].val);
    const txs = try msg.txRanges(a, rows);
    const msgs = try msg.messages(a, txs);
    var pl = try bsha.plan(a, raw, msgs);
    const nodes = try merkle.tree(a, ntx);
    const root = try merkle.extendPlan(a, &pl, nodes);
    if (!std.mem.eql(u8, raw[36..68], &bsha.digestBytes(root)) and !ctx.force) return error.BadMerkleRoot;

    // Sizes: the checks and the walker need the fields' layout first; size by the largest need.
    const wnodes = try wmerkle.tree(a, ntx);
    var scripts_len: usize = 0;
    for (rows) |r| if ((r.kind == fields.K_IN or r.kind == fields.K_OUT) and r.val > 0) {
        scripts_len += r.val;
    };
    const comps_est = pl.compressions.len + 3 * (wnodes.len + 1);
    const need = @max(@max(msg.rowsNeeded(msgs), raw.len + 1, rows.len + 1, (comps_est + 1) * shaw.PERIOD), @max(nodes.len + 2, wnodes.len + 2, scripts_len + 1, 256), @max(undo.len + 1, commit.rowsNeeded(undo.len)));
    const log_size: u32 = std.math.log2_int_ceil(usize, need);

    const fm = try fields.generate(a, log_size, raw, rows);
    const chk = try checks.fill(a, fm, raw, rows, ctx);
    const wk = try walk.generate(a, log_size, raw, chk.scripts);
    const cid = wmerkle.commitId(wnodes);
    const cx = try ctxw.generate(a, log_size, .{ .raw = raw, .ctx = ctx, .tx0 = txs[0], .chk = chk, .sigops = wk.sigops, .cid = cid });
    if (cx.hc) {
        const cdig = try wmerkle.extendPlan(a, &pl, wnodes, cx.nonce);
        const c = chk.commit.?;
        if (!std.mem.eql(u8, raw[c[0] + 6 ..][0..32], &bsha.digestBytes(cdig)) and !ctx.force) return error.BadWitnessCommitment;
    } else if (chk.nseg != 0 and !ctx.force) return error.UnexpectedWitness;

    // Multiplicities. The context reads the header's digest once (the public block hash).
    for (pl.meta) |*m| if (m.dbl and m.mid == 0) {
        m.ym += 1;
    };
    fields.setTxUses(fm, rows, 2);
    for (rows, 0..) |r, i| if (r.kind == fields.K_LOCK) {
        fm[117][i] = fm[117][i].add(M31.one()); // transaction 0's tuple: the context component's use
        break;
    };
    var reads = std.ArrayList(u32).empty;
    const mm = try msg.generate(a, log_size, raw, msgs, &reads);
    msg.setUses(mm);
    merkle.addHeaderUses(mm);
    const sm = try bsha.generate(a, log_size, pl);
    const km = try merkle.generate(a, log_size, ntx, nodes, root);
    const wm = try wmerkle.generate(a, log_size, ntx, wnodes, cx.hc);
    try reads.appendSlice(a, try fields.reads(a, rows));
    try reads.appendSlice(a, chk.reads);
    try reads.appendSlice(a, wk.reads);
    try reads.appendSlice(a, cx.reads);
    var undo_reads = std.ArrayList(u32).empty;
    const b2m = try commit.msgColumns(a, log_size, undo, &undo_reads);
    const um = try commit.undoColumns(a, log_size, undo, undo_reads.items);
    const b2sm = try commit.b2sColumns(a, log_size, undo);
    const bm = try bytes.generate(a, log_size, raw, reads.items);
    var ranges = std.ArrayList(u32).empty;
    try ranges.appendSlice(a, chk.ranges);
    try ranges.appendSlice(a, wk.ranges);
    try ranges.appendSlice(a, cx.ranges);
    const tm = try checks.tables(a, log_size, ranges.items, wk.opcodes);

    const cw = try commit.commitment(a, undo);
    var pubs: [N_PUB]M31 = undefined;
    @memcpy(pubs[0..8], &checks.pubs(raw, ntx, ctx));
    pubs[8] = M31.fromCanonical(@intCast(undo.len));
    @memcpy(pubs[9..25], &commit.pubLimbs(cw));
    @memcpy(pubs[PUB_HASH..N_PUB], &hashLimbs(raw[0..80]));
    return .{
        .log_size = log_size,
        .pubs = pubs,
        .commitment_words = cw,
        .mains = .{ bm, fm, mm, sm, km, tm, wk.cols, cx.cols, wm, um, b2m, b2sm },
        .ntx = ntx,
        .sigops = wk.sigops,
        .weight = 4 * @as(u64, raw.len) - 3 * @as(u64, chk.w),
        .commitment = cx.hc,
        .reads = reads.items,
    };
}

/// The block hash's public limbs: SHA256d of the header as SHA-256 state words (big-endian words of
/// the hash in internal byte order), limb `2w + h` half `h` of word `w` (Lean: `HashPub.hash_pub`).
pub fn hashLimbs(header: *const [80]u8) [16]M31 {
    var h1: [32]u8 = undefined;
    var h2: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(header, &h1, .{});
    std.crypto.hash.sha2.Sha256.hash(&h1, &h2, .{});
    return hashLimbsOf(h2);
}

/// The public limbs of a block hash given in internal byte order.
pub fn hashLimbsOf(h: [32]u8) [16]M31 {
    var w: [8]u32 = undefined;
    for (0..8) |i| w[i] = std.mem.readInt(u32, h[4 * i ..][0..4], .big);
    return commit.pubLimbs(w);
}

pub fn parts(airs: *const [N_COMP]ir.Air, b: *const Built) [N_COMP]system.Part {
    var out: [N_COMP]system.Part = undefined;
    for (&out, 0..) |*p, i| p.* = .{ .air = &airs[i], .log_size = b.log_size, .pubs = b.pubs[0..n_pubs[i]] };
    return out;
}

/// The first violated constraint of any component, for diagnostics.
pub fn firstViolation(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !?struct { comp: usize, row: usize, constraint: usize } {
    const interp = @import("../air/interp.zig");
    for (0..N_COMP) |i| {
        const tr = interp.RowTrace{ .log_size = b.log_size, .pubs = b.pubs[0..n_pubs[i]], .preprocessed = @ptrCast(try airs[i].genPreprocessed(a, b.log_size)), .main = @ptrCast(b.mains[i]) };
        if (try interp.firstViolation(a, airs[i], tr)) |v| return .{ .comp = i, .row = v.row, .constraint = v.constraint };
    }
    return null;
}

/// LogUp balance without proving: per relation, `Σ mult / (z − fingerprint)` over every site and row
/// at fixed random challenges. Returns the first unbalanced relation, or null.
pub fn unbalanced(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !?u32 {
    const interp = @import("../air/interp.zig");
    const QM31 = @import("stwo_core").fields.qm31.QM31;
    const z = QM31.fromU32Unchecked(123456789, 987654321, 192837465, 564738291);
    const alpha = QM31.fromU32Unchecked(1029384756, 1122334455, 99887766, 13572468);
    var sums = [_]QM31{QM31.zero()} ** 32;
    for (0..N_COMP) |i| {
        const air = airs[i];
        if (air.lookups.len == 0) continue;
        var t = interp.RowTrace{ .log_size = b.log_size, .pubs = b.pubs[0..n_pubs[i]], .preprocessed = @ptrCast(try air.genPreprocessed(a, b.log_size)), .main = @ptrCast(b.mains[i]) };
        const scratch = try a.alloc(M31, air.exprs.len);
        const out = try a.alloc(M31, air.constraints.len);
        const n = @as(usize, 1) << @intCast(b.log_size);
        for (0..n) |row| {
            t.row = row;
            interp.evalConstraints(M31, air, t.pubs, scratch, &t, out);
            for (air.lookups) |l| {
                const m = scratch[l.mult];
                if (m.isZero()) continue;
                var fp = QM31.fromBase(M31.fromCanonical(l.rel));
                var pw = alpha;
                for (l.vals) |v| {
                    fp = fp.add(pw.mulM31(scratch[v]));
                    pw = pw.mul(alpha);
                }
                sums[l.rel] = sums[l.rel].add(QM31.fromBase(m).mul(try z.sub(fp).inv()));
            }
        }
    }
    for (sums, 0..) |s, rel| if (!s.isZero()) return @intCast(rel);
    return null;
}

pub fn proveVerify(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !void {
    const rec = @import("../air/prove_rec.zig");
    const ps = parts(airs, b);
    const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), b.log_size);
    const E = rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var mains: [N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    try system.verifyExt(a, cfg, &ps, &.{}, try system.prove(E, a, cfg, &ps, &mains));
}

test "block system: small samples prove and verify with all nine components" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    for (checks.samples_small) |s| {
        const b = try build(a, s.raw, s.ctx);
        if (try firstViolation(a, &airs, &b)) |v| {
            std.debug.print("height {d}: {s} row {d} violates constraint {d}\n", .{ s.ctx.height, names[v.comp], v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        if (try unbalanced(a, &airs, &b)) |rel| {
            std.debug.print("height {d}: relation {d} unbalanced\n", .{ s.ctx.height, rel });
            return error.TestUnexpectedResult;
        }
        try proveVerify(a, &airs, &b);
        std.debug.print("height {d}: {d} txs, sigops {d}, weight {d}, log {d}: proved and verified\n", .{ s.ctx.height, b.ntx, b.sigops, b.weight, b.log_size });
    }
}

test "block system: large samples satisfy every component (run with ReleaseFast)" {
    var air_arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer air_arena.deinit();
    const airs = try parseAirs(air_arena.allocator());
    for (checks.samples_large) |s| {
        // About 900 columns at one shared size: a block above ~3.5 MB needs 2^23 rows and more memory
        // than a 24 GB machine has for the in-memory check (proving needs lifting or a bigger machine).
        if (s.raw.len > 3_500_000) {
            std.debug.print("height {d}: {d} bytes, skipped (in-memory check exceeds 24 GB)\n", .{ s.ctx.height, s.raw.len });
            continue;
        }
        var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer arena.deinit();
        const a = arena.allocator();
        const b = try build(a, s.raw, s.ctx);
        if (try firstViolation(a, &airs, &b)) |v| {
            std.debug.print("height {d}: {s} row {d} violates constraint {d}\n", .{ s.ctx.height, names[v.comp], v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        if (try unbalanced(a, &airs, &b)) |rel| {
            std.debug.print("height {d}: relation {d} unbalanced\n", .{ s.ctx.height, rel });
            return error.TestUnexpectedResult;
        }
        std.debug.print("height {d}: {d} txs, sigops {d}, weight {d}, commitment {}, log {d}: constraints hold, lookups balance\n", .{ s.ctx.height, b.ntx, b.sigops, b.weight, b.commitment, b.log_size });
    }
}

test "block system: the block hash is public (limbs of SHA256d(header)); a tampered limb is rejected" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    const s = checks.samples_small[0];
    var b = try build(a, s.raw, s.ctx);
    // Genesis: 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f (displayed reversed).
    if (s.ctx.height == 0) {
        var h: [32]u8 = undefined;
        _ = try std.fmt.hexToBytes(&h, "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f");
        std.mem.reverse(u8, &h);
        const want = hashLimbsOf(h);
        for (0..16) |j| try std.testing.expect(b.pubs[PUB_HASH + j].eql(want[j]));
    }
    try std.testing.expect(try unbalanced(a, &airs, &b) == null);
    b.pubs[PUB_HASH + 3] = b.pubs[PUB_HASH + 3].add(M31.one());
    try std.testing.expect(try unbalanced(a, &airs, &b) != null);
}
