//! The block system (M3a.5, D-035): every component of the block proof, at one log size, in the
//! order the Lean statement uses: bytes, fields, messages, SHA, txid tree, tables, sigop walker,
//! context, witness tree. `build` computes all witnesses for a raw block in its context.

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

pub const N_COMP = 9;
pub const jsons = [N_COMP][]const u8{ bytes.json, fields.json, msg.json, bsha.json, merkle.json, checks.tables_json, walk.json, ctxw.json, wmerkle.json };
pub const names = [N_COMP][]const u8{ "bytes", "fields", "msg", "sha", "merkle", "tables", "walk", "ctx", "wmerkle" };
/// Public inputs each component's AIR references (a prefix of the block's seven).
pub const n_pubs = [N_COMP]usize{ 1, 7, 0, 0, 2, 0, 0, 7, 2 };

pub const Built = struct {
    log_size: u32,
    pubs: [7]M31,
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

pub fn build(a: std.mem.Allocator, raw: []const u8, ctx: checks.Ctx) !Built {
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
    const need = @max(@max(msg.rowsNeeded(msgs), raw.len + 1, rows.len + 1, (comps_est + 1) * shaw.PERIOD), @max(nodes.len + 2, wnodes.len + 2, scripts_len + 1, 256));
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

    // Multiplicities.
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
    const bm = try bytes.generate(a, log_size, raw, reads.items);
    var ranges = std.ArrayList(u32).empty;
    try ranges.appendSlice(a, chk.ranges);
    try ranges.appendSlice(a, wk.ranges);
    try ranges.appendSlice(a, cx.ranges);
    const tm = try checks.tables(a, log_size, ranges.items, wk.opcodes);

    return .{
        .log_size = log_size,
        .pubs = checks.pubs(raw, ntx, ctx),
        .mains = .{ bm, fm, mm, sm, km, tm, wk.cols, cx.cols, wm },
        .ntx = ntx,
        .sigops = wk.sigops,
        .weight = 4 * @as(u64, raw.len) - 3 * @as(u64, chk.w),
        .commitment = cx.hc,
        .reads = reads.items,
    };
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
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    for (checks.samples_large) |s| {
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
