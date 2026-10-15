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
const coin = @import("coin.zig");
const ancw = @import("anc.zig");

pub const N_COMP = 16;
pub const jsons = [N_COMP][]const u8{ bytes.json, fields.json, msg.json, bsha.json, merkle.json, checks.tables_json, walk.json, ctxw.json, wmerkle.json, commit.undo_json, commit.msg_json, commit.b2s_json, coin.fpwalk_json, coin.urec_json, coin.coin_json, ancw.json };
pub const names = [N_COMP][]const u8{ "bytes", "fields", "msg", "sha", "merkle", "tables", "walk", "ctx", "wmerkle", "undo", "b2msg", "b2s", "fpwalk", "urec", "coin", "anc" };
/// Public inputs each component's AIR references (a prefix of the block's 159: the eight checks inputs,
/// the undo length, the commitment's 16 limbs, the block hash's 16 limbs; then M3b's `γ`, `z`, `α`, the
/// partial sum, the input count and the BIP30-lost bit).
pub const N_PUB = coin.N_PUB;
pub const PUB_HASH = 25;
pub const n_pubs = [N_COMP]usize{ 1, 7, 0, 0, 2, 0, 0, 41, 2, 9, 9, 25, 45, 9, N_PUB, 41 };

/// Per-component trace sizes (D-045, docs/design/component-sizes.md). A block's sizes are a
/// function of (L, profile) only, so a verifying key is keyed by the pair.
pub const Profile = enum(u8) {
    /// Every component at 2^L (the system before D-045; its proofs are unchanged).
    uniform = 0,
    /// {sha, msg, bytes, walk} at L; {fpwalk, b2s, undo, b2msg} at L−2; ctx and tables at 8;
    /// anc at 12; the rest at max(L−5, 8). Requires L ≥ 12, so the largest size is L.
    tiered = 1,
};

/// Component indices (the order of `jsons`).
pub const C = struct {
    pub const bytes = 0;
    pub const fields = 1;
    pub const msg = 2;
    pub const sha = 3;
    pub const merkle = 4;
    pub const tables = 5;
    pub const walk = 6;
    pub const ctx = 7;
    pub const wmerkle = 8;
    pub const undo = 9;
    pub const b2msg = 10;
    pub const b2s = 11;
    pub const fpwalk = 12;
    pub const urec = 13;
    pub const coin = 14;
    pub const anc = 15;
};

pub const TIERED_MIN_L: u32 = 12;

/// The component log sizes of (L, profile). The largest is L.
pub fn profileLogs(L: u32, profile: Profile) [N_COMP]u32 {
    var out: [N_COMP]u32 = @splat(L);
    if (profile == .uniform) return out;
    std.debug.assert(L >= TIERED_MIN_L);
    out = @splat(@max(L - 5, 8));
    for ([_]usize{ C.sha, C.msg, C.bytes, C.walk }) |i| out[i] = L;
    for ([_]usize{ C.fpwalk, C.b2s, C.undo, C.b2msg }) |i| out[i] = L - 2;
    out[C.ctx] = 8;
    out[C.tables] = 8;
    out[C.anc] = 12;
    return out;
}

/// Lookup sites per row of the 15 hashed-system components (Lean `hashRows`, Link.lean).
pub const SITES = [15]u64{ 1, 36, 4, 6, 11, 2, 5, 12, 3, 1, 6, 11, 4, 20, 94 };

/// Lean's `SizeOk` (Link.lean): each hashed-system component has at most 2^24 rows and the lookup
/// site count `Σ kᵢ·2^logsᵢ` is below P. The soundness theorems cover only such sizes: uniform up to
/// L = 23, tiered up to L = 24.
pub fn sizeOk(logs: [N_COMP]u32) bool {
    var sum: u64 = 0;
    for (SITES, logs[0..15]) |k, l| {
        if (l > 24) return false;
        sum += k << @intCast(l);
    }
    return sum < (1 << 31) - 1;
}

pub const Built = struct {
    /// L: the largest component log size (every component's under `uniform`).
    log_size: u32,
    profile: Profile = .uniform,
    /// Each component's log size, `profileLogs(log_size, profile)`.
    logs: [N_COMP]u32,
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
    /// M3b: the block's partial LogUp sum and its non-coinbase input count.
    coin_sum: @import("stwo_core").fields.qm31.QM31 = @import("stwo_core").fields.qm31.QM31.zero(),
    nin: u32 = 0,
    /// The `block_sha` inputs (compressions and final per-period `Meta`, after the digest
    /// multiplicities) and the in-circuit undo stream (`block_b2s`'s message): what a device witness
    /// generator needs (src/gpu/cuda/witness.zig).
    sha_plan: bsha.Plan = .{ .compressions = &.{}, .meta = &.{}, .digests = &.{} },
    undo: []const u8 = &.{},
    /// The `block_msg` and `block_walk` inputs: the block, its hash messages and the walker's row
    /// records (`walk.plan`).
    raw: []const u8 = &.{},
    msgs: []const msg.Message = &.{},
    walk_recs: []const walk.Rec = &.{},
    /// The `block_bytes` multiplicities (reads per block position), with `skip_device_columns`.
    byte_mults: []const u32 = &.{},
};

/// M3b options: the epoch's challenge and the spent coins' creating transaction indices.
pub const Opts = struct {
    chal: coin.Challenge = coin.Challenge.testing(),
    ctx: ?[]const u32 = null,
    /// Pad the trace to at least 2^min_log rows (benchmarks: a small block at a real block's size).
    min_log: u32 = 0,
    /// The size profile to try; `tiered` falls back to `uniform` when the block doesn't fit it.
    profile: Profile = .uniform,
    /// Choose the profile by size (the production default, D-045 as decided 2026-10-13): `tiered`
    /// when the uniform size is at least 2^TIERED_MIN_L (with its fallback), `uniform` below.
    /// Overrides `profile`.
    auto: bool = false,
    /// Leave `mains[C.sha]`, `mains[C.b2s]`, `mains[C.msg]`, `mains[C.walk]` and `mains[C.bytes]`
    /// empty: a device generates them from `Built.sha_plan`, `Built.undo`, `Built.msgs`,
    /// `Built.walk_recs` and `Built.byte_mults` (src/gpu/cuda/witness.zig). Everything else is
    /// unchanged.
    skip_device_columns: bool = false,
};

pub fn parseAirs(a: std.mem.Allocator) ![N_COMP]ir.Air {
    var out: [N_COMP]ir.Air = undefined;
    for (&out, jsons) |*x, j| x.* = (try ir.Air.parseJson(a, j)).value;
    return out;
}

/// `build` with an empty undo record (`undo = 0x01`).
/// Builds with a synthetic undo stream (tests of single blocks): per non-coinbase input a record from
/// the height before, non-coinbase, empty script; a transaction's first record carries its outputs' total
/// (no fee), the others 0. The multiset only balances over an epoch, so
/// a single block's events need no real coins; use `buildU` with the node's undo data otherwise.
pub fn build(a: std.mem.Allocator, raw: []const u8, ctx: checks.Ctx) !Built {
    return buildU(a, raw, try syntheticUndo(a, raw, ctx.height), ctx);
}

pub fn syntheticUndo(a: std.mem.Allocator, raw: []const u8, height: u32) ![]u8 {
    const rows = fields.tokenize(a, raw) catch return a.dupe(u8, &.{1});
    // Each transaction's output total.
    var totals = std.ArrayList(u64).empty;
    var t: u64 = 0;
    for (rows) |r| {
        if (r.kind == fields.K_OUT and r.start + 8 <= raw.len) t +|= std.mem.readInt(u64, raw[r.start..][0..8], .little);
        if (r.kind == fields.K_LOCK) {
            try totals.append(a, t);
            t = 0;
        }
    }
    var out = std.ArrayList(u8).empty;
    try out.append(a, 1);
    var txi: u32 = 0;
    var first = true;
    for (rows) |r| {
        if (r.kind == fields.K_LOCK) {
            txi += 1;
            first = true;
        }
        if (r.kind == fields.K_IN and txi > 0) {
            if (height == 0) return error.NoEarlierHeight;
            var rec: [13]u8 = [_]u8{0} ** 13;
            std.mem.writeInt(u32, rec[0..4], 2 * (height - 1), .little);
            const v: u64 = if (first and txi < totals.items.len) @min(totals.items[txi], coin.MAX_MONEY) else 0;
            std.mem.writeInt(u64, rec[4..12], v, .little);
            first = false;
            try out.appendSlice(a, &rec);
        }
    }
    return out.toOwnedSlice(a);
}

pub fn buildU(a: std.mem.Allocator, raw: []const u8, undo: []const u8, ctx: checks.Ctx) !Built {
    return buildFull(a, raw, undo, ctx, .{});
}

/// The txids (SHA digests of the txid messages, internal byte order).
fn txidsOf(a: std.mem.Allocator, ntx: u32, msgs: []const msg.Message, digests: anytype) ![][32]u8 {
    const txids = try a.alloc([32]u8, ntx);
    for (msgs, digests[0..msgs.len]) |m, d| if (!m.hdr and !m.wtx) {
        txids[(m.id - 1) / 2] = bsha.digestBytes(d);
    };
    return txids;
}

/// The in-circuit undo stream of a block (`coin.undoStream`): the fetched records with their creating
/// transactions' indices. Its Blake2s is the block's public commitment.
pub fn undoStreamOf(a: std.mem.Allocator, raw: []const u8, fetched: []const u8, ctxs: ?[]const u32, height: u32) ![]u8 {
    const rows = try fields.tokenize(a, raw);
    const ntx: u32 = @intCast(rows[0].val);
    const msgs = try msg.messages(a, try msg.txRanges(a, rows));
    const pl = try bsha.plan(a, raw, msgs);
    return coin.undoStream(a, fetched, ctxs, raw, rows, try txidsOf(a, ntx, msgs, pl.digests), height);
}

/// What sizing a block needs, before any witness column: its tokens, messages, SHA plan (with the
/// txid tree's compressions), in-circuit undo stream, trees, records and fingerprint segments, and the
/// rows each component needs (`needs`; their maximum is the uniform size). `buildFull` sizes by these;
/// the chain survey (`survey`, docs/design/chain-survey.md) calls this alone.
pub const Shape = struct {
    rows: []fields.Row,
    ntx: u32,
    txs: []msg.TxRange,
    msgs: []msg.Message,
    pl: bsha.Plan,
    txids: [][32]u8,
    undo: []u8,
    nodes: []merkle.Node,
    root: @import("../sha256/spec.zig").State,
    wnodes: []merkle.Node,
    recs: []coin.Rec,
    osegs: []coin.Seg,
    usegs: []coin.Seg,
    needs: [N_COMP]usize,
};

/// `fetched`: the fetched undo stream; `ctxs`: the spent coins' creating transaction indices (or null).
/// A wrong merkle root is an error unless `force`.
pub fn shape(a: std.mem.Allocator, raw: []const u8, fetched: []const u8, ctxs: ?[]const u32, height: u32, force: bool) !Shape {
    const rows = try fields.tokenize(a, raw);
    const ntx: u32 = @intCast(rows[0].val);
    const txs = try msg.txRanges(a, rows);
    const msgs = try msg.messages(a, txs);
    var pl = try bsha.plan(a, raw, msgs);
    // M3b: the txids, and the in-circuit undo stream.
    const txids = try txidsOf(a, ntx, msgs, pl.digests);
    const undo = try coin.undoStream(a, fetched, ctxs, raw, rows, txids, height);
    const nodes = try merkle.tree(a, ntx);
    const root = try merkle.extendPlan(a, &pl, nodes);
    if (!std.mem.eql(u8, raw[36..68], &bsha.digestBytes(root)) and !force) return error.BadMerkleRoot;

    // Sizes: the checks and the walker need the fields' layout first; size by the largest need.
    const wnodes = try wmerkle.tree(a, ntx);
    var scripts_len: usize = 0;
    for (rows) |r| if ((r.kind == fields.K_IN or r.kind == fields.K_OUT) and r.val > 0) {
        scripts_len += r.val;
    };
    const comps_est = pl.compressions.len + 3 * (wnodes.len + 1);
    // M3b: undo records, fingerprint segments (outputs, then undo records' serTxOut), coin rows.
    const recs = try coin.records(a, undo);
    const osegs = try coin.outputSegs(a, rows);
    const usegs = try coin.undoSegs(a, recs);
    var fp_rows: usize = 0;
    for (osegs) |sg| fp_rows += sg.len;
    for (usegs) |sg| fp_rows += sg.len;
    var tok_rows: usize = 0;
    for (rows) |r| if (r.kind == fields.K_IN or r.kind == fields.K_OUT) {
        tok_rows += 1;
    };
    // Rows each component needs (their maximum is the uniform size).
    var needs: [N_COMP]usize = @splat(256);
    needs[C.bytes] = raw.len + 1;
    needs[C.fields] = rows.len + 1;
    needs[C.msg] = msg.rowsNeeded(msgs);
    needs[C.sha] = (comps_est + 1) * shaw.PERIOD;
    needs[C.merkle] = nodes.len + 2;
    needs[C.wmerkle] = wnodes.len + 2;
    needs[C.walk] = scripts_len + 1;
    needs[C.undo] = undo.len + 1;
    needs[C.b2msg] = commit.rowsNeeded(undo.len);
    needs[C.b2s] = commit.rowsNeeded(undo.len);
    needs[C.fpwalk] = fp_rows + 1;
    needs[C.urec] = recs.len + 1;
    needs[C.coin] = tok_rows + 1;
    needs[C.anc] = if (height >= checks.CSV_HEIGHT) ancw.MIN_ROWS_CSV else 256;
    for (&needs) |*n| n.* = @max(n.*, 256);
    return .{ .rows = rows, .ntx = ntx, .txs = txs, .msgs = msgs, .pl = pl, .txids = txids, .undo = undo, .nodes = nodes, .root = root, .wnodes = wnodes, .recs = recs, .osegs = osegs, .usegs = usegs, .needs = needs };
}

/// `fetched`: the fetched undo stream (`coin.undoStream`), with the creating transactions' indices in
/// `opts.ctx`.
pub fn buildFull(a: std.mem.Allocator, raw: []const u8, fetched: []const u8, ctx0: checks.Ctx, opts: Opts) !Built {
    // Below the CSV height the previous MTP is unused and its public limbs are 0 (D-043 part 3).
    var ctx = ctx0;
    if (!ctx.csv()) ctx.prev_mtp = 0;
    if (ctx.csv() and ctx.anc == null) return error.MissingAncestors;
    const sh = try shape(a, raw, fetched, opts.ctx, ctx.height, ctx.force);
    const rows = sh.rows;
    const ntx = sh.ntx;
    const txs = sh.txs;
    const msgs = sh.msgs;
    var pl = sh.pl;
    const txids = sh.txids;
    const undo = sh.undo;
    const nodes = sh.nodes;
    const root = sh.root;
    const wnodes = sh.wnodes;
    const recs = sh.recs;
    const osegs = sh.osegs;
    const usegs = sh.usegs;
    const needs = sh.needs;
    const sized = if (opts.auto) sizesAuto(needs, opts.min_log) else sizesFor(needs, opts.profile, opts.min_log);
    const log_size = sized.L;
    const logs = profileLogs(log_size, sized.profile);
    if (!sizeOk(logs)) return error.SizesNotCovered;

    const fm = try fields.generate(a, logs[C.fields], raw, rows);
    const chk = try checks.fill(a, fm, raw, rows, ctx);
    const wp = try walk.plan(a, logs[C.walk], raw, chk.scripts);
    const wk = walk.Out{ .cols = if (opts.skip_device_columns) &.{} else try walk.columns(a, logs[C.walk], raw, wp), .reads = wp.reads, .opcodes = wp.opcodes, .ranges = wp.ranges, .sigops = wp.sigops };
    const cid = wmerkle.commitId(wnodes);
    const cx = try ctxw.generate(a, logs[C.ctx], .{ .raw = raw, .ctx = ctx, .tx0 = txs[0], .chk = chk, .sigops = wk.sigops, .cid = cid });
    if (cx.hc) {
        const cdig = try wmerkle.extendPlan(a, &pl, wnodes, cx.nonce);
        const c = chk.commit.?;
        if (!std.mem.eql(u8, raw[c[0] + 6 ..][0..32], &bsha.digestBytes(cdig)) and !ctx.force) return error.BadWitnessCommitment;
    } else if (chk.nseg != 0 and !ctx.force) return error.UnexpectedWitness;

    // M3b: the coin events.
    var coin_raw_reads = std.ArrayList(u32).empty;
    var coin_ranges = std.ArrayList(u32).empty;
    const lost = lostHeight(ctx.height);
    const co = try coin.coinColumns(a, logs[C.coin], .{ .raw = raw, .undo = undo, .rows = rows, .height = ctx.height, .txids = txids, .recs = recs, .lost = lost, .chal = opts.chal }, &coin_raw_reads, &coin_ranges);
    var fp_raw_reads = std.ArrayList(u32).empty;
    var fp_undo_reads = std.ArrayList(u32).empty;
    const allsegs = try std.mem.concat(a, coin.Seg, &.{ osegs, usegs });
    const fpm = try coin.fpwalkColumns(a, logs[C.fpwalk], raw, undo, allsegs, opts.chal.gamma, &fp_raw_reads, &fp_undo_reads);
    var urec_reads = std.ArrayList(u32).empty;
    const urm = try coin.urecColumns(a, logs[C.urec], undo, recs, &urec_reads);

    // Multiplicities. The context reads the header's digest once (the public block hash); the coin
    // component reads each output's txid digest.
    for (pl.meta) |*m| if (m.dbl and m.mid == 0) {
        m.ym += 1;
    };
    for (pl.meta) |*m| if (m.dbl and m.mid % 2 == 1 and m.mid < 2 * ntx + 1) {
        m.ym += co.digest_uses[(m.mid - 1) / 2];
    };
    fields.setTxUses(fm, rows, 2);
    for (rows, 0..) |r, i| if (r.kind == fields.K_LOCK) {
        fm[117][i] = fm[117][i].add(M31.one()); // transaction 0's tuple: the context component's use
        break;
    };
    var reads = std.ArrayList(u32).empty;
    const mm: [][]M31 = if (opts.skip_device_columns) blk: {
        try msg.appendReads(a, msgs, &reads);
        break :blk &.{};
    } else blk: {
        const cols = try msg.generate(a, logs[C.msg], raw, msgs, &reads);
        msg.setUses(cols);
        merkle.addHeaderUses(cols);
        break :blk cols;
    };
    const sm: [][]M31 = if (opts.skip_device_columns) &.{} else try bsha.generate(a, logs[C.sha], pl);
    const km = try merkle.generate(a, logs[C.merkle], ntx, nodes, root);
    const wm = try wmerkle.generate(a, logs[C.wmerkle], ntx, wnodes, cx.hc);
    try reads.appendSlice(a, try fields.reads(a, rows));
    try reads.appendSlice(a, chk.reads);
    try reads.appendSlice(a, wk.reads);
    try reads.appendSlice(a, cx.reads);
    try reads.appendSlice(a, coin_raw_reads.items);
    try reads.appendSlice(a, fp_raw_reads.items);
    var undo_reads = std.ArrayList(u32).empty;
    try undo_reads.appendSlice(a, fp_undo_reads.items);
    try undo_reads.appendSlice(a, urec_reads.items);
    const b2m = try commit.msgColumns(a, logs[C.b2msg], undo, &undo_reads);
    const um = try commit.undoColumns(a, logs[C.undo], undo, undo_reads.items);
    const b2sm: [][]M31 = if (opts.skip_device_columns) &.{} else try commit.b2sColumns(a, logs[C.b2s], undo);
    const bm: [][]M31 = if (opts.skip_device_columns) &.{} else try bytes.generate(a, logs[C.bytes], raw, reads.items);
    const byte_mults: []const u32 = if (opts.skip_device_columns) try bytes.multiplicities(a, raw.len, reads.items) else &.{};
    var ranges = std.ArrayList(u32).empty;
    try ranges.appendSlice(a, chk.ranges);
    try ranges.appendSlice(a, wk.ranges);
    try ranges.appendSlice(a, cx.ranges);
    try ranges.appendSlice(a, coin_ranges.items);
    const tm = try checks.tables(a, logs[C.tables], ranges.items, wk.opcodes);

    const am = try ancw.generate(a, logs[C.anc], raw[0..80], if (ctx.csv()) ctx.anc.? else null, ctx.prev_mtp, ctx.force);
    const cw = try commit.commitment(a, undo);
    var pubs: [N_PUB]M31 = undefined;
    @memcpy(pubs[0..8], &checks.pubs(raw, ntx, ctx));
    pubs[8] = M31.fromCanonical(@intCast(undo.len));
    @memcpy(pubs[9..25], &commit.pubLimbs(cw));
    @memcpy(pubs[PUB_HASH..41], &hashLimbs(raw[0..80]));
    @memcpy(pubs[41..N_PUB], &coin.pubs(opts.chal, co.sum, co.nin, lost, ctx.height));
    return .{
        .log_size = log_size,
        .profile = sized.profile,
        .logs = logs,
        .pubs = pubs,
        .commitment_words = cw,
        .mains = .{ bm, fm, mm, sm, km, tm, wk.cols, cx.cols, wm, um, b2m, b2sm, fpm, urm, co.cols, am },
        .ntx = ntx,
        .sigops = wk.sigops,
        .weight = 4 * @as(u64, raw.len) - 3 * @as(u64, chk.w),
        .commitment = cx.hc,
        .reads = reads.items,
        .coin_sum = co.sum,
        .nin = co.nin,
        .sha_plan = pl,
        .undo = undo,
        .raw = raw,
        .msgs = msgs,
        .walk_recs = wp.recs,
        .byte_mults = byte_mults,
    };
}

/// The block hash's public limbs: SHA256d of the header as SHA-256 state words (big-endian words of
/// the hash in internal byte order), limb `2w + h` half `h` of word `w` (Lean: `HashPub.hash_pub`).
/// Coinbases whose outputs are never created: genesis (Core never connects it) and the two BIP30
/// coinbases Core overwrote unspent (public input 158).
pub fn lostHeight(h: u32) bool {
    return h == 0 or h == 91722 or h == 91812;
}

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
    return partsAt(airs, b.logs, &b.pubs);
}

/// The system's parts at the given component sizes.
pub fn partsAt(airs: *const [N_COMP]ir.Air, logs: [N_COMP]u32, pubs: *const [N_PUB]M31) [N_COMP]system.Part {
    var out: [N_COMP]system.Part = undefined;
    for (&out, 0..) |*p, i| p.* = .{ .air = &airs[i], .log_size = logs[i], .pubs = pubs[0..n_pubs[i]] };
    return out;
}

/// (L, profile) for components needing `needs` rows: `tiered` when asked for and every component
/// fits its tier, else `uniform`; L at least `min_log`.
pub const Sized = struct { L: u32, profile: Profile };

/// The production choice: tiered for blocks of uniform size 2^12 and more, uniform below.
pub fn sizesAuto(needs: [N_COMP]usize, min_log: u32) Sized {
    const u = sizesFor(needs, .uniform, min_log);
    if (u.L < TIERED_MIN_L) return u;
    return sizesFor(needs, .tiered, min_log);
}

pub fn sizesFor(needs: [N_COMP]usize, profile: Profile, min_log: u32) Sized {
    var max: usize = 0;
    for (needs) |n| max = @max(max, n);
    const uniform_L = @max(std.math.log2_int_ceil(usize, max), min_log);
    if (profile == .uniform) return .{ .L = uniform_L, .profile = .uniform };
    var top: usize = 0;
    for ([_]usize{ C.sha, C.msg, C.bytes, C.walk }) |i| top = @max(top, needs[i]);
    const L = @max(std.math.log2_int_ceil(usize, top), min_log, TIERED_MIN_L);
    const logs = profileLogs(L, .tiered);
    for (needs, logs) |n, l| if (n > @as(usize, 1) << @intCast(l)) return .{ .L = uniform_L, .profile = .uniform };
    return .{ .L = L, .profile = .tiered };
}

/// A block's size as the survey reports it (docs/design/chain-survey.md): `sizesAuto`'s choice, the
/// uniform L, the component whose need sets L (`binding`; null when a floor does: 2^8 rows, or tiered's
/// 2^12), and on a fallback to uniform the first component that misses its tier (`misfit`). `covered`:
/// Lean's `SizeOk` holds (else `buildFull` refuses the block).
pub const SizeReport = struct { sized: Sized, uniform_L: u32, binding: ?usize, misfit: ?usize, covered: bool };

pub fn sizeReport(needs: [N_COMP]usize) SizeReport {
    const sized = sizesAuto(needs, 0);
    const u = sizesFor(needs, .uniform, 0);
    var misfit: ?usize = null;
    if (u.L >= TIERED_MIN_L and sized.profile == .uniform) {
        var top: usize = 0;
        for ([_]usize{ C.sha, C.msg, C.bytes, C.walk }) |i| top = @max(top, needs[i]);
        const logs = profileLogs(@max(std.math.log2_int_ceil(usize, top), TIERED_MIN_L), .tiered);
        for (needs, logs, 0..) |n, l, i| if (n > @as(usize, 1) << @intCast(l)) {
            misfit = i;
            break;
        };
    }
    var binding: ?usize = null;
    var best: usize = 0;
    for (needs, 0..) |n, i| {
        if (sized.profile == .tiered and i != C.sha and i != C.msg and i != C.bytes and i != C.walk) continue;
        if (n > best) {
            best = n;
            binding = i;
        }
    }
    if (best <= 256 or std.math.log2_int_ceil(usize, best) != sized.L) binding = null;
    return .{ .sized = sized, .uniform_L = u.L, .binding = binding, .misfit = misfit, .covered = sizeOk(profileLogs(sized.L, sized.profile)) };
}

/// The first violated constraint of any component, for diagnostics.
pub fn firstViolation(a: std.mem.Allocator, airs: *const [N_COMP]ir.Air, b: *const Built) !?struct { comp: usize, row: usize, constraint: usize } {
    const interp = @import("../air/interp.zig");
    for (0..N_COMP) |i| {
        const tr = interp.RowTrace{ .log_size = b.logs[i], .pubs = b.pubs[0..n_pubs[i]], .preprocessed = @ptrCast(try airs[i].genPreprocessed(a, b.logs[i])), .main = @ptrCast(b.mains[i]) };
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
        var t = interp.RowTrace{ .log_size = b.logs[i], .pubs = b.pubs[0..n_pubs[i]], .preprocessed = @ptrCast(try air.genPreprocessed(a, b.logs[i])), .main = @ptrCast(b.mains[i]) };
        const scratch = try a.alloc(M31, air.exprs.len);
        const out = try a.alloc(M31, air.constraints.len);
        const n = @as(usize, 1) << @intCast(b.logs[i]);
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
        const b = try buildU(a, s.raw, s.undo, s.ctx);
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
        const b = try buildU(a, s.raw, s.undo, s.ctx);
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
    var b = try buildU(a, s.raw, s.undo, s.ctx);
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

test "block system: block 0's STWZEVA-composed proof is byte-identical and verifies" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const rec = @import("../air/prove_rec.zig");
    const airs = try parseAirs(a);
    const s = checks.samples_small[0];
    const b = try buildU(a, s.raw, s.undo, s.ctx);
    const ps = parts(&airs, &b);
    const cfg = rec.Config.fromFriAndTraceSize(try @import("stwo_core").pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1), b.log_size);
    var mains: [N_COMP][]const []const M31 = undefined;
    for (&mains, b.mains) |*m, x| m.* = @ptrCast(x);
    var timer = try std.time.Timer.start();
    const n = try system.checkStwzevaProof(rec.Engine(@import("stwo_cpu_backend").CpuBackend), a, cfg, &ps, &mains, &.{});
    std.debug.print("block 0 (log {d}, {d} components): STWZEVA proof byte-identical ({d} bytes, both proofs + verify {d} ms)\n", .{ b.log_size, N_COMP, n, timer.read() / std.time.ns_per_ms });
}

/// SHA-256 of the uniform-profile proof bytes (`system.proofBytes`) of each `checks.samples_small`
/// block, proved by `proof_file.prove` at test strength (10 PoW bits, 3 queries, blowup 1), as
/// m3a5 (2196ba3) produced them: per-component sizes (D-045) must not change a uniform proof.
pub const golden_small = [_][]const u8{
    "b03d4b8a1fc12a64fb44c0b2933dd941fedd220110d2d999185962e2794e24a0", // 0
    "0b9bb2796927f868ff476b77ea57778b8b89d5ce6b2e129abfa57f93ff4bc7d7", // 170
    "062de839b0e31810ca2971795336217e8a33486810375a0a07d56a48ce553c13", // 91722
    "ee1f06d290adf5789f8df283b2c9bf6bdf852d750b4338adcd7980f1fc6e1cab", // 91812
    "d3bff4057f8dfefb911ed42e76b9612b06d4eaa0ce15ba9b421a8250272d1a14", // 91842
    "f7273a6d416ed97cabbfc32457f13974fc8862ad1e7f262d1040846c122fa8e3", // 91880
};

test "block system: uniform proofs of the small samples match the m3a5 golden hashes" {
    const pf = @import("proof_file.zig");
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    for (checks.samples_small, 0..) |s, i| {
        const b = try buildU(a, s.raw, s.undo, s.ctx);
        const proof_bytes = try system.proofBytes(a, try pf.prove(a, &airs, &b, pf.testFri()));
        var digest: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(proof_bytes, &digest, .{});
        const hex = std.fmt.bytesToHex(digest, .lower);
        std.debug.print("golden height {d}: {s}\n", .{ s.ctx.height, hex });
        try std.testing.expectEqualStrings(golden_small[i], &hex);
    }
}

test "block system: tiered profile (D-045): the small samples satisfy every component, prove and verify through a proof file" {
    const pf = @import("proof_file.zig");
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try parseAirs(a);
    for (checks.samples_small) |s| {
        const b = try buildFull(a, s.raw, s.undo, s.ctx, .{ .profile = .tiered });
        try std.testing.expectEqual(Profile.tiered, b.profile);
        if (try firstViolation(a, &airs, &b)) |v| {
            std.debug.print("height {d}: {s} row {d} violates constraint {d}\n", .{ s.ctx.height, names[v.comp], v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        if (try unbalanced(a, &airs, &b)) |rel| {
            std.debug.print("height {d}: relation {d} unbalanced\n", .{ s.ctx.height, rel });
            return error.TestUnexpectedResult;
        }
        const proof = try pf.prove(a, &airs, &b, pf.testFri());
        const bytes_ = try pf.encode(a, &.{ .log_size = b.log_size, .profile = b.profile, .pubs = b.pubs, .proof = proof, .provenance = "test" });
        const f = try pf.decode(a, bytes_);
        try pf.verifyStark(a, &airs, &f, pf.testFri());
        // The same proof read as uniform fails.
        var g = try pf.decode(a, bytes_);
        g.profile = .uniform;
        try std.testing.expect(std.meta.isError(pf.verifyStark(a, &airs, &g, pf.testFri())));
        std.debug.print("height {d}: tiered L={d} sizes {any}: proved, verified ({d} bytes)\n", .{ s.ctx.height, b.log_size, b.logs, bytes_.len });
    }
}

test "block system: sizesFor picks tiered only when every component fits, else uniform" {
    var needs: [N_COMP]usize = @splat(256);
    needs[C.sha] = 1 << 20;
    needs[C.b2s] = 1 << 18;
    needs[C.coin] = 1 << 15;
    const t = sizesFor(needs, .tiered, 0);
    try std.testing.expectEqual(Profile.tiered, t.profile);
    try std.testing.expectEqual(@as(u32, 20), t.L);
    needs[C.coin] = (1 << 15) + 1; // above L − 5
    const u = sizesFor(needs, .tiered, 0);
    try std.testing.expectEqual(Profile.uniform, u.profile);
    try std.testing.expectEqual(@as(u32, 20), u.L);
    try std.testing.expectEqual(Profile.uniform, sizesFor(needs, .uniform, 0).profile);
    // Small blocks: tiered L is at least 12 (anc's size), and min_log pads it.
    needs = @splat(256);
    try std.testing.expectEqual(@as(u32, 12), sizesFor(needs, .tiered, 0).L);
    try std.testing.expectEqual(@as(u32, 16), sizesFor(needs, .tiered, 16).L);
    const logs = profileLogs(16, .tiered);
    try std.testing.expectEqualSlices(u32, &.{ 16, 11, 16, 16, 11, 8, 16, 8, 11, 14, 14, 14, 14, 11, 11, 12 }, &logs);
}

test "block system: SizeOk matches the AIRs' lookups; uniform stops at 23, tiered reaches 24" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const airs = try parseAirs(arena.allocator());
    for (SITES, airs[0..15]) |k, air| try std.testing.expectEqual(k, air.lookups.len);
    try std.testing.expect(sizeOk(profileLogs(23, .uniform)));
    try std.testing.expect(!sizeOk(profileLogs(24, .uniform)));
    try std.testing.expect(sizeOk(profileLogs(24, .tiered)));
    try std.testing.expect(!sizeOk(profileLogs(25, .tiered)));
}

test "block sizes: auto is uniform below 2^12 and tiered from 2^12" {
    var needs: [N_COMP]usize = @splat(256);
    needs[C.sha] = 2000; // uniform 2^11
    const small = sizesAuto(needs, 0);
    try std.testing.expectEqual(Profile.uniform, small.profile);
    try std.testing.expectEqual(@as(u32, 11), small.L);
    needs[C.sha] = 3000; // uniform 2^12
    try std.testing.expectEqual(Profile.tiered, sizesAuto(needs, 0).profile);
    needs[C.sha] = 1 << 22;
    const big = sizesAuto(needs, 0);
    try std.testing.expectEqual(Profile.tiered, big.profile);
    try std.testing.expectEqual(@as(u32, 22), big.L);
    needs[C.coin] = 1 << 21; // too big for its tier (L − 5): falls back to uniform
    try std.testing.expectEqual(Profile.uniform, sizesAuto(needs, 0).profile);
}

test "tiered real block (STARKED_TIERED_LARGE=height): constraints hold and lookups balance" {
    const want = std.process.getEnvVarOwned(std.heap.page_allocator, "STARKED_TIERED_LARGE") catch return error.SkipZigTest;
    const height = try std.fmt.parseInt(u32, want, 10);
    var air_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer air_arena.deinit();
    const airs = try parseAirs(air_arena.allocator());
    for (checks.samples_large) |s| {
        if (s.ctx.height != height) continue;
        var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer arena.deinit();
        const a = arena.allocator();
        var timer = try std.time.Timer.start();
        const b = try buildFull(a, s.raw, s.undo, s.ctx, .{ .profile = .tiered });
        std.debug.print("height {d}: profile {s}, L={d}, sizes {any}, witness {d} ms\n", .{ s.ctx.height, @tagName(b.profile), b.log_size, b.logs, timer.lap() / std.time.ns_per_ms });
        if (try firstViolation(a, &airs, &b)) |v| {
            std.debug.print("height {d}: {s} row {d} violates constraint {d}\n", .{ s.ctx.height, names[v.comp], v.row, v.constraint });
            return error.TestUnexpectedResult;
        }
        if (try unbalanced(a, &airs, &b)) |rel| {
            std.debug.print("height {d}: relation {d} unbalanced\n", .{ s.ctx.height, rel });
            return error.TestUnexpectedResult;
        }
        std.debug.print("height {d}: constraints hold, lookups balance ({d} ms)\n", .{ s.ctx.height, timer.read() / std.time.ns_per_ms });
        return;
    }
    return error.NoSuchSample;
}

test "block sizes: shape's needs give buildFull's (L, profile) on every sample (large: STARKED_SURVEY_LARGE=1, ReleaseFast)" {
    const large = if (std.process.getEnvVarOwned(std.heap.page_allocator, "STARKED_SURVEY_LARGE")) |_| true else |_| false;
    const all = checks.samples_small ++ checks.samples_large;
    for (all, 0..) |s, k| {
        if (k >= checks.samples_small.len and !large) continue;
        var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
        defer arena.deinit();
        const a = arena.allocator();
        const sh = try shape(a, s.raw, s.undo, null, s.ctx.height, false);
        const r = sizeReport(sh.needs);
        const b = try buildFull(a, s.raw, s.undo, s.ctx, .{ .auto = true });
        std.debug.print("height {d}: survey L={d} {s} (uniform {d}, binding {s}); buildFull L={d} {s}\n", .{ s.ctx.height, r.sized.L, @tagName(r.sized.profile), r.uniform_L, if (r.binding) |i| names[i] else "floor", b.log_size, @tagName(b.profile) });
        try std.testing.expectEqual(b.log_size, r.sized.L);
        try std.testing.expectEqual(b.profile, r.sized.profile);
        try std.testing.expect(r.covered);
    }
}

test "block sizes: sizeReport names the binding component and the misfit" {
    var needs: [N_COMP]usize = @splat(256);
    try std.testing.expectEqual(@as(?usize, null), sizeReport(needs).binding);
    needs[C.sha] = 3000;
    needs[C.coin] = 5000; // uniform 2^13 by coin; tiered 2^12 by sha with coin above 2^8: fallback
    const r = sizeReport(needs);
    try std.testing.expectEqual(Profile.uniform, r.sized.profile);
    try std.testing.expectEqual(@as(u32, 13), r.sized.L);
    try std.testing.expectEqual(@as(?usize, C.coin), r.binding);
    try std.testing.expectEqual(@as(?usize, C.coin), r.misfit);
    needs[C.coin] = 256;
    needs[C.walk] = 1 << 20;
    const t = sizeReport(needs);
    try std.testing.expectEqual(Profile.tiered, t.sized.profile);
    try std.testing.expectEqual(@as(?usize, C.walk), t.binding);
    try std.testing.expectEqual(@as(?usize, null), t.misfit);
}
