//! Native reference of the two `ConnectBlock` rules of CONNECT-RULES (docs/design/connect-rules.md):
//! the sigop cost (`GetTransactionSigOpCost`: legacy, P2SH and witness parts) and the BIP68 sequence
//! locks (`SequenceLocks`). It mirrors `lean/StarkedAir/Spec/ConnectRules.lean`, which is fuzzed against
//! Core (`tools/specfuzz/core_connect_cases.cpp`); `zig build test` checks this file on the same cases
//! when STARKED_CONNECT_CASES names the fuzzer's output. Nothing here is proven or used by a prover yet:
//! the survey runs it over real blocks, and the witness generators will be tested against it.

const std = @import("std");
const walk = @import("walk.zig");

pub const MAX_BLOCK_SIGOPS_COST: u64 = 80000;
pub const CSV_HEIGHT: u32 = 419328;

pub const Op = struct { op: u8, data: []const u8 };

/// `CScript::GetOp`: `next` returns null at the end or at a push that runs past it (`failed`).
pub const OpIter = struct {
    s: []const u8,
    pc: usize = 0,
    failed: bool = false,

    pub fn next(it: *OpIter) ?Op {
        if (it.failed or it.pc >= it.s.len) return null;
        const s = it.s;
        const o = s[it.pc];
        var pc = it.pc + 1;
        if (o > 0x4e) {
            it.pc = pc;
            return .{ .op = o, .data = s[pc..pc] };
        }
        var n: usize = o;
        if (o >= 0x4c) {
            const k: usize = if (o == 0x4c) 1 else if (o == 0x4d) 2 else 4;
            if (s.len - pc < k) {
                it.failed = true;
                return null;
            }
            n = 0;
            for (0..k) |i| n |= @as(usize, s[pc + i]) << @intCast(8 * i);
            pc += k;
        }
        if (s.len - pc < n) {
            it.failed = true;
            return null;
        }
        it.pc = pc + n;
        return .{ .op = o, .data = s[pc .. pc + n] };
    }
};

/// `GetSigOpCount(true)`: `OP_CHECKMULTISIG(VERIFY)` after `OP_1 … OP_16` counts that number, else 20.
pub fn sigOpsAccurate(s: []const u8) u32 {
    var it: OpIter = .{ .s = s };
    var last: u8 = 0xff;
    var n: u32 = 0;
    while (it.next()) |x| {
        n += switch (x.op) {
            0xac, 0xad => 1,
            0xae, 0xaf => if (last >= 0x51 and last <= 0x60) last - 0x50 else 20,
            else => 0,
        };
        last = x.op;
    }
    return n;
}

/// `CScript::IsPayToScriptHash`.
pub fn isP2SH(s: []const u8) bool {
    return s.len == 23 and s[0] == 0xa9 and s[1] == 0x14 and s[22] == 0x87;
}

pub const Program = struct { version: u8, prog: []const u8 };

/// `CScript::IsWitnessProgram`.
pub fn witnessProgram(s: []const u8) ?Program {
    if (s.len < 4 or s.len > 42) return null;
    if (s[0] != 0 and (s[0] < 0x51 or s[0] > 0x60)) return null;
    if (@as(usize, s[1]) + 2 != s.len) return null;
    return .{ .version = if (s[0] == 0) 0 else s[0] - 0x50, .prog = s[2..] };
}

/// The data of the last operation of a push-only script (`IsPushOnly`: it parses and no opcode is above
/// `OP_16`); null if the script is not push-only. Empty for an empty script.
pub fn lastPush(s: []const u8) ?[]const u8 {
    var it: OpIter = .{ .s = s };
    var last: []const u8 = s[0..0];
    while (it.next()) |x| {
        if (x.op > 0x60) return null;
        last = x.data;
    }
    return if (it.failed) null else last;
}

/// What `GetP2SHSigOpCount` adds for one input.
pub fn p2shSigOps(spent: []const u8, script_sig: []const u8) u32 {
    if (!isP2SH(spent)) return 0;
    return sigOpsAccurate(lastPush(script_sig) orelse return 0);
}

fn witnessSigOps(p: Program, last_witness: ?[]const u8) u32 {
    if (p.version != 0) return 0;
    if (p.prog.len == 20) return 1;
    if (p.prog.len == 32) return if (last_witness) |w| sigOpsAccurate(w) else 0;
    return 0;
}

/// `CountWitnessSigOps` with the witness flag set. `last_witness`: the input's last witness item, null
/// when its witness stack is empty.
pub fn countWitnessSigOps(script_sig: []const u8, spent: []const u8, last_witness: ?[]const u8) u32 {
    if (witnessProgram(spent)) |p| return witnessSigOps(p, last_witness);
    if (isP2SH(spent)) if (lastPush(script_sig)) |redeem| if (witnessProgram(redeem)) |p| return witnessSigOps(p, last_witness);
    return 0;
}

pub const Lock = union(enum) { none, height: u16, time: u16 };

/// The relative lock of one input under BIP68 (transaction version at least 2 and CSV active are the
/// caller's): bit 31 disables, bit 22 selects time (units of 512 s), the low 16 bits are the lock.
pub fn inputLock(sequence: u32) Lock {
    if (sequence & 0x80000000 != 0) return .none;
    const v: u16 = @truncate(sequence);
    return if (sequence & 0x00400000 != 0) .{ .time = v } else .{ .height = v };
}

pub const In = struct { script_sig: []const u8, sequence: u32, last_witness: ?[]const u8 = null };
pub const Tx = struct { version: u32, ins: []In, outs: [][]const u8, coinbase: bool };

fn compact(raw: []const u8, p: *usize) !usize {
    if (p.* >= raw.len) return error.Truncated;
    const b = raw[p.*];
    p.* += 1;
    const n: usize = switch (b) {
        0xfd => 2,
        0xfe => 4,
        0xff => 8,
        else => return b,
    };
    if (raw.len - p.* < n) return error.Truncated;
    var v: u64 = 0;
    for (0..n) |i| v |= @as(u64, raw[p.* + i]) << @intCast(8 * i);
    p.* += n;
    return std.math.cast(usize, v) orelse error.Truncated;
}

fn take(raw: []const u8, p: *usize, n: usize) ![]const u8 {
    if (raw.len - p.* < n) return error.Truncated;
    defer p.* += n;
    return raw[p.* .. p.* + n];
}

/// One transaction of a block (Core's serialization with witness), advancing `p`.
pub fn parseTx(a: std.mem.Allocator, raw: []const u8, p: *usize) !Tx {
    const version = std.mem.readInt(u32, (try take(raw, p, 4))[0..4], .little);
    var segwit = false;
    if (raw.len - p.* >= 2 and raw[p.*] == 0 and raw[p.* + 1] != 0) {
        segwit = true;
        p.* += 2;
    }
    const nin = try compact(raw, p);
    if (nin > raw.len) return error.Truncated;
    const ins = try a.alloc(In, nin);
    var coinbase = false;
    for (ins, 0..) |*in, i| {
        const prev = try take(raw, p, 36);
        if (i == 0 and nin == 1) coinbase = std.mem.allEqual(u8, prev[0..32], 0) and std.mem.readInt(u32, prev[32..36], .little) == 0xffffffff;
        const ss = try take(raw, p, try compact(raw, p));
        in.* = .{ .script_sig = ss, .sequence = std.mem.readInt(u32, (try take(raw, p, 4))[0..4], .little) };
    }
    const nout = try compact(raw, p);
    if (nout > raw.len) return error.Truncated;
    const outs = try a.alloc([]const u8, nout);
    for (outs) |*o| {
        _ = try take(raw, p, 8);
        o.* = try take(raw, p, try compact(raw, p));
    }
    if (segwit) for (ins) |*in| {
        const items = try compact(raw, p);
        for (0..items) |_| in.last_witness = try take(raw, p, try compact(raw, p));
    };
    _ = try take(raw, p, 4);
    return .{ .version = version, .ins = ins, .outs = outs, .coinbase = coinbase };
}

pub const SigOps = struct { legacy: u32 = 0, p2sh: u32 = 0, witness: u32 = 0 };

/// The parts of `GetTransactionSigOpCost`; `spent[i]` is the script of the coin input `i` spends (unused
/// for a coinbase). `strict`: the P2SH and witness flags (true for every mainnet block but the BIP16
/// exception at height 170,060).
pub fn txSigOps(tx: Tx, spent: []const []const u8, strict: bool) SigOps {
    var r: SigOps = .{};
    for (tx.ins) |in| r.legacy += walk.sigOps(in.script_sig);
    for (tx.outs) |o| r.legacy += walk.sigOps(o);
    if (tx.coinbase or !strict) return r;
    for (tx.ins, spent) |in, s| {
        r.p2sh += p2shSigOps(s, in.script_sig);
        r.witness += countWitnessSigOps(in.script_sig, s, in.last_witness);
    }
    return r;
}

pub fn cost(s: SigOps) u64 {
    return 4 * (@as(u64, s.legacy) + s.p2sh) + s.witness;
}

pub const TimeLock = struct { coin_height: u32, lock: u16 };

pub const BlockRules = struct {
    sigops: SigOps = .{},
    inputs: u32 = 0,
    /// Height-based locks that apply (version at least 2, CSV active, bit 31 clear), and those not met.
    height_locks: u32 = 0,
    height_failed: u32 = 0,
    /// Time-based locks that apply: the caller checks them, as they need median times past.
    time_locks: []TimeLock = &.{},
};

/// Both rules over a raw block and its undo stream (`0x01`, then per non-coinbase input LE32 code
/// `2·height + coinbase`, LE64 value, CompactSize length, script).
pub fn blockRules(a: std.mem.Allocator, raw: []const u8, undo: []const u8, height: u32, strict: bool) !BlockRules {
    var out: BlockRules = .{};
    var tl: std.ArrayList(TimeLock) = .empty;
    var spent: std.ArrayList([]const u8) = .empty;
    var p: usize = 80;
    var u: usize = 1;
    if (raw.len < 80 or undo.len < 1) return error.Truncated;
    const ntx = try compact(raw, &p);
    for (0..ntx) |t| {
        const tx = try parseTx(a, raw, &p);
        if (tx.coinbase != (t == 0)) return error.CoinbasePosition;
        spent.clearRetainingCapacity();
        if (!tx.coinbase) for (tx.ins) |in| {
            const code = std.mem.readInt(u32, (try take(undo, &u, 4))[0..4], .little);
            _ = try take(undo, &u, 8);
            try spent.append(a, try take(undo, &u, try compact(undo, &u)));
            out.inputs += 1;
            if (height < CSV_HEIGHT or tx.version < 2) continue;
            const c = code >> 1;
            switch (inputLock(in.sequence)) {
                .none => {},
                .height => |l| {
                    out.height_locks += 1;
                    if (@as(u64, c) + l > height) out.height_failed += 1;
                },
                .time => |l| try tl.append(a, .{ .coin_height = c, .lock = l }),
            }
        };
        const s = txSigOps(tx, spent.items, strict);
        out.sigops.legacy += s.legacy;
        out.sigops.p2sh += s.p2sh;
        out.sigops.witness += s.witness;
    }
    if (p != raw.len or u != undo.len) return error.LengthMismatch;
    out.time_locks = try tl.toOwnedSlice(a);
    return out;
}

test "accurate sigops and witness programs (the Lean spec's examples)" {
    try std.testing.expectEqual(@as(u32, 3), sigOpsAccurate(&.{ 0x52, 0x53, 0xae }));
    try std.testing.expectEqual(@as(u32, 20), walk.sigOps(&.{ 0x52, 0x53, 0xae }));
    try std.testing.expectEqual(@as(u32, 0), sigOpsAccurate(&.{ 0x52, 0x21 }));
    const p2sh = [_]u8{ 0xa9, 0x14 } ++ [_]u8{1} ** 20 ++ [_]u8{0x87};
    const ss = [_]u8{ 0x16, 0x00, 0x14 } ++ [_]u8{7} ** 20;
    try std.testing.expectEqual(@as(u32, 1), countWitnessSigOps(&ss, &p2sh, null));
    try std.testing.expectEqual(@as(u32, 0), p2shSigOps(&p2sh, &ss));
    const p2tr = [_]u8{ 0x51, 0x20 } ++ [_]u8{1} ** 32;
    try std.testing.expectEqual(@as(u32, 0), countWitnessSigOps(&.{}, &p2tr, &.{0xac}));
    const p2wsh = [_]u8{ 0x00, 0x20 } ++ [_]u8{1} ** 32;
    try std.testing.expectEqual(@as(u32, 3), countWitnessSigOps(&.{}, &p2wsh, &.{ 0x52, 0x53, 0xae }));
    try std.testing.expectEqual(@as(u32, 0), countWitnessSigOps(&.{}, &p2wsh, null));
    try std.testing.expect(lastPush(&.{ 0x01, 0xac, 0xac }) == null);
    try std.testing.expect(lastPush(&.{0x02}) == null);
    try std.testing.expectEqual(Lock{ .height = 10 }, inputLock(10));
    try std.testing.expectEqual(Lock{ .time = 3 }, inputLock(0x00400003));
    try std.testing.expectEqual(Lock.none, inputLock(0x80000003));
}

fn unhex(a: std.mem.Allocator, s: []const u8) ![]u8 {
    if (std.mem.eql(u8, s, "-")) return a.alloc(u8, 0);
    const out = try a.alloc(u8, s.len / 2);
    return std.fmt.hexToBytes(out, s);
}

test "the fuzzer's cases, answered as Core does (STARKED_CONNECT_CASES)" {
    const path = std.posix.getenv("STARKED_CONNECT_CASES") orelse return error.SkipZigTest;
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const text = try std.fs.cwd().readFileAlloc(a, path, 1 << 30);
    var lines = std.mem.splitScalar(u8, text, '\n');
    var n: [3]u32 = .{ 0, 0, 0 };
    while (lines.next()) |line| {
        var tab = std.mem.splitScalar(u8, line, '\t');
        var f = std.mem.splitScalar(u8, tab.first(), ' ');
        const want = tab.next() orelse continue;
        const kind = f.first();
        if (std.mem.eql(u8, kind, "sigacc")) {
            try std.testing.expectEqual(try std.fmt.parseInt(u32, want, 10), sigOpsAccurate(try unhex(a, f.next().?)));
            n[0] += 1;
        } else if (std.mem.eql(u8, kind, "sigcost")) {
            const strict = std.mem.eql(u8, f.next().?, "1");
            var p: usize = 0;
            const tx = try parseTx(a, try unhex(a, f.next().?), &p);
            var spent: std.ArrayList([]const u8) = .empty;
            var it = std.mem.splitScalar(u8, f.next().?, ',');
            while (it.next()) |h| try spent.append(a, try unhex(a, h));
            try std.testing.expectEqual(try std.fmt.parseInt(u64, want, 10), cost(txSigOps(tx, spent.items, strict)));
            n[1] += 1;
        } else if (std.mem.eql(u8, kind, "seqlock")) {
            const enforce = std.mem.eql(u8, f.next().?, "1");
            var times: std.ArrayList(u32) = .empty;
            var it = std.mem.splitScalar(u8, f.next().?, ',');
            while (it.next()) |t| try times.append(a, try std.fmt.parseInt(u32, t, 10));
            var p: usize = 0;
            const tx = try parseTx(a, try unhex(a, f.next().?), &p);
            const height: u32 = @intCast(times.items.len - 1);
            var ok = true;
            var hs = std.mem.splitScalar(u8, f.next().?, ',');
            for (tx.ins) |in| {
                const c = try std.fmt.parseInt(u32, hs.next().?, 10);
                if (!enforce or tx.version < 2) continue;
                switch (inputLock(in.sequence)) {
                    .none => {},
                    .height => |l| ok = ok and c + l <= height,
                    .time => |l| ok = ok and @as(u64, mtp(times.items, c -| 1)) + 512 * @as(u64, l) <= mtp(times.items, height - 1),
                }
            }
            var w = std.mem.splitBackwardsScalar(u8, want, ' ');
            try std.testing.expectEqual(std.mem.eql(u8, w.first(), "1"), ok);
            n[2] += 1;
        }
    }
    try std.testing.expect(n[0] > 0 and n[1] > 0 and n[2] > 0);
}

/// `GetMedianTimePast` of block `k` from the chain's block times.
pub fn mtp(times: []const u32, k: usize) u32 {
    var buf: [11]u32 = undefined;
    const lo = if (k >= 10) k - 10 else 0;
    const l = buf[0 .. k + 1 - lo];
    @memcpy(l, times[lo .. k + 1]);
    std.mem.sort(u32, l, {}, std.sort.asc(u32));
    return l[l.len / 2];
}
