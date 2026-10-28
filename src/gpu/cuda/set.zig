//! `cuda-set`: the segment proofs of a coin-set pass (`chainproof prove-set`'s first half) on the
//! resident CUDA prover, in one process and one CUDA session (docs/design/gpu-cuda.md § Set pass).
//!
//!   cuda-set <set.bin> <work-dir> --challenge <ch.bin> [--test-strength] [--logs l0,...,l11]
//!            [--jobs n] [--only <list>] [--first n] [--cpu-check n] [--verify] [--mock] [--host-only]
//!
//! Writes `<work-dir>/challenge.bin` (the challenge used; a rerun must use the same) and
//! `<work-dir>/seg/<i>.sbseg` exactly as `set_tree.provePass` does (same cut, same witnesses, the
//! device proof byte-identical to the CPU's), skipping segments whose file exists. `cuda-set-tree` (or
//! `chainproof prove-set`, which reuses the files) then proves the tree. The challenge file comes from
//! `chainproof set-challenge <epoch> <ch.bin>`; `--testing-challenge` uses `epoch.challenge(7…)` (tests).
//!
//! The segments' incoming states are chained first, without witnesses (`set_seg.advance`); each
//! witness's outgoing state must equal the next incoming one. Then `--jobs` workers (default 2) build
//! witnesses, plans and host trees (`prover.Input.witness = null`: every column built on the host)
//! while the main thread, which owns the runtime, proves on the device.
//!
//! `--cpu-check n`: the first segment proved and every n-th after it are also proved on the CPU
//! (`set_tree.proveSeg`) and the files must be byte-identical. `--verify`: every proof is verified on
//! the host (`set_tree.verifySeg`). `--mock`: CPU proofs through the same pipeline (any host).
//! `--only <list>` proves only the listed segment indices, `--first n` only segments 0..n−1.
//! `--host-only`: witnesses, plans and host trees only (no runtime, no files): host time and memory.
//!
//! Stdout-like lines on stderr: `<i> witness_s plans_s device_s total_s bytes`, a summary at the end.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const res = @import("cuda_resident");
const prover = res.prover;
const system = sb.air.system;
const rec = sb.air.prove_rec;
const SS = sb.block.set_seg;
const ST = sb.recursion.set_tree;
const PF = sb.block.proof_file;
const S = sb.recursion.store;
const M31 = core.fields.m31.M31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;

/// `chainproof` `default_set_logs`.
const default_logs: ST.Logs = .{ 23, 8, 6, 16, 22, 21, 23, 23, 23, 22, 23, 23 };

fn usage() noreturn {
    std.debug.print("usage: cuda-set <set.bin> <work-dir> (--challenge <ch.bin> | --testing-challenge) [--test-strength] [--logs l0,...,l11] [--jobs n] [--only <list>] [--first n] [--cpu-check n] [--verify] [--mock] [--host-only]\n", .{});
    std.process.exit(2);
}

fn gibOf(n: usize) f64 {
    return @as(f64, @floatFromInt(n)) / (1 << 30);
}

/// Host peak RSS in GiB (getrusage: KiB on Linux, bytes on macOS).
fn rssGib() f64 {
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    const raw: usize = @intCast(ru.maxrss);
    return gibOf(if (@import("builtin").os.tag == .macos) raw else raw * 1024);
}

fn secs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e9;
}

fn readList(a: std.mem.Allocator, path: []const u8) ![]const u32 {
    var list = std.ArrayList(u32).empty;
    var it = std.mem.tokenizeAny(u8, try S.readFile(a, path), " \r\n\t,");
    while (it.next()) |tok| try list.append(a, try std.fmt.parseInt(u32, tok, 10));
    return list.items;
}

/// One segment's host work, done by a worker; owned by its arena.
const Job = struct {
    arena: std.heap.ArenaAllocator,
    b: *SS.Built = undefined,
    parts: *[SS.N_COMP]system.Part = undefined,
    mains: *[SS.N_COMP][]const []const M31 = undefined,
    prepared: ?prover.Prepared = null,
    host: ?prover.HostTrees = null,
    t_witness: u64 = 0,
    t_plans: u64 = 0,
    err: ?anyerror = null,

    fn deinit(self: *Job) void {
        const ba = self.arena.allocator();
        if (self.host) |*h| h.deinit(ba);
        if (self.prepared) |*p| p.deinit();
        var arena = self.arena;
        arena.child_allocator.destroy(self);
        arena.deinit();
    }
};

const Slot = struct {
    job: ?*Job = null,
    ready: std.Thread.ResetEvent = .{},
    free: std.Thread.ResetEvent = .{},
};

const Pipe = struct {
    gpa: std.mem.Allocator,
    file: []const u8,
    starts: []const usize,
    ends: []const usize,
    states: []const SS.State,
    ch: sb.block.coin.Challenge,
    logs: ST.Logs,
    todo: []const usize,
    slots: []Slot,
    mock: bool,
    airs: *const [SS.N_COMP]sb.air.ir.Air,
    catalog: *const res.catalog.Catalog,
    cfg: rec.Config,
    stop: std.atomic.Value(bool) = .init(false),

    fn worker(self: *Pipe, w: usize) void {
        const slot = &self.slots[w];
        var j = w;
        while (j < self.todo.len) : (j += self.slots.len) {
            slot.free.wait();
            slot.free.reset();
            if (self.stop.load(.acquire)) return;
            const job = self.gpa.create(Job) catch {
                std.debug.print("cuda-set: worker out of memory\n", .{});
                std.process.exit(1);
            };
            job.* = .{ .arena = std.heap.ArenaAllocator.init(self.gpa) };
            self.build(job, self.todo[j]) catch |e| {
                job.err = e;
            };
            slot.job = job;
            slot.ready.set();
        }
    }

    fn build(self: *Pipe, job: *Job, i: usize) !void {
        const ba = job.arena.allocator();
        var lap = try std.time.Timer.start();
        const b = try ba.create(SS.Built);
        b.* = try SS.buildAt(ba, self.ch, self.states[i], self.file[self.starts[i]..self.ends[i]], self.logs);
        if (!std.meta.eql(b.out, self.states[i + 1])) return error.StateChainMismatch;
        job.b = b;
        job.t_witness = lap.lap();
        job.parts = try ba.create([SS.N_COMP]system.Part);
        job.parts.* = ST.partsOf(self.airs, b.logs, &b.pubs);
        job.mains = try ba.create([SS.N_COMP][]const []const M31);
        for (job.mains, b.mains) |*m, x| m.* = @ptrCast(x);
        if (self.mock) return;
        const in = prover.Input{ .parts = job.parts, .mains = job.mains, .config = self.cfg, .catalog = self.catalog };
        job.prepared = try prover.Prepared.init(ba, job.parts, self.catalog, self.cfg, .device_logup);
        job.host = try prover.hostTraceTrees(ba, in);
        job.t_plans = lap.lap();
    }
};

pub fn main() !void {
    const gpa = std.heap.page_allocator;
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const args = try std.process.argsAlloc(a);
    if (args.len < 3) usage();
    var weak = false;
    var verify = false;
    var mock = false;
    var host_only = false;
    var logs = default_logs;
    var jobs: usize = 2;
    var only: ?[]const u32 = null;
    var first: ?usize = null;
    var cpu_check: ?usize = null;
    var ch_path: ?[]const u8 = null;
    var testing_ch = false;
    var i: usize = 3;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        const has = i + 1 < args.len;
        if (std.mem.eql(u8, x, "--test-strength")) weak = true else if (std.mem.eql(u8, x, "--verify")) verify = true else if (std.mem.eql(u8, x, "--mock")) mock = true else if (std.mem.eql(u8, x, "--testing-challenge")) testing_ch = true else if (std.mem.eql(u8, x, "--host-only")) host_only = true else if (std.mem.eql(u8, x, "--challenge") and has) {
            i += 1;
            ch_path = args[i];
        } else if (std.mem.eql(u8, x, "--logs") and has) {
            i += 1;
            var it = std.mem.splitScalar(u8, args[i], ',');
            for (&logs) |*l| l.* = try std.fmt.parseInt(u32, it.next() orelse usage(), 10);
            if (it.next() != null) usage();
        } else if (std.mem.eql(u8, x, "--jobs") and has) {
            i += 1;
            jobs = try std.fmt.parseInt(usize, args[i], 10);
            if (jobs == 0) usage();
        } else if (std.mem.eql(u8, x, "--only") and has) {
            i += 1;
            only = try readList(a, args[i]);
        } else if (std.mem.eql(u8, x, "--first") and has) {
            i += 1;
            first = try std.fmt.parseInt(usize, args[i], 10);
        } else if (std.mem.eql(u8, x, "--cpu-check") and has) {
            i += 1;
            cpu_check = try std.fmt.parseInt(usize, args[i], 10);
            if (cpu_check.? == 0) usage();
        } else usage();
    }
    if ((ch_path == null) == !testing_ch) usage();
    const ch = if (ch_path) |p| try ST.decodeChallenge(try S.readFile(a, p)) else sb.block.epoch.challenge(@splat(7));
    const dir = args[2];
    const sfri: FriConfigV2 = if (weak) PF.testFri() else PF.productionFri();
    var timer = try std.time.Timer.start();

    const file = try S.readFile(a, args[1]);
    if (file.len < 4) return error.Truncated;
    const ends = try SS.cut(a, file, logs);
    const starts = try a.alloc(usize, ends.len);
    for (starts, 0..) |*s, k| s.* = if (k == 0) 4 else ends[k - 1];
    // The incoming states, without witnesses.
    const states = try a.alloc(SS.State, ends.len + 1);
    states[0] = SS.begin(file[0..4].*);
    for (0..ends.len) |k| states[k + 1] = try SS.advance(gpa, ch, states[k], file[starts[k]..ends[k]]);
    if (states[ends.len].i != std.mem.readInt(u32, file[0..4], .little)) return error.CountMismatch;
    std.debug.print("{s}: {d} bytes, {d} coins, {d} segments at logs {any}; states chained ({d:.1} s); {s}, {s}\n", .{ args[1], file.len, states[ends.len].i, ends.len, logs, secs(timer.lap()), if (weak) "test strength" else "production", if (mock) "--mock (CPU proofs)" else "device proofs, one CUDA session" });

    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    var catalog = try res.catalog.Catalog.init(a, airs);
    defer catalog.deinit();
    const cfg = rec.Config.fromFriAndTraceSize(sfri, ST.maxLog(logs));
    try std.fs.cwd().makePath(try std.fmt.allocPrint(a, "{s}/seg", .{dir}));
    // The challenge the segments are proved under, beside them (`cuda-set-tree` verifies the pass with it).
    {
        const path = try std.fmt.allocPrint(a, "{s}/challenge.bin", .{dir});
        const enc = try ST.encodeChallenge(a, ch);
        if (S.readFile(a, path)) |old| {
            if (!std.mem.eql(u8, old, enc)) return error.ChallengeChanged;
        } else |e| if (e == error.FileNotFound) try S.writeFileAtomic(path, enc) else return e;
    }

    var todo = std.ArrayList(usize).empty;
    var skipped: usize = 0;
    for (0..ends.len) |k| {
        if (only) |l| if (std.mem.indexOfScalar(u32, l, @intCast(k)) == null) continue;
        if (first) |n| if (k >= n) continue;
        if (std.fs.cwd().access(try ST.segPath(a, dir, k), .{})) |_| {
            skipped += 1;
            continue;
        } else |err| if (err != error.FileNotFound) return err;
        try todo.append(a, k);
    }

    var runtime: ?cuda.runtime.NativeRuntime = if (mock or host_only or todo.items.len == 0) null else try cuda.runtime.NativeRuntime.open(&prover.accepted_sms);
    defer if (runtime) |*r| r.close() catch |err| std.debug.print("cuda-set: runtime close failed: {s}\n", .{@errorName(err)});
    if (runtime != null) std.debug.print("CUDA runtime open ({d:.2} s)\n", .{secs(timer.lap())});
    var twiddles: ?prover.Twiddles = null;
    defer if (twiddles) |*t| t.deinit();

    const n_jobs: usize = @max(1, @min(jobs, todo.items.len));
    var pipe: Pipe = .{ .gpa = gpa, .file = file, .starts = starts, .ends = ends, .states = states, .ch = ch, .logs = logs, .todo = todo.items, .slots = try a.alloc(Slot, n_jobs), .mock = mock, .airs = airs, .catalog = &catalog, .cfg = cfg };
    for (pipe.slots) |*sl| sl.* = .{};
    for (pipe.slots) |*sl| sl.free.set();
    const threads = try a.alloc(std.Thread, n_jobs);
    for (threads, 0..) |*th, w| th.* = try std.Thread.spawn(.{}, Pipe.worker, .{ &pipe, w });
    defer {
        pipe.stop.store(true, .release);
        for (pipe.slots) |*sl| sl.free.set();
        for (threads) |th| th.join();
    }
    var run = try std.time.Timer.start();
    var device_total: f64 = 0;
    var bytes_total: usize = 0;
    var checked: usize = 0;
    std.debug.print("segment witness_s plans_s device_s total_s bytes\n", .{});
    for (todo.items, 0..) |k, jj| {
        const slot = &pipe.slots[jj % n_jobs];
        slot.ready.wait();
        slot.ready.reset();
        const job = slot.job.?;
        slot.job = null;
        defer {
            job.deinit();
            slot.free.set();
        }
        if (job.err) |e| {
            std.debug.print("cuda-set: segment {d}: {s}\n", .{ k, @errorName(e) });
            return e;
        }
        if (host_only) {
            std.debug.print("{d} {d:.3} {d:.3} host only: arena {d:.1} GiB, host trees {d:.1} GiB, peak RSS {d:.1} GiB\n", .{ k, secs(job.t_witness), secs(job.t_plans), gibOf(try job.prepared.?.memory.bytes()), gibOf(job.host.?.bytes(0) + job.host.?.bytes(1)), rssGib() });
            continue;
        }
        const ba = job.arena.allocator();
        const b = job.b;
        var lap = try std.time.Timer.start();
        var t_device: u64 = 0;
        const seg: ST.SegFile = if (mock) blk: {
            const f = try ST.proveSeg(ba, airs, b, sfri);
            t_device = lap.lap();
            break :blk f;
        } else blk: {
            const in = prover.Input{ .parts = job.parts, .mains = job.mains, .config = cfg, .catalog = &catalog, .runtime = &runtime.? };
            if (twiddles == null) twiddles = try prover.Twiddles.init(gpa, job.prepared.?.plans.twiddle_words);
            const result = prover.proofPass(ba, &job.prepared.?, &job.host.?, &twiddles.?, in, null) catch |err| {
                if (err == error.InsufficientDeviceMemory) std.debug.print("cuda-set: the segment arena ({d:.1} GiB) does not fit this device; use smaller --logs (docs/design/gpu-cuda.md § Set pass)\n", .{@as(f64, @floatFromInt(try job.prepared.?.memory.bytes())) / (1 << 30)});
                return err;
            };
            t_device = lap.lap();
            break :blk .{ .logs = b.logs, .pubs = b.pubs, .proof = result.proof };
        };
        const bytes = try ST.encodeSeg(ba, &seg);
        if (verify) {
            var g = try ST.decodeSeg(ba, bytes);
            try ST.verifySeg(ba, airs, &g, sfri);
        }
        if (!mock) if (cpu_check) |every| if (jj % every == 0) {
            // After the device proof: the CPU prover may discard the witness columns.
            const cpu_seg = try ST.proveSeg(ba, airs, b, sfri);
            const want = try ST.encodeSeg(ba, &cpu_seg);
            if (!std.mem.eql(u8, want, bytes)) {
                std.debug.print("CPU/GPU MISMATCH at segment {d}: CPU {d} bytes, device {d} bytes; device file kept at {s}.gpu\n", .{ k, want.len, bytes.len, try ST.segPath(ba, dir, k) });
                try S.writeFileAtomic(try std.fmt.allocPrint(ba, "{s}.gpu", .{try ST.segPath(ba, dir, k)}), bytes);
                return error.GpuCpuMismatch;
            }
            var sha: [32]u8 = undefined;
            std.crypto.hash.sha2.Sha256.hash(bytes, &sha, .{});
            std.debug.print("  segment {d}: CPU proof byte-identical ({d} bytes, sha256 {x})\n", .{ k, bytes.len, sha[0..8] });
            checked += 1;
        };
        try S.writeFileAtomic(try ST.segPath(ba, dir, k), bytes);
        const t_total = job.t_witness + job.t_plans + t_device + lap.lap();
        device_total += secs(t_device);
        bytes_total += bytes.len;
        std.debug.print("{d} {d:.3} {d:.3} {d:.3} {d:.3} {d}{s}\n", .{ k, secs(job.t_witness), secs(job.t_plans), secs(t_device), secs(t_total), bytes.len, if (verify) " verified" else "" });
    }
    const elapsed = secs(run.read());
    const n = todo.items.len;
    std.debug.print("SEGMENTS DONE: {d} proved ({d:.1} MB), {d} already there, {d} CPU-checked; {d:.1} s, {d:.3} s/segment (device {d:.3} s)\n", .{ n, @as(f64, @floatFromInt(bytes_total)) / 1e6, skipped, checked, elapsed, elapsed / @as(f64, @floatFromInt(@max(n, 1))), device_total / @as(f64, @floatFromInt(@max(n, 1))) });
}
