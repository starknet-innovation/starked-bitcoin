//! `cuda-epoch`: an epoch's block proofs on the resident CUDA prover, in one process and one CUDA
//! session. The GPU twin of `chainproof prove-epoch` (src/block/epoch_run.zig): the same inputs,
//! the same challenge, the same `<dir>/proofs/<h>.sbblock` and `<dir>/set-<to>.bin` (the device
//! proof is byte-identical to the CPU's), checked by `chainproof verify-epoch`.
//!
//!   zig-out/bin/cuda-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>]
//!                          [--test-strength] [--uniform | --tiered] [--verify] [--mock]
//!                          [--only <list>] [--skip <list>] [--resume] [--jobs <n>]
//!   zig-out/bin/cuda-epoch <headers.bin> <dir> - <file.sbchain> --heights <list> [options]
//!
//! `--heights`: a standalone run over the heights listed in a file (one per line), each block under
//! the testing challenge and without a coin set: proofs not bound to an epoch, for measurements
//! over chosen blocks (e.g. a sample per size class).
//!
//! An epoch's proofs can come from several runs (each loads the whole epoch: the challenge binds every
//! block): `--only` proves just the listed heights (e.g. the blocks too large for an 80 GB device, on an
//! H200), `--skip` all but them, `--resume` skips heights whose proof file exists. A block the device
//! cannot hold (`InsufficientDeviceMemory`, checked before any allocation) is deferred, not fatal: the
//! run goes on and lists the deferred heights in `<dir>/deferred-<to>.txt`, for an `--only` run.
//!
//! Per process: the AIRs, the AOT catalog, a `NativeRuntime` (CUDA context and AOT loader, kept
//! open: no per-block context creation or module load) and the twiddles of each size. Per block:
//! the lean witness (the device generates `block_sha`, `block_b2s`, `block_msg`, `block_walk`,
//! `block_bytes` and tree 0), plans, the device proof, the file. The witness and plans of the next
//! blocks are built on `--jobs` worker threads (default 3) while the device proves, so the GPU waits
//! on the host only when a block's host work outlasts the device work of the blocks before it; the
//! device proofs stay on the main thread, which owns the runtime (CUDA contexts are per thread). `--verify` checks each proof on
//! the host (`system.verifyExt`, slow); `--mock` proves on the CPU instead (any host: the plumbing).
//! One line per block (`height L profile witness plans device total bytes`), a summary at the end.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const res = @import("cuda_resident");
const prover = res.prover;
const system = sb.air.system;
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const PF = sb.block.proof_file;
const ER = sb.block.epoch_run;
const S = sb.recursion.store;
const M31 = core.fields.m31.M31;

fn usage() noreturn {
    std.debug.print("usage: cuda-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength] [--uniform | --tiered] [--verify] [--mock] [--only <list>] [--skip <list>] [--resume] [--jobs <n>]\n       cuda-epoch <headers.bin> <dir> - <file.sbchain> --heights <list> [options]\n", .{});
    std.process.exit(2);
}

fn secs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e9;
}

/// Heights listed in a file (one per line, or separated by spaces or commas).
fn readHeights(a: std.mem.Allocator, path: []const u8) ![]const u32 {
    var list = std.ArrayList(u32).empty;
    var it = std.mem.tokenizeAny(u8, try S.readFile(a, path), " \r\n\t,");
    while (it.next()) |tok| try list.append(a, try std.fmt.parseInt(u32, tok, 10));
    return list.items;
}

/// Device seconds per (L, profile) class, for the summary.
const Class = struct { n: usize = 0, total: f64 = 0, device: f64 = 0 };

/// One block's host work, done by a worker: the witness and (on the device path) the plans and host
/// trees. Owned by its arena; the main thread proves it and frees it.
const Job = struct {
    arena: std.heap.ArenaAllocator,
    b: *bs.Built = undefined,
    parts: *[bs.N_COMP]system.Part = undefined,
    mains: *[bs.N_COMP][]const []const M31 = undefined,
    cfg: rec.Config = undefined,
    inputs: ?*res.witness.Inputs = null,
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

/// A worker's hand-off slot: `ready` when its job is built, `free` when the main thread is done with it.
const Slot = struct {
    job: ?*Job = null,
    ready: std.Thread.ResetEvent = .{},
    free: std.Thread.ResetEvent = .{},
};

/// The host side of the run: worker `w` builds the jobs `todo[w], todo[w + jobs], …`, one at a time in
/// its slot, so at most `jobs` blocks are built ahead of the device. Nothing here touches the runtime.
const Pipe = struct {
    gpa: std.mem.Allocator,
    ep: *const ER.Epoch,
    todo: []const usize,
    slots: []Slot,
    size: ER.Size,
    mock: bool,
    airs: *const [bs.N_COMP]sb.air.ir.Air,
    catalog: *const res.catalog.Catalog,
    fri: core.pcs.config_v2.FriConfigV2,
    stop: std.atomic.Value(bool) = .init(false),

    fn worker(self: *Pipe, w: usize) void {
        const slot = &self.slots[w];
        var j = w;
        while (j < self.todo.len) : (j += self.slots.len) {
            slot.free.wait();
            slot.free.reset();
            if (self.stop.load(.acquire)) return;
            const job = self.gpa.create(Job) catch |e| {
                std.debug.print("cuda-epoch: worker out of memory: {s}\n", .{@errorName(e)});
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

    fn build(self: *Pipe, job: *Job, k: usize) !void {
        const ba = job.arena.allocator();
        var lap = try std.time.Timer.start();
        const b = try ba.create(bs.Built);
        b.* = try self.ep.build(ba, k, self.size, !self.mock);
        job.b = b;
        job.t_witness = lap.lap();
        job.parts = try ba.create([bs.N_COMP]system.Part);
        job.parts.* = bs.parts(self.airs, b);
        job.mains = try ba.create([bs.N_COMP][]const []const M31);
        for (job.mains, b.mains) |*m, x| m.* = @ptrCast(x);
        job.cfg = rec.Config.fromFriAndTraceSize(self.fri, b.log_size);
        if (self.mock) return;
        const inputs = try ba.create(res.witness.Inputs);
        inputs.* = try res.witness.Inputs.ofBlock(ba, b);
        inputs.fixed_capacity = true; // one memory plan per size class: one prepared arena each
        job.inputs = inputs;
        // No runtime here: the host trees need only the plans; the device work runs on the main thread.
        const in = prover.Input{ .parts = job.parts, .mains = job.mains, .config = job.cfg, .catalog = self.catalog, .witness = inputs, .runtime = null };
        job.prepared = try prover.Prepared.initWitness(ba, job.parts, self.catalog, job.cfg, .device_logup, inputs);
        job.host = try prover.hostTraceTreesFor(ba, in, job.prepared.?.witness);
        job.t_plans = lap.lap();
    }
};

pub fn main() !void {
    const gpa = std.heap.page_allocator;
    var arena_state = std.heap.ArenaAllocator.init(gpa);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const args = try std.process.argsAlloc(a);
    if (args.len < 5) usage();
    var from = ER.From{};
    var size: ER.Size = .auto;
    var weak = false;
    var verify = false;
    var mock = false;
    var heights_path: ?[]const u8 = null;
    var only: ?[]const u32 = null;
    var skip: []const u32 = &.{};
    var resume_run = false;
    var jobs: usize = 3;
    var i: usize = 5;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        if (std.mem.eql(u8, x, "--test-strength")) weak = true else if (std.mem.eql(u8, x, "--tiered")) size = .tiered else if (std.mem.eql(u8, x, "--uniform")) size = .uniform else if (std.mem.eql(u8, x, "--verify")) verify = true else if (std.mem.eql(u8, x, "--mock")) mock = true else if (std.mem.eql(u8, x, "--from") and i + 2 < args.len) {
            from = .{ .height = try std.fmt.parseInt(u32, args[i + 1], 10), .prev_set = args[i + 2] };
            i += 2;
        } else if (std.mem.eql(u8, x, "--only") and i + 1 < args.len) {
            only = try readHeights(a, args[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, x, "--skip") and i + 1 < args.len) {
            skip = try readHeights(a, args[i + 1]);
            i += 1;
        } else if (std.mem.eql(u8, x, "--jobs") and i + 1 < args.len) {
            jobs = try std.fmt.parseInt(usize, args[i + 1], 10);
            if (jobs == 0) usage();
            i += 1;
        } else if (std.mem.eql(u8, x, "--resume")) resume_run = true else if (std.mem.eql(u8, x, "--heights") and i + 1 < args.len) {
            heights_path = args[i + 1];
            i += 1;
        } else usage();
    }
    const dir = args[2];
    var timer = try std.time.Timer.start();

    var chain = try S.Chain.decode(gpa, a, try S.readFile(a, args[4]));
    const n: u32 = @intCast(chain.headers());
    chain.deinit();
    const raw_headers = try S.readFile(a, args[1]);
    if (raw_headers.len % 80 != 0) return error.BadHeaderFile;
    const all = std.mem.bytesAsSlice([80]u8, raw_headers);
    const ep = if (heights_path) |path|
        try ER.loadHeights(a, @alignCast(all), n, dir, try readHeights(a, path))
    else try ER.load(a, @alignCast(all), n, dir, from, try std.fmt.parseInt(u32, args[3], 10));
    const fri = if (weak) PF.testFri() else PF.productionFri();
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    var catalog = try res.catalog.Catalog.init(a, airs);
    defer catalog.deinit();
    std.fs.cwd().makePath(try std.fmt.allocPrint(a, "{s}/proofs", .{dir})) catch {};
    std.debug.print("{s} {d}..{d}: {d} blocks loaded ({d:.1} s); {s}, {s}\n", .{ if (ep.standalone) "standalone (testing challenge)" else "epoch", ep.from, ep.to, ep.count(), secs(timer.lap()), if (weak) "test strength" else "production", if (mock) "--mock (CPU proofs)" else "device proofs, one CUDA session" });

    var runtime: ?cuda.runtime.NativeRuntime = if (mock) null else try cuda.runtime.NativeRuntime.open(&prover.accepted_sms);
    defer if (runtime) |*r| r.close() catch |err| std.debug.print("cuda-epoch: runtime close failed: {s}\n", .{@errorName(err)});
    if (!mock) std.debug.print("CUDA runtime open ({d:.2} s)\n", .{secs(timer.lap())});

    var twiddles = std.AutoHashMap(usize, prover.Twiddles).init(gpa);
    defer {
        var it = twiddles.valueIterator();
        while (it.next()) |t| t.deinit();
        twiddles.deinit();
    }
    var classes = std.AutoHashMap(u64, Class).init(gpa);
    defer classes.deinit();
    var run = try std.time.Timer.start();
    var proof_bytes: usize = 0;
    var proved: usize = 0;
    var passed: usize = 0;
    var deferred = std.ArrayList(u32).empty;
    std.debug.print("height L profile witness_s plans_s device_s total_s bytes\n", .{});
    // The blocks this run proves.
    var todo = std.ArrayList(usize).empty;
    for (0..ep.count()) |k| {
        const hh = ep.heights[k];
        if (only) |l| if (std.mem.indexOfScalar(u32, l, hh) == null) {
            passed += 1;
            continue;
        };
        if (std.mem.indexOfScalar(u32, skip, hh) != null) {
            passed += 1;
            continue;
        }
        if (resume_run) {
            const path = try ER.pathOf(a, dir, "proofs", hh, "sbblock");
            defer a.free(path);
            if (std.fs.cwd().access(path, .{})) |_| {
                passed += 1;
                continue;
            } else |err| if (err != error.FileNotFound) return err;
        }
        try todo.append(a, k);
    }
    // Witness and plans (host) on `jobs` worker threads, up to `jobs` blocks ahead; the device proofs
    // on this thread, which owns the runtime, in order.
    const n_jobs: usize = @max(1, @min(jobs, todo.items.len));
    var pipe: Pipe = .{ .gpa = gpa, .ep = &ep, .todo = todo.items, .slots = try a.alloc(Slot, n_jobs), .size = size, .mock = mock, .airs = airs, .catalog = &catalog, .fri = fri };
    for (pipe.slots) |*sl| sl.* = .{};
    for (pipe.slots) |*sl| sl.free.set();
    const threads = try a.alloc(std.Thread, n_jobs);
    for (threads, 0..) |*th, w| th.* = try std.Thread.spawn(.{}, Pipe.worker, .{ &pipe, w });
    defer {
        pipe.stop.store(true, .release);
        for (pipe.slots) |*sl| sl.free.set();
        for (threads) |th| th.join();
    }
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
        if (job.err) |e| return e;
        const hh = ep.heights[k];
        const ba = job.arena.allocator();
        const b = job.b;
        var lap = try std.time.Timer.start();
        var t_device: u64 = 0;
        const proof = if (mock) blk: {
            const p = try PF.prove(ba, airs, b, fri);
            t_device = lap.lap();
            break :blk p;
        } else blk: {
            const in = prover.Input{ .parts = job.parts, .mains = job.mains, .config = job.cfg, .catalog = &catalog, .witness = job.inputs, .runtime = &runtime.? };
            const words = job.prepared.?.plans.twiddle_words;
            const gop = try twiddles.getOrPut(words);
            if (!gop.found_existing) gop.value_ptr.* = prover.Twiddles.init(gpa, words) catch |err| {
                _ = twiddles.remove(words);
                return err;
            };
            const result = prover.proofPass(ba, &job.prepared.?, &job.host.?, gop.value_ptr, in, null) catch |err| {
                if (err != error.InsufficientDeviceMemory) return err;
                std.debug.print("{d} {d} {s} deferred: InsufficientDeviceMemory\n", .{ hh, b.log_size, @tagName(b.profile) });
                try deferred.append(a, hh);
                continue;
            };
            t_device = lap.lap();
            break :blk result.proof;
        };
        if (verify) try system.verifyExt(ba, job.cfg, job.parts, &.{}, proof);
        const bytes = try ep.encode(ba, k, b, proof);
        try ep.writeProof(ba, k, bytes);
        const t_total = job.t_witness + job.t_plans + t_device + lap.lap();
        proof_bytes += bytes.len;
        proved += 1;
        const key = @as(u64, b.log_size) << 1 | @intFromEnum(b.profile);
        const c = try classes.getOrPut(key);
        if (!c.found_existing) c.value_ptr.* = .{};
        c.value_ptr.n += 1;
        c.value_ptr.total += secs(t_total);
        c.value_ptr.device += secs(t_device);
        std.debug.print("{d} {d} {s} {d:.3} {d:.3} {d:.3} {d:.3} {d}{s}\n", .{ hh, b.log_size, @tagName(b.profile), secs(job.t_witness), secs(job.t_plans), secs(t_device), secs(t_total), bytes.len, if (verify) " verified" else "" });
    }
    const elapsed = secs(run.read());
    std.debug.print("{s} {d}..{d}: {d} block proofs ({d:.1} MB), coin set of {d} coins{s}; {d:.1} s, {d:.3} s/block\n", .{ if (ep.standalone) "standalone" else "epoch", ep.from, ep.to, proved, @as(f64, @floatFromInt(proof_bytes)) / 1e6, if (ep.fin) |f| f.count else 0, if (ep.standalone) " (none written)" else " written", elapsed, elapsed / @as(f64, @floatFromInt(@max(proved, 1))) });
    if (passed > 0) std.debug.print("  {d} blocks not proved in this run (--only, --skip, --resume)\n", .{passed});
    if (deferred.items.len > 0) {
        var out = std.ArrayList(u8).empty;
        for (deferred.items) |hh| try out.print(a, "{d}\n", .{hh});
        const path = try std.fmt.allocPrint(a, "{s}/deferred-{d}.txt", .{ dir, ep.to });
        try S.writeFileAtomic(path, out.items);
        std.debug.print("  {d} blocks deferred (device memory), listed in {s}\n", .{ deferred.items.len, path });
    }
    var it = classes.iterator();
    while (it.next()) |e| {
        const v = e.value_ptr.*;
        std.debug.print("  L {d} {s}: {d} blocks, mean {d:.3} s (device {d:.3} s)\n", .{ e.key_ptr.* >> 1, @tagName(@as(bs.Profile, @enumFromInt(e.key_ptr.* & 1))), v.n, v.total / @as(f64, @floatFromInt(v.n)), v.device / @as(f64, @floatFromInt(v.n)) });
    }
}
