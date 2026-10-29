//! `cuda-set-tree`: the set tree of a coin-set pass (`set_tree.proveTree`) on stwo-zig's resident CUDA
//! circuit prover, from the segment files `cuda-set` wrote (docs/design/gpu-cuda.md § Set pass).
//!
//!   cuda-set-tree <work-dir> [--test-strength] [--jobs n] [--cpu-check n] [--cpu-prover]
//!                 [--challenge <ch.bin>]
//!
//! Reads `<work-dir>/seg/0..k−1.sbseg`, writes `<work-dir>/setvk.bin` (from segment 0, as `provePass`),
//! one file per tree proof `<work-dir>/stree/<lo>-<n>.sbproof` (skipped when there: a stopped run
//! resumes) and `<work-dir>/pass.bin`: the same files as `chainproof prove-set`. The final state is the
//! last segment's outgoing state (`set_tree.outState`). The pass is then verified (`set_tree.verifyPass`,
//! as `chainproof verify-set` does) under `--challenge`, or `<work-dir>/challenge.bin` (`cuda-set`'s).
//!
//! Leaves and nodes share one padded shape, so the device arena is one size for the whole tree. The
//! proofs go level by level (`set_tree.tasks`: leaves, then nodes by height); in a level `--jobs` host
//! threads (default 4) build circuits and hand the proves to the main thread, which owns the runtime.
//! Every proof is checked against the VK's identity, natively verified, and its output digest compared
//! with the native summary. `--cpu-check n`: the first proof of each level and every n-th after it are
//! also proved on the CPU and must be byte-identical. `--cpu-prover`: no GPU (any host).
//!
//! Stdout: one line per proof, `<lo> <n> <h> <gpu s> <total s> <bytes>`; stderr: progress, and per proof
//! `phases` (read, circuit, pad, check, prove, verify, CPU check; seconds).

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const CG = @import("circuit_gpu.zig");

const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const finalize = circuit.common.finalize;
const PF = sb.block.proof_file;
const BF = sb.recursion.block_forest;
const SS = sb.block.set_seg;
const ST = sb.recursion.set_tree;
const leaf = sb.recursion.leaf;
const store = sb.recursion.store;
const secs = CG.secs;

const Opts = struct {
    weak: bool = false,
    jobs: u32 = 4,
    cpu_check: ?u32 = null,
    cpu_prover: bool = false,
    challenge: ?[]const u8 = null,
};

const Run = struct {
    gpa: std.mem.Allocator,
    dir: []const u8,
    airs: *const [SS.N_COMP]sb.air.ir.Air,
    sfri: FriConfigV2,
    tables: *const leaf.Tables,
    shape: *const ST.Shape,
    vk: *const ST.Vk,
    pre: ST.PreRoot, // the segments' preprocessed root (`ST.preRoot`), once for the pass
    g: *CG.Gpu,
    opts: Opts,

    level: []const ST.Task = &.{},
    next: std.atomic.Value(usize) = .init(0),
    failed: std.atomic.Value(bool) = .init(false),
    mutex: std.Thread.Mutex = .{},
    err: ?anyerror = null,
    err_task: ST.Task = .{ .lo = 0, .n = 0, .h = 0 },
    done: usize = 0,
    gpu_total: f64 = 0,

    fn worker(r: *Run) void {
        while (!r.failed.load(.acquire)) {
            const i = r.next.fetchAdd(1, .monotonic);
            if (i >= r.level.len) return;
            r.one(i) catch |e| {
                r.mutex.lock();
                defer r.mutex.unlock();
                if (r.err == null) {
                    r.err = e;
                    r.err_task = r.level[i];
                }
                r.failed.store(true, .release);
            };
        }
    }

    fn gpuWorker(r: *Run) void {
        defer r.g.leave();
        r.worker();
    }

    fn one(r: *Run, i: usize) !void {
        const t = r.level[i];
        var arena = std.heap.ArenaAllocator.init(r.gpa);
        defer arena.deinit();
        const a = arena.allocator();
        const path = try ST.proofPath(a, r.dir, t.lo, t.n);
        if (std.fs.cwd().access(path, .{})) |_| return else |e| if (e != error.FileNotFound) return e;
        var timer = try std.time.Timer.start();
        var ph: [7]f64 = @splat(0); // read+expected, circuit, pad, valid, prove, verify, cpu-check

        var kids: [2]ST.Proved = undefined;
        var n_kids: usize = 0;
        defer for (kids[0..n_kids]) |*c| c.proof.deinit();
        var seg: ST.SegFile = undefined;
        const w = if (t.n == 1) blk: {
            seg = try ST.decodeSeg(a, try store.readFile(a, try ST.segPath(a, r.dir, t.lo)));
            if (!std.meta.eql(seg.logs, r.vk.logs)) return error.SegmentLogsNotPinned;
            break :blk try ST.expectedProof(r.vk, t, &seg, null);
        } else blk: {
            for (ST.childTasks(t), &kids) |c, *k| {
                k.* = try ST.decodeProved(r.gpa, a, try store.readFile(a, try ST.proofPath(a, r.dir, c.lo, c.n)));
                n_kids += 1;
            }
            break :blk try ST.expectedProof(r.vk, t, null, .{ &kids[0], &kids[1] });
        };
        ph[0] = secs(timer.lap());
        var ctx = if (t.n == 1)
            try ST.leafCircuitOfPre(r.gpa, a, r.airs, &seg, r.sfri, r.pre)
        else
            try ST.nodeCircuitOf(r.gpa, a, r.tables, r.shape, &kids[0], &kids[1]);
        defer ctx.deinit();
        ph[1] = secs(timer.lap());
        try finalize.padToTargets(QM31, &ctx, r.shape.target);
        ph[2] = secs(timer.lap());
        if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;
        ph[3] = secs(timer.lap());

        var gpu_s: f64 = 0;
        var cp = if (r.opts.cpu_prover) blk: {
            var tm = try std.time.Timer.start();
            const c = try leaf.proveCircuit(r.gpa, a, &ctx, null, r.shape.fri);
            gpu_s = secs(tm.read());
            break :blk c;
        } else try CG.gpuProve(r.gpa, a, r.g, &ctx, r.shape.fri, w.id.root, &gpu_s);
        defer cp.deinit();
        ph[4] = secs(timer.lap());
        // The VK's identity, the circuit verifier, the native summary.
        if (!std.mem.eql(u32, &cp.request.preprocessed_root, &w.id.root)) return error.WrongPreprocessedRoot;
        if (!std.mem.eql(u32, &cp.circuit_hash, &w.id.hash)) return error.WrongCircuitHash;
        const out = try leaf.verifyCircuit(r.gpa, r.tables, &cp);
        if (!std.mem.eql(u32, &out, &leaf.pubsDigest(w.key, &w.sum))) return error.WrongDigest;
        ph[5] = secs(timer.lap());
        if (!r.opts.cpu_prover) if (r.opts.cpu_check) |every| if (i % every == 0) {
            var cc = try leaf.proveCircuit(r.gpa, a, &ctx, null, r.shape.fri);
            defer cc.deinit();
            if (!std.mem.eql(u8, cc.bytes, cp.bytes) or !std.mem.eql(u32, &cc.circuit_hash, &cp.circuit_hash)) {
                std.debug.print("CPU/GPU MISMATCH at lo {d} n {d}\n", .{ t.lo, t.n });
                return error.GpuCpuMismatch;
            }
            std.debug.print("  lo {d} n {d}: CPU proof byte-identical\n", .{ t.lo, t.n });
        };
        ph[6] = secs(timer.lap());
        std.debug.print("phases lo {d} n {d}: {any}\n", .{ t.lo, t.n, ph });
        const p: ST.Proved = .{ .proof = cp, .key = w.key, .sum = w.sum };
        try store.writeFileAtomic(path, try ST.encodeProved(a, &p));

        r.mutex.lock();
        defer r.mutex.unlock();
        r.done += 1;
        r.gpu_total += gpu_s;
        const o = std.fs.File.stdout().deprecatedWriter();
        o.print("{d} {d} {d} {d:.3} {d:.3} {d}\n", .{ t.lo, t.n, t.h, gpu_s, @reduce(.Add, @as(@Vector(7, f64), ph)) + secs(timer.read()), cp.bytes.len }) catch {};
    }

    fn runLevel(r: *Run, level: []const ST.Task) !void {
        r.level = level;
        r.next.store(0, .monotonic);
        const jobs = @min(r.opts.jobs, level.len);
        if (r.opts.cpu_prover) {
            const threads = try r.gpa.alloc(std.Thread, jobs -| 1);
            defer r.gpa.free(threads);
            for (threads) |*th| th.* = try std.Thread.spawn(.{}, worker, .{r});
            r.worker();
            for (threads) |th| th.join();
        } else {
            const threads = try r.gpa.alloc(std.Thread, jobs);
            defer r.gpa.free(threads);
            r.g.workers_left = jobs;
            for (threads) |*th| th.* = try std.Thread.spawn(.{}, gpuWorker, .{r});
            r.g.serve(r.gpa);
            for (threads) |th| th.join();
        }
        if (r.err) |e| {
            std.debug.print("FAILED at lo {d} n {d}: {s}\n", .{ r.err_task.lo, r.err_task.n, @errorName(e) });
            return e;
        }
    }
};

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    const usage = "usage: cuda-set-tree <work-dir> [--test-strength] [--jobs n] [--cpu-check n] [--cpu-prover] [--challenge <ch.bin>]\n";
    if (args.len < 2) {
        std.debug.print("{s}", .{usage});
        return error.Usage;
    }
    const dir = args[1];
    var opts: Opts = .{};
    var i: usize = 2;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        if (std.mem.eql(u8, x, "--test-strength")) opts.weak = true else if (std.mem.eql(u8, x, "--cpu-prover")) opts.cpu_prover = true else if (std.mem.eql(u8, x, "--jobs") and i + 1 < args.len) {
            i += 1;
            opts.jobs = try std.fmt.parseInt(u32, args[i], 10);
            if (opts.jobs == 0) return error.Usage;
        } else if (std.mem.eql(u8, x, "--cpu-check") and i + 1 < args.len) {
            i += 1;
            opts.cpu_check = try std.fmt.parseInt(u32, args[i], 10);
            if (opts.cpu_check.? == 0) return error.Usage;
        } else if (std.mem.eql(u8, x, "--challenge") and i + 1 < args.len) {
            i += 1;
            opts.challenge = args[i];
        } else {
            std.debug.print("{s}", .{usage});
            return error.Usage;
        }
    }

    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    var timer = try std.time.Timer.start();
    // The segments: 0..k−1, contiguous.
    var k: u32 = 0;
    while (true) : (k += 1) {
        std.fs.cwd().access(try ST.segPath(a, dir, k), .{}) catch |e| if (e == error.FileNotFound) break else return e;
    }
    if (k == 0) return error.NoSegments;
    try std.fs.cwd().makePath(try std.fmt.allocPrint(a, "{s}/stree", .{dir}));
    const airs = try a.create([SS.N_COMP]sb.air.ir.Air);
    airs.* = try SS.parseAirs(a);
    const sfri: FriConfigV2 = if (opts.weak) PF.testFri() else PF.productionFri();
    const cfri: FriConfigV2 = if (opts.weak) try FriConfigV2.init(10, 0, 1, 3, 1) else BF.circuitFri();
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const first = try ST.decodeSeg(a, try store.readFile(a, try ST.segPath(a, dir, 0)));
    var su = try ST.setup(gpa, a, tables, airs, &first, sfri, cfri);
    defer su.shape.deinit(gpa);
    const vk_path = try std.fmt.allocPrint(a, "{s}/setvk.bin", .{dir});
    const vk_bytes = try su.vk.encode(a);
    if (store.readFile(a, vk_path)) |old| {
        if (!std.mem.eql(u8, old, vk_bytes)) return error.SetVkChanged; // another strength or other logs
    } else |e| if (e == error.FileNotFound) try store.writeFileAtomic(vk_path, vk_bytes) else return e;
    const pre = try ST.preRoot(a, airs, su.vk.logs, sfri);
    std.debug.print("setup: {d} segments at logs {any}; leaves and nodes at 2^{d} ({d:.1}s)\n", .{ k, su.vk.logs, su.vk.trace_log, secs(timer.lap()) });

    var g = try CG.Gpu.init(gpa, !opts.cpu_prover);
    defer g.deinit(gpa);
    std.debug.print("{s}; {d} jobs\n", .{ if (opts.cpu_prover) "CPU circuit prover (--cpu-prover)" else "GPU: CUDA runtime open", opts.jobs });

    const all = try ST.tasks(a, k);
    var run: Run = .{ .gpa = gpa, .dir = dir, .airs = airs, .sfri = sfri, .tables = tables, .shape = &su.shape, .vk = &su.vk, .pre = pre, .g = &g, .opts = opts };
    var at: usize = 0;
    while (at < all.len) {
        var end = at;
        while (end < all.len and all[end].h == all[at].h) end += 1;
        const before = run.done;
        var lt = try std.time.Timer.start();
        try run.runLevel(all[at..end]);
        std.debug.print("level h={d}: {d} proofs ({d} new) in {d:.1}s; GPU {d:.0}s so far\n", .{ all[at].h, end - at, run.done - before, secs(lt.read()), run.gpu_total });
        at = end;
    }
    // The pass file.
    const root = try ST.decodeProved(gpa, a, try store.readFile(a, try ST.proofPath(a, dir, 0, k)));
    const last = try ST.decodeSeg(a, try store.readFile(a, try ST.segPath(a, dir, k - 1)));
    var pass = try ST.passOf(k, &last.pubs, root);
    defer pass.root.proof.deinit();
    try store.writeFileAtomic(try std.fmt.allocPrint(a, "{s}/pass.bin", .{dir}), try ST.encodePass(a, &pass));
    std.debug.print("TREE DONE: {d} proofs ({d} new) over {d} segments in {d:.0}s (GPU {d:.0}s); {s}/pass.bin written\n", .{ all.len, run.done, k, secs(timer.read()), run.gpu_total, dir });
    const ch_path = opts.challenge orelse blk: {
        const p = try std.fmt.allocPrint(a, "{s}/challenge.bin", .{dir});
        break :blk if (std.fs.cwd().access(p, .{})) |_| p else |_| null;
    };
    if (ch_path) |p| {
        const ch = try ST.decodeChallenge(try store.readFile(a, p));
        const f = try ST.verifyPass(gpa, tables, &su.vk, &pass, ch);
        std.debug.print("VERIFIED set pass {s}: {d} coins, amount {d} sat, digest {x}, hash_serialized {x}\n", .{ dir, f.count, f.amount, f.digest, f.hash });
    }
}
