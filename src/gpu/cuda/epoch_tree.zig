//! `cuda-epoch-tree`: an epoch's recursion forest with wide nodes (`recursion/block_tree.zig`) on
//! stwo-zig's resident CUDA circuit prover, from the epoch's block proofs (`cuda-epoch`'s files).
//!
//!   cuda-epoch-tree <dir> <from> <to> [--test-strength] [--jobs n] [--cpu-check n] [--cpu-prover]
//!
//! Writes the tree VK `<dir>/treevk.bin` (reused when there) and every proof of the forest to
//! `<dir>/tree/<k>-<x>.sbproof` (`block_tree.Dir`), skipping those already there: a stopped run resumes.
//! `chainproof prove-epoch-wide` then assembles the forest file from them (no proving left) and
//! `verify-epoch-wide` checks it.
//!
//! The proofs go level by level (`block_tree.tasks`: every leaf, then the nodes over leaves, …), so the
//! device arena of one circuit size is reused from proof to proof (one `NativeRuntime`). In a level,
//! `--jobs` host threads (default 4) each build a circuit (a leaf: the block proof verified natively
//! with capture; a node: its children read back), pad and preprocess it, hand the prove to the main
//! thread (the runtime's owner: every device call runs there), then verify the device proof natively, convert it to the verifier proof a node verifies
//! in-circuit, and check that with stwo-zig's circuit verifier. Every proof must carry its identity
//! from the tree VK (preprocessed root, which the GPU is given and still commits, and circuit hash)
//! and the native output digest.
//!
//! `--cpu-check n`: the first proof of each level and every n-th after it are also proved by the CPU
//! circuit prover and must be byte-identical. `--cpu-prover`: no GPU at all, every proof by the CPU
//! circuit prover through the same pipeline (to test it on a host without one). `--shapes-only`: print
//! the leaf and node sizes and stop.
//!
//! Stdout: one line per proof, `<k> <x> <gpu s> <total s> <bytes>`; stderr: progress and the end.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const cpu = @import("stwo_circuit_cpu_integration");
const cuda = @import("stwo_circuit_cuda_integration");
const cuda_backend = @import("stwo_cuda_backend");

const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;
const PcsConfigV2 = core.pcs.config_v2.PcsConfigV2;
const finalize = circuit.common.finalize;
const preprocessed = circuit.common.preprocessed;
const component_list = circuit.common.component_list;
const Context = circuit.builder.Context;
const ComponentSizes = finalize.ComponentSizes;
const PF = sb.block.proof_file;
const bs = sb.block.system;
const leaf = sb.recursion.leaf;
const store = sb.recursion.store;
const br = sb.recursion.block_rec;
const wk = sb.recursion.block_node_k;
const BF = sb.recursion.block_forest;
const BT = sb.recursion.block_tree;

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

fn gib(n: usize) f64 {
    return @as(f64, @floatFromInt(n)) / (1 << 30);
}

/// Host peak RSS in GiB (getrusage: KiB on Linux, bytes on macOS).
fn rssGib() f64 {
    const ru = std.posix.getrusage(std.posix.rusage.SELF);
    const raw: usize = @intCast(ru.maxrss);
    const bytes = if (@import("builtin").os.tag == .macos) raw else raw * 1024;
    return gib(bytes);
}

const Opts = struct {
    weak: bool = false,
    jobs: u32 = 4,
    cpu_check: ?u32 = null,
    cpu_prover: bool = false,
    shapes_only: bool = false,
};

/// What one proof is checked against: its identity in the tree VK and the native view of its output.
const Want = struct { id: BF.Id, key: leaf.Key, sum: br.Summary };

const CG = @import("circuit_gpu.zig");
const Gpu = CG.Gpu;
const gpuProve = CG.gpuProve;

/// The checks every proof passes, whichever prover made it: its identity (the tree VK's), the circuit
/// verifier, and the output digest of `want`'s key and summary.
fn check(gpa: std.mem.Allocator, tables: *const leaf.Tables, cp: *const leaf.CircuitProof, want: *const Want) !void {
    if (!std.mem.eql(u32, &cp.request.preprocessed_root, &want.id.root)) return error.WrongPreprocessedRoot;
    if (!std.mem.eql(u32, &cp.circuit_hash, &want.id.hash)) return error.WrongCircuitHash;
    const out = try leaf.verifyCircuit(gpa, tables, cp);
    if (!std.mem.eql(u32, &out, &leaf.pubsDigest(want.key, &want.sum))) return error.WrongDigest;
}

const Run = struct {
    gpa: std.mem.Allocator,
    dir: BT.Dir,
    airs: *const [bs.N_COMP]sb.air.ir.Air,
    bfri: FriConfigV2,
    roots: *PF.PreRoots,
    tables: *const leaf.Tables,
    shapes: *const BT.Shapes,
    vk: *const BT.Vk,
    g: *Gpu,
    opts: Opts,
    timer: std.time.Timer,

    // One level's work queue.
    level: []const BT.Task = &.{},
    next: std.atomic.Value(usize) = .init(0),
    failed: std.atomic.Value(bool) = .init(false),
    mutex: std.Thread.Mutex = .{},
    err: ?anyerror = null,
    err_task: BT.Task = .{ .k = 0, .x = 0 },
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
        const path = try r.dir.treePath(a, t.k, t.x);
        if (std.fs.cwd().access(path, .{})) |_| return else |e| if (e != error.FileNotFound) return e;
        var timer = try std.time.Timer.start();

        var want: Want = undefined;
        var target: ComponentSizes = undefined;
        var fri: FriConfigV2 = undefined;
        var kids: [1 << BT.MAX_A]br.Proved = undefined;
        var n_kids: usize = 0;
        defer for (kids[0..n_kids]) |*c| c.proof.deinit();
        var ctx = if (t.k == 0) blk: {
            const f = try r.dir.loadBlock(a, t.x);
            if (f.pubs[2].toU32() != t.x) return error.WrongHeight;
            want = .{ .id = try r.vk.leafFor(BF.sizeKey(f.log_size, f.profile)), .key = leaf.zero_key, .sum = br.leafSummary(&f.pubs) };
            target = r.shapes.leaf.target;
            fri = r.shapes.leaf.fri;
            break :blk try br.leafCircuitOfRoots(r.gpa, a, r.airs, &f, r.bfri, r.roots);
        } else blk: {
            const ar = BT.topArity(t.k);
            const kind = BT.kindOf(t.k);
            var refs: [1 << BT.MAX_A]*const br.Proved = undefined;
            const n = @as(usize, 1) << @intCast(ar);
            for (0..n) |j| {
                const cx = t.x + @as(u32, @intCast(j << @intCast(t.k - ar)));
                kids[j] = try BT.decodeProved(r.gpa, a, try store.readFile(a, try r.dir.treePath(a, t.k - ar, cx)));
                n_kids += 1;
                refs[j] = &kids[j];
            }
            const view = r.shapes.nodeView(kind);
            const e = try wk.expected(a, refs[0..n]);
            want = .{ .id = r.vk.nodeFor(kind, ar), .key = e.key, .sum = e.sum };
            target = view.target;
            fri = view.fri;
            break :blk try wk.circuitOf(r.gpa, a, r.tables, ar, &view, refs[0..n]);
        };
        defer ctx.deinit();
        try finalize.padToTargets(QM31, &ctx, target);
        if (!try ctx.isCircuitValid()) return error.CircuitUnsatisfied;

        var gpu_s: f64 = 0;
        var cp = if (r.opts.cpu_prover) blk: {
            var tm = try std.time.Timer.start();
            const c = try leaf.proveCircuit(r.gpa, a, &ctx, null, fri);
            gpu_s = secs(tm.read());
            break :blk c;
        } else try gpuProve(r.gpa, a, r.g, &ctx, fri, want.id.root, &gpu_s);
        defer cp.deinit();
        try check(r.gpa, r.tables, &cp, &want);
        if (!r.opts.cpu_prover) if (r.opts.cpu_check) |every| if (i % every == 0) {
            var cc = try leaf.proveCircuit(r.gpa, a, &ctx, null, fri);
            defer cc.deinit();
            if (!std.mem.eql(u8, cc.bytes, cp.bytes) or !std.mem.eql(u32, &cc.circuit_hash, &cp.circuit_hash)) {
                std.debug.print("CPU/GPU MISMATCH at k {d} x {d}\n", .{ t.k, t.x });
                return error.GpuCpuMismatch;
            }
            std.debug.print("  k {d} x {d}: CPU proof byte-identical\n", .{ t.k, t.x });
        };
        const p: br.Proved = .{ .proof = cp, .key = want.key, .sum = want.sum };
        try store.writeFileAtomic(path, try BT.encodeProved(a, &p));

        r.mutex.lock();
        defer r.mutex.unlock();
        r.done += 1;
        r.gpu_total += gpu_s;
        const out = std.fs.File.stdout().deprecatedWriter();
        out.print("{d} {d} {d:.3} {d:.3} {d}\n", .{ t.k, t.x, gpu_s, secs(timer.read()), cp.bytes.len }) catch {};
    }

    fn runLevel(r: *Run, level: []const BT.Task) !void {
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
            // Every device prove on this thread, which opened the runtime.
            const threads = try r.gpa.alloc(std.Thread, jobs);
            defer r.gpa.free(threads);
            r.g.workers_left = jobs;
            for (threads) |*th| th.* = try std.Thread.spawn(.{}, gpuWorker, .{r});
            r.g.serve(r.gpa);
            for (threads) |th| th.join();
        }
        if (r.err) |e| {
            std.debug.print("FAILED at k {d} x {d}: {s}\n", .{ r.err_task.k, r.err_task.x, @errorName(e) });
            return e;
        }
    }
};

pub fn main() !void {
    const gpa = std.heap.c_allocator;
    const args = try std.process.argsAlloc(gpa);
    defer std.process.argsFree(gpa, args);
    const usage = "usage: cuda-epoch-tree <dir> <from> <to> [--test-strength] [--jobs n] [--cpu-check n] [--cpu-prover] [--shapes-only]\n";
    if (args.len < 4) {
        std.debug.print("{s}", .{usage});
        return error.Usage;
    }
    const dir = args[1];
    const from = try std.fmt.parseInt(u32, args[2], 10);
    const to = try std.fmt.parseInt(u32, args[3], 10);
    if (to < from) return error.EmptyEpoch;
    var opts: Opts = .{};
    var i: usize = 4;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        if (std.mem.eql(u8, x, "--test-strength")) opts.weak = true else if (std.mem.eql(u8, x, "--shapes-only")) opts.shapes_only = true else if (std.mem.eql(u8, x, "--cpu-prover")) opts.cpu_prover = true else if (std.mem.eql(u8, x, "--jobs") and i + 1 < args.len) {
            i += 1;
            opts.jobs = try std.fmt.parseInt(u32, args[i], 10);
            if (opts.jobs == 0) return error.Usage;
        } else if (std.mem.eql(u8, x, "--cpu-check") and i + 1 < args.len) {
            i += 1;
            opts.cpu_check = try std.fmt.parseInt(u32, args[i], 10);
            if (opts.cpu_check.? == 0) return error.Usage;
        } else {
            std.debug.print("{s}", .{usage});
            return error.Usage;
        }
    }

    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    var timer = try std.time.Timer.start();
    const td: BT.Dir = .{ .dir = dir };
    try std.fs.cwd().makePath(try std.fmt.allocPrint(a, "{s}/tree", .{dir}));
    const nb = to - from + 1;
    const keys = try BT.epochKeys(a, td, from, nb);
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    const bfri = if (opts.weak) PF.testFri() else PF.productionFri();
    var roots = PF.PreRoots{ .airs = airs, .fri = bfri };
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    var shapes = try BT.Shapes.init(gpa, &tables.table, try BT.leafStart(gpa, a, airs, keys.firsts, bfri, &roots), BT.circuitFri());
    defer shapes.deinit(gpa);
    if (opts.shapes_only) {
        std.debug.print("shapes: {d} block sizes; leaves at 2^{d}, nodes at 2^{d} ({d:.1}s)\n", .{ keys.firsts.len, try BT.traceLogOf(shapes.leaf.target), try BT.traceLogOf(shapes.node.target), secs(timer.lap()) });
        for ([_]BT.Kind{ .over_leaves, .over_nodes }) |kind| for (1..BT.MAX_A + 1) |ar| {
            const view = shapes.nodeView(kind);
            var topo = try wk.topology(gpa, &tables.table, @intCast(ar), &view.shared);
            defer topo.deinit();
            std.debug.print("  node {s} 2^{d} children: {d} vars, natural trace log {d}\n", .{ @tagName(kind), ar, topo.circuit.n_vars, try BT.traceLogOf(finalize.computePaddedSizes(.fromBuilder(&topo.circuit))) });
        };
        return;
    }
    const vk = try BT.loadOrSetupVk(gpa, a, tables, airs, keys.firsts, bfri, &roots, &shapes, td);
    std.debug.print("setup: epoch {d}..{d}, {d} block sizes, leaves at 2^{d}, nodes at 2^{d} ({d:.1}s)\n", .{ from, to, keys.firsts.len, vk.leaf_log, vk.node_log, secs(timer.lap()) });

    var g = try Gpu.init(gpa, !opts.cpu_prover);
    defer g.deinit(gpa);
    std.debug.print("{s}; {d} jobs\n", .{ if (opts.cpu_prover) "CPU circuit prover (--cpu-prover)" else "GPU: CUDA runtime open", opts.jobs });

    const all = try BT.tasks(a, from, nb);
    var run: Run = .{ .gpa = gpa, .dir = td, .airs = airs, .bfri = bfri, .roots = &roots, .tables = tables, .shapes = &shapes, .vk = &vk, .g = &g, .opts = opts, .timer = try std.time.Timer.start() };
    var at: usize = 0;
    while (at < all.len) {
        var end = at;
        while (end < all.len and all[end].k == all[at].k) end += 1;
        const before = run.done;
        var lt = try std.time.Timer.start();
        try run.runLevel(all[at..end]);
        std.debug.print("level k={d}: {d} proofs ({d} new) in {d:.1}s; total {d:.0}s, GPU {d:.0}s; host peak RSS {d:.1} GiB\n", .{ all[at].k, end - at, run.done - before, secs(lt.read()), secs(run.timer.read()), run.gpu_total, rssGib() });
        at = end;
    }
    std.debug.print("TREE DONE: {d} proofs ({d} new) for blocks {d}..{d} in {d:.0}s (GPU {d:.0}s); assemble with chainproof prove-epoch-wide\n", .{ all.len, run.done, from, to, secs(timer.read()), run.gpu_total });
}
