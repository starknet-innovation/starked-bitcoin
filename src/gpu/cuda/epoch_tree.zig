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
//! with capture; a node: its children read back), pad and preprocess it, take the GPU for the prove
//! only, then verify the device proof natively, convert it to the verifier proof a node verifies
//! in-circuit, and check that with stwo-zig's circuit verifier. Every proof must carry its identity
//! from the tree VK (preprocessed root, which the GPU is given and still commits, and circuit hash)
//! and the native output digest.
//!
//! `--cpu-check n`: the first proof of each level and every n-th after it are also proved by the CPU
//! circuit prover and must be byte-identical. `--cpu-prover`: no GPU at all, every proof by the CPU
//! circuit prover through the same pipeline (to test it on a host without one).
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
};

/// The process's GPU: the AIR template (bound per circuit), the AOT catalog, one runtime whose device
/// arena is reused by consecutive proofs of one size, and the lock that makes the proves one at a time.
const Gpu = struct {
    template: cpu.air.Bundle,
    catalog: cuda.air_aot.Catalog,
    runtime: ?cuda_backend.runtime.NativeRuntime,
    mutex: std.Thread.Mutex = .{},

    fn init(gpa: std.mem.Allocator, open: bool) !Gpu {
        var template = try cpu.air.parse(gpa, leaf.bundle_bytes);
        errdefer template.deinit();
        var catalog = try cuda.air_aot.build(gpa, leaf.bundle_bytes);
        errdefer catalog.deinit();
        return .{ .template = template, .catalog = catalog, .runtime = if (open) try cuda_backend.runtime.NativeRuntime.open(&.{ 80, 90 }) else null };
    }

    fn deinit(self: *Gpu) void {
        if (self.runtime) |*r| r.close() catch |err| std.debug.print("cuda-epoch-tree: runtime close failed: {s}\n", .{@errorName(err)});
        self.catalog.deinit();
        self.template.deinit();
    }
};

/// What one proof is checked against: its identity in the tree VK and the native view of its output.
const Want = struct { id: BF.Id, key: leaf.Key, sum: br.Summary };

/// Proves the padded, satisfied `ctx` on the GPU under `fri` with the circuit's known preprocessed root
/// `id.root`; verifies the device proof natively; converts it to the verifier proof a node verifies
/// (`leaf.CircuitProof`); checks it with stwo-zig's circuit verifier and against `want`. The result's
/// bytes and request live in `a`.
fn gpuProve(gpa: std.mem.Allocator, a: std.mem.Allocator, g: *Gpu, ctx: *Context(QM31), fri: FriConfigV2, want: *const Want, gpu_s: *f64) !leaf.CircuitProof {
    var pp = try preprocessed.PreprocessedCircuit.preprocessContext(QM31, gpa, ctx);
    defer pp.deinit(gpa);
    const layout = pp.layout();
    const log_sizes = try component_list.circuitComponentLogSizes(&layout);
    var air = try cpu.air.bind(gpa, &g.template, log_sizes, &layout);
    defer air.deinit();
    const config = PcsConfigV2.fromFriAndTraceSize(fri, pp.traceLogSize());
    const input = cuda.resident_prover.Input{
        .values = ctx.values(),
        .preprocessed = &pp,
        .air = &air,
        .catalog = &g.catalog,
        .config = config,
        .profile = .internal,
        .expected_preprocessed_root = want.id.root,
        .runtime = if (g.runtime) |*r| r else null,
    };
    var result = blk: {
        g.mutex.lock();
        defer g.mutex.unlock();
        var timer = try std.time.Timer.start();
        const r = try cuda.resident_prover.prove(gpa, input);
        gpu_s.* = secs(timer.read());
        break :blk r;
    };
    defer result.deinit();
    if (!result.verdict.isResident() or result.verdict.counters.cpu_fallback_attempts != 0) return error.NonresidentCircuitProof;
    var verified = try cuda.resident_verifier.verify(gpa, input, &result);
    defer verified.deinit();

    const dec = result.terminal_proof.decoded;
    const claim_words = dec.words[dec.layout.interaction_claim.start..dec.layout.interaction_claim.end];
    if (claim_words.len != component_list.N_COMPONENTS * 4) return error.InvalidCircuitResidentClaim;
    var claims: [component_list.N_COMPONENTS]QM31 = undefined;
    for (&claims, 0..) |*out, i| {
        const w = claim_words[i * 4 ..][0..4];
        out.* = QM31.fromU32Unchecked(w[0], w[1], w[2], w[3]);
    }
    var prepared = try cpu.verifier_proof.fromVerifiedCapture(gpa, &result.stark, &verified.capture, try cpu.verifier_proof.proofConfig(pp.columns.len, config), &claims, dec.interactionNonce(), 0);
    errdefer prepared.deinit();
    const pp_root = result.stark.commitment_scheme_proof.commitments.items[0];
    const circuit_hash = try circuit.common.circuit_hash.hostCircuitHash(log_sizes, fri.log_blowup_factor, pp_root);
    const output_start = circuit.witness.trace.U_VAR_IDX + 1;
    if (pp.n_outputs != 8 or output_start + 8 > ctx.values().len) return error.InvalidCircuitResidentOutput;
    var digest: [8]u32 = undefined;
    for (&digest, ctx.values()[output_start..][0..8]) |*w, value| {
        const limbs = circuit.builder.ivalue.limbs(value);
        if (limbs[2] != 0 or limbs[3] != 0 or limbs[0] > 0xffff or limbs[1] > 0xffff) return error.InvalidCircuitResidentOutput;
        w.* = limbs[0] | (limbs[1] << 16);
    }
    const cp: leaf.CircuitProof = .{
        .bytes = try prepared.serialize(a),
        .prepared = prepared,
        .circuit_hash = core.vcs.blake2_hash.digestToU32s(circuit_hash),
        .request = .{
            .pcs_config = config,
            .preprocessed_column_log_sizes = try leaf.requestColumns(a, &pp),
            .preprocessed_root = core.vcs.blake2_hash.digestToU32s(pp_root),
            .output_digest = digest,
        },
    };
    return cp;
}

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
        } else try gpuProve(r.gpa, a, r.g, &ctx, fri, &want, &gpu_s);
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
        const threads = try r.gpa.alloc(std.Thread, jobs -| 1);
        defer r.gpa.free(threads);
        for (threads) |*th| th.* = try std.Thread.spawn(.{}, worker, .{r});
        r.worker();
        for (threads) |th| th.join();
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
    const usage = "usage: cuda-epoch-tree <dir> <from> <to> [--test-strength] [--jobs n] [--cpu-check n] [--cpu-prover]\n";
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
        if (std.mem.eql(u8, x, "--test-strength")) opts.weak = true else if (std.mem.eql(u8, x, "--cpu-prover")) opts.cpu_prover = true else if (std.mem.eql(u8, x, "--jobs") and i + 1 < args.len) {
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
    const vk = try BT.loadOrSetupVk(gpa, a, tables, airs, keys.firsts, bfri, &roots, &shapes, td);
    std.debug.print("setup: epoch {d}..{d}, {d} block sizes, leaves at 2^{d}, nodes at 2^{d} ({d:.1}s)\n", .{ from, to, keys.firsts.len, vk.leaf_log, vk.node_log, secs(timer.lap()) });

    var g = try Gpu.init(gpa, !opts.cpu_prover);
    defer g.deinit();
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
