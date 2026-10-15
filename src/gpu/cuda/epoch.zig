//! `cuda-epoch`: an epoch's block proofs on the resident CUDA prover, in one process and one CUDA
//! session. The GPU twin of `chainproof prove-epoch` (src/block/epoch_run.zig): the same inputs,
//! the same challenge, the same `<dir>/proofs/<h>.sbblock` and `<dir>/set-<to>.bin` (the device
//! proof is byte-identical to the CPU's), checked by `chainproof verify-epoch`.
//!
//!   zig-out/bin/cuda-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>]
//!                          [--test-strength] [--uniform | --tiered] [--verify] [--mock]
//!   zig-out/bin/cuda-epoch <headers.bin> <dir> - <file.sbchain> --heights <list> [options]
//!
//! `--heights`: a standalone run over the heights listed in a file (one per line), each block under
//! the testing challenge and without a coin set: proofs not bound to an epoch, for measurements
//! over chosen blocks (e.g. a sample per size class).
//!
//! Per process: the AIRs, the AOT catalog, a `NativeRuntime` (CUDA context and AOT loader, kept
//! open: no per-block context creation or module load) and the twiddles of each size. Per block:
//! the lean witness (the device generates `block_sha`, `block_b2s`, `block_msg`, `block_walk`,
//! `block_bytes` and tree 0), plans, the device proof, the file. `--verify` checks each proof on
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
    std.debug.print("usage: cuda-epoch <headers.bin> <dir> <to> <file.sbchain> [--from <a> <prev-set.bin>] [--test-strength] [--uniform | --tiered] [--verify] [--mock]\n       cuda-epoch <headers.bin> <dir> - <file.sbchain> --heights <list> [options]\n", .{});
    std.process.exit(2);
}

fn secs(ns: u64) f64 {
    return @as(f64, @floatFromInt(ns)) / 1e9;
}

/// Device seconds per (L, profile) class, for the summary.
const Class = struct { n: usize = 0, total: f64 = 0, device: f64 = 0 };

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
    var i: usize = 5;
    while (i < args.len) : (i += 1) {
        const x = args[i];
        if (std.mem.eql(u8, x, "--test-strength")) weak = true else if (std.mem.eql(u8, x, "--tiered")) size = .tiered else if (std.mem.eql(u8, x, "--uniform")) size = .uniform else if (std.mem.eql(u8, x, "--verify")) verify = true else if (std.mem.eql(u8, x, "--mock")) mock = true else if (std.mem.eql(u8, x, "--from") and i + 2 < args.len) {
            from = .{ .height = try std.fmt.parseInt(u32, args[i + 1], 10), .prev_set = args[i + 2] };
            i += 2;
        } else if (std.mem.eql(u8, x, "--heights") and i + 1 < args.len) {
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
    const ep = if (heights_path) |path| blk: {
        var list = std.ArrayList(u32).empty;
        var it = std.mem.tokenizeAny(u8, try S.readFile(a, path), " \r\n\t,");
        while (it.next()) |tok| try list.append(a, try std.fmt.parseInt(u32, tok, 10));
        break :blk try ER.loadHeights(a, @alignCast(all), n, dir, list.items);
    } else try ER.load(a, @alignCast(all), n, dir, from, try std.fmt.parseInt(u32, args[3], 10));
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
    std.debug.print("height L profile witness_s plans_s device_s total_s bytes\n", .{});
    for (0..ep.count()) |k| {
        var block_arena = std.heap.ArenaAllocator.init(gpa);
        defer block_arena.deinit();
        const ba = block_arena.allocator();
        var lap = try std.time.Timer.start();
        const b = try ba.create(bs.Built);
        b.* = try ep.build(ba, k, size, !mock);
        const t_witness = lap.lap();
        const parts = try ba.create([bs.N_COMP]system.Part);
        parts.* = bs.parts(airs, b);
        const mains = try ba.create([bs.N_COMP][]const []const M31);
        for (mains, b.mains) |*m, x| m.* = @ptrCast(x);
        const cfg = rec.Config.fromFriAndTraceSize(fri, b.log_size);
        var t_plans: u64 = 0;
        var t_device: u64 = 0;
        const proof = if (mock) blk: {
            const p = try PF.prove(ba, airs, b, fri);
            t_device = lap.lap();
            break :blk p;
        } else blk: {
            const inputs = try ba.create(res.witness.Inputs);
            inputs.* = try res.witness.Inputs.ofBlock(ba, b);
            inputs.fixed_capacity = true; // one memory plan per size class: one prepared arena each
            const in = prover.Input{ .parts = parts, .mains = mains, .config = cfg, .catalog = &catalog, .witness = inputs, .runtime = &runtime.? };
            var prepared = try prover.Prepared.initWitness(ba, parts, &catalog, cfg, .device_logup, inputs);
            defer prepared.deinit();
            var host = try prover.hostTraceTreesFor(ba, in, prepared.witness);
            defer host.deinit(ba);
            const words = prepared.plans.twiddle_words;
            const gop = try twiddles.getOrPut(words);
            if (!gop.found_existing) gop.value_ptr.* = prover.Twiddles.init(gpa, words) catch |err| {
                _ = twiddles.remove(words);
                return err;
            };
            t_plans = lap.lap();
            const result = try prover.proofPass(ba, &prepared, &host, gop.value_ptr, in, null);
            t_device = lap.lap();
            break :blk result.proof;
        };
        if (verify) try system.verifyExt(ba, cfg, parts, &.{}, proof);
        const bytes = try ep.encode(ba, k, b, proof);
        try ep.writeProof(ba, k, bytes);
        const t_total = t_witness + t_plans + t_device + lap.lap();
        proof_bytes += bytes.len;
        const key = @as(u64, b.log_size) << 1 | @intFromEnum(b.profile);
        const c = try classes.getOrPut(key);
        if (!c.found_existing) c.value_ptr.* = .{};
        c.value_ptr.n += 1;
        c.value_ptr.total += secs(t_total);
        c.value_ptr.device += secs(t_device);
        std.debug.print("{d} {d} {s} {d:.3} {d:.3} {d:.3} {d:.3} {d}{s}\n", .{ ep.heights[k], b.log_size, @tagName(b.profile), secs(t_witness), secs(t_plans), secs(t_device), secs(t_total), bytes.len, if (verify) " verified" else "" });
    }
    if (!ep.standalone) try ep.writeSet(a);
    const elapsed = secs(run.read());
    std.debug.print("{s} {d}..{d}: {d} block proofs ({d:.1} MB), coin set of {d} coins{s}; {d:.1} s, {d:.3} s/block\n", .{ if (ep.standalone) "standalone" else "epoch", ep.from, ep.to, ep.count(), @as(f64, @floatFromInt(proof_bytes)) / 1e6, ep.set.len, if (ep.standalone) " (none written)" else " written", elapsed, elapsed / @as(f64, @floatFromInt(ep.count())) });
    var it = classes.iterator();
    while (it.next()) |e| {
        const v = e.value_ptr.*;
        std.debug.print("  L {d} {s}: {d} blocks, mean {d:.3} s (device {d:.3} s)\n", .{ e.key_ptr.* >> 1, @tagName(@as(bs.Profile, @enumFromInt(e.key_ptr.* & 1))), v.n, v.total / @as(f64, @floatFromInt(v.n)), v.device / @as(f64, @floatFromInt(v.n)) });
    }
}
