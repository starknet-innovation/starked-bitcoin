//! `cuda-prove`: one block proof on the resident CUDA prover, checked against the CPU prover.
//!
//!   zig-out/bin/cuda-prove [--small i | --large height] [--profile test|production]
//!                          [--size uniform|tiered] [--min-log k]
//!                          [--skip-cpu] [--cpu-sha hexprefix] [--cpu-len bytes]
//!                          [--cpu-proof file] [--save-cpu file] [--save-device file] [--mock]
//!                          [--host-logup]
//!
//! Steps, each printed with its time:
//!  1. build the block's witness (`block.system.buildFull`);
//!  2. CPU proof (`system.proveOpts`, compact storage) unless `--skip-cpu` / `--cpu-proof`;
//!  3. host: plans, the preprocessed trees (generated) and the main ones (the witness, borrowed) in
//!     natural row order (the device reorders them), twiddles; with
//!     `--host-logup` (the first version, for A/B) also the trace roots (CPU commit of trees 0–1),
//!     (z, α) and the interaction trace;
//!  4. the device proof (one transaction; LogUp on the device unless `--host-logup`);
//!  5. a structured comparison with the CPU proof in stage order (claims, roots 0–3, sampled
//!     values, FRI roots, last layer, nonce, openings): the first difference names the stage
//!     that produced it;
//!  6. byte comparison (sha256, length; first differing offset), `system.verifyExt`.
//! `--mock` replaces the device with a second CPU proof (default storage): it exercises everything
//! but the GPU, on any host. Exit status 0 only if every check passes.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const CpuBackend = @import("stwo_cpu_backend").CpuBackend;
const res = @import("cuda_resident");
const prover = res.prover;
const system = sb.air.system;
const rec = sb.air.prove_rec;
const bs = sb.block.system;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;

const Opts = struct {
    small: usize = 0,
    large: ?u32 = null,
    production: bool = false,
    tiered: bool = false,
    min_log: u32 = 0,
    skip_cpu: bool = false,
    cpu_sha: ?[]const u8 = null,
    cpu_len: ?usize = null,
    cpu_proof: ?[]const u8 = null,
    save_cpu: ?[]const u8 = null,
    save_device: ?[]const u8 = null,
    mock: bool = false,
    host_logup: bool = false,
};

fn parse(args: []const []const u8) !Opts {
    var o = Opts{};
    var i: usize = 1;
    while (i < args.len) : (i += 1) {
        const a = args[i];
        const next = struct {
            fn f(xs: []const []const u8, j: *usize) ![]const u8 {
                j.* += 1;
                if (j.* >= xs.len) return error.MissingArgumentValue;
                return xs[j.*];
            }
        }.f;
        if (std.mem.eql(u8, a, "--small")) o.small = try std.fmt.parseInt(usize, try next(args, &i), 10) else if (std.mem.eql(u8, a, "--large")) o.large = try std.fmt.parseInt(u32, try next(args, &i), 10) else if (std.mem.eql(u8, a, "--profile")) {
            const v = try next(args, &i);
            o.production = std.mem.eql(u8, v, "production");
            if (!o.production and !std.mem.eql(u8, v, "test")) return error.BadProfile;
        } else if (std.mem.eql(u8, a, "--size")) {
            const v = try next(args, &i);
            o.tiered = std.mem.eql(u8, v, "tiered");
            if (!o.tiered and !std.mem.eql(u8, v, "uniform")) return error.BadSize;
        } else if (std.mem.eql(u8, a, "--min-log")) o.min_log = try std.fmt.parseInt(u32, try next(args, &i), 10) else if (std.mem.eql(u8, a, "--skip-cpu")) o.skip_cpu = true else if (std.mem.eql(u8, a, "--cpu-sha")) o.cpu_sha = try next(args, &i) else if (std.mem.eql(u8, a, "--cpu-len")) o.cpu_len = try std.fmt.parseInt(usize, try next(args, &i), 10) else if (std.mem.eql(u8, a, "--cpu-proof")) o.cpu_proof = try next(args, &i) else if (std.mem.eql(u8, a, "--save-cpu")) o.save_cpu = try next(args, &i) else if (std.mem.eql(u8, a, "--save-device")) o.save_device = try next(args, &i) else if (std.mem.eql(u8, a, "--mock")) o.mock = true else if (std.mem.eql(u8, a, "--host-logup")) o.host_logup = true else {
            std.debug.print("unknown argument {s}\n", .{a});
            return error.BadArgument;
        }
    }
    return o;
}

var timer: std.time.Timer = undefined;
fn lap(what: []const u8) void {
    std.debug.print("[{d:>9.3} s] {s}\n", .{ @as(f64, @floatFromInt(timer.read())) / 1e9, what });
}

fn hex(bytes: []const u8, out: []u8) []const u8 {
    const digits = "0123456789abcdef";
    for (bytes, 0..) |b, i| {
        out[2 * i] = digits[b >> 4];
        out[2 * i + 1] = digits[b & 15];
    }
    return out[0 .. 2 * bytes.len];
}

fn sha(bytes: []const u8) [32]u8 {
    var d: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(bytes, &d, .{});
    return d;
}

/// `system.proofBytes` read back: claimed sums (`n_claims` × 16 bytes), then the postcard proof.
fn loadProof(a: std.mem.Allocator, bytes: []const u8, n_claims: usize) !system.Proof {
    if (bytes.len < 16 * n_claims) return error.ShortProofFile;
    const sums = try a.alloc(QM31, n_claims);
    for (sums, 0..) |*s, i| {
        const w = bytes[16 * i ..][0..16];
        s.* = QM31.fromU32Unchecked(std.mem.readInt(u32, w[0..4], .little), std.mem.readInt(u32, w[4..8], .little), std.mem.readInt(u32, w[8..12], .little), std.mem.readInt(u32, w[12..16], .little));
    }
    var fbs = std.io.fixedBufferStream(bytes[16 * n_claims ..]);
    const stark = try @import("stwo_postcard").deserializeProof(rec.Hasher, a, fbs.reader());
    return .{ .stark = stark, .claimed_sums = sums };
}

/// First difference between two proofs, in the order the device produces them.
fn diffProofs(cpu: *const system.Proof, dev: *const system.Proof) bool {
    const c = &cpu.stark.commitment_scheme_proof;
    const d = &dev.stark.commitment_scheme_proof;
    const hint = [_][]const u8{ "preprocessed commit (ingress upload / LDE / Merkle)", "main commit", "interaction commit (device LogUp: fraction kernels, completion, sources gather; host LogUp: upload, or (z, α) drawn differently)", "composition (constraint kernels, ext params, lift/split)" };
    if (cpu.claimed_sums.len != dev.claimed_sums.len) {
        std.debug.print("DIFF claimed sums: count {d} vs {d}\n", .{ cpu.claimed_sums.len, dev.claimed_sums.len });
        return true;
    }
    for (cpu.claimed_sums, dev.claimed_sums, 0..) |x, y, i| if (!x.eql(y)) {
        std.debug.print("DIFF claimed sum {d} (LogUp: fractions or completion; (z, α) if every claim differs)\n", .{i});
        return true;
    };
    for (c.commitments.items, d.commitments.items, 0..) |x, y, t| if (!std.mem.eql(u8, std.mem.asBytes(&x), std.mem.asBytes(&y))) {
        std.debug.print("DIFF root of tree {d}: {s}\n", .{ t, hint[@min(t, 3)] });
        return true;
    };
    for (c.sampled_values.items, d.sampled_values.items, 0..) |tc, td, t| {
        if (tc.len != td.len) {
            std.debug.print("DIFF sampled values tree {d}: {d} vs {d} columns (OODS plan)\n", .{ t, tc.len, td.len });
            return true;
        }
        for (tc, td, 0..) |cc, cd, col| {
            if (cc.len != cd.len) {
                std.debug.print("DIFF sampled values tree {d} column {d}: {d} vs {d} samples (mask)\n", .{ t, col, cc.len, cd.len });
                return true;
            }
            for (cc, cd, 0..) |x, y, k| if (!x.eql(y)) {
                std.debug.print("DIFF sampled value tree {d} column {d} sample {d} (OODS evaluation; OODS point if every value differs)\n", .{ t, col, k });
                return true;
            };
        }
    }
    const fc = &c.fri_proof;
    const fd = &d.fri_proof;
    if (!std.mem.eql(u8, std.mem.asBytes(&fc.first_layer.commitment), std.mem.asBytes(&fd.first_layer.commitment))) {
        std.debug.print("DIFF FRI first-layer root (DEEP quotient)\n", .{});
        return true;
    }
    if (fc.inner_layers.len != fd.inner_layers.len) {
        std.debug.print("DIFF FRI layer count {d} vs {d}\n", .{ fc.inner_layers.len, fd.inner_layers.len });
        return true;
    }
    for (fc.inner_layers, fd.inner_layers, 0..) |x, y, i| if (!std.mem.eql(u8, std.mem.asBytes(&x.commitment), std.mem.asBytes(&y.commitment))) {
        std.debug.print("DIFF FRI inner root {d} (fold)\n", .{i});
        return true;
    };
    for (fc.last_layer_poly.coeffs, fd.last_layer_poly.coeffs, 0..) |x, y, i| if (!x.eql(y)) {
        std.debug.print("DIFF FRI last layer coefficient {d}\n", .{i});
        return true;
    };
    if (c.proof_of_work != d.proof_of_work) {
        std.debug.print("DIFF query PoW nonce {d} vs {d}\n", .{ c.proof_of_work, d.proof_of_work });
        return true;
    }
    for (c.queried_values.items, d.queried_values.items, 0..) |tc, td, t| for (tc, td, 0..) |cc, cd, col| {
        if (cc.len != cd.len or !std.mem.eql(u8, std.mem.sliceAsBytes(cc), std.mem.sliceAsBytes(cd))) {
            std.debug.print("DIFF queried values tree {d} column {d} (decommit)\n", .{ t, col });
            return true;
        }
    };
    for (fc.first_layer.fri_witness, fd.first_layer.fri_witness, 0..) |x, y, i| if (!x.eql(y)) {
        std.debug.print("DIFF FRI first-layer witness {d} (decommit)\n", .{i});
        return true;
    };
    return false;
}

fn firstDiff(x: []const u8, y: []const u8) ?usize {
    for (x[0..@min(x.len, y.len)], y[0..@min(x.len, y.len)], 0..) |p, q, i| if (p != q) return i;
    return if (x.len == y.len) null else @min(x.len, y.len);
}

pub fn main() !void {
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena_state.deinit();
    const a = arena_state.allocator();
    const opts = try parse(try std.process.argsAlloc(a));
    timer = try std.time.Timer.start();

    // ---- block and witness
    const sample = if (opts.large) |h| blk: {
        for (sb.block.checks.samples_large) |s| if (s.ctx.height == h) break :blk s;
        return error.NoSuchLargeSample;
    } else sb.block.checks.samples_small[opts.small];
    const airs = try a.create([bs.N_COMP]sb.air.ir.Air);
    airs.* = try bs.parseAirs(a);
    const built = try a.create(bs.Built);
    built.* = try bs.buildFull(a, sample.raw, sample.undo, sample.ctx, .{ .min_log = opts.min_log, .profile = if (opts.tiered) .tiered else .uniform });
    const parts = try a.create([bs.N_COMP]system.Part);
    parts.* = bs.parts(airs, built);
    var mains: [bs.N_COMP][]const []const M31 = undefined;
    for (&mains, built.mains) |*m, x| m.* = @ptrCast(x);
    const fri = if (opts.production) try core.pcs.config_v2.FriConfigV2.init(26, 0, 1, 70, 1) else try core.pcs.config_v2.FriConfigV2.init(10, 0, 1, 3, 1);
    const cfg = rec.Config.fromFriAndTraceSize(fri, built.log_size);
    var n_claims: usize = 0;
    for (parts) |p| n_claims += @intFromBool(p.air.lookups.len != 0);
    std.debug.print("block {d}: {s} profile, L = {d}, logs {any}; {s} (queries {d}, PoW {d}); device SMs accepted {any}\n", .{
        sample.ctx.height, @tagName(built.profile), built.log_size, built.logs, if (opts.production) "production" else "test", fri.n_queries, fri.pow_bits, prover.accepted_sms,
    });
    lap("witness built");

    // ---- CPU reference
    var cpu_proof: ?system.Proof = null;
    var cpu_bytes: ?[]const u8 = null;
    if (opts.cpu_proof) |path| {
        cpu_bytes = try std.fs.cwd().readFileAlloc(a, path, 1 << 30);
        cpu_proof = try loadProof(a, cpu_bytes.?, n_claims);
        lap("CPU proof loaded");
    } else if (!opts.skip_cpu) {
        cpu_proof = try system.proveOpts(rec.Engine(CpuBackend), a, cfg, parts, &mains, .{ .storage = .compact });
        cpu_bytes = try system.proofBytes(a, cpu_proof.?);
        lap("CPU proof");
        if (opts.save_cpu) |path| try std.fs.cwd().writeFile(.{ .sub_path = path, .data = cpu_bytes.? });
    }
    if (cpu_bytes) |b| {
        var buf: [64]u8 = undefined;
        std.debug.print("  CPU proof: {d} B, sha256 {s}\n", .{ b.len, hex(&sha(b), &buf) });
    }

    // ---- device
    var catalog = try res.catalog.Catalog.init(a, airs);
    const in = prover.Input{ .parts = parts, .mains = &mains, .config = cfg, .catalog = &catalog };
    var failed = false;
    var dev_proof: system.Proof = undefined;
    if (opts.mock) {
        std.debug.print("  --mock: the device is a second CPU proof (default storage)\n", .{});
        dev_proof = try system.proveOpts(rec.Engine(CpuBackend), a, cfg, parts, &mains, .{});
        lap("mock device proof");
    } else {
        var prepared = try prover.Prepared.init(a, parts, &catalog, cfg, if (opts.host_logup) .host_logup else .device_logup);
        std.debug.print("  LogUp on the {s}; planned arena {d:.2} GiB, geometry {x}\n", .{
            if (opts.host_logup) "host" else "device", @as(f64, @floatFromInt(try prepared.memory.bytes())) / (1 << 30), prepared.plans.geometry.identity[0..8],
        });
        lap("plans");
        var host = try prover.hostTraceTrees(a, in);
        std.debug.print("  host trees (natural order): preprocessed {d:.2} GiB generated, main {d:.2} GiB borrowed from the witness\n", .{
            @as(f64, @floatFromInt(host.bytes(0))) / (1 << 30), @as(f64, @floatFromInt(host.bytes(1))) / (1 << 30),
        });
        lap("host trace trees");
        var twiddles = try prover.Twiddles.init(a, prepared.plans.twiddle_words);
        lap("twiddles");
        var host_logup: ?prover.HostLogup = null;
        if (opts.host_logup) {
            const roots = try system.traceRoots(a, cfg, parts, &mains);
            lap("host trace roots (CPU commit of trees 0-1)");
            if (cpu_proof) |cp| for (roots, 0..) |r, t| {
                if (!std.mem.eql(u8, std.mem.asBytes(&r), std.mem.asBytes(&cp.stark.commitment_scheme_proof.commitments.items[t]))) {
                    std.debug.print("HOST ROOT MISMATCH tree {d} (system.traceRoots vs proveOpts)\n", .{t});
                    return error.HostRootMismatch;
                }
            };
            const el = try prover.lookupElements(&prepared, cfg, roots);
            const inter = try system.interactionTrace(a, parts, &mains, el);
            host.trees[2] = inter.columns;
            host_logup = .{ .el = el, .sums = inter.sums };
            lap("host (z, alpha) and interaction trace");
        }
        const result = try prover.proofPass(a, &prepared, &host, &twiddles, in, host_logup);
        lap("device proof");
        const k = result.verdict.counters;
        std.debug.print("  device: peak live {d:.2} GiB, h2d {d:.2} GiB, {d} kernel launches, AOT misses {d}\n", .{
            @as(f64, @floatFromInt(k.peak_live_bytes)) / (1 << 30), @as(f64, @floatFromInt(k.h2d_bytes)) / (1 << 30), k.kernel_launches, result.verdict.aot.aot_misses,
        });
        if (k.device_timing_intervals != 0) for (k.stages, 0..) |st, i| if (st.device_elapsed_ns != 0)
            std.debug.print("    stage {s}: {d:.1} ms\n", .{ @tagName(@as(@import("stwo_cuda_backend").runtime.telemetry.Stage, @enumFromInt(i))), @as(f64, @floatFromInt(st.device_elapsed_ns)) / 1e6 });
        dev_proof = result.proof;
    }
    const dev_bytes = try system.proofBytes(a, dev_proof);
    var buf: [64]u8 = undefined;
    const dev_sha = sha(dev_bytes);
    std.debug.print("  device proof: {d} B, sha256 {s}\n", .{ dev_bytes.len, hex(&dev_sha, &buf) });
    if (opts.save_device) |path| try std.fs.cwd().writeFile(.{ .sub_path = path, .data = dev_bytes });

    // ---- comparisons
    if (cpu_proof) |*cp| {
        if (diffProofs(cp, &dev_proof)) failed = true;
        if (firstDiff(cpu_bytes.?, dev_bytes)) |off| {
            const claims = 16 * n_claims;
            std.debug.print("BYTES DIFFER at offset {d} ({s}); lengths {d} vs {d}\n", .{ off, if (off < claims) "claimed sums" else "postcard STARK proof", cpu_bytes.?.len, dev_bytes.len });
            failed = true;
        } else std.debug.print("  BYTE-IDENTICAL to the CPU proof\n", .{});
    }
    if (opts.cpu_sha) |want| {
        const got = hex(&dev_sha, &buf);
        if (!std.mem.startsWith(u8, got, want)) {
            std.debug.print("SHA MISMATCH: device {s}, expected prefix {s}\n", .{ got, want });
            failed = true;
        } else std.debug.print("  sha256 prefix matches {s}\n", .{want});
    }
    if (opts.cpu_len) |want| if (want != dev_bytes.len) {
        std.debug.print("LENGTH MISMATCH: device {d}, expected {d}\n", .{ dev_bytes.len, want });
        failed = true;
    };
    system.verifyExt(a, cfg, parts, &.{}, dev_proof) catch |err| {
        std.debug.print("VERIFY FAILED: {s}\n", .{@errorName(err)});
        failed = true;
    };
    if (!failed) std.debug.print("  verifyExt: accepted\n", .{});
    lap(if (failed) "FAILED" else "OK");
    if (failed) std.process.exit(1);
}
