//! **REC-FUZZ** (roadmap; proof review 2026-10-09, finding 1): mutation testing of the plain
//! in-circuit verifier (`plain_verifier.zig`), which every leaf trusts and Lean does not cover.
//!
//! The circuit *guesses* every proof value. A soundness bug of the classic kind is a guessed value
//! the circuit never binds (to the transcript, a Merkle root, a fold or a range check). So: start
//! from real proofs the native verifier accepts, change one guessed value at a time, and require
//! the circuit to reject. Every scalar is a site:
//! roots, OODS samples, claimed sums, decommitted values, authentication paths, FRI commitments,
//! last-layer coefficients, FRI witnesses, the PoW nonce; and, for `M31` wrappers, also an
//! out-of-range encoding of the same value. The statement (public
//! inputs) is mutated too.
//!
//! `zig build test -Doptimize=ReleaseFast -Dtest-filter="rec fuzz"` samples sites; set
//! `REC_FUZZ_ALL=1` to mutate every site (long).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const pv = @import("plain_verifier.zig");
const ir = @import("../air/ir.zig");
const prove_base = @import("../air/prove.zig");
const prove_rec = @import("../air/prove_rec.zig");

const builder = circuit.builder;
const Context = builder.Context;
const Var = builder.Var;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const M31W = builder.wrappers.M31Wrapper(QM31);
const U32W = builder.wrappers.U32Wrapper(QM31);
const HashValue = builder.blake.HashValue;

const Site = union(enum) {
    q: *QM31,
    m: *M31W,
    u: *U32W,
};

const Labeled = struct { site: Site, label: []const u8 };

fn addHash(a: std.mem.Allocator, out: *std.ArrayList(Labeled), h: *HashValue(QM31), label: []const u8) !void {
    for (&h.words, 0..) |*w, i| try out.append(a, .{ .site = .{ .u = w }, .label = try std.fmt.allocPrint(a, "{s}.w{d}", .{ label, i }) });
}

fn addQs(a: std.mem.Allocator, out: *std.ArrayList(Labeled), xs: []QM31, label: []const u8) !void {
    for (xs, 0..) |*x, i| try out.append(a, .{ .site = .{ .q = x }, .label = try std.fmt.allocPrint(a, "{s}[{d}]", .{ label, i }) });
}

/// Every guessed scalar of `p`.
fn sites(a: std.mem.Allocator, p: *pv.PlainProof(QM31)) ![]Labeled {
    var out = std.ArrayList(Labeled).empty;
    try addHash(a, &out, &p.trace_root, "trace_root");
    if (p.interaction_root) |*r| try addHash(a, &out, r, "interaction_root");
    try addHash(a, &out, &p.composition_root, "composition_root");
    try addQs(a, &out, p.preprocessed_at_oods, "preprocessed_at_oods");
    for (p.trace_at_oods, 0..) |xs, c| try addQs(a, &out, xs, try std.fmt.allocPrint(a, "trace_at_oods[{d}]", .{c}));
    for (p.interaction_at_oods, 0..) |xs, c| try addQs(a, &out, xs, try std.fmt.allocPrint(a, "interaction_at_oods[{d}]", .{c}));
    try addQs(a, &out, p.claimed_sums, "claimed_sums");
    try addQs(a, &out, &p.composition_eval_at_oods, "composition_eval_at_oods");
    for (&p.eval_domain_samples.data, 0..) |xs, t| for (xs, 0..) |*x, i|
        try out.append(a, .{ .site = .{ .m = x }, .label = try std.fmt.allocPrint(a, "eval_domain_samples[{d}][{d}]", .{ t, i }) });
    for (p.eval_domain_auth_paths.trees, 0..) |nodes, t| for (nodes, 0..) |*h, i|
        try addHash(a, &out, h, try std.fmt.allocPrint(a, "auth_paths[{d}][{d}]", .{ t, i }));
    try out.append(a, .{ .site = .{ .q = &p.pow_nonce }, .label = "pow_nonce" });
    for (p.fri.layer_commitments, 0..) |*h, i| try addHash(a, &out, h, try std.fmt.allocPrint(a, "fri.layer_commitments[{d}]", .{i}));
    try addQs(a, &out, p.fri.last_layer_coefs, "fri.last_layer_coefs");
    for (p.fri.auth_paths.trees, 0..) |nodes, t| for (nodes, 0..) |*h, i|
        try addHash(a, &out, h, try std.fmt.allocPrint(a, "fri.auth_paths[{d}][{d}]", .{ t, i }));
    for (p.fri.witness, 0..) |xs, l| try addQs(a, &out, xs, try std.fmt.allocPrint(a, "fri.witness[{d}]", .{l}));
    return out.items;
}

/// The mutations of a site: a different valid value, and for wrappers an out-of-range encoding.
const Kind = enum { value, encoding };

fn mutate(site: Site, kind: Kind, rng: std.Random) void {
    switch (site) {
        .q => |x| x.* = x.*.add(QM31.fromM31Array(.{
            M31.fromCanonical(rng.intRangeAtMost(u32, 1, 0x7ffffffe)),
            M31.fromCanonical(rng.int(u16)),
            M31.zero(),
            M31.fromCanonical(rng.int(u8)),
        })),
        .m => |x| {
            const v = x.get().toM31Array();
            x.* = switch (kind) {
                .value => builder.wrappers.m31Value(QM31, v[0].add(M31.fromCanonical(rng.intRangeAtMost(u32, 1, 0x7ffffffe)))),
                // Same base value, nonzero extension coordinates: not an M31.
                .encoding => M31W.newUnsafe(QM31.fromM31Array(.{ v[0], M31.one(), v[2], v[3] })),
            };
        },
        .u => |x| {
            const v = x.get().toM31Array();
            const word = v[0].toU32() | (v[1].toU32() << 16);
            x.* = switch (kind) {
                .value => builder.wrappers.u32Value(QM31, word ^ (@as(u32, 1) << rng.int(u5))),
                // Same number with a carry left in the low limb: low + 2^16, high − 1 (or a limb
                // above 16 bits when high is 0).
                .encoding => if (v[1].toU32() > 0)
                    U32W.newUnsafe(QM31.fromM31Array(.{ M31.fromCanonical(v[0].toU32() + 0x10000), M31.fromCanonical(v[1].toU32() - 1), v[2], v[3] }))
                else
                    U32W.newUnsafe(QM31.fromM31Array(.{ v[0], M31.fromCanonical(0x10000), v[2], v[3] })),
            };
        },
    }
}

const Saved = union(enum) { q: QM31, m: M31W, u: U32W };

fn save(site: Site) Saved {
    return switch (site) {
        .q => |x| .{ .q = x.* },
        .m => |x| .{ .m = x.* },
        .u => |x| .{ .u = x.* },
    };
}

fn restore(site: Site, s: Saved) void {
    switch (site) {
        .q => |x| x.* = s.q,
        .m => |x| x.* = s.m,
        .u => |x| x.* = s.u,
    }
}

/// Runs the mutation campaign over `values` with `run` (true = the circuit accepts). Returns the
/// labels of accepted mutations (findings).
fn campaign(a: std.mem.Allocator, values: *pv.PlainProof(QM31), runner: anytype, name: []const u8, budget: usize) ![]const []const u8 {
    var prng = std.Random.DefaultPrng.init(0x5eed);
    const rng = prng.random();
    const all = try sites(a, values);
    const every = std.process.hasEnvVarConstant("REC_FUZZ_ALL");
    const step = if (every or all.len <= budget) 1 else all.len / budget;
    var findings = std.ArrayList([]const u8).empty;
    var n_runs: usize = 0;
    var timer = try std.time.Timer.start();
    var i: usize = rng.uintLessThan(usize, step);
    while (i < all.len) : (i += step) {
        const s = all[i];
        // u32 wrappers: the witness builder itself refuses limbs above 16 bits (`unpackU32` panics),
        // so only M31 wrappers get an out-of-range encoding.
        const kinds: []const Kind = if (s.site == .m) &.{ .value, .encoding } else &.{.value};
        for (kinds) |kind| {
            const saved = save(s.site);
            mutate(s.site, kind, rng);
            const accepted = try runner.run(values);
            restore(s.site, saved);
            n_runs += 1;
            if (accepted) {
                std.debug.print("REC-FUZZ FINDING ({s}): mutation {s} of {s} accepted\n", .{ name, @tagName(kind), s.label });
                try findings.append(a, try std.fmt.allocPrint(a, "{s}:{s}:{s}", .{ name, @tagName(kind), s.label }));
            }
        }
    }
    std.debug.print("rec fuzz {s}: {d} sites in total, {d} mutations run in {d:.1}s, {d} accepted\n", .{ name, all.len, n_runs, @as(f64, @floatFromInt(timer.read())) / 1e9, findings.items.len });
    // The unmutated proof is still accepted (restores were exact).
    if (!try runner.run(values)) return error.BaselineRejected;
    return findings.items;
}

fn sampleBudget() usize {
    const v = std.process.getEnvVarOwned(std.heap.page_allocator, "REC_FUZZ_BUDGET") catch return 150;
    defer std.heap.page_allocator.free(v);
    return std.fmt.parseInt(usize, v, 10) catch 150;
}

test "rec fuzz: every guessed value of a header-chain proof is bound" {
    const H = @import("../btc/header_chain.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const air = (try ir.Air.parseJson(a, H.lean_json)).value;
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const log_size: u32 = 12;
    const wit = try H.generate(a, log_size, headers);
    const cfg = try prove_rec.config(log_size);
    const digest = try air.digest(a);
    const statement = prove_base.AirStatement{ .log_size = log_size, .digest = digest, .pubs = &wit.pubs, .air = &air, .allocator = a };
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const proof_a = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    const proof_b = try prove_rec.prove(E, a, cfg, statement, @ptrCast(wit.main));
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try prove_rec.verifyCapture(a, cfg, air, log_size, &wit.pubs, proof_a, &capture);
    const config = try pv.PlainConfig.single(log_size, cfg.fri_config, air.n_preprocessed, try pv.mainOffsets(a, air), a);
    const pre_root: [32]u8 = std.mem.toBytes(try prove_rec.preprocessedRoot(a, cfg, air, log_size));
    var values = try pv.fromCapture(a, prove_rec.Hasher, &proof_b, &capture, config, &.{});

    const Runner = struct {
        a: std.mem.Allocator,
        config: pv.PlainConfig,
        air: *const ir.Air,
        digest: [32]u8,
        pre_root: [32]u8,
        pubs: []const M31,
        fn run(self: @This(), v: *const pv.PlainProof(QM31)) !bool {
            // A fresh arena per run: circuits are large and the campaign runs many.
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            const ra = run_arena.allocator();
            var ctx = try Context(QM31).init(ra, 0);
            defer ctx.deinit();
            const g = try pv.guess(QM31, &ctx, v);
            const pub_vars = try ra.alloc(Var, self.pubs.len);
            for (pub_vars, self.pubs) |*w, x| w.* = try ctx.guess(QM31.fromBase(x));
            const st = pv.PlainStatement{ .parts = &.{.{ .air = self.air, .digest = self.digest, .pubs = pub_vars }}, .preprocessed_root = self.pre_root };
            pv.verifyPlain(QM31, &ctx, &g, self.config, &st) catch |e| return if (e == error.OutOfMemory) e else false;
            ctx.finalizeGuessedVars() catch |e| return if (e == error.OutOfMemory) e else false;
            return ctx.isCircuitValid();
        }
    };
    var runner = Runner{ .a = a, .config = config, .air = &air, .digest = digest, .pre_root = pre_root, .pubs = &wit.pubs };
    try std.testing.expect(try runner.run(&values));
    const findings = try campaign(a, &values, runner, "header-chain", sampleBudget());

    // The statement: every public input, the AIR digest and the preprocessed root.
    var stmt_findings: usize = 0;
    for (0..wit.pubs.len) |k| {
        var pubs = wit.pubs;
        pubs[k] = pubs[k].add(M31.one());
        runner.pubs = &pubs;
        if (try runner.run(&values)) {
            std.debug.print("REC-FUZZ FINDING (header-chain): public input {d} not bound\n", .{k});
            stmt_findings += 1;
        }
    }
    runner.pubs = &wit.pubs;
    for ([_]usize{ 0, 13, 31 }) |byte| {
        runner.digest[byte] ^= 1;
        if (try runner.run(&values)) stmt_findings += 1;
        runner.digest[byte] ^= 1;
        runner.pre_root[byte] ^= 1;
        if (try runner.run(&values)) stmt_findings += 1;
        runner.pre_root[byte] ^= 1;
    }
    try std.testing.expectEqual(@as(usize, 0), findings.len + stmt_findings);
}

test "rec fuzz: every guessed value of a LogUp system proof is bound" {
    const system = @import("../air/system.zig");
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try system.byteSystem(a);
    const log_size: u32 = 8;
    const parts = [_]system.Part{ .{ .air = &airs[0], .log_size = log_size }, .{ .air = &airs[1], .log_size = log_size } };
    const cfg = prove_rec.Config.fromFriAndTraceSize(try pv.FriConfig.init(10, 0, 1, 3, 1), log_size);
    var prng = std.Random.DefaultPrng.init(23);
    const x = try a.alloc(M31, 256);
    const mult = try a.alloc(M31, 256);
    @memset(mult, M31.zero());
    for (x) |*v| {
        const b = prng.random().int(u8);
        v.* = M31.fromCanonical(b);
        mult[b] = mult[b].add(M31.one());
    }
    const config = pv.PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .system = true, .parts = &.{
        .{ .n_preprocessed = 1, .main_offsets = try pv.mainOffsets(a, airs[0]), .n_inter = 4 },
        .{ .n_preprocessed = 0, .main_offsets = try pv.mainOffsets(a, airs[1]), .n_inter = 4 },
    } };
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const mains = [_][]const []const M31{ &.{mult}, &.{x} };
    const pa = try system.prove(E, a, cfg, &parts, &mains);
    const pb = try system.prove(E, a, cfg, &parts, &mains);
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try system.verifyCapture(a, cfg, &parts, &.{}, pa, &capture);
    var values = try pv.fromCapture(a, prove_rec.Hasher, &pb.stark, &capture, config, pb.claimed_sums);

    const Runner = struct {
        a: std.mem.Allocator,
        airs: *const [2]ir.Air,
        config: pv.PlainConfig,
        pre_root: [32]u8,
        fn run(self: @This(), v: *const pv.PlainProof(QM31)) !bool {
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            const ra = run_arena.allocator();
            var ctx = try Context(QM31).init(ra, 0);
            defer ctx.deinit();
            const g = try pv.guess(QM31, &ctx, v);
            const st = pv.PlainStatement{ .preprocessed_root = self.pre_root, .parts = &.{
                .{ .air = &self.airs[0], .digest = try self.airs[0].digest(ra), .pubs = &.{} },
                .{ .air = &self.airs[1], .digest = try self.airs[1].digest(ra), .pubs = &.{} },
            } };
            pv.verifyPlain(QM31, &ctx, &g, self.config, &st) catch |e| return if (e == error.OutOfMemory) e else false;
            ctx.finalizeGuessedVars() catch |e| return if (e == error.OutOfMemory) e else false;
            return ctx.isCircuitValid();
        }
    };
    const runner = Runner{ .a = a, .airs = &airs, .config = config, .pre_root = pre_root };
    try std.testing.expect(try runner.run(&values));
    const findings = try campaign(a, &values, runner, "logup-system", sampleBudget());
    try std.testing.expectEqual(@as(usize, 0), findings.len);
}
