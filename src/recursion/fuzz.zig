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

/// How mutations were rejected: by an error while building the circuit (an evaluation-time
/// equality check), or by an unsatisfied circuit.
var rejected_by_error: usize = 0;
var rejected_by_circuit: usize = 0;

fn verdict(ctx: anytype) !bool {
    const ok = try ctx.isCircuitValid();
    if (!ok) rejected_by_circuit += 1;
    return ok;
}

fn errored(e: anyerror) anyerror!bool {
    if (e == error.OutOfMemory) return e;
    rejected_by_error += 1;
    return false;
}

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
    rejected_by_error = 0;
    rejected_by_circuit = 0;
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
    std.debug.print("rec fuzz {s}: {d} sites in total, {d} mutations run in {d:.1}s, {d} accepted; rejected by an evaluation check {d}, by the circuit {d}\n", .{ name, all.len, n_runs, @as(f64, @floatFromInt(timer.read())) / 1e9, findings.items.len, rejected_by_error, rejected_by_circuit });
    // The unmutated proof is still accepted (restores were exact).
    if (!try runner.run(values)) return error.BaselineRejected;
    return findings.items;
}

pub fn sampleBudget() usize {
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
            pv.verifyPlain(QM31, &ctx, &g, self.config, &st) catch |e| return errored(e);
            ctx.finalizeGuessedVars() catch |e| return errored(e);
            return verdict(&ctx);
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
            pv.verifyPlain(QM31, &ctx, &g, self.config, &st) catch |e| return errored(e);
            ctx.finalizeGuessedVars() catch |e| return errored(e);
            return verdict(&ctx);
        }
    };
    const runner = Runner{ .a = a, .airs = &airs, .config = config, .pre_root = pre_root };
    try std.testing.expect(try runner.run(&values));
    const findings = try campaign(a, &values, runner, "logup-system", sampleBudget());
    try std.testing.expectEqual(@as(usize, 0), findings.len);
}

test "rec fuzz: every guessed value of a header-tree segment proof is bound, through the leaf circuit" {
    // The production shape: the (headers, Blake2s tree) system with its public lookup entry
    // node(k, 0, T), verified by the actual leaf circuit (glue program + plain verifier).
    const H = @import("../btc/header_chain.zig");
    const HT = @import("../btc/header_tree.zig");
    const system = @import("../air/system.zig");
    const leaf = @import("leaf.zig");
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size: u32 = 12;
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const hair = (try ir.Air.parseJson(a, HT.header_json)).value;
    const tair = (try ir.Air.parseJson(a, HT.tree_json)).value;
    const hw = try H.generateFrom(a, log_size, headers, H.genesis_start);
    const tw = try HT.generate(a, log_size, hw);
    const k: u32 = log_size - 8;
    const parts = [_]system.Part{ .{ .air = &hair, .log_size = log_size, .pubs = &hw.pubs }, .{ .air = &tair, .log_size = log_size } };
    const mains = [_][]const []const M31{ @ptrCast(tw.header_main), @ptrCast(tw.tree_main) };
    const ext = [_]system.PubEntry{try HT.rootEntry(a, k, tw.root)};
    const cfg = try prove_rec.config(log_size);
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    const proof_a = try system.prove(E, a, cfg, &parts, &mains);
    const proof_b = try system.prove(E, a, cfg, &parts, &mains);
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try system.verifyCapture(a, cfg, &parts, &ext, proof_a, &capture);
    const config = pv.PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .system = true, .parts = &.{
        .{ .n_preprocessed = hair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, hair), .n_inter = 4 },
        .{ .n_preprocessed = tair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, tair), .n_inter = 8 },
    } };
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    var values = try pv.fromCapture(a, prove_rec.Hasher, &proof_b.stark, &capture, config, proof_b.claimed_sums);
    var pubs: [leaf.N_PUB]M31 = undefined;
    @memcpy(pubs[0..leaf.T_BASE], &hw.pubs);
    @memcpy(pubs[leaf.T_BASE..], &HT.limbs(tw.root));

    const Runner = struct {
        gpa: std.mem.Allocator,
        config: pv.PlainConfig,
        airs: [2]*const ir.Air,
        digests: [2][32]u8,
        pre_root: [32]u8,
        k: u32,
        pubs: []const M31,
        fn run(self: @This(), v: *const pv.PlainProof(QM31)) !bool {
            var ctx = leaf.buildLeafCircuit(self.gpa, v, self.config, self.airs, self.digests, self.pre_root, self.k, self.pubs) catch |e|
                return errored(e);
            defer ctx.deinit();
            return verdict(&ctx);
        }
    };
    var runner = Runner{ .gpa = gpa, .config = config, .airs = .{ &hair, &tair }, .digests = .{ try hair.digest(a), try tair.digest(a) }, .pre_root = pre_root, .k = k, .pubs = &pubs };
    try std.testing.expect(try runner.run(&values));
    const findings = try campaign(a, &values, runner, "header-tree segment (leaf circuit)", sampleBudget());

    // The statement: every public input, including the tree root T in the public entry.
    var stmt_findings: usize = 0;
    var prng = std.Random.DefaultPrng.init(99);
    for (0..pubs.len) |i| {
        if (!std.process.hasEnvVarConstant("REC_FUZZ_ALL") and prng.random().uintLessThan(usize, 4) != 0) continue;
        var bad = pubs;
        bad[i] = bad[i].add(M31.one());
        runner.pubs = &bad;
        if (try runner.run(&values)) {
            std.debug.print("REC-FUZZ FINDING (segment): public input {d} not bound\n", .{i});
            stmt_findings += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 0), findings.len + stmt_findings);
}

// ---------------------------------------------------------------- VL-ORACLE: the native verifier as oracle

/// A scalar of the native proof (`system.Proof`). `both`: the circuit receives the same value through
/// `fromCapture`, so the two verifiers must agree; otherwise (Merkle hash witnesses, FRI witnesses) the
/// circuit gets the honest per-query paths and cosets from the capture, and only the native verdict is
/// checked (the circuit-side counterparts are mutated by the campaigns above).
const NSite = union(enum) { hash: []u8, q: *QM31, m: *M31, w: *u64 };
const NLabeled = struct { site: NSite, label: []const u8, both: bool };

fn nHash(a: std.mem.Allocator, out: *std.ArrayList(NLabeled), h: anytype, both: bool, label: []const u8) !void {
    try out.append(a, .{ .site = .{ .hash = std.mem.asBytes(h) }, .label = label, .both = both });
}

fn nativeSites(a: std.mem.Allocator, p: anytype) ![]NLabeled {
    var out = std.ArrayList(NLabeled).empty;
    const s = &p.stark.commitment_scheme_proof;
    // Tree 0's root is not a proof input of the circuit: it pins the expected preprocessed root as a
    // statement constant, so only the native verifier reads it.
    for (s.commitments.items, 0..) |*h, t| try nHash(a, &out, h, t != 0, try std.fmt.allocPrint(a, "commitments[{d}]", .{t}));
    for (s.sampled_values.items, 0..) |cols, t| for (cols, 0..) |xs, c| for (xs, 0..) |*x, i|
        try out.append(a, .{ .site = .{ .q = x }, .label = try std.fmt.allocPrint(a, "sampled_values[{d}][{d}][{d}]", .{ t, c, i }), .both = true });
    for (p.claimed_sums, 0..) |*x, i| try out.append(a, .{ .site = .{ .q = x }, .label = try std.fmt.allocPrint(a, "claimed_sums[{d}]", .{i}), .both = true });
    for (s.queried_values.items, 0..) |cols, t| for (cols, 0..) |xs, c| for (xs, 0..) |*x, i|
        try out.append(a, .{ .site = .{ .m = x }, .label = try std.fmt.allocPrint(a, "queried_values[{d}][{d}][{d}]", .{ t, c, i }), .both = true });
    for (s.decommitments.items, 0..) |d, t| for (d.hash_witness, 0..) |*h, i|
        try nHash(a, &out, h, false, try std.fmt.allocPrint(a, "decommitments[{d}].hash_witness[{d}]", .{ t, i }));
    try out.append(a, .{ .site = .{ .w = &s.proof_of_work }, .label = "proof_of_work", .both = true });
    const fri = &s.fri_proof;
    const layers = try a.alloc(*@TypeOf(fri.first_layer), 1 + fri.inner_layers.len);
    layers[0] = &fri.first_layer;
    for (fri.inner_layers, layers[1..]) |*l, *o| o.* = l;
    for (layers, 0..) |l, k| {
        try nHash(a, &out, &l.commitment, true, try std.fmt.allocPrint(a, "fri.layer[{d}].commitment", .{k}));
        for (l.fri_witness, 0..) |*x, i| try out.append(a, .{ .site = .{ .q = x }, .label = try std.fmt.allocPrint(a, "fri.layer[{d}].fri_witness[{d}]", .{ k, i }), .both = false });
        for (l.decommitment.hash_witness, 0..) |*h, i|
            try nHash(a, &out, h, false, try std.fmt.allocPrint(a, "fri.layer[{d}].hash_witness[{d}]", .{ k, i }));
    }
    for (fri.last_layer_poly.coeffs, 0..) |*x, i| try out.append(a, .{ .site = .{ .q = x }, .label = try std.fmt.allocPrint(a, "fri.last_layer[{d}]", .{i}), .both = true });
    return out.items;
}

const NSaved = union(enum) { hash: [64]u8, q: QM31, m: M31, w: u64 };

fn nMutate(site: NSite, rng: std.Random) NSaved {
    switch (site) {
        .hash => |b| {
            var saved: [64]u8 = undefined;
            @memcpy(saved[0..b.len], b);
            const bit = rng.uintLessThan(usize, 8 * b.len);
            b[bit / 8] ^= @as(u8, 1) << @intCast(bit % 8);
            return .{ .hash = saved };
        },
        .q => |x| {
            const old = x.*;
            x.* = x.*.add(QM31.fromM31Array(.{ M31.fromCanonical(rng.intRangeAtMost(u32, 1, 0x7ffffffe)), M31.fromCanonical(rng.int(u16)), M31.zero(), M31.fromCanonical(rng.int(u8)) }));
            return .{ .q = old };
        },
        .m => |x| {
            const old = x.*;
            x.* = x.*.add(M31.fromCanonical(rng.intRangeAtMost(u32, 1, 0x7ffffffe)));
            return .{ .m = old };
        },
        .w => |x| {
            const old = x.*;
            x.* ^= @as(u64, 1) << rng.int(u6);
            return .{ .w = old };
        },
    }
}

fn nRestore(site: NSite, s: NSaved) void {
    switch (site) {
        .hash => |b| @memcpy(b, s.hash[0..b.len]),
        .q => |x| x.* = s.q,
        .m => |x| x.* = s.m,
        .w => |x| x.* = s.w,
    }
}

/// Mutates native proof scalars one at a time; `runner.native(p)` and `runner.circuit(p)` give the
/// verdicts. Returns the number of disagreements (both-sided sites) and native acceptances (native-only
/// sites); each is printed.
fn oracleCampaign(a: std.mem.Allocator, p: anytype, runner: anytype, name: []const u8, budget: usize, skip_fri: bool) !usize {
    var prng = std.Random.DefaultPrng.init(0x0ac1e);
    const rng = prng.random();
    const all_sites = try nativeSites(a, p);
    var kept = std.ArrayList(NLabeled).empty;
    for (all_sites) |s| if (!(skip_fri and std.mem.startsWith(u8, s.label, "fri."))) try kept.append(a, s);
    const all = kept.items;
    const every = std.process.hasEnvVarConstant("REC_FUZZ_ALL");
    const step = if (every or all.len <= budget) 1 else all.len / budget;
    var bad: usize = 0;
    var n_both: usize = 0;
    var n_native: usize = 0;
    var timer = try std.time.Timer.start();
    var i: usize = rng.uintLessThan(usize, step);
    while (i < all.len) : (i += step) {
        const s = all[i];
        const saved = nMutate(s.site, rng);
        const nat = try runner.native(p);
        const circ: ?bool = if (s.both) try runner.circuit(p) else null;
        nRestore(s.site, saved);
        if (circ) |c| {
            n_both += 1;
            if (c != nat) {
                std.debug.print("VL-ORACLE DISAGREEMENT ({s}): {s}: native {s}, circuit {s}\n", .{ name, s.label, if (nat) "accepts" else "rejects", if (c) "accepts" else "rejects" });
                bad += 1;
            }
        } else {
            n_native += 1;
            if (nat) {
                std.debug.print("VL-ORACLE FINDING ({s}): {s} accepted natively\n", .{ name, s.label });
                bad += 1;
            }
        }
    }
    std.debug.print("vl oracle {s}: {d} native sites, {d} mutations checked by both verifiers, {d} natively only, in {d:.1}s; {d} disagreements or acceptances\n", .{ name, all.len, n_both, n_native, @as(f64, @floatFromInt(timer.read())) / 1e9, bad });
    if (!try runner.native(p) or !try runner.circuit(p)) return error.BaselineRejected;
    return bad;
}

/// The oracle on a LogUp system proof (the byte system); returns the number of disagreements.
pub fn oracleLogupSystem(gpa: std.mem.Allocator, budget: usize, skip_fri: bool) !usize {
    const system = @import("../air/system.zig");
    var arena = std.heap.ArenaAllocator.init(gpa);
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
    var proof = try system.prove(E, a, cfg, &parts, &mains);
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &parts, &.{}, &proof, &capture);

    const Runner = struct {
        airs: *const [2]ir.Air,
        parts: []const system.Part,
        cfg: prove_rec.Config,
        config: pv.PlainConfig,
        pre_root: [32]u8,
        capture: *const core.verifier.ProofCapture(prove_rec.Hasher),
        fn native(self: @This(), p: *const system.Proof) !bool {
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            var c: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
            system.verifyCaptureBorrowed(run_arena.allocator(), self.cfg, self.parts, &.{}, p, &c) catch |e| {
                if (e == error.OutOfMemory) return e;
                return false;
            };
            return true;
        }
        fn circuit(self: @This(), p: *const system.Proof) !bool {
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            const ra = run_arena.allocator();
            const v = pv.fromCapture(ra, prove_rec.Hasher, &p.stark, self.capture, self.config, p.claimed_sums) catch return false;
            var ctx = try Context(QM31).init(ra, 0);
            defer ctx.deinit();
            const g = try pv.guess(QM31, &ctx, &v);
            const st = pv.PlainStatement{ .preprocessed_root = self.pre_root, .parts = &.{
                .{ .air = &self.airs[0], .digest = try self.airs[0].digest(ra), .pubs = &.{} },
                .{ .air = &self.airs[1], .digest = try self.airs[1].digest(ra), .pubs = &.{} },
            } };
            pv.verifyPlain(QM31, &ctx, &g, self.config, &st) catch |e| {
                if (e == error.OutOfMemory) return e;
                return false;
            };
            ctx.finalizeGuessedVars() catch return false;
            return ctx.isCircuitValid();
        }
    };
    const runner = Runner{ .airs = &airs, .parts = &parts, .cfg = cfg, .config = config, .pre_root = pre_root, .capture = &capture };
    return oracleCampaign(a, &proof, runner, "logup-system", budget, skip_fri);
}

/// The oracle on a production-shape header-tree segment proof, the circuit side through the leaf
/// circuit; returns the number of disagreements.
pub fn oracleSegment(gpa: std.mem.Allocator, budget: usize, skip_fri: bool) !usize {
    const H = @import("../btc/header_chain.zig");
    const HT = @import("../btc/header_tree.zig");
    const system = @import("../air/system.zig");
    const leaf = @import("leaf.zig");
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const log_size: u32 = 12;
    const headers = try H.loadHeaders(a, @embedFile("testdata:mainnet_headers_0_16"));
    const hair = (try ir.Air.parseJson(a, HT.header_json)).value;
    const tair = (try ir.Air.parseJson(a, HT.tree_json)).value;
    const hw = try H.generateFrom(a, log_size, headers, H.genesis_start);
    const tw = try HT.generate(a, log_size, hw);
    const k: u32 = log_size - 8;
    const parts = [_]system.Part{ .{ .air = &hair, .log_size = log_size, .pubs = &hw.pubs }, .{ .air = &tair, .log_size = log_size } };
    const mains = [_][]const []const M31{ @ptrCast(tw.header_main), @ptrCast(tw.tree_main) };
    const ext = [_]system.PubEntry{try HT.rootEntry(a, k, tw.root)};
    const cfg = try prove_rec.config(log_size);
    const E = prove_rec.Engine(@import("stwo_cpu_backend").CpuBackend);
    var proof = try system.prove(E, a, cfg, &parts, &mains);
    var capture: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
    try system.verifyCaptureBorrowed(a, cfg, &parts, &ext, &proof, &capture);
    const config = pv.PlainConfig{ .log_trace_size = log_size, .fri = cfg.fri_config, .system = true, .parts = &.{
        .{ .n_preprocessed = hair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, hair), .n_inter = 4 },
        .{ .n_preprocessed = tair.n_preprocessed, .main_offsets = try pv.mainOffsets(a, tair), .n_inter = 8 },
    } };
    const pre_root: [32]u8 = std.mem.toBytes(try system.preprocessedRoot(a, cfg, &parts));
    var pubs: [leaf.N_PUB]M31 = undefined;
    @memcpy(pubs[0..leaf.T_BASE], &hw.pubs);
    @memcpy(pubs[leaf.T_BASE..], &HT.limbs(tw.root));

    const Runner = struct {
        gpa: std.mem.Allocator,
        parts: []const system.Part,
        ext: []const system.PubEntry,
        cfg: prove_rec.Config,
        config: pv.PlainConfig,
        airs: [2]*const ir.Air,
        digests: [2][32]u8,
        pre_root: [32]u8,
        k: u32,
        pubs: []const M31,
        capture: *const core.verifier.ProofCapture(prove_rec.Hasher),
        fn native(self: @This(), p: *const system.Proof) !bool {
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            var c: core.verifier.ProofCapture(prove_rec.Hasher) = undefined;
            system.verifyCaptureBorrowed(run_arena.allocator(), self.cfg, self.parts, self.ext, p, &c) catch |e| {
                if (e == error.OutOfMemory) return e;
                return false;
            };
            return true;
        }
        fn circuit(self: @This(), p: *const system.Proof) !bool {
            var run_arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
            defer run_arena.deinit();
            const v = pv.fromCapture(run_arena.allocator(), prove_rec.Hasher, &p.stark, self.capture, self.config, p.claimed_sums) catch return false;
            var ctx = leaf.buildLeafCircuit(self.gpa, &v, self.config, self.airs, self.digests, self.pre_root, self.k, self.pubs) catch |e| {
                if (e == error.OutOfMemory) return e;
                return false;
            };
            defer ctx.deinit();
            return ctx.isCircuitValid();
        }
    };
    const runner = Runner{ .gpa = gpa, .parts = &parts, .ext = &ext, .cfg = cfg, .config = config, .airs = .{ &hair, &tair }, .digests = .{ try hair.digest(a), try tair.digest(a) }, .pre_root = pre_root, .k = k, .pubs = &pubs, .capture = &capture };
    return oracleCampaign(a, &proof, runner, "header-tree segment (leaf circuit)", budget, skip_fri);
}

// No test runs these: stwo-zig's native verifier logs an error on every rejection (Merkle, FRI), which
// fails a Zig test. `zig build oracle` (src/bin/oracle.zig) runs them.
