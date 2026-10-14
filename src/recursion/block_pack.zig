//! Leaf-packing spike (aggregation on GPU, docs/design/block-rec.md § Leaf packing): k block proofs
//! verified in **one** circuit. Each block gets the full block-leaf body (`block_rec.leafBody`: plain
//! verifier, leaf checks, leaf output program); the circuit's output is Blake2s over the k leaf
//! digests. This measures capacity (variables, component sizes, prover time and memory as k grows).
//! It is not yet a sound range leaf: the in-circuit join of the k summaries (the node glue's
//! adjacency, challenge and sum checks, a few hashes per pair) is left out, and nothing proves it in
//! Lean.

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");
const block_rec = @import("block_rec.zig");
const leaf = @import("leaf.zig");
const ir = @import("../air/ir.zig");
const bs = @import("../block/system.zig");
const PF = @import("../block/proof_file.zig");

const builder = circuit.builder;
const finalize = circuit.common.finalize;
const component_list = circuit.common.component_list;
const Context = builder.Context;
const U32Wrapper = builder.wrappers.U32Wrapper;
const Var = builder.Var;
const QM31 = core.fields.qm31.QM31;
const FriConfigV2 = core.pcs.config_v2.FriConfigV2;

/// The packed circuit (finalized, unpadded) over the block proofs `files`, each verified natively first.
pub fn buildPacked(gpa: std.mem.Allocator, a: std.mem.Allocator, airs: *const [bs.N_COMP]ir.Air, files: []const PF.File, fri: FriConfigV2) !Context(QM31) {
    var ctx = try Context(QM31).init(gpa, component_list.N_RESERVED);
    errdefer ctx.deinit();
    const words = try a.alloc(U32Wrapper(Var), 8 * files.len);
    for (files, 0..) |*f, i| {
        const in = try block_rec.leafInputsOf(a, airs, f, fri);
        const out = try block_rec.leafBody(&ctx, &in.values, in.config, airs, &in.digests, in.pre_root, &f.pubs);
        if (out.len != 8) return error.UnexpectedLeafOutput;
        for (words[8 * i ..][0..8], out) |*w, v| w.* = .newUnsafe(v);
    }
    try leaf.finish(QM31, &ctx, try builder.blake.blake2sU32s(QM31, &ctx, words, 4 * words.len));
    return ctx;
}

fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

fn log2(n: usize) u32 {
    return if (n <= 1) 0 else std.math.log2_int_ceil(usize, n);
}

/// `blockpack <dir> <from> <k...> [prove]`: for each k, packs the block proofs `<dir>/proofs/<from..from+k>.sbblock`,
/// prints the circuit's size and padded component sizes, and with `prove` proves it (stwo-zig's CPU
/// circuit prover, 70 queries, 26 PoW bits) and verifies it natively.
pub fn measure(gpa: std.mem.Allocator, dir: []const u8, from: u32, ks: []const usize, prove: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = try bs.parseAirs(a);
    const tables = try leaf.Tables.init(gpa);
    defer tables.deinit(gpa);
    const fri = PF.productionFri();
    const cfri = try FriConfigV2.init(26, 0, 1, 70, 1);
    var max_k: usize = 0;
    for (ks) |k| max_k = @max(max_k, k);
    const files = try a.alloc(PF.File, max_k);
    for (files, 0..) |*f, i| {
        const path = try std.fmt.allocPrint(a, "{s}/proofs/{d}.sbblock", .{ dir, from + @as(u32, @intCast(i)) });
        f.* = try PF.decode(a, try std.fs.cwd().readFileAlloc(a, path, 1 << 30));
    }
    for (ks) |k| {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        defer scratch.deinit();
        var timer = try std.time.Timer.start();
        var ctx = try buildPacked(gpa, scratch.allocator(), &airs, files[0..k], fri);
        defer ctx.deinit();
        const build_s = secs(timer.lap());
        const sz = finalize.computePaddedSizes(.fromBuilder(&ctx.circuit));
        std.debug.print("k={d} (blocks {d}..{d}, L {d}..): {d} vars, built in {d:.1}s; padded log sizes eq {d} qm31_ops {d} m31_to_u32 {d} triple_xor {d} blake_g {d}\n", .{
            k, from, from + k - 1, files[0].log_size, ctx.circuit.n_vars, build_s,
            log2(sz.eq), log2(sz.qm31_ops), log2(sz.m31_to_u32), log2(sz.triple_xor), log2(sz.blake_g_gate),
        });
        if (!prove) continue;
        var cp = try leaf.proveCircuit(gpa, scratch.allocator(), &ctx, null, cfri);
        defer cp.deinit();
        const prove_s = secs(timer.lap());
        _ = try leaf.verifyCircuit(gpa, tables, &cp);
        std.debug.print("k={d}: proved in {d:.1}s ({d:.2}s per block), verified in {d:.2}s, proof {d} bytes\n", .{
            k, prove_s, prove_s / @as(f64, @floatFromInt(k)), secs(timer.lap()), cp.bytes.len,
        });
    }
}
