//! stwo-zig's resident CUDA circuit prover for our recursion circuits, shared by `cuda-epoch-tree`
//! (block forest) and `cuda-set-tree` (set tree): one process-owned runtime whose thread serves every
//! device prove (workers queue them), and `gpuProve`, which proves a padded circuit, verifies it
//! natively and converts it to the `leaf.CircuitProof` a node verifies (the CPU prover's bytes).

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
const preprocessed = circuit.common.preprocessed;
const component_list = circuit.common.component_list;
const Context = circuit.builder.Context;
const leaf = sb.recursion.leaf;

pub fn secs(t: u64) f64 {
    return @as(f64, @floatFromInt(t)) / 1e9;
}

/// One device prove, handed by a worker to the GPU thread.
pub const GpuJob = struct {
    input: cuda.resident_prover.Input,
    result: ?cuda.resident_prover.Result = null,
    err: ?anyerror = null,
    gpu_s: f64 = 0,
    done: std.Thread.ResetEvent = .{},
};

/// The process's GPU: the AIR template (bound per circuit), the AOT catalog, and one runtime whose device
/// arena is reused by consecutive proofs of one size. The runtime belongs to the thread that opened it
/// (CUDA contexts are per thread; the runtime checks its owner), so every prove runs there: workers
/// queue jobs (`submit`) and that thread serves them (`serve`).
pub const Gpu = struct {
    template: cpu.air.Bundle,
    catalog: cuda.air_aot.Catalog,
    runtime: ?cuda_backend.runtime.NativeRuntime,
    mutex: std.Thread.Mutex = .{},
    cond: std.Thread.Condition = .{},
    queue: std.ArrayList(*GpuJob) = .empty,
    workers_left: usize = 0,

    /// From a worker: queues `job` and waits for the GPU thread to prove it.
    pub fn submit(self: *Gpu, gpa: std.mem.Allocator, job: *GpuJob) !void {
        {
            self.mutex.lock();
            defer self.mutex.unlock();
            try self.queue.append(gpa, job);
            self.cond.signal();
        }
        job.done.wait();
    }

    /// From a worker, when it stops.
    pub fn leave(self: *Gpu) void {
        self.mutex.lock();
        defer self.mutex.unlock();
        self.workers_left -= 1;
        self.cond.signal();
    }

    /// On the thread that opened the runtime: proves queued jobs until every worker has left.
    pub fn serve(self: *Gpu, gpa: std.mem.Allocator) void {
        while (true) {
            const job = blk: {
                self.mutex.lock();
                defer self.mutex.unlock();
                while (self.queue.items.len == 0 and self.workers_left > 0) self.cond.wait(&self.mutex);
                if (self.queue.items.len == 0) return;
                break :blk self.queue.orderedRemove(0);
            };
            var timer = std.time.Timer.start() catch unreachable;
            if (cuda.resident_prover.prove(gpa, job.input)) |r| job.result = r else |e| job.err = e;
            job.gpu_s = secs(timer.read());
            job.done.set();
        }
    }

    pub fn init(gpa: std.mem.Allocator, open: bool) !Gpu {
        var template = try cpu.air.parse(gpa, leaf.bundle_bytes);
        errdefer template.deinit();
        var catalog = try cuda.air_aot.build(gpa, leaf.bundle_bytes);
        errdefer catalog.deinit();
        return .{ .template = template, .catalog = catalog, .runtime = if (open) try cuda_backend.runtime.NativeRuntime.open(&.{ 80, 90 }) else null };
    }

    pub fn deinit(self: *Gpu, gpa: std.mem.Allocator) void {
        self.queue.deinit(gpa);
        if (self.runtime) |*r| r.close() catch |err| std.debug.print("cuda circuit prover: runtime close failed: {s}\n", .{@errorName(err)});
        self.catalog.deinit();
        self.template.deinit();
    }
};

/// Proves the padded, satisfied `ctx` on the GPU under `fri` with the circuit's known preprocessed root
/// `expected_root`; verifies the device proof natively; converts it to the verifier proof a node verifies
/// (`leaf.CircuitProof`); checks it with stwo-zig's circuit verifier and against `want`. The result's
/// bytes and request live in `a`.
pub fn gpuProve(gpa: std.mem.Allocator, a: std.mem.Allocator, g: *Gpu, ctx: *Context(QM31), fri: FriConfigV2, expected_root: [8]u32, gpu_s: *f64) !leaf.CircuitProof {
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
        .expected_preprocessed_root = expected_root,
        .runtime = if (g.runtime) |*r| r else null,
    };
    var job: GpuJob = .{ .input = input };
    try g.submit(gpa, &job);
    gpu_s.* = job.gpu_s;
    if (job.err) |e| return e;
    var result = job.result.?;
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

