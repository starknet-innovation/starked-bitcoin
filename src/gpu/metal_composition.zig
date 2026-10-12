//! GPU plan step 2: a device composition stage for `MetalCommitBackend` proofs over our lowered
//! STWZEVA programs (`system.proveOpts(.{ .composition = .stwzeva, .device = ... })`).
//!
//! It implements stwo-zig's `device_stage.Device` (the hook `circuit_metal` fills with
//! `cairo_metal.composition_stage`), but compiles its kernels from MSL at runtime
//! (`Runtime.compileEvalLibrary`, as `metal_parity.zig` does) instead of loading a digest-pinned
//! Xcode metallib. stwo-zig's `device_stage.Bound` keeps the accumulator protocol (coefficient
//! assignment, fresh-bucket stores) and evaluates declined components on the host, so proofs
//! stay byte-identical.
//!
//! Public inputs: each AIR is lowered once more as a *template* (`stwzeva.lowerTemplate`), with
//! public input k as base `param` k. The kernel is compiled once per AIR and cached for the life
//! of the process (the OS Metal cache also keeps it across processes); a proof only binds its
//! public inputs into the arena. The host program (literals) and the template compute the same
//! field values, so the bytes are unchanged.
//!
//! Each evaluation copies the component's committed columns (on the evaluation domain) into one
//! reused resident arena, dispatches, and stores or adds the four coordinate planes into the
//! accumulator bucket. Columns the host holds only as coefficients are expanded by stwo-zig's
//! trace lease first.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const metal_backend = @import("stwo_metal_backend");
const metal = metal_backend.runtime;
const shared_runtime = metal_backend.shared_runtime;
const codegen = @import("cairo_metal_eval_codegen");
const stwzeva = sb.air.stwzeva;
const ir = sb.air.ir;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const composition = stwzeva.composition;
const device_stage = stwzeva.device_stage;

const Kernel = struct {
    template: stwzeva.eval.Program,
    library: metal.EvalLibrary,
    name: []u8,
};

pub const Stats = struct {
    compiles: usize = 0,
    compile_ns: u64 = 0,
    evaluations: usize = 0,
    copy_ns: u64 = 0,
    gpu_ms: f64 = 0,
};

/// The device. Long-lived: it caches one compiled kernel per AIR (by name).
pub const MetalComposition = struct {
    allocator: std.mem.Allocator,
    kernels: std.StringHashMapUnmanaged(*Kernel) = .empty,
    arena: ?metal.ResidentBuffer = null,
    arena_words: usize = 0,
    /// This proof's components: their AIRs and public inputs, in bundle order.
    parts: []const sb.air.system.Part = &.{},
    /// Per component of the open session: its template kernel.
    session_kernels: []*Kernel = &.{},
    stats: Stats = .{},

    pub fn init(allocator: std.mem.Allocator) MetalComposition {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *MetalComposition) void {
        var it = self.kernels.iterator();
        while (it.next()) |e| {
            e.value_ptr.*.library.deinit();
            e.value_ptr.*.template.deinit();
            self.allocator.free(e.value_ptr.*.name);
            self.allocator.free(e.key_ptr.*);
            self.allocator.destroy(e.value_ptr.*);
        }
        self.kernels.deinit(self.allocator);
        if (self.arena) |*arena| arena.deinit();
        self.allocator.free(self.session_kernels);
    }

    /// The device for the next proof of `parts` (the same parts `system.proveOpts` gets).
    pub fn device(self: *MetalComposition, parts: []const sb.air.system.Part) stwzeva.Device {
        self.parts = parts;
        return .{ .context = self, .open = open };
    }

    fn kernelFor(self: *MetalComposition, runtime: *metal.Runtime, air: ir.Air, log_size: u32) !*Kernel {
        if (self.kernels.get(air.name)) |k| return k;
        var template = try stwzeva.lowerTemplate(self.allocator, air, log_size);
        errdefer template.deinit();
        const source = try codegen.generate(self.allocator, template);
        defer self.allocator.free(source);
        var timer = try std.time.Timer.start();
        var library = try runtime.compileEvalLibrary(source);
        errdefer library.deinit();
        self.stats.compile_ns += timer.read();
        self.stats.compiles += 1;
        const name = try codegen.kernelName(self.allocator, template.header.semantic_hash);
        errdefer self.allocator.free(name);
        const key = try self.allocator.dupe(u8, air.name);
        const kernel = try self.allocator.create(Kernel);
        kernel.* = .{ .template = template, .library = library, .name = name };
        try self.kernels.put(self.allocator, key, kernel);
        return kernel;
    }

    fn open(
        context: *anyopaque,
        allocator: std.mem.Allocator,
        components: []const composition.Component,
        _: []const []u32,
    ) anyerror!?device_stage.Session {
        const self: *MetalComposition = @ptrCast(@alignCast(context));
        if (components.len != self.parts.len) return error.PartsMismatch;
        var lease = try shared_runtime.acquireExisting();
        defer lease.deinit();
        self.allocator.free(self.session_kernels);
        self.session_kernels = try self.allocator.alloc(*Kernel, components.len);
        const accepts = try allocator.alloc(bool, components.len);
        for (components, self.parts, self.session_kernels, accepts) |c, p, *k, *ok| {
            if (!std.mem.eql(u8, c.label, p.air.name)) return error.PartsMismatch;
            k.* = try self.kernelFor(lease.runtime, p.air.*, p.log_size);
            ok.* = true;
        }
        return .{ .context = self, .accepts = accepts, .evaluate = evaluate, .close = close };
    }

    fn close(_: *anyopaque) void {}

    fn ensureArena(self: *MetalComposition, runtime: *metal.Runtime, words: usize) ![*]u32 {
        if (self.arena == null or self.arena_words < words) {
            if (self.arena) |*old| old.deinit();
            self.arena = null;
            self.arena = try runtime.allocateResidentBuffer(words * @sizeOf(u32));
            self.arena_words = words;
        }
        return @ptrCast(@alignCast(self.arena.?.contents));
    }

    fn evaluate(context: *anyopaque, request: *const device_stage.Request) anyerror!void {
        const self: *MetalComposition = @ptrCast(@alignCast(context));
        const captured = request.captured;
        const index = for (self.parts, 0..) |p, i| {
            if (std.mem.eql(u8, p.air.name, captured.label)) break i;
        } else return error.UnknownComponent;
        const kernel = self.session_kernels[index];
        const part = self.parts[index];
        const program = kernel.template;
        if (captured.parts.len != 1 or program.header.n_constraints != captured.n_constraints) return error.TemplateMismatch;
        var lease = try shared_runtime.acquireExisting();
        defer lease.deinit();
        const runtime = lease.runtime;
        var timer = try std.time.Timer.start();

        const rows: usize = @as(usize, 1) << @intCast(captured.evaluation_log_size);
        const n_pre = captured.preprocessed_indices.len;
        var spans: [3]usize = .{ n_pre, 0, 0 };
        for (captured.trace_spans) |s| spans[s.tree] = s.end - s.start;
        const n_cols = spans[0] + spans[1] + spans[2];
        // Columns the program reads.
        const read = try self.allocator.alloc(bool, n_cols);
        defer self.allocator.free(read);
        @memset(read, false);
        for (program.base_insts) |inst| {
            if (inst.op != .trace_col and inst.op != .preprocessed_col) continue;
            const base: usize = switch (inst.interaction) {
                0 => 0,
                1 => spans[0],
                else => spans[0] + spans[1],
            };
            read[base + inst.a] = true;
        }
        var n_read: usize = 0;
        for (read) |r| n_read += @intFromBool(r);

        var next: usize = 1;
        const column_base = next;
        next += n_read * rows;
        const trace_offsets = next;
        next += n_cols;
        const interaction_offsets = next;
        next += 3;
        const base_params = next;
        next += part.pubs.len;
        const ext_params = next;
        next += 4 * request.extension_parameters.len;
        const random_coeffs = next;
        next += 4 * request.random_coefficients.len;
        const denom_inv = next;
        next += captured.denominator_inverses.len;
        var coordinates: [4]u32 = undefined;
        for (&coordinates) |*c| {
            c.* = @intCast(next);
            next += rows;
        }
        const words = try self.ensureArena(runtime, next);

        var slot: usize = 0;
        var global: usize = 0;
        for (0..3) |tree| {
            words[interaction_offsets + tree] = @intCast(global);
            for (0..spans[tree]) |local| {
                defer global += 1;
                words[trace_offsets + global] = 0;
                if (!read[global]) continue;
                const column = try request.trace.resolve(request.trace.context, @intCast(tree), @intCast(local));
                if (column.row_indexed or column.base != 0 or column.shift_amt != 1 or column.values.len != rows)
                    return error.UnsupportedTraceShape;
                const at = column_base + slot * rows;
                @memcpy(words[at..][0..rows], @as([]const u32, @ptrCast(column.values)));
                words[trace_offsets + global] = @intCast(at);
                slot += 1;
            }
        }
        for (part.pubs, 0..) |p, i| words[base_params + i] = p.toU32();
        @memcpy(words[ext_params..][0 .. 4 * request.extension_parameters.len], @as([]const u32, @ptrCast(request.extension_parameters)));
        @memcpy(words[random_coeffs..][0 .. 4 * request.random_coefficients.len], @as([]const u32, @ptrCast(request.random_coefficients)));
        @memcpy(words[denom_inv..][0..captured.denominator_inverses.len], captured.denominator_inverses);
        for (coordinates) |c| @memset(words[c..][0..rows], 0);
        self.stats.copy_ns += timer.lap();

        var plan = try runtime.prepareEvalFromLibrary(kernel.library, kernel.name, .{
            .trace_offsets = @intCast(trace_offsets),
            .interaction_offsets = @intCast(interaction_offsets),
            .base_params = @intCast(base_params),
            .ext_params = @intCast(ext_params),
            .random_coeffs = @intCast(random_coeffs),
            .denom_inv = @intCast(denom_inv),
            .coordinates = coordinates,
            .row_count = @intCast(rows),
            .trace_log_size = captured.trace_log_size,
            .domain_log_size = captured.trace_log_size,
            .rc_base = 0,
        });
        defer plan.deinit();
        self.stats.gpu_ms += try runtime.evalPrepared(self.arena.?, plan);
        self.stats.evaluations += 1;

        timer.reset();
        for (request.output, coordinates) |out, c| {
            const src: []const u32 = words[c..][0..rows];
            const dst: []u32 = @ptrCast(out);
            if (request.additive) {
                for (dst, src) |*d, v| d.* = M31.fromCanonical(d.*).add(M31.fromCanonical(v)).toU32();
            } else @memcpy(dst, src);
        }
        self.stats.copy_ns += timer.read();
    }
};
