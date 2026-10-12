//! Lowering of an `ir.Air` (with its LogUp lookups) to stwo-zig's `STWZEVA/1` constraint
//! bytecode (`frontends/cairo/witness/eval_program.zig`), and a component that drives the
//! composition with it (GPU plan step 1, docs/design/gpu.md).
//!
//! The lowering produces, per component, one `composition_bundle.Component` with one program part:
//! the same object stwo-zig's Cairo/circuit lanes consume (the SIMD interpreter, the C/CUDA/Metal
//! code generators, the Metal device composition stage). `encodeBundle` writes the `STWZEVA\0`
//! bundle bytes (format of `tools/stwo-eval-program-abi/src/bundle.rs`), and every program is
//! re-parsed by stwo-zig's own `Program.parse` (which checks the semantic hash and validates).
//!
//! Mapping (see docs/design/gpu.md, "Step 1 results"):
//! - `col{main, i, off}`  → `trace_col` interaction 1, column i (local to the tree-1 span), imm off.
//! - `col{pre, i, 0}`     → `trace_col` interaction 0, local column i (`preprocessed_indices[i]`
//!   = the component's global preprocessed column). Only offset 0 (our component's rule too).
//! - `const c`, `pub i`   → base `constant` (public inputs are baked in as literals; CUDA's
//!   parametric normaliser turns every base literal into a session constant anyway).
//! - add/sub/mul/neg      → base add/sub/mul/neg (M31).
//! - constraint root r    → ext `secure_col(r, 0, 0, 0)`, in IR order.
//! - LogUp (pairs of lookups, `component.logupConstraintValues`): ext arithmetic over the
//!   interaction-tree reads (interaction 2, 4 limbs per batch, last batch also at offset −1) and the
//!   ext params `[z, α¹ … α^w, claimed_sum/2^log]` (`ExtSource` lookup_z, lookup_alpha_power,
//!   claimed_sum_scaled). Constraint order: IR constraints, then batches.
//!
//! Every read of a column is emitted once, in a prologue, in the order our component's mask
//! lists the offsets (main: ascending; interaction: −1 then 0), because stwo-zig derives a
//! component's mask from the first appearance of each (column, offset) read.

const std = @import("std");
const ir = @import("ir.zig");
const component_mod = @import("component.zig");
const cairo = @import("stwo_cairo_frontend");
const core = @import("stwo_core");
const prover_component = @import("stwo_prover_engine").air.component_prover;
const prover_air_accumulation = @import("stwo_prover_engine").air.accumulation;
const core_air_accumulation = core.air.accumulation;
const core_air_components = core.air.components;
const core_air_derive = core.air.derive;
const core_constraints = core.constraints;
const canonic = core.poly.circle.canonic;
const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const CirclePointQM31 = core.circle.CirclePointQM31;

pub const eval = cairo.witness.eval_program;
pub const composition = cairo.witness.composition_bundle;
pub const Captured = cairo.proving.air.component.Component;
pub const RuntimeComponent = cairo.witness.resident_verifier.RuntimeComponent;
pub const Native = cairo.proving.air.native_evaluator.Executor;
/// stwo-zig's whole-stage device composition hook over captured components.
pub const device_stage = cairo.proving.air.device_stage;
pub const Device = device_stage.Device;
pub const DeviceBound = device_stage.Bound;
pub const DeviceCounts = device_stage.Counts;

/// Where a component sits in the shared trees (as `system.components` wires it).
pub const Geometry = struct {
    log_size: u32,
    pre_offset: u32 = 0,
    main_offset: u32 = 0,
    inter_offset: u32 = 0,
    /// Index of the component's first constraint in the whole system (bundle metadata only).
    rc_offset: u32 = 0,
};

pub const Error = error{
    PreprocessedOffsetUnsupported,
    TooManyRegisters,
    NoConstraints,
    LookupTooWide,
};

const max_regs: u32 = 65536;

/// Ext parameter slots of a component with lookups: `[z, α¹ … α^w, claimed_sum/2^log]`.
fn extSources(allocator: std.mem.Allocator, air: ir.Air) ![]composition.ExtSource {
    if (air.lookups.len == 0) return allocator.alloc(composition.ExtSource, 0);
    var width: usize = 0;
    for (air.lookups) |l| width = @max(width, l.vals.len);
    if (width > component_mod.MAX_LOOKUP_VALS) return Error.LookupTooWide;
    const out = try allocator.alloc(composition.ExtSource, width + 2);
    out[0] = .lookup_z;
    for (1..width + 1) |p| out[p] = .{ .lookup_alpha_power = @intCast(p) };
    out[width + 1] = .claimed_sum_scaled;
    return out;
}

const ProgramBuilder = struct {
    allocator: std.mem.Allocator,
    base: std.ArrayList(eval.BaseInst) = .empty,
    ext: std.ArrayList(eval.ExtInst) = .empty,
    roots: std.ArrayList(u32) = .empty,
    n_base: u32 = 0,
    n_ext: u32 = 0,
    constants: std.AutoHashMapUnmanaged(u32, u16) = .empty,

    fn deinit(self: *ProgramBuilder) void {
        self.base.deinit(self.allocator);
        self.ext.deinit(self.allocator);
        self.roots.deinit(self.allocator);
        self.constants.deinit(self.allocator);
    }

    fn baseInst(self: *ProgramBuilder, op: eval.BaseOpcode, interaction: u8, a: u32, b: u32, imm: i32) !u16 {
        if (self.n_base >= max_regs) return Error.TooManyRegisters;
        const dst: u16 = @intCast(self.n_base);
        self.n_base += 1;
        try self.base.append(self.allocator, .{ .op = op, .interaction = interaction, .dst = dst, .a = a, .b = b, .imm = imm });
        return dst;
    }

    fn read(self: *ProgramBuilder, interaction: u8, column: u32, offset: i32) !u16 {
        return self.baseInst(.trace_col, interaction, column, 0, offset);
    }

    fn constant(self: *ProgramBuilder, value: u32) !u16 {
        if (self.constants.get(value)) |reg| return reg;
        const reg = try self.baseInst(.constant, 0, value, 0, 0);
        try self.constants.put(self.allocator, value, reg);
        return reg;
    }

    fn extInst(self: *ProgramBuilder, op: eval.ExtOpcode, a: u32, b: u32, c: u32, d: u32) !u32 {
        if (self.n_ext >= max_regs) return Error.TooManyRegisters;
        const dst = self.n_ext;
        self.n_ext += 1;
        try self.ext.append(self.allocator, .{ .op = op, .dst = @intCast(dst), .a = a, .b = b, .c = c, .d = d });
        return dst;
    }

    /// A base register lifted to the extension field.
    fn lift(self: *ProgramBuilder, reg: u16, zero: u16) !u32 {
        return self.extInst(.secure_col, reg, zero, zero, zero);
    }
    fn secure(self: *ProgramBuilder, limbs: [4]u16) !u32 {
        return self.extInst(.secure_col, limbs[0], limbs[1], limbs[2], limbs[3]);
    }
    fn param(self: *ProgramBuilder, slot: u32) !u32 {
        return self.extInst(.param, slot, 0, 0, 0);
    }
    fn add(self: *ProgramBuilder, a: u32, b: u32) !u32 {
        return self.extInst(.add, a, b, 0, 0);
    }
    fn sub(self: *ProgramBuilder, a: u32, b: u32) !u32 {
        return self.extInst(.sub, a, b, 0, 0);
    }
    fn mul(self: *ProgramBuilder, a: u32, b: u32) !u32 {
        return self.extInst(.mul, a, b, 0, 0);
    }
};

/// Lowers one AIR to its STWZEVA program, as the bytes stwo-zig parses (`eval.Program.parse`).
/// `pubs` are baked in as literals. The caller owns the result.
pub fn lowerProgram(allocator: std.mem.Allocator, air: ir.Air, pubs: []const M31, log_size: u32) ![]u8 {
    return lowerProgramMode(allocator, air, .{ .literal = pubs }, log_size);
}

/// How public inputs enter a program.
pub const PubMode = union(enum) {
    /// As base `constant` literals (one program per statement). Every stwo-zig evaluator accepts it.
    literal: []const M31,
    /// As base `param` k (`n_base_params = n_pub`): one program per AIR, the values bound at
    /// dispatch. stwo-zig's CPU evaluators reject base params; its Metal code generator reads
    /// them from `args.base_params`.
    param,
};

/// The program with public inputs as base parameters (see `PubMode.param`).
pub fn lowerTemplate(allocator: std.mem.Allocator, air: ir.Air, log_size: u32) !eval.Program {
    const bytes = try lowerProgramMode(allocator, air, .param, log_size);
    defer allocator.free(bytes);
    return eval.Program.parse(allocator, bytes);
}

fn lowerProgramMode(allocator: std.mem.Allocator, air: ir.Air, mode: PubMode, log_size: u32) ![]u8 {
    var b = ProgramBuilder{ .allocator = allocator };
    defer b.deinit();
    const pub_regs = try allocator.alloc(?u16, air.n_pub);
    defer allocator.free(pub_regs);
    @memset(pub_regs, null);

    // Live expressions: reachable from a constraint or a lookup.
    const live = try allocator.alloc(bool, air.exprs.len);
    defer allocator.free(live);
    @memset(live, false);
    for (air.constraints) |c| live[c] = true;
    for (air.lookups) |l| {
        live[l.mult] = true;
        for (l.vals) |v| live[v] = true;
    }
    var id = air.exprs.len;
    while (id > 0) {
        id -= 1;
        if (!live[id]) continue;
        switch (air.exprs[id]) {
            .add, .sub, .mul => |args| for (args) |x| {
                live[x] = true;
            },
            .neg => |x| live[x] = true,
            else => {},
        }
    }

    // Mask prologue. Main: every column's offsets in ascending order (the reference mask);
    // preprocessed: offset 0 of each column read.
    const offsets = try air.columnOffsets(allocator, .main);
    defer {
        for (offsets) |o| allocator.free(o);
        allocator.free(offsets);
    }
    const main_regs = try allocator.alloc([]u16, air.n_main);
    defer {
        for (main_regs) |r| allocator.free(r);
        allocator.free(main_regs);
    }
    for (offsets, main_regs, 0..) |offs, *regs, col| {
        regs.* = try allocator.alloc(u16, offs.len);
        for (offs, regs.*) |off, *r| r.* = try b.read(1, @intCast(col), off);
    }
    const pre_regs = try allocator.alloc(?u16, air.n_preprocessed);
    defer allocator.free(pre_regs);
    @memset(pre_regs, null);
    for (air.exprs) |e| switch (e) {
        .col => |c| if (c.tree == .preprocessed) {
            if (c.offset != 0) return Error.PreprocessedOffsetUnsupported;
            if (pre_regs[c.index] == null) pre_regs[c.index] = 0;
        },
        else => {},
    };
    for (pre_regs, 0..) |*r, col| if (r.* != null) {
        r.* = try b.read(0, @intCast(col), 0);
    };
    // Interaction: 4 limbs per batch at offset 0; the last batch also at −1 (read first).
    const n_batches = component_mod.nBatches(air);
    const inter_cur = try allocator.alloc(u16, 4 * n_batches);
    defer allocator.free(inter_cur);
    var inter_prev: [4]u16 = undefined;
    for (0..4 * n_batches) |k| {
        if (k + 4 >= 4 * n_batches) inter_prev[k % 4] = try b.read(2, @intCast(k), -1);
        inter_cur[k] = try b.read(2, @intCast(k), 0);
    }

    // Base expressions.
    const regs = try allocator.alloc(u16, air.exprs.len);
    defer allocator.free(regs);
    for (air.exprs, 0..) |e, i| {
        if (!live[i]) continue;
        regs[i] = switch (e) {
            .col => |c| switch (c.tree) {
                .main => main_regs[c.index][std.mem.indexOfScalar(i32, offsets[c.index], c.offset).?],
                .preprocessed => pre_regs[c.index].?,
            },
            .constant => |v| try b.constant(v),
            .@"pub" => |p| switch (mode) {
                .literal => |pubs| try b.constant(pubs[p].toU32()),
                .param => pub_regs[p] orelse blk: {
                    const r = try b.baseInst(.param, 0, p, 0, 0);
                    pub_regs[p] = r;
                    break :blk r;
                },
            },
            .add => |a| try b.baseInst(.add, 0, regs[a[0]], regs[a[1]], 0),
            .sub => |a| try b.baseInst(.sub, 0, regs[a[0]], regs[a[1]], 0),
            .mul => |a| try b.baseInst(.mul, 0, regs[a[0]], regs[a[1]], 0),
            .neg => |a| try b.baseInst(.neg, 0, regs[a], 0, 0),
        };
    }
    const zero = try b.constant(0);

    // Constraint roots, then LogUp batches.
    for (air.constraints) |c| try b.roots.append(allocator, try b.lift(regs[c], zero));
    var n_params: u32 = 0;
    if (n_batches != 0) {
        var width: u32 = 0;
        for (air.lookups) |l| width = @max(width, @as(u32, @intCast(l.vals.len)));
        n_params = width + 2;
        const z = try b.param(0);
        const shift = try b.param(width + 1);
        const nl = air.lookups.len;
        const nums = try allocator.alloc(u32, nl);
        defer allocator.free(nums);
        const dens = try allocator.alloc(u32, nl);
        defer allocator.free(dens);
        for (air.lookups, nums, dens) |l, *n, *d| {
            n.* = try b.lift(regs[l.mult], zero);
            // rel + Σ vᵢ αⁱ⁺¹ − z  (`component.denominator`).
            var acc = try b.extInst(.constant, l.rel, 0, 0, 0);
            for (l.vals, 0..) |v, i| {
                const term = try b.mul(try b.lift(regs[v], zero), try b.param(@intCast(i + 1)));
                acc = try b.add(acc, term);
            }
            d.* = try b.sub(acc, z);
        }
        const s = try allocator.alloc(u32, n_batches);
        defer allocator.free(s);
        for (s, 0..) |*sv, k| sv.* = try b.secure(inter_cur[4 * k ..][0..4].*);
        const s_prev = try b.secure(inter_prev);
        for (0..n_batches) |k| {
            const j = 2 * k;
            const pair = j + 1 < nl;
            const N = if (pair) try b.add(try b.mul(nums[j], dens[j + 1]), try b.mul(nums[j + 1], dens[j])) else nums[j];
            const D = if (pair) try b.mul(dens[j], dens[j + 1]) else dens[j];
            var diff: u32 = undefined;
            if (k + 1 < n_batches) {
                diff = if (k == 0) s[k] else try b.sub(s[k], s[k - 1]);
            } else {
                diff = try b.sub(s[k], s_prev);
                if (n_batches > 1) diff = try b.sub(diff, s[n_batches - 2]);
                diff = try b.add(diff, shift);
            }
            try b.roots.append(allocator, try b.sub(try b.mul(diff, D), N));
        }
    }
    if (b.roots.items.len == 0) return Error.NoConstraints;
    return encodeProgram(allocator, .{
        .flags = eval.Flag.prefinalized_logup,
        .semantic_hash = 0,
        .capability_bits = eval.Capability.ext_mul | eval.Capability.prefinalized_logup,
        .n_interactions = 3,
        .n_base_params = if (mode == .param) air.n_pub else 0,
        .n_ext_params = n_params,
        .n_constraints = @intCast(b.roots.items.len),
        .max_base_regs = @max(b.n_base, 1),
        .max_ext_regs = @max(b.n_ext, 1),
        .domain_log_size = log_size,
    }, b.base.items, b.ext.items, b.roots.items);
}

fn put(out: *std.ArrayList(u8), allocator: std.mem.Allocator, comptime T: type, value: T) !void {
    var bytes: [@sizeOf(T)]u8 = undefined;
    std.mem.writeInt(T, &bytes, value, .little);
    try out.appendSlice(allocator, &bytes);
}

fn fnv(hash: *u64, bytes: []const u8) void {
    for (bytes) |byte| {
        hash.* ^= byte;
        hash.* *%= 0x100000001b3;
    }
}

/// `STWZEVA/1` program bytes (header, five sections, payload; `encoding.rs`), semantic hash filled.
pub fn encodeProgram(
    allocator: std.mem.Allocator,
    header: eval.Header,
    base: []const eval.BaseInst,
    ext: []const eval.ExtInst,
    roots: []const u32,
) ![]u8 {
    var payload = std.ArrayList(u8).empty;
    defer payload.deinit(allocator);
    // base_consts and ext_consts are empty: literals live in `constant` instructions.
    for (base) |i| {
        try payload.append(allocator, @intFromEnum(i.op));
        try payload.append(allocator, i.interaction);
        try put(&payload, allocator, u16, i.dst);
        try put(&payload, allocator, u32, i.a);
        try put(&payload, allocator, u32, i.b);
        try put(&payload, allocator, i32, i.imm);
    }
    const ext_start = payload.items.len;
    for (ext) |i| {
        try payload.append(allocator, @intFromEnum(i.op));
        try payload.append(allocator, 0);
        try put(&payload, allocator, u16, i.dst);
        try put(&payload, allocator, u32, i.a);
        try put(&payload, allocator, u32, i.b);
        try put(&payload, allocator, u32, i.c);
        try put(&payload, allocator, u32, i.d);
    }
    const roots_start = payload.items.len;
    for (roots) |r| try put(&payload, allocator, u32, r);
    var hash: u64 = 0xcbf29ce484222325;
    fnv(&hash, payload.items);

    var out = std.ArrayList(u8).empty;
    errdefer out.deinit(allocator);
    try put(&out, allocator, u32, eval.magic);
    try put(&out, allocator, u16, eval.abi_major);
    try put(&out, allocator, u16, eval.abi_minor);
    try put(&out, allocator, u32, 5);
    try put(&out, allocator, u32, header.flags);
    try put(&out, allocator, u64, hash);
    try put(&out, allocator, u64, header.capability_bits);
    try put(&out, allocator, u32, header.n_interactions);
    try put(&out, allocator, u32, header.n_base_params);
    try put(&out, allocator, u32, header.n_ext_params);
    try put(&out, allocator, u32, header.n_constraints);
    try put(&out, allocator, u32, header.max_base_regs);
    try put(&out, allocator, u32, header.max_ext_regs);
    try put(&out, allocator, u32, 4); // secure extension degree
    try put(&out, allocator, u32, header.domain_log_size); // reserved[0]
    for (1..8) |_| try put(&out, allocator, u32, 0);
    try put(&out, allocator, u32, 0);
    std.debug.assert(out.items.len == eval.header_bytes);
    const Section = struct { kind: eval.SectionKind, size: u32, offset: usize, count: usize };
    const sections = [_]Section{
        .{ .kind = .base_consts, .size = 4, .offset = 0, .count = 0 },
        .{ .kind = .ext_consts, .size = 16, .offset = 0, .count = 0 },
        .{ .kind = .base_insts, .size = 16, .offset = 0, .count = base.len },
        .{ .kind = .ext_insts, .size = 20, .offset = ext_start, .count = ext.len },
        .{ .kind = .constraint_roots, .size = 4, .offset = roots_start, .count = roots.len },
    };
    for (sections) |s| {
        try put(&out, allocator, u32, @intFromEnum(s.kind));
        try put(&out, allocator, u32, s.size);
        try put(&out, allocator, u64, s.offset);
        try put(&out, allocator, u64, s.count);
    }
    try out.appendSlice(allocator, payload.items);
    return out.toOwnedSlice(allocator);
}

/// The bundle component of one AIR at `geometry`, its program parsed (and so validated) by
/// stwo-zig. Free with `composition.deinitComponent`.
pub fn lowerComponent(allocator: std.mem.Allocator, air: ir.Air, pubs: []const M31, geometry: Geometry) !composition.Component {
    const bytes = try lowerProgram(allocator, air, pubs, geometry.log_size);
    defer allocator.free(bytes);
    var program = try eval.Program.parse(allocator, bytes);
    errdefer program.deinit();
    const n_batches: u32 = @intCast(component_mod.nBatches(air));
    const label = try allocator.dupe(u8, air.name);
    errdefer allocator.free(label);
    const spans = try allocator.dupe(composition.TraceSpan, &.{
        .{ .tree = 1, .start = geometry.main_offset, .end = geometry.main_offset + air.n_main },
        .{ .tree = 2, .start = geometry.inter_offset, .end = geometry.inter_offset + 4 * n_batches },
    });
    errdefer allocator.free(spans);
    const pre = try allocator.alloc(u32, air.n_preprocessed);
    errdefer allocator.free(pre);
    for (pre, 0..) |*p, i| p.* = geometry.pre_offset + @as(u32, @intCast(i));
    const denominators = try composition.denominatorInverses(allocator, geometry.log_size, geometry.log_size + 1);
    errdefer allocator.free(denominators);
    const sources = try extSources(allocator, air);
    errdefer allocator.free(sources);
    const parts = try allocator.alloc(composition.Part, 1);
    parts[0] = .{ .rc_base = 0, .semantic_hash = program.header.semantic_hash, .program = program };
    return .{
        .label = label,
        .instance = 0,
        .trace_log_size = geometry.log_size,
        .evaluation_log_size = geometry.log_size + 1,
        .n_constraints = program.header.n_constraints,
        .random_coefficient_offset = geometry.rc_offset,
        .trace_spans = spans,
        .preprocessed_indices = pre,
        .denominator_inverses = denominators,
        .ext_sources = sources,
        .parts = parts,
    };
}

/// One system part: the AIR, its public inputs and its place in the trees.
pub const Lowered = struct {
    air: *const ir.Air,
    pubs: []const M31,
    geometry: Geometry,
};

/// `STWZEVA\0` bundle bytes (format version 1, `bundle.rs`) of `components`, in order. The
/// result parses with `composition.Bundle.parse`.
pub fn encodeBundle(allocator: std.mem.Allocator, components: []const composition.Component) ![]u8 {
    var out = std.ArrayList(u8).empty;
    errdefer out.deinit(allocator);
    var total: u64 = 0;
    var max_eval: u32 = 0;
    for (components) |c| {
        total += c.n_constraints;
        max_eval = @max(max_eval, c.evaluation_log_size);
    }
    try out.appendSlice(allocator, &composition.magic);
    try put(&out, allocator, u32, composition.version);
    try put(&out, allocator, u32, 1_000_000); // MAX_KERNEL_INSTRUCTIONS
    try put(&out, allocator, u64, total);
    try put(&out, allocator, u32, max_eval);
    try put(&out, allocator, u32, @intCast(components.len));
    try put(&out, allocator, u64, 0); // plan hash, below
    for (components) |c| {
        try put(&out, allocator, u16, @intCast(c.label.len));
        try put(&out, allocator, u16, 0);
        try put(&out, allocator, u32, c.instance);
        try put(&out, allocator, u32, c.trace_log_size);
        try put(&out, allocator, u32, c.evaluation_log_size);
        try put(&out, allocator, u32, c.n_constraints);
        try put(&out, allocator, u32, c.random_coefficient_offset);
        try put(&out, allocator, u32, @intCast(c.trace_spans.len));
        try put(&out, allocator, u32, @intCast(c.preprocessed_indices.len));
        try put(&out, allocator, u32, @intCast(c.denominator_inverses.len));
        try put(&out, allocator, u32, @intCast(c.ext_sources.len));
        try put(&out, allocator, u32, @intCast(c.parts.len));
        try out.appendSlice(allocator, c.label);
        for (c.trace_spans) |s| {
            try put(&out, allocator, u32, s.tree);
            try put(&out, allocator, u32, s.start);
            try put(&out, allocator, u32, s.end);
        }
        for (c.preprocessed_indices) |p| try put(&out, allocator, u32, p);
        for (c.denominator_inverses) |d| try put(&out, allocator, u32, d);
        for (c.ext_sources) |s| {
            const words: [8]u32 = switch (s) {
                .constant => |v| .{ 0, 0, 0, 0, v[0], v[1], v[2], v[3] },
                .lookup_z => .{ 1, 0, 0, 0, 0, 0, 0, 0 },
                .lookup_alpha_power => |p| .{ 2, p, 0, 0, 0, 0, 0, 0 },
                .claimed_sum_scaled => .{ 3, 0, 0, 0, 0, 0, 0, 0 },
                .lookup_alpha_power_scaled => |x| .{ 4, x.power, x.scale, 0, 0, 0, 0, 0 },
            };
            for (words) |w| try put(&out, allocator, u32, w);
        }
        for (c.parts) |part| {
            const bytes = try reencode(allocator, part.program);
            defer allocator.free(bytes);
            try put(&out, allocator, u32, part.rc_base);
            try put(&out, allocator, u32, @intCast(bytes.len));
            try put(&out, allocator, u64, part.program.header.semantic_hash);
            try out.appendSlice(allocator, bytes);
        }
    }
    // Version 1 bundles carry the FNV-1a of the encoding with the plan-hash field zeroed.
    var hash: u64 = 0xcbf29ce484222325;
    fnv(&hash, out.items);
    std.mem.writeInt(u64, out.items[32..40], hash, .little);
    return out.toOwnedSlice(allocator);
}

/// Bytes of a parsed program (constants are always instructions in our programs).
fn reencode(allocator: std.mem.Allocator, program: eval.Program) ![]u8 {
    std.debug.assert(program.base_consts.len == 0 and program.ext_consts.len == 0);
    return encodeProgram(allocator, program.header, program.base_insts, program.ext_insts, program.constraint_roots);
}

// ------------------------------------------------------------------ component

/// A component whose composition is evaluated by stwo-zig's captured-AIR runtime over the
/// lowered STWZEVA program, with the mask geometry of our reference `component.Component`.
/// - Domain (prover): `cairo.proving.air.component.Component` (the SIMD STWZEVA interpreter,
///   or a native kernel from the C code generator when `native_executor` is set).
/// - Point (verifier side): `evalAtPoint`, the STWZEVA program interpreted over QM31 against our
///   mask. (stwo-zig's own `RuntimeComponent` does the same but requires every column of a span
///   to be read at least once; every block AIR now is: `block_coin`'s four unread columns were
///   removed.)
pub const Component = struct {
    reference: *const component_mod.Component,
    captured: *const composition.Component,
    prover: Captured,
    preprocessed_logs: []u32,

    const Adapter = core_air_derive.ComponentAdapter(
        @This(),
        prover_component.ComponentProver,
        prover_component.Trace,
        prover_air_accumulation.DomainEvaluationAccumulator,
    );

    /// `reference.logup` must be set (when the AIR has lookups) before proving.
    pub fn init(allocator: std.mem.Allocator, reference: *const component_mod.Component, captured: *const composition.Component, n_preprocessed_total: usize) !Component {
        const logs = try allocator.alloc(u32, n_preprocessed_total);
        @memset(logs, reference.log_size);
        const lu = reference.logup orelse component_mod.Logup{ .z = QM31.zero(), .alpha = QM31.zero(), .claimed_sum = QM31.zero() };
        return .{
            .reference = reference,
            .captured = captured,
            .prover = Captured.init(allocator, captured, logs, reference.log_size + 1, lu.z, lu.alpha, lu.claimed_sum),
            .preprocessed_logs = logs,
        };
    }

    pub fn asProverComponent(self: *const @This()) prover_component.ComponentProver {
        return Adapter.asProverComponent(self);
    }
    pub fn asVerifierComponent(self: *const @This()) core_air_components.Component {
        return Adapter.asVerifierComponent(self);
    }

    pub fn nConstraints(self: *const @This()) usize {
        return self.captured.n_constraints;
    }
    pub fn maxConstraintLogDegreeBound(self: *const @This()) u32 {
        return self.captured.evaluation_log_size;
    }
    pub fn traceLogDegreeBounds(self: *const @This(), allocator: std.mem.Allocator) !core_air_components.TraceLogDegreeBounds {
        return self.reference.traceLogDegreeBounds(allocator);
    }
    pub fn maskPoints(self: *const @This(), allocator: std.mem.Allocator, point: CirclePointQM31, max_log_degree_bound: u32) !core_air_components.MaskPoints {
        return self.reference.maskPoints(allocator, point, max_log_degree_bound);
    }
    pub fn preprocessedColumnIndices(self: *const @This(), allocator: std.mem.Allocator) ![]usize {
        return self.reference.preprocessedColumnIndices(allocator);
    }

    pub fn evaluateConstraintQuotientsAtPoint(
        self: *const @This(),
        point: CirclePointQM31,
        mask: *const core_air_components.MaskValues,
        accumulator: *core_air_accumulation.PointEvaluationAccumulator,
        max_log_degree_bound: u32,
    ) !void {
        if (max_log_degree_bound != self.reference.log_size) return error.LiftingUnsupported;
        const params = try self.prover.runtime.extensionParameters();
        defer self.prover.runtime.allocator.free(params);
        const denominator_inv = try core_constraints.cosetVanishing(
            QM31,
            canonic.CanonicCoset.new(self.reference.log_size).coset(),
            point,
        ).inv();
        for (self.captured.parts) |part|
            try evalAtPoint(self.prover.runtime.allocator, part.program, self.reference, mask, params, denominator_inv, accumulator);
    }

    pub fn evaluateConstraintQuotientsOnDomain(
        self: *const @This(),
        trace: *const prover_component.Trace,
        accumulator: *prover_air_accumulation.DomainEvaluationAccumulator,
    ) !void {
        // The captured runtime addresses three trees; a system without lookups has two.
        if (trace.polys.items.len >= 3) return self.prover.evaluateConstraintQuotientsOnDomain(trace, accumulator);
        var trees: [3][]const prover_component.Poly = .{ &.{}, &.{}, &.{} };
        for (trace.polys.items, 0..) |t, i| trees[i] = t;
        var padded = trace.*;
        padded.polys = .{ .items = &trees };
        return self.prover.evaluateConstraintQuotientsOnDomain(&padded, accumulator);
    }
};

/// Interprets `program` at the OODS point over QM31 (as `RuntimeComponent.evaluateProgram`),
/// reading the mask laid out by our reference component.
pub fn evalAtPoint(
    allocator: std.mem.Allocator,
    program: eval.Program,
    reference: *const component_mod.Component,
    mask: *const core_air_components.MaskValues,
    params: []const QM31,
    denominator_inv: QM31,
    accumulator: *core_air_accumulation.PointEvaluationAccumulator,
) !void {
    if (program.header.n_base_params != 0 or program.header.n_ext_params != params.len) return error.InvalidProgram;
    const base = try allocator.alloc(QM31, program.header.max_base_regs);
    defer allocator.free(base);
    const ext = try allocator.alloc(QM31, program.header.max_ext_regs);
    defer allocator.free(ext);
    const n_inter = 4 * component_mod.nBatches(reference.air);
    for (program.base_insts) |inst| {
        base[inst.dst] = switch (inst.op) {
            .trace_col, .preprocessed_col => switch (inst.interaction) {
                0 => mask.items[0][reference.pre_offset + inst.a][0],
                1 => blk: {
                    const at = std.mem.indexOfScalar(i32, reference.main_offsets[inst.a], inst.imm) orelse return error.MissingMaskValue;
                    break :blk mask.items[1][reference.main_offset + inst.a][at];
                },
                2 => blk: {
                    // Last batch: samples (prev, point); others: (point).
                    const last = inst.a + 4 >= n_inter;
                    const at: usize = if (!last) 0 else if (inst.imm == -1) 0 else 1;
                    if (!last and inst.imm != 0) return error.MissingMaskValue;
                    break :blk mask.items[2][reference.inter_offset + inst.a][at];
                },
                else => return error.MissingMaskValue,
            },
            .param => return error.InvalidProgram,
            .constant => QM31.fromBase(M31.fromCanonical(inst.a)),
            .add => base[inst.a].add(base[inst.b]),
            .sub => base[inst.a].sub(base[inst.b]),
            .mul => base[inst.a].mul(base[inst.b]),
            .neg => base[inst.a].neg(),
            .inv => try base[inst.a].inv(),
        };
    }
    for (program.ext_insts) |inst| {
        ext[inst.dst] = switch (inst.op) {
            .secure_col => QM31.fromPartialEvals(.{ base[inst.a], base[inst.b], base[inst.c], base[inst.d] }),
            .param => params[inst.a],
            .constant => QM31.fromU32Unchecked(inst.a, inst.b, inst.c, inst.d),
            .add => ext[inst.a].add(ext[inst.b]),
            .sub => ext[inst.a].sub(ext[inst.b]),
            .mul => ext[inst.a].mul(ext[inst.b]),
            .neg => ext[inst.a].neg(),
        };
    }
    for (program.constraint_roots) |root| accumulator.accumulate(ext[root].mul(denominator_inv));
}

// ------------------------------------------------------------- C code generator

/// The AIRs without public inputs compiled by stwo-zig's C code generator at build time
/// (`build.zig`, `stwzeva_cpu_aot`). Public inputs are literals in a program, so an AIR with them
/// has one program per statement; these have one program each.
pub const aot_airs = [_][]const u8{ "byte_table", "byte_user", "block_reader", "block_tables", "block_msg", "block_walk", "block_sha" };
/// The committed bundle the build generates C from (`testdata/stwzeva/pubfree.bin`).
pub const aot_bundle_path = "testdata/stwzeva/pubfree.bin";
const aot_log_size: u32 = 8;

fn aotJson(comptime name: []const u8) []const u8 {
    return @embedFile("air:" ++ name);
}

/// The bundle of `aot_airs` (laid out as one system at 2^8 rows).
pub fn aotBundle(a: std.mem.Allocator) ![]u8 {
    var comps: [aot_airs.len]composition.Component = undefined;
    var g = Geometry{ .log_size = aot_log_size };
    inline for (aot_airs, 0..) |name, i| {
        const air = (try ir.Air.parseJson(a, aotJson(name))).value;
        if (air.n_pub != 0) return error.PublicInputsInAotAir;
        comps[i] = try lowerComponent(a, air, &.{}, g);
        g.pre_offset += air.n_preprocessed;
        g.main_offset += air.n_main;
        g.inter_offset += @intCast(4 * component_mod.nBatches(air));
        g.rc_offset += comps[i].n_constraints;
    }
    return encodeBundle(a, &comps);
}

// ---------------------------------------------------------------------- tests

const testing = std.testing;
const P = core.fields.m31.Modulus;

fn randM31(r: std.Random) M31 {
    return M31.fromCanonical(r.uintLessThan(u32, P));
}
fn randQM31(r: std.Random) QM31 {
    return QM31.fromM31(randM31(r), randM31(r), randM31(r), randM31(r));
}

/// What a parity run compared.
pub const ParityReport = struct {
    rows: usize,
    constraints: usize,
    instructions: usize,
    runtime_checked: bool,
};

/// Parity (a) for one AIR: on a random trace (arbitrary values on the evaluation domain) and a
/// random OODS point and mask, the composition of our interpreter (`component.Component`) equals
/// stwo-zig's captured-AIR evaluation of the lowered program, on the domain (SIMD STWZEVA
/// interpreter) and at the point (`evalAtPoint`, and stwo-zig's `RuntimeComponent` when every
/// column is read). `pubs` are random.
pub fn checkParity(a: std.mem.Allocator, air: ir.Air, log_size: u32, seed: u64) !ParityReport {
    return checkParityWith(a, air, log_size, seed, null);
}

/// `checkParity`, the domain evaluated by a native kernel of `native` (which must have one).
pub fn checkParityWith(a: std.mem.Allocator, air: ir.Air, log_size: u32, seed: u64, native: ?Native) !ParityReport {
    var prng = std.Random.DefaultPrng.init(seed);
    const r = prng.random();
    const pubs = try a.alloc(M31, air.n_pub);
    for (pubs) |*p| p.* = randM31(r);
    var reference = try component_mod.Component.init(a, air, log_size, pubs);
    const n_batches = component_mod.nBatches(air);
    const trees: usize = if (n_batches != 0) 3 else 2;
    reference.n_trees = trees;
    if (n_batches != 0) reference.logup = .{ .z = randQM31(r), .alpha = randQM31(r), .claimed_sum = randQM31(r) };
    var captured = try lowerComponent(a, air, pubs, .{ .log_size = log_size });
    var wrapped = try Component.init(a, &reference, &captured, air.n_preprocessed);
    if (native) |executor| {
        if (executor.resolve(cairo.proving.air.native_evaluator.identity(captured.parts[0].program)) == null) return error.NoNativeKernel;
        wrapped.prover.native_executor = executor;
    }
    const n_constraints = reference.nConstraints();
    try testing.expectEqual(n_constraints, wrapped.nConstraints());

    // Domain.
    const eval_log = log_size + 1;
    const n_eval = @as(usize, 1) << @intCast(eval_log);
    const counts = [3]usize{ air.n_preprocessed, air.n_main, 4 * n_batches };
    var tree_polys: [3][]prover_component.Poly = undefined;
    for (&tree_polys, counts) |*t, n| {
        t.* = try a.alloc(prover_component.Poly, n);
        for (t.*) |*poly| {
            const values = try a.alloc(M31, n_eval);
            for (values) |*v| v.* = randM31(r);
            poly.* = .{ .log_size = eval_log, .values = values };
        }
    }
    var items: [3][]const prover_component.Poly = .{ tree_polys[0], tree_polys[1], tree_polys[2] };
    const trace = prover_component.Trace{ .polys = .{ .items = items[0..trees] } };
    const rc = randQM31(r);
    var acc_ref = try prover_air_accumulation.DomainEvaluationAccumulator.init(a, rc, eval_log, n_constraints);
    try reference.evaluateConstraintQuotientsOnDomain(&trace, &acc_ref);
    var acc_low = try prover_air_accumulation.DomainEvaluationAccumulator.init(a, rc, eval_log, n_constraints);
    try wrapped.evaluateConstraintQuotientsOnDomain(&trace, &acc_low);
    const want = try acc_ref.finalize();
    const got = try acc_low.finalize();
    for (want.columns, got.columns) |w, g| try testing.expectEqualSlices(M31, w, g);

    // Point.
    const point = CirclePointQM31{ .x = randQM31(r), .y = randQM31(r) };
    var points = try reference.maskPoints(a, point, log_size);
    const mask_items = try a.alloc([][]QM31, points.items.len);
    for (points.items, mask_items) |tree, *out| {
        out.* = try a.alloc([]QM31, tree.len);
        for (tree, out.*) |col, *vals| {
            vals.* = try a.alloc(QM31, col.len);
            for (vals.*) |*v| v.* = randQM31(r);
        }
    }
    _ = &points;
    const mask = core_air_components.MaskValues.initOwned(mask_items);
    var p_ref = core_air_accumulation.PointEvaluationAccumulator.init(rc);
    try reference.evaluateConstraintQuotientsAtPoint(point, &mask, &p_ref, log_size);
    var p_low = core_air_accumulation.PointEvaluationAccumulator.init(rc);
    try wrapped.evaluateConstraintQuotientsAtPoint(point, &mask, &p_low, log_size);
    try testing.expect(p_ref.finalize().eql(p_low.finalize()));

    // stwo-zig's own verifier-side runtime needs a read of every column.
    var all_read = true;
    for (reference.main_offsets) |o| all_read = all_read and o.len != 0;
    if (all_read) {
        var p_rt = core_air_accumulation.PointEvaluationAccumulator.init(rc);
        try wrapped.prover.runtime.asComponent().evaluateConstraintQuotientsAtPoint(point, &mask, &p_rt, log_size);
        try testing.expect(p_ref.finalize().eql(p_rt.finalize()));
    }
    const program = captured.parts[0].program;
    return .{
        .rows = n_eval,
        .constraints = n_constraints,
        .instructions = program.base_insts.len + program.ext_insts.len,
        .runtime_checked = all_read,
    };
}

test "stwzeva: lowered AIRs match the interpreter's composition (domain and OODS point)" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const block_system = @import("../block/system.zig");
    const Named = struct { name: []const u8, json: []const u8 };
    var list = std.ArrayList(Named).empty;
    try list.append(a, .{ .name = "header_chain", .json = @embedFile("air:header_chain") });
    try list.append(a, .{ .name = "byte_table", .json = @embedFile("air:byte_table") });
    try list.append(a, .{ .name = "byte_user", .json = @embedFile("air:byte_user") });
    try list.append(a, .{ .name = "block_reader", .json = @embedFile("air:block_reader") });
    for (block_system.names, block_system.jsons) |n, j| try list.append(a, .{ .name = n, .json = j });
    for (list.items, 0..) |item, i| {
        const air = (try ir.Air.parseJson(a, item.json)).value;
        const rep = checkParity(a, air, 6, 0x5717_2e7a + i) catch |e| {
            std.debug.print("{s}: parity failed: {s}\n", .{ item.name, @errorName(e) });
            return e;
        };
        std.debug.print("stwzeva parity {s}: {d} constraints, {d} instructions, {d} rows, runtime={}\n", .{ item.name, rep.constraints, rep.instructions, rep.rows, rep.runtime_checked });
        // Every block AIR reads every main column, so stwo-zig's own runtime (and the resident GPU
        // geometry built from the programs) checks it too.
        if (std.mem.startsWith(u8, item.name, "block_") or i >= 4) try testing.expect(rep.runtime_checked);
    }
}

test "stwzeva: bundles round-trip through stwo-zig's parser" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const airs = [_]ir.Air{
        (try ir.Air.parseJson(a, @embedFile("air:byte_table"))).value,
        (try ir.Air.parseJson(a, @embedFile("air:byte_user"))).value,
    };
    var comps: [2]composition.Component = undefined;
    comps[0] = try lowerComponent(a, airs[0], &.{}, .{ .log_size = 8 });
    comps[1] = try lowerComponent(a, airs[1], &.{}, .{ .log_size = 8, .pre_offset = 1, .main_offset = 1, .inter_offset = 4, .rc_offset = comps[0].n_constraints });
    const bytes = try encodeBundle(a, &comps);
    var bundle = try composition.Bundle.parse(a, bytes);
    defer bundle.deinit();
    try testing.expectEqual(@as(usize, 2), bundle.components.len);
    for (bundle.components, comps) |got, want| {
        try testing.expectEqual(want.parts[0].program.header.semantic_hash, got.parts[0].program.header.semantic_hash);
        try testing.expectEqualSlices(u32, want.denominator_inverses, got.denominator_inverses);
    }
}

test "stwzeva: the committed C-codegen bundle is the current lowering" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const bytes = try aotBundle(a);
    // `STWZEVA_WRITE_BUNDLE=1` regenerates the file (then rebuild: the C kernels come from it).
    if (std.process.hasEnvVarConstant("STWZEVA_WRITE_BUNDLE")) {
        try std.fs.cwd().makePath("testdata/stwzeva");
        try std.fs.cwd().writeFile(.{ .sub_path = aot_bundle_path, .data = bytes });
    }
    const committed = try std.fs.cwd().readFileAlloc(a, aot_bundle_path, 64 << 20);
    try testing.expectEqualSlices(u8, committed, bytes);
}

test "stwzeva: stwo-zig's C code generator's kernels match the interpreter's composition" {
    var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const aot = @import("stwzeva_cpu_aot");
    try testing.expectEqual(@as(usize, aot_airs.len), aot.generated_program_count);
    inline for (aot_airs, 0..) |name, i| {
        const air = (try ir.Air.parseJson(a, aotJson(name))).value;
        for ([_]u32{ 6, 10 }) |log_size| {
            const rep = try checkParityWith(a, air, log_size, 0xc0de + i, aot.executor());
            std.debug.print("stwzeva C kernel {s} (log {d}): {d} constraints match\n", .{ name, log_size, rep.constraints });
        }
    }
}

// ------------------------------------------------------------- row tiles

pub const trace_lease = device_stage.trace_lease;

/// Row tiles of a component's coefficient-only columns for our interpreter's composition
/// (`component.Tiling`), planned by stwo-zig's `trace_lease.Tiles` from the lowered program's read
/// sites: the composition then holds about `budget` bytes of expanded columns instead of every
/// column of the component on the whole evaluation domain.
pub const TileSource = struct {
    allocator: std.mem.Allocator,
    captured: *const composition.Component,
    budget: usize,
    trace: ?*const prover_component.Trace = null,
    tiles: ?trace_lease.Tiles = null,

    pub fn tiling(self: *TileSource) component_mod.Tiling {
        return .{ .ctx = self, .plan = plan, .load = load, .resolve = resolve, .release = release };
    }

    fn cast(ctx: *anyopaque) *TileSource {
        return @ptrCast(@alignCast(ctx));
    }

    fn plan(ctx: *anyopaque, trace: *const prover_component.Trace) anyerror!?component_mod.TilePlan {
        const self = cast(ctx);
        if (trace.polys.items.len < 3) return null;
        self.trace = trace;
        self.tiles = try trace_lease.Tiles.plan(self.allocator, trace, self.captured, self.budget, self.budget);
        const t = &(self.tiles orelse return null);
        return .{ .tiles = t.tileCount(), .rows = t.tileRows() };
    }

    fn load(ctx: *anyopaque, tile: usize) anyerror!void {
        try cast(ctx).tiles.?.load(tile);
    }

    fn resolve(ctx: *anyopaque, tree: u8, local: u32, offset: i32) anyerror!component_mod.Resolved {
        const self = cast(ctx);
        const eval_log = self.captured.evaluation_log_size;
        const key = try trace_lease.address(self.trace.?, self.captured, tree, local);
        if (self.tiles.?.view(key, offset)) |v| return .{
            .values = v.values,
            .shift = @intCast(eval_log - v.coset_log + 1),
            .base = v.base,
            .row_indexed = v.row_indexed,
        };
        // Read in place: a column already on its evaluation domain.
        const column = self.trace.?.polys.items[key.tree][key.column];
        if (column.values.len == 0) return error.InvalidTraceShape;
        return .{ .values = column.values, .shift = @intCast(eval_log - column.log_size + 1) };
    }

    fn release(ctx: *anyopaque) void {
        const self = cast(ctx);
        if (self.tiles) |*t| t.deinit();
        self.tiles = null;
        self.trace = null;
    }
};
