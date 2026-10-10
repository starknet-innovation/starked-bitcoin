//! Replays a Lean-defined glue program (`lean/StarkedAir/Circuit/Gadgets.lean`, exported to
//! `airs/*_glue.json`) into circuit builder calls. Each op becomes the builder call the Lean
//! semantics (`Op.holds`) describes; registers are single-assignment (checked), so one Lean
//! register is one circuit variable. Hooks hand control to host code (the trusted verifier).

const std = @import("std");
const core = @import("stwo_core");
const circuit = @import("stwo_circuit_frontend");

const builder = circuit.builder;
const Context = builder.context.Context;
const Var = builder.circuit.Var;
const QM31 = core.fields.qm31.QM31;
const M31 = core.fields.m31.M31;

pub const node_json = @embedFile("air:node_glue");
pub const leaf_json = @embedFile("air:leaf_glue");

const Hint = union(enum) {
    ext: u32,
    reg: u32,
    coord: struct { j: u32, h: *const Hint },
    is_eq: struct { h: *const Hint, k: u32 },
};

const Op = union(enum) {
    @"const": struct { o: u32, v: [4]u32 },
    add: [3]u32,
    sub: [3]u32,
    mul: [3]u32,
    eq: [2]u32,
    guess_m31: struct { o: u32, h: Hint },
    guess_u16: struct { o: u32, h: Hint },
    m31_to_u32: [2]u32,
    blake_g: [7]u32,
    triple_xor: [4]u32,
    hook: struct { id: u32, args: []const u32, outs: []const u32 },
    zero: u32,
    one: u32,
    inv: [2]u32,
    pointwise_mul: [3]u32,
    unused: u32,
};

pub const Program = struct {
    ops: []const Op,
    results: []const u32,
    n_regs: u32,
};

fn num(v: std.json.Value) !u32 {
    return switch (v) {
        .integer => |i| std.math.cast(u32, i) orelse error.BadGlue,
        else => error.BadGlue,
    };
}

fn nums(a: std.mem.Allocator, v: std.json.Value) ![]const u32 {
    const items = switch (v) {
        .array => |arr| arr.items,
        else => return error.BadGlue,
    };
    const out = try a.alloc(u32, items.len);
    for (out, items) |*o, x| o.* = try num(x);
    return out;
}

fn parseHint(a: std.mem.Allocator, v: std.json.Value) !Hint {
    const obj = switch (v) {
        .object => |o| o,
        else => return error.BadGlue,
    };
    if (obj.get("ext")) |x| return .{ .ext = try num(x) };
    if (obj.get("reg")) |x| return .{ .reg = try num(x) };
    if (obj.get("coord")) |x| {
        const h = try a.create(Hint);
        h.* = try parseHint(a, x.array.items[1]);
        return .{ .coord = .{ .j = try num(x.array.items[0]), .h = h } };
    }
    if (obj.get("is_eq")) |x| {
        const h = try a.create(Hint);
        h.* = try parseHint(a, x.array.items[0]);
        return .{ .is_eq = .{ .h = h, .k = try num(x.array.items[1]) } };
    }
    return error.BadGlue;
}

/// Parses an exported program (allocations in `a`).
pub fn parse(a: std.mem.Allocator, json: []const u8) !Program {
    const root = (try std.json.parseFromSliceLeaky(std.json.Value, a, json, .{})).object;
    if (!std.mem.eql(u8, root.get("schema").?.string, "starked-glue-v1")) return error.BadGlue;
    const items = root.get("ops").?.array.items;
    const ops = try a.alloc(Op, items.len);
    var max_reg: u32 = 0;
    for (ops, items) |*op, item| {
        const f = item.array.items;
        const tag = f[0].string;
        op.* = if (std.mem.eql(u8, tag, "const"))
            .{ .@"const" = .{ .o = try num(f[1]), .v = .{ try num(f[2]), try num(f[3]), try num(f[4]), try num(f[5]) } } }
        else if (std.mem.eql(u8, tag, "add"))
            .{ .add = .{ try num(f[1]), try num(f[2]), try num(f[3]) } }
        else if (std.mem.eql(u8, tag, "sub"))
            .{ .sub = .{ try num(f[1]), try num(f[2]), try num(f[3]) } }
        else if (std.mem.eql(u8, tag, "mul"))
            .{ .mul = .{ try num(f[1]), try num(f[2]), try num(f[3]) } }
        else if (std.mem.eql(u8, tag, "eq"))
            .{ .eq = .{ try num(f[1]), try num(f[2]) } }
        else if (std.mem.eql(u8, tag, "guess_m31"))
            .{ .guess_m31 = .{ .o = try num(f[1]), .h = try parseHint(a, f[2]) } }
        else if (std.mem.eql(u8, tag, "guess_u16"))
            .{ .guess_u16 = .{ .o = try num(f[1]), .h = try parseHint(a, f[2]) } }
        else if (std.mem.eql(u8, tag, "m31_to_u32"))
            .{ .m31_to_u32 = .{ try num(f[1]), try num(f[2]) } }
        else if (std.mem.eql(u8, tag, "blake_g")) blk: {
            var g: [7]u32 = undefined;
            for (&g, f[1..8]) |*x, y| x.* = try num(y);
            break :blk .{ .blake_g = g };
        } else if (std.mem.eql(u8, tag, "triple_xor"))
            .{ .triple_xor = .{ try num(f[1]), try num(f[2]), try num(f[3]), try num(f[4]) } }
        else if (std.mem.eql(u8, tag, "hook"))
            .{ .hook = .{ .id = try num(f[1]), .args = try nums(a, f[2]), .outs = try nums(a, f[3]) } }
        else if (std.mem.eql(u8, tag, "zero"))
            .{ .zero = try num(f[1]) }
        else if (std.mem.eql(u8, tag, "one"))
            .{ .one = try num(f[1]) }
        else if (std.mem.eql(u8, tag, "inv"))
            .{ .inv = .{ try num(f[1]), try num(f[2]) } }
        else if (std.mem.eql(u8, tag, "pointwise_mul"))
            .{ .pointwise_mul = .{ try num(f[1]), try num(f[2]), try num(f[3]) } }
        else if (std.mem.eql(u8, tag, "unused"))
            .{ .unused = try num(f[1]) }
        else
            return error.BadGlue;
        for (f[1..]) |x| if (x == .integer) {
            max_reg = @max(max_reg, try num(x));
        };
        if (op.* == .hook) for (op.hook.outs) |o| {
            max_reg = @max(max_reg, o);
        };
    }
    return .{ .ops = ops, .results = try nums(a, root.get("results").?), .n_regs = max_reg + 4 };
}

/// Replays `prog` into `ctx`. `ext` supplies guessed values (`QM31` mode) or is ignored
/// (topology mode). `hooks.call(id, args)` runs host code and returns the hook's output
/// variables. Returns the result registers' variables (scratch-owned).
pub fn run(comptime V: type, ctx: *Context(V), prog: *const Program, ext: []const V, hooks: anytype) ![]Var {
    const regs = try ctx.scratch().alloc(?Var, prog.n_regs);
    @memset(regs, null);
    const R = struct {
        regs: []?Var,
        fn get(self: @This(), r: u32) !Var {
            return self.regs[r] orelse error.GlueRegisterUndefined;
        }
        fn set(self: @This(), r: u32, v: Var) !void {
            if (self.regs[r] != null) return error.GlueRegisterRedefined;
            self.regs[r] = v;
        }
    };
    const rr = R{ .regs = regs };
    for (prog.ops) |op| switch (op) {
        .@"const" => |c| try rr.set(c.o, try ctx.constant(QM31.fromU32Unchecked(c.v[0], c.v[1], c.v[2], c.v[3]))),
        .add => |g| try rr.set(g[0], try ctx.add(try rr.get(g[1]), try rr.get(g[2]))),
        .sub => |g| try rr.set(g[0], try ctx.sub(try rr.get(g[1]), try rr.get(g[2]))),
        .mul => |g| try rr.set(g[0], try ctx.mul(try rr.get(g[1]), try rr.get(g[2]))),
        .eq => |g| try ctx.eq(try rr.get(g[0]), try rr.get(g[1])),
        .guess_m31 => |g| try rr.set(g.o, try ctx.guessM31(try hintValue(V, ctx, rr, ext, &g.h))),
        .guess_u16 => |g| try rr.set(g.o, try ctx.guessU16(try hintValue(V, ctx, rr, ext, &g.h))),
        .m31_to_u32 => |g| try rr.set(g[0], (try builder.blake.m31ToU32(V, ctx, try rr.get(g[1]))).get()),
        .blake_g => |g| {
            var in: [6]builder.wrappers.U32Wrapper(Var) = undefined;
            for (&in, g[1..7]) |*w, r| w.* = .newUnsafe(try rr.get(r));
            const out = try builder.blake.blakeGGate(V, ctx, in[0], in[1], in[2], in[3], in[4], in[5]);
            for (out, 0..) |w, k| try rr.set(g[0] + @as(u32, @intCast(k)), w.get());
        },
        .triple_xor => |g| try rr.set(g[0], (try builder.blake.tripleXor(V, ctx, .newUnsafe(try rr.get(g[1])), .newUnsafe(try rr.get(g[2])), .newUnsafe(try rr.get(g[3])))).get()),
        .zero => |o| try rr.set(o, ctx.zero()),
        .one => |o| try rr.set(o, ctx.one()),
        .inv => |g| try rr.set(g[0], try ctx.inv(try rr.get(g[1]))),
        .pointwise_mul => |g| try rr.set(g[0], try ctx.pointwiseMul(try rr.get(g[1]), try rr.get(g[2]))),
        .unused => |r| try ctx.markAsUnused(try rr.get(r)),
        .hook => |h| {
            const args = try ctx.scratch().alloc(Var, h.args.len);
            for (args, h.args) |*v, r| v.* = try rr.get(r);
            const outs = try hooks.call(h.id, args);
            if (outs.len != h.outs.len) return error.GlueHookArity;
            for (h.outs, outs) |r, v| try rr.set(r, v);
        },
    };
    const res = try ctx.scratch().alloc(Var, prog.results.len);
    for (res, prog.results) |*v, r| v.* = try rr.get(r);
    return res;
}

fn hintValue(comptime V: type, ctx: anytype, rr: anytype, ext: []const V, h: *const Hint) !V {
    if (V != QM31) return .{};
    return switch (h.*) {
        .ext => |k| ext[k],
        .reg => |r| ctx.get(try rr.get(r)),
        .coord => |c| QM31.fromBase(M31.fromCanonical(builder.ivalue.limbs(try hintValue(V, ctx, rr, ext, c.h))[c.j])),
        .is_eq => |e| QM31.fromBase(M31.fromCanonical(if (builder.ivalue.limbs(try hintValue(V, ctx, rr, ext, e.h))[0] == e.k) 1 else 0)),
    };
}

/// Test helper: two circuits have the same gates, in the same order, over the same variables.
pub fn expectSameCircuit(a: *const builder.circuit.Circuit, b: *const builder.circuit.Circuit) !void {
    const t = std.testing;
    try t.expectEqual(a.n_vars, b.n_vars);
    inline for (.{ "add", "sub", "mul", "pointwise_mul", "eq", "triple_xor", "m31_to_u32", "blake_g_gate", "output" }) |f| {
        try t.expectEqualSlices(u8, std.mem.sliceAsBytes(@field(a, f).items), std.mem.sliceAsBytes(@field(b, f).items));
    }
    try t.expectEqualSlices(u32, a.permutation.ends.items, b.permutation.ends.items);
    try t.expectEqualSlices(u32, a.permutation.inputs.items, b.permutation.inputs.items);
    try t.expectEqualSlices(u32, a.permutation.outputs.items, b.permutation.outputs.items);
}
