//! Reference interpreter for the constraint IR.
//!
//! One evaluation routine is shared by every consumer: the verifier (at the
//! out-of-domain point, over QM31), the prover's composition (per row of the
//! evaluation domain), and witness checks in tests (per trace row, over M31).
//! Each consumer only supplies how to read `col{tree, index, offset}`.

const std = @import("std");
const ir = @import("ir.zig");
const M31 = @import("stwo_core").fields.m31.M31;
const QM31 = @import("stwo_core").fields.qm31.QM31;

/// `F` is M31 or QM31. `ctx.read(tree, index, offset) F` supplies column values.
pub fn evalConstraints(
    comptime F: type,
    air: ir.Air,
    scratch: []F,
    ctx: anytype,
    out: []F,
) void {
    std.debug.assert(scratch.len >= air.exprs.len and out.len == air.constraints.len);
    for (air.exprs, 0..) |e, id| scratch[id] = switch (e) {
        .col => |c| ctx.read(c.tree, c.index, c.offset),
        .constant => |v| lift(F, M31.fromCanonical(v)),
        .add => |a| scratch[a[0]].add(scratch[a[1]]),
        .sub => |a| scratch[a[0]].sub(scratch[a[1]]),
        .mul => |a| scratch[a[0]].mul(scratch[a[1]]),
        .neg => |a| scratch[a].neg(),
    };
    for (air.constraints, out) |root, *o| o.* = scratch[root];
}

fn lift(comptime F: type, v: M31) F {
    return if (F == QM31) QM31.fromBase(v) else v;
}

/// Plain trace in natural row order, for witness checking.
pub const RowTrace = struct {
    log_size: u32,
    preprocessed: []const []const M31,
    main: []const []const M31,
    row: usize = 0,

    pub fn read(self: *const RowTrace, tree: ir.Tree, index: u32, offset: i32) M31 {
        const n: isize = @as(isize, 1) << @intCast(self.log_size);
        const r: usize = @intCast(@mod(@as(isize, @intCast(self.row)) + offset, n));
        return switch (tree) {
            .preprocessed => self.preprocessed[index][r],
            .main => self.main[index][r],
        };
    }
};

/// Returns the first (row, constraint) that does not vanish, or null.
pub fn firstViolation(
    allocator: std.mem.Allocator,
    air: ir.Air,
    trace: RowTrace,
) !?struct { row: usize, constraint: usize } {
    const scratch = try allocator.alloc(M31, air.exprs.len);
    defer allocator.free(scratch);
    const out = try allocator.alloc(M31, air.constraints.len);
    defer allocator.free(out);
    var t = trace;
    const n = @as(usize, 1) << @intCast(trace.log_size);
    for (0..n) |row| {
        t.row = row;
        evalConstraints(M31, air, scratch, &t, out);
        for (out, 0..) |v, c| if (!v.isZero()) return .{ .row = row, .constraint = c };
    }
    return null;
}

test "matches the Lean semantics (Expr.eval) on the probe oracle" {
    // airs/probe_oracle.json is produced by lean/StarkedAir/Testing/Probe.lean:
    // offsets −3…+5 with wrap-around, every preprocessed kind, every operator.
    const Oracle = struct {
        log_size: u32,
        air: std.json.Value,
        main: []const []const u32,
        evals: []const []const u32,
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    const bytes = @embedFile("air:probe_oracle");
    const oracle = try std.json.parseFromSliceLeaky(Oracle, a, bytes, .{});
    var air_json: std.Io.Writer.Allocating = .init(a);
    try std.json.Stringify.value(oracle.air, .{}, &air_json.writer);
    const air = (try ir.Air.parseJson(a, air_json.written())).value;

    const n = @as(usize, 1) << @intCast(oracle.log_size);
    const main = try a.alloc([]M31, oracle.main.len);
    for (main, oracle.main) |*col, src| {
        col.* = try a.alloc(M31, n);
        for (col.*, src) |*v, x| v.* = M31.fromCanonical(x);
    }
    var t = RowTrace{
        .log_size = oracle.log_size,
        .preprocessed = @ptrCast(try air.genPreprocessed(a, oracle.log_size)),
        .main = @ptrCast(main),
    };
    const scratch = try a.alloc(M31, air.exprs.len);
    const out = try a.alloc(M31, air.constraints.len);
    try std.testing.expectEqual(n, oracle.evals.len);
    for (0..n) |row| {
        t.row = row;
        evalConstraints(M31, air, scratch, &t, out);
        for (out, oracle.evals[row]) |got, want| try std.testing.expectEqual(want, got.toU32());
    }
}
