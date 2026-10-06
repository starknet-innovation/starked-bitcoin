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
