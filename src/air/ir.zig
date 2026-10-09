//! Canonical constraint IR (schema `starked-air-v0`).
//!
//! This is the single source of truth for an AIR's constraints. The plan is for
//! AIRs to be authored and proven in Lean, exported to this JSON format, and
//! consumed here. The verifier evaluates the IR directly (see `interp.zig`), so
//! the artifact the Lean proofs talk about is exactly what verification runs.
//!
//! Semantics (mirrored by the Lean model):
//! - The trace has N = 2^log_size rows; every column is a function
//!   `Fin N → M31`.
//! - `col{tree, index, offset}` at row i denotes `column[(i + offset) mod N]`.
//!   Wrap-around is real. Constraints that must not wrap need an explicit
//!   preprocessed selector.
//! - `pub i` is public input i (canonical M31), part of the statement and
//!   mixed into the Fiat–Shamir transcript.
//! - Every constraint expression must evaluate to 0 at every row i ∈ [0, N).
//! - Trees: 0 = preprocessed, 1 = main witness. Preprocessed columns are
//!   *defined by the AIR* (`PreCol`), generated identically by prover and
//!   verifier, and the verifier checks their commitment root. They are never
//!   prover-supplied.
//! - Lookups (schema v2, Lean `Lookup.lean`): at every row, lookup `{rel, mult, vals}` emits
//!   the entry `(rel, vals(row))` with multiplicity `mult(row)`. A system of components is
//!   satisfied when every AIR is and every relation balances (multiplicities of each tuple sum
//!   to zero). The LogUp encoding (interaction tree) is derived from the lookups.

const std = @import("std");
const M31 = @import("stwo_core").fields.m31.M31;
const P = @import("stwo_core").fields.m31.Modulus;

pub const schema = "starked-air-v1";
/// Schema of AIRs with lookups. AIRs without lookups keep the v1 bytes (and digests).
pub const schema_v2 = "starked-air-v2";

pub const Tree = enum(u8) { preprocessed = 0, main = 1 };

pub const ExprId = u32;

/// Definition of a preprocessed column as a function of row i ∈ [0, N).
pub const PreCol = union(enum) {
    /// 1 at row 0, else 0.
    is_first,
    /// 0 at row N-1, else 1.
    not_last,
    /// values[i mod values.len] (canonical M31). The period need not divide N.
    periodic: []const u32,
    /// 1 on rows < k, else 0.
    row_lt: u32,
    /// 1 on the last k rows (row + k ≥ N), else 0.
    row_ge_end: u32,

    pub fn at(self: PreCol, row: usize, n: usize) M31 {
        return switch (self) {
            .is_first => if (row == 0) M31.one() else M31.zero(),
            .not_last => if (row + 1 < n) M31.one() else M31.zero(),
            .periodic => |v| M31.fromCanonical(v[row % v.len]),
            .row_lt => |k| if (row < k) M31.one() else M31.zero(),
            .row_ge_end => |k| if (row + k >= n) M31.one() else M31.zero(),
        };
    }
};

pub const Expr = union(enum) {
    col: struct { tree: Tree, index: u32, offset: i32 },
    constant: u32, // canonical M31 value, < 2^31 - 1
    add: [2]ExprId,
    sub: [2]ExprId,
    mul: [2]ExprId,
    neg: ExprId,
    @"pub": u32,
};

/// `(rel, vals)` emitted with multiplicity `mult` at every row; expressions are DAG nodes.
pub const Lookup = struct {
    rel: u32,
    mult: ExprId,
    vals: []const ExprId,
};

/// An AIR as a DAG of expressions (children always precede parents) plus
/// a list of constraint roots.
pub const Air = struct {
    name: []const u8,
    n_preprocessed: u32,
    n_main: u32,
    n_pub: u32 = 0,
    preprocessed: []const PreCol,
    exprs: []const Expr,
    constraints: []const ExprId,
    lookups: []const Lookup = &.{},

    /// Preprocessed columns in natural row order.
    pub fn genPreprocessed(self: Air, allocator: std.mem.Allocator, log_size: u32) ![][]M31 {
        const n = @as(usize, 1) << @intCast(log_size);
        const out = try allocator.alloc([]M31, self.preprocessed.len);
        for (self.preprocessed, out) |def, *col| {
            col.* = try allocator.alloc(M31, n);
            for (col.*, 0..) |*v, i| v.* = def.at(i, n);
        }
        return out;
    }

    pub fn validate(self: Air) !void {
        if (self.preprocessed.len != self.n_preprocessed) return error.PreprocessedCountMismatch;
        for (self.preprocessed) |def| switch (def) {
            .periodic => |v| {
                if (v.len == 0) return error.EmptyPeriodicColumn;
                for (v) |x| if (x >= P) return error.NonCanonicalConstant;
            },
            else => {},
        };
        for (self.exprs, 0..) |e, id| switch (e) {
            .col => |c| {
                const n = if (c.tree == .preprocessed) self.n_preprocessed else self.n_main;
                if (c.index >= n) return error.ColumnOutOfRange;
            },
            .constant => |v| if (v >= P) return error.NonCanonicalConstant,
            .add, .sub, .mul => |args| for (args) |a| if (a >= id) return error.NotTopological,
            .neg => |a| if (a >= id) return error.NotTopological,
            .@"pub" => |i| if (i >= self.n_pub) return error.PublicInputOutOfRange,
        };
        for (self.constraints) |c| if (c >= self.exprs.len) return error.ConstraintOutOfRange;
        for (self.lookups) |l| {
            if (l.mult >= self.exprs.len) return error.LookupOutOfRange;
            for (l.vals) |v| if (v >= self.exprs.len) return error.LookupOutOfRange;
        }
    }

    /// Total degree of each expression (columns have degree 1).
    pub fn degrees(self: Air, allocator: std.mem.Allocator) ![]u32 {
        const out = try allocator.alloc(u32, self.exprs.len);
        for (self.exprs, 0..) |e, id| out[id] = switch (e) {
            .col => 1,
            .constant => 0,
            .add, .sub => |a| @max(out[a[0]], out[a[1]]),
            .mul => |a| out[a[0]] + out[a[1]],
            .neg => |a| out[a],
            .@"pub" => 0,
        };
        return out;
    }

    pub fn maxConstraintDegree(self: Air, allocator: std.mem.Allocator) !u32 {
        const deg = try self.degrees(allocator);
        defer allocator.free(deg);
        var max: u32 = 0;
        for (self.constraints) |c| max = @max(max, deg[c]);
        return max;
    }

    /// Sorted distinct row offsets used by each column of `tree`.
    pub fn columnOffsets(self: Air, allocator: std.mem.Allocator, tree: Tree) ![][]i32 {
        const n = if (tree == .preprocessed) self.n_preprocessed else self.n_main;
        var lists = try allocator.alloc(std.ArrayList(i32), n);
        defer allocator.free(lists);
        for (lists) |*l| l.* = .empty;
        for (self.exprs) |e| switch (e) {
            .col => |c| if (c.tree == tree) {
                const list = &lists[c.index];
                if (std.mem.indexOfScalar(i32, list.items, c.offset) == null)
                    try list.append(allocator, c.offset);
            },
            else => {},
        };
        const out = try allocator.alloc([]i32, n);
        for (lists, out) |*l, *o| {
            std.mem.sort(i32, l.items, {}, std.sort.asc(i32));
            o.* = try l.toOwnedSlice(allocator);
        }
        return out;
    }

    // ------------------------------------------------------------- JSON

    pub fn writeJson(self: Air, writer: *std.Io.Writer) !void {
        if (self.lookups.len != 0) return std.json.Stringify.value(JsonAirV2{
            .schema = schema_v2,
            .name = self.name,
            .n_preprocessed = self.n_preprocessed,
            .n_main = self.n_main,
            .n_pub = self.n_pub,
            .preprocessed = self.preprocessed,
            .exprs = self.exprs,
            .constraints = self.constraints,
            .lookups = self.lookups,
        }, .{}, writer);
        try std.json.Stringify.value(JsonAir{
            .schema = schema,
            .name = self.name,
            .n_preprocessed = self.n_preprocessed,
            .n_main = self.n_main,
            .n_pub = self.n_pub,
            .preprocessed = self.preprocessed,
            .exprs = self.exprs,
            .constraints = self.constraints,
        }, .{}, writer);
    }

    /// Canonical serialization (compact JSON, field order as declared) and
    /// its SHA-256, used to bind the AIR identity into the proof statement.
    pub fn digest(self: Air, allocator: std.mem.Allocator) ![32]u8 {
        var out: std.Io.Writer.Allocating = .init(allocator);
        defer out.deinit();
        try self.writeJson(&out.writer);
        var d: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(out.written(), &d, .{});
        return d;
    }

    pub fn parseJson(allocator: std.mem.Allocator, bytes: []const u8) !std.json.Parsed(Air) {
        const parsed = try std.json.parseFromSlice(JsonAirIn, allocator, bytes, .{});
        errdefer parsed.deinit();
        const v2 = std.mem.eql(u8, parsed.value.schema, schema_v2);
        if (!v2 and !std.mem.eql(u8, parsed.value.schema, schema)) return error.UnknownSchema;
        if (v2 == (parsed.value.lookups.len == 0)) return error.UnknownSchema;
        const air = Air{
            .name = parsed.value.name,
            .n_preprocessed = parsed.value.n_preprocessed,
            .n_main = parsed.value.n_main,
            .n_pub = parsed.value.n_pub,
            .preprocessed = parsed.value.preprocessed,
            .exprs = parsed.value.exprs,
            .constraints = parsed.value.constraints,
            .lookups = parsed.value.lookups,
        };
        try air.validate();
        return .{ .arena = parsed.arena, .value = air };
    }
};

const JsonAir = struct {
    schema: []const u8,
    name: []const u8,
    n_preprocessed: u32,
    n_main: u32,
    n_pub: u32,
    preprocessed: []const PreCol,
    exprs: []const Expr,
    constraints: []const ExprId,
};

const JsonAirV2 = struct {
    schema: []const u8,
    name: []const u8,
    n_preprocessed: u32,
    n_main: u32,
    n_pub: u32,
    preprocessed: []const PreCol,
    exprs: []const Expr,
    constraints: []const ExprId,
    lookups: []const Lookup,
};

const JsonAirIn = struct {
    schema: []const u8,
    name: []const u8,
    n_preprocessed: u32,
    n_main: u32,
    n_pub: u32,
    preprocessed: []const PreCol,
    exprs: []const Expr,
    constraints: []const ExprId,
    lookups: []const Lookup = &.{},
};

/// Convenience builder for authoring AIRs in Zig (tests and prototypes).
/// Production AIRs are meant to come from the Lean export.
pub const Builder = struct {
    allocator: std.mem.Allocator,
    exprs: std.ArrayList(Expr) = .empty,
    constraints: std.ArrayList(ExprId) = .empty,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Builder) void {
        self.exprs.deinit(self.allocator);
        self.constraints.deinit(self.allocator);
    }

    fn push(self: *Builder, e: Expr) !ExprId {
        try self.exprs.append(self.allocator, e);
        return @intCast(self.exprs.items.len - 1);
    }

    pub fn main(self: *Builder, index: u32, offset: i32) !ExprId {
        return self.push(.{ .col = .{ .tree = .main, .index = index, .offset = offset } });
    }
    pub fn pre(self: *Builder, index: u32, offset: i32) !ExprId {
        return self.push(.{ .col = .{ .tree = .preprocessed, .index = index, .offset = offset } });
    }
    pub fn constant(self: *Builder, v: u32) !ExprId {
        return self.push(.{ .constant = v % P });
    }
    pub fn add(self: *Builder, a: ExprId, b: ExprId) !ExprId {
        return self.push(.{ .add = .{ a, b } });
    }
    pub fn sub(self: *Builder, a: ExprId, b: ExprId) !ExprId {
        return self.push(.{ .sub = .{ a, b } });
    }
    pub fn mul(self: *Builder, a: ExprId, b: ExprId) !ExprId {
        return self.push(.{ .mul = .{ a, b } });
    }
    pub fn scale(self: *Builder, k: u32, a: ExprId) !ExprId {
        return self.mul(try self.constant(k), a);
    }
    pub fn assertZero(self: *Builder, e: ExprId) !void {
        try self.constraints.append(self.allocator, e);
    }
    /// x(x-1) = 0
    pub fn assertBool(self: *Builder, x: ExprId) !void {
        try self.assertZero(try self.mul(x, try self.sub(x, try self.constant(1))));
    }

    pub fn finish(self: *Builder, name: []const u8, preprocessed: []const PreCol, n_main: u32) !Air {
        const air = Air{
            .name = name,
            .n_preprocessed = @intCast(preprocessed.len),
            .n_main = n_main,
            .preprocessed = try self.allocator.dupe(PreCol, preprocessed),
            .exprs = try self.exprs.toOwnedSlice(self.allocator),
            .constraints = try self.constraints.toOwnedSlice(self.allocator),
        };
        try air.validate();
        return air;
    }
};

test "AIRs without lookups keep the v1 bytes; lookups round-trip as v2" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    var b = Builder.init(a);
    const x = try b.main(0, 0);
    try b.assertBool(x);
    var air = try b.finish("t", &.{}, 1);
    var out: std.Io.Writer.Allocating = .init(a);
    try air.writeJson(&out.writer);
    try std.testing.expect(std.mem.indexOf(u8, out.written(), "starked-air-v1") != null);
    try std.testing.expect(std.mem.indexOf(u8, out.written(), "lookups") == null);
    air.lookups = &.{.{ .rel = 1, .mult = 0, .vals = &.{0} }};
    var out2: std.Io.Writer.Allocating = .init(a);
    try air.writeJson(&out2.writer);
    const back = (try Air.parseJson(a, out2.written())).value;
    try std.testing.expectEqual(@as(usize, 1), back.lookups.len);
    try std.testing.expectEqual(@as(u32, 1), back.lookups[0].rel);
}

pub fn freeAir(allocator: std.mem.Allocator, air: Air) void {
    allocator.free(air.preprocessed);
    allocator.free(air.exprs);
    allocator.free(air.constraints);
}

test "every exported AIR re-serializes to Lean's exact text, so its digest is SHA-256 of that text" {
    // Proof review 2026-10-09, §5 item 10 (the cheap half): the digest the verifiers mix into the
    // transcript is `digest(parse(json))`; byte-identical re-serialization means it is SHA-256 of the
    // file Lean printed (`lake env lean --run Export.lean <name>`), so the statement is bound to it.
    const files = .{
        "air:add32_chain",      "air:sha256_compress", "air:header_chain",
        "air:byte_table",       "air:byte_user",       "air:blake2s_compress", "air:blake2s_tree",
        "air:header_chain_v7",  "air:block_bytes",     "air:block_reader",  "air:block_sha",
        "air:block_msg",        "air:block_fields",    "air:block_merkle",
    };
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    const a = arena.allocator();
    inline for (files) |name| {
        const text = std.mem.trimRight(u8, @embedFile(name), "\n");
        const air = (Air.parseJson(a, text) catch |e| {
            std.debug.print("{s}: parse failed\n", .{name});
            return e;
        }).value;
        var out: std.Io.Writer.Allocating = .init(a);
        try air.writeJson(&out.writer);
        std.testing.expectEqualStrings(text, out.written()) catch |e| {
            std.debug.print("{s}: re-serialization differs from Lean's text\n", .{name});
            return e;
        };
        var want: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(text, &want, .{});
        try std.testing.expectEqualSlices(u8, &want, &try air.digest(a));
    }
}
