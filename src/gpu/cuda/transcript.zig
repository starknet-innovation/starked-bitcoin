//! The block system's transcript, as a resident CUDA sink and as a host reference.
//!
//! `system.proveOpts` (src/air/system.zig) absorbs, before the STARK tail:
//!   1. the FRI configuration (`Revision.proving_5a7c5ed.mixConfig`: two felts);
//!   2. the preprocessed root;
//!   3. the statement (`system.mixStatements`): `[n]`, then per component `[log, digest₀..₇,
//!      n_pub]` and one `[p]` per public input, each its own `mix_u32s`;
//!   4. the main root;
//!   5. draws the lookup elements `(z, α)` (two secure felts);
//!   6. the claimed sums (one `mix_felts`);
//!   7. the interaction root.
//! The circuit-recursion prefix (`circuit_cuda/transcript_prefix.zig`) is different (channel salt,
//! circuit hash, output claim, a 20-bit interaction grind), so it is replaced here. The tail
//! (composition α and root, OODS point, sampled values, DEEP α, FRI roots and α's, last layer,
//! query grind, queries) is stwo's `prove_ex` order, the same for both, and keeps the calls
//! `circuit_cuda/resident_fri.zig`, `resident_decommit.zig` and the pipeline make on a sink.
//!
//! `Prefix` enforces the order over any sink. `HostSink` runs it on the CPU channel
//! (`rec.Channel`); `DeviceSink` issues it as stwo-zig's resident transcript kernels
//! (`cuda.runtime.stages.transcript`), adapted from `circuit_cuda/resident_transcript.zig`.

const std = @import("std");
const sb = @import("starked_bitcoin");
const core = @import("stwo_core");
const cuda = @import("stwo_cuda_backend");
const common = cuda.runtime.stages.common;
const stage_transcript = cuda.runtime.stages.transcript;
const rec = sb.air.prove_rec;
const system = sb.air.system;
const QM31 = core.fields.qm31.QM31;
const PcsConfig = core.pcs.config_v2.PcsConfigV2;
const Revision = core.protocol_revision.Revision;
const lookup_transcript = core.channel.lookup_transcript;

/// The statement's `mix_u32s` calls as one word array: `words[ends[i-1]..ends[i]]` is call `i`.
pub const Statement = struct {
    words: []u32,
    ends: []u32,

    pub fn init(allocator: std.mem.Allocator, parts: []const system.Part) !Statement {
        var words = std.ArrayList(u32).empty;
        errdefer words.deinit(allocator);
        var ends = std.ArrayList(u32).empty;
        errdefer ends.deinit(allocator);
        try words.append(allocator, @intCast(parts.len));
        try ends.append(allocator, @intCast(words.items.len));
        for (parts) |p| {
            const digest = try p.air.digest(allocator);
            try words.append(allocator, p.log_size);
            for (0..8) |i| try words.append(allocator, std.mem.readInt(u32, digest[4 * i ..][0..4], .little));
            try words.append(allocator, @intCast(p.pubs.len));
            try ends.append(allocator, @intCast(words.items.len));
            for (p.pubs) |x| {
                try words.append(allocator, x.toU32());
                try ends.append(allocator, @intCast(words.items.len));
            }
        }
        return .{ .words = try words.toOwnedSlice(allocator), .ends = try ends.toOwnedSlice(allocator) };
    }

    pub fn deinit(self: *Statement, allocator: std.mem.Allocator) void {
        allocator.free(self.words);
        allocator.free(self.ends);
        self.* = undefined;
    }

    pub fn calls(self: Statement) usize {
        return self.ends.len;
    }

    pub fn range(self: Statement, i: usize) struct { start: usize, len: usize } {
        const start: usize = if (i == 0) 0 else self.ends[i - 1];
        return .{ .start = start, .len = self.ends[i] - start };
    }
};

pub const Stage = enum { initial, config, preprocessed, statement, main, lookup_elements, interaction_claim, interaction };

/// Our prefix over `Sink`, which supplies `Root`, `Words`, `Felts`, `Lookup` and the operations
/// below. Out-of-order calls fail.
pub fn Prefix(comptime Sink: type) type {
    return struct {
        sink: *Sink,
        stage: Stage = .initial,

        const Self = @This();

        fn advance(self: *Self, from: Stage, to: Stage) !void {
            if (self.stage != from) return error.TranscriptOrder;
            self.stage = to;
        }

        pub fn mixConfig(self: *Self, config: PcsConfig) !void {
            try self.advance(.initial, .config);
            try self.sink.mixConfig(config);
        }

        pub fn commitPreprocessed(self: *Self, root: Sink.Root) !void {
            try self.advance(.config, .preprocessed);
            try self.sink.mixRoot(root);
        }

        pub fn mixStatement(self: *Self, statement: Statement, words: Sink.Words) !void {
            try self.advance(.preprocessed, .statement);
            for (0..statement.calls()) |i| {
                const r = statement.range(i);
                try self.sink.mixU32s(try Sink.slice(words, r.start, r.len));
            }
        }

        pub fn commitMain(self: *Self, root: Sink.Root) !void {
            try self.advance(.statement, .main);
            try self.sink.mixRoot(root);
        }

        pub fn drawLookupElements(self: *Self) !Sink.Lookup {
            try self.advance(.main, .lookup_elements);
            return self.sink.drawLookupElements();
        }

        pub fn mixInteractionClaim(self: *Self, sums: Sink.Felts) !void {
            try self.advance(.lookup_elements, .interaction_claim);
            try self.sink.mixFelts(sums);
        }

        pub fn commitInteraction(self: *Self, root: Sink.Root) !void {
            try self.advance(.interaction_claim, .interaction);
            try self.sink.mixRoot(root);
        }

        pub fn admitComposition(self: *Self) !void {
            if (self.stage != .interaction) return error.TranscriptOrder;
        }
    };
}

/// The prefix on the CPU channel: the reference the device sink must reproduce.
pub const HostSink = struct {
    channel: rec.Channel = .{},

    pub const Root = rec.Hasher.Hash;
    pub const Words = []const u32;
    pub const Felts = []const QM31;
    pub const Lookup = lookup_transcript.LookupElements;

    pub fn slice(words: Words, start: usize, len: usize) !Words {
        return words[start..][0..len];
    }
    pub fn mixConfig(self: *HostSink, config: PcsConfig) !void {
        Revision.proving_5a7c5ed.mixConfig(config, &self.channel);
    }
    pub fn mixRoot(self: *HostSink, root: Root) !void {
        rec.MerkleChannel.mixRoot(&self.channel, root);
    }
    pub fn mixU32s(self: *HostSink, words: Words) !void {
        self.channel.mixU32s(words);
    }
    pub fn mixFelts(self: *HostSink, felts: Felts) !void {
        self.channel.mixFelts(felts);
    }
    pub fn drawLookupElements(self: *HostSink) !Lookup {
        return lookup_transcript.drawLookupElements(std.heap.page_allocator, &self.channel);
    }
};

/// Device bindings: the channel state and its boundary snapshot, the FRI configuration words
/// (uploaded at ingress), the drawn lookup elements and the query-grind scratch.
pub const Bindings = struct {
    state: common.Words,
    boundary_snapshot: common.Words,
    fri_config: common.Words,
    lookup: common.SecureFields,
    pow_prefix: common.Words,
    pow_best_nonce: common.Nonce,
    pow_completed_blocks: common.Words,
    pow_nonce_words: common.Words,

    pub fn validate(self: Bindings) !void {
        if (self.state.len != 16 or self.boundary_snapshot.len != 16 or self.fri_config.len != 8 or
            self.lookup.len != 2 or self.pow_prefix.len != 8 or self.pow_best_nonce.len != 1 or
            self.pow_completed_blocks.len == 0 or self.pow_nonce_words.len != 2)
            return error.InvalidTranscriptBindings;
        const owner = self.state.owner;
        const generation = self.state.generation;
        inline for (.{ self.boundary_snapshot, self.fri_config, self.lookup, self.pow_prefix, self.pow_best_nonce, self.pow_completed_blocks, self.pow_nonce_words }) |view| {
            if (view.owner != owner or view.generation != generation) return error.InvalidTranscriptBindings;
        }
    }
};

/// stwo-zig's grind search bound for the resident sinks.
pub const pow_search_end: u64 = cc_transcript.pow_search_end;
const cc_transcript = @import("stwo_circuit_cuda_integration").resident_transcript;

/// Our transcript on the device. `Session` is the resident proof session, `Transcript` and `Fri`
/// stwo-zig's transcript and FRI (grind) stage operations; tests substitute host models.
pub fn DeviceSink(comptime Session: type, comptime Transcript: type, comptime Fri: type) type {
    return struct {
        session: *Session,
        bindings: Bindings,
        chain_seed: u64,
        config: ?PcsConfig = null,
        fri_host: [8]u32 = @splat(0),
        initialized: bool = false,
        next_step: u32 = 0,
        /// Set once the prefix is done (`readyForComposition`); the tail's steps follow.
        tail_start: ?u32 = null,
        fri_layers: ?u32 = null,
        fri_round: u32 = 0,
        composition_drawn: bool = false,

        pub const Root = common.Words;
        pub const Words = common.Words;
        pub const Felts = common.Words;
        pub const Lookup = common.SecureFields;

        const Self = @This();

        pub fn slice(words: Words, start: usize, len: usize) !Words {
            return words.sub(start, len);
        }

        pub fn init(session: *Session, bindings: Bindings, geometry_identity: [32]u8) !Self {
            try bindings.validate();
            if (std.mem.allEqual(u8, &geometry_identity, 0)) return error.InvalidTranscriptGeometry;
            return .{ .session = session, .bindings = bindings, .chain_seed = std.mem.readInt(u64, geometry_identity[0..8], .little) };
        }

        /// Ingress: the FRI configuration words, as `FriConfigV2.mixInto` lays them out.
        pub fn prime(self: *Self, config: PcsConfig) !void {
            if (self.config != null) return error.TranscriptAlreadyPrimed;
            const f = config.fri_config;
            self.fri_host = .{ f.pow_bits, f.log_blowup_factor, f.n_queries, f.log_last_layer_degree_bound, f.fold_step, 0, 0, 0 };
            try self.session.context.uploadSlice(u32, self.bindings.fri_config, &self.fri_host);
            self.config = config;
        }

        /// The zero channel (`rec.Channel{}`), at the start of `.trace_commit`.
        pub fn initialize(self: *Self) !void {
            if (self.config == null or self.initialized) return error.InvalidTranscriptState;
            try Transcript.initializeM31(self.session, .trace_commit, self.bindings.state, null, null, chainAt(self.chain_seed, 0));
            self.initialized = true;
        }

        pub fn mixConfig(self: *Self, config: PcsConfig) !void {
            if (self.next_step != 0 or !std.meta.eql(self.config orelse return error.InvalidTranscriptState, config))
                return error.InvalidTranscriptPayload;
            try self.mix(.trace_commit, self.bindings.fri_config, true);
        }
        pub fn mixRoot(self: *Self, root: Root) !void {
            if (root.len != 8 or self.tail_start != null) return error.InvalidTranscriptPayload;
            try self.mix(.trace_commit, root, false);
        }
        /// Statement words are arbitrary u32 (AIR digests): not M31-validated.
        pub fn mixU32s(self: *Self, words: Words) !void {
            if (words.len == 0) return error.InvalidTranscriptPayload;
            try self.mix(.trace_commit, words, false);
        }
        pub fn mixFelts(self: *Self, values: Felts) !void {
            if (values.len == 0 or values.len % 4 != 0 or self.tail_start != null) return error.InvalidTranscriptPayload;
            try self.mix(.trace_commit, values, true);
        }
        pub fn drawLookupElements(self: *Self) !Lookup {
            if (!self.initialized) return error.InvalidTranscriptState;
            try Transcript.drawSecure(self.session, .trace_commit, self.bindings.state, self.boundary(), 2, 64, self.bindings.lookup, self.bindings.lookup);
            self.next_step += 1;
            return self.bindings.lookup;
        }

        /// The prefix is complete: the STARK tail starts.
        pub fn readyForComposition(self: *Self) void {
            self.tail_start = self.next_step;
        }

        pub fn drawCompositionAlpha(self: *Self, output: common.SecureFields) !void {
            if (self.tail_start == null or self.composition_drawn) return error.InvalidTranscriptState;
            self.composition_drawn = true;
            try self.draw(.constraint_evaluation, output);
        }
        pub fn mixCompositionRoot(self: *Self, root: common.Words) !void {
            if (!self.composition_drawn or root.len != 8) return error.InvalidTranscriptState;
            try self.mix(.constraint_evaluation, root, false);
        }
        pub fn drawOodsParameter(self: *Self, output: common.SecureFields) !void {
            try self.draw(.oods, output);
        }
        pub fn mixSampledValues(self: *Self, values: common.SecureFields) !void {
            if (values.len == 0) return error.InvalidTranscriptPayload;
            try self.mix(.oods, try values.cast(u32), true);
        }
        pub fn drawQuotientAlpha(self: *Self, output: common.SecureFields) !void {
            try self.draw(.oods, output);
        }
        pub fn setFriLayers(self: *Self, count: u32) !void {
            if (self.fri_layers != null or count == 0 or count > 32) return error.InvalidTranscriptState;
            self.fri_layers = count;
        }
        pub fn mixFriRoot(self: *Self, root: common.Words) !void {
            const count = self.fri_layers orelse return error.InvalidTranscriptState;
            if (root.len != 8 or self.fri_round >= count) return error.InvalidTranscriptPayload;
            try self.mix(.fri_commit, root, false);
        }
        pub fn drawFriAlpha(self: *Self, output: common.SecureFields) !void {
            const count = self.fri_layers orelse return error.InvalidTranscriptState;
            if (self.fri_round >= count) return error.InvalidTranscriptState;
            try self.draw(.fri_commit, output);
            self.fri_round += 1;
        }
        pub fn mixLastLayer(self: *Self, coefficients: common.SecureFields) !void {
            const count = self.fri_layers orelse return error.InvalidTranscriptState;
            if (self.fri_round != count or coefficients.len == 0) return error.InvalidTranscriptState;
            try self.mix(.fri_commit, try coefficients.cast(u32), true);
        }
        /// The query grind (26 bits in production): searched and absorbed on the device.
        pub fn absorbQueryPow(self: *Self) !void {
            const count = self.fri_layers orelse return error.InvalidTranscriptState;
            if (self.fri_round != count) return error.InvalidTranscriptState;
            const bits = (self.config orelse return error.InvalidTranscriptState).fri_config.pow_bits;
            const v = self.bindings;
            try Fri.grindPowAtStage(self.session, .pow, v.state, bits, pow_search_end, v.pow_prefix, v.pow_best_nonce, v.pow_completed_blocks, v.pow_nonce_words);
            try Transcript.absorbPowAtStage(self.session, .pow, v.state, self.boundary(), v.pow_nonce_words, bits, v.pow_nonce_words);
            self.next_step += 1;
        }
        pub fn drawQueries(self: *Self, output: common.Words, log_domain_size: u32) !void {
            const config = self.config orelse return error.InvalidTranscriptState;
            if (output.len != config.fri_config.n_queries or log_domain_size == 0 or log_domain_size > 30)
                return error.InvalidTranscriptState;
            try Transcript.drawQueries(self.session, self.bindings.state, self.boundary(), log_domain_size, output, output);
            self.next_step += 1;
        }

        fn draw(self: *Self, at: cuda.runtime.telemetry.Stage, output: common.SecureFields) !void {
            if (!self.initialized or output.len != 1 or output.owner != self.bindings.state.owner or output.generation != self.bindings.state.generation)
                return error.InvalidTranscriptState;
            try Transcript.drawSecure(self.session, at, self.bindings.state, self.boundary(), 1, 64, output, output);
            self.next_step += 1;
        }

        fn mix(self: *Self, at: cuda.runtime.telemetry.Stage, source: common.Words, validate_m31: bool) !void {
            if (!self.initialized or source.owner != self.bindings.state.owner or source.generation != self.bindings.state.generation)
                return error.InvalidTranscriptState;
            try Transcript.mixWords(self.session, at, self.bindings.state, self.boundary(), source, validate_m31, source);
            self.next_step += 1;
        }

        fn boundary(self: *const Self) stage_transcript.Boundary {
            return .{
                .expected_step = self.next_step,
                .expected_chain = chainAt(self.chain_seed, self.next_step),
                .next_chain = chainAt(self.chain_seed, self.next_step + 1),
                .snapshot = self.bindings.boundary_snapshot,
            };
        }
    };
}

pub const NativeSink = DeviceSink(cuda.runtime.NativeSession, cuda.runtime.stages.transcript.Native, cuda.runtime.stages.fri.Native);

fn chainAt(seed: u64, step: u32) u64 {
    var value = seed ^ (@as(u64, step) *% 0x9e37_79b9_7f4a_7c15);
    value ^= value >> 30;
    value *%= 0xbf58_476d_1ce4_e5b9;
    value ^= value >> 27;
    value *%= 0x94d0_49bb_1331_11eb;
    value ^= value >> 31;
    return value;
}

// ------------------------------------------------------------------ host model of the device

/// A host model of the resident session for the device sink: device words live in a map from
/// address to host words, and the transcript operations run on a CPU channel (`rec.Channel`)
/// with the device ABI's payloads. It checks the sink's call sequence and payload layout against
/// the CPU transcript; the kernels themselves are stwo-zig's (qualified for this channel).
pub const HostModel = struct {
    allocator: std.mem.Allocator,
    regions: std.AutoArrayHashMapUnmanaged(usize, []u32) = .empty,
    channel: rec.Channel = .{},
    /// The nonce the model's grind finds (the CPU grinder's canonical minimum).
    last_nonce: u64 = 0,
    calls: u32 = 0,
    next_address: usize = 0x1000,

    pub const Context = struct {
        model: *HostModel,
        pub fn uploadSlice(self: *Context, comptime F: type, destination: anytype, source: []const F) !void {
            const words = try self.model.wordsOf(destination);
            const bytes = std.mem.sliceAsBytes(source);
            if (bytes.len != words.len * 4) return error.InvalidUpload;
            @memcpy(std.mem.sliceAsBytes(words), bytes);
        }
    };

    pub const Session = struct {
        model: *HostModel,
        context: Context,
    };

    pub fn deinit(self: *HostModel) void {
        for (self.regions.values()) |r| self.allocator.free(r);
        self.regions.deinit(self.allocator);
    }

    /// A fresh device region of `len` elements of `F`.
    pub fn alloc(self: *HostModel, comptime F: type, len: usize) !cuda.runtime.column.DeviceSlice(F) {
        const words = (len * @sizeOf(F) + 3) / 4;
        const backing = try self.allocator.alloc(u32, @max(words, 1));
        @memset(backing, 0);
        const address = self.next_address;
        self.next_address += (words + 64) * 4;
        try self.regions.put(self.allocator, address, backing);
        return .{ .address = address, .len = len, .owner = 1, .generation = 1 };
    }

    /// Host words of a device view (any element type) inside one region.
    pub fn wordsOf(self: *HostModel, view: anytype) ![]u32 {
        const T = @TypeOf(view);
        const element: usize = if (T == common.Words) 4 else if (T == common.SecureFields) 16 else if (T == common.Nonce) 8 else @compileError("unsupported device view");
        const bytes = view.len * element;
        var it = self.regions.iterator();
        while (it.next()) |e| {
            const start = e.key_ptr.*;
            const region = e.value_ptr.*;
            if (view.address >= start and view.address + bytes <= start + region.len * 4) {
                const first = (view.address - start) / 4;
                return region[first..][0 .. (bytes + 3) / 4];
            }
        }
        return error.UnknownDeviceAddress;
    }

    fn writeFelts(self: *HostModel, output: common.SecureFields, felts: []const QM31) !void {
        const words = try self.wordsOf(output);
        for (felts, 0..) |f, i| for (f.toM31Array(), 0..) |x, k| {
            words[4 * i + k] = x.toU32();
        };
    }

    pub const Transcript = struct {
        pub fn initializeM31(session: *Session, _: cuda.runtime.telemetry.Stage, _: common.Words, _: ?common.Words, _: ?common.Words, _: u64) !void {
            session.model.channel = .{};
            session.model.calls += 1;
        }
        pub fn mixWords(session: *Session, _: cuda.runtime.telemetry.Stage, _: common.Words, b: stage_transcript.Boundary, source: common.Words, validate_m31: bool, _: common.Words) !void {
            const m = session.model;
            if (b.expected_step + 1 != m.calls) return error.ModelStepMismatch;
            const words = try m.wordsOf(source);
            if (validate_m31) for (words) |w| if (w >= core.fields.m31.Modulus) return error.ModelNonCanonicalM31;
            m.channel.mixU32s(words);
            m.calls += 1;
        }
        pub fn drawSecure(session: *Session, _: cuda.runtime.telemetry.Stage, _: common.Words, b: stage_transcript.Boundary, count: u32, _: u32, output: common.SecureFields, _: common.SecureFields) !void {
            const m = session.model;
            if (b.expected_step + 1 != m.calls) return error.ModelStepMismatch;
            const felts = try m.channel.drawSecureFelts(m.allocator, count);
            defer m.allocator.free(felts);
            try m.writeFelts(output, felts);
            m.calls += 1;
        }
        pub fn absorbPowAtStage(session: *Session, _: cuda.runtime.telemetry.Stage, _: common.Words, b: stage_transcript.Boundary, nonce_words: common.Words, bits: u32, _: common.Words) !void {
            const m = session.model;
            if (b.expected_step + 1 != m.calls) return error.ModelStepMismatch;
            const words = try m.wordsOf(nonce_words);
            const nonce = @as(u64, words[0]) | (@as(u64, words[1]) << 32);
            if (!m.channel.verifyPowNonce(bits, nonce)) return error.ModelBadNonce;
            m.channel.mixU64(nonce);
            m.calls += 1;
        }
        pub fn drawQueries(session: *Session, _: common.Words, b: stage_transcript.Boundary, log_domain_size: u32, output: common.Words, _: common.Words) !void {
            const m = session.model;
            if (b.expected_step + 1 != m.calls) return error.ModelStepMismatch;
            const words = try m.wordsOf(output);
            const raw = try core.queries.drawQueries(&m.channel, m.allocator, log_domain_size, words.len);
            defer m.allocator.free(raw);
            for (raw, words) |q, *w| w.* = @intCast(q);
            m.calls += 1;
        }
    };

    pub const Fri = struct {
        pub fn grindPowAtStage(session: *Session, _: cuda.runtime.telemetry.Stage, _: common.Words, bits: u32, _: u64, _: common.Words, _: common.Nonce, _: common.Words, nonce_words: common.Words) !void {
            const m = session.model;
            const nonce = m.channel.grind(bits);
            const words = try m.wordsOf(nonce_words);
            words[0] = @truncate(nonce);
            words[1] = @intCast(nonce >> 32);
            m.last_nonce = nonce;
        }
    };
};

pub const ModelSink = DeviceSink(HostModel.Session, HostModel.Transcript, HostModel.Fri);
