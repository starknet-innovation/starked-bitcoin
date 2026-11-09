//! `webverify.wasm`: the seal verifier and the membership check for the browser (WEB-MEMBER).
//!
//! Exports (wasm32-freestanding, no WASI): `wv_alloc`/`wv_free` for the host to pass bytes, then
//! - `verify_seal(chain, chain_len, seal, seal_len)`: `verify-seal`'s checks on the mainnet seal
//!   935,001–972,500 with every VK the pinned one embedded here (header, join, both trees, set, SEAL-T);
//! - `verify_member(members, len)`: each membership proof in an `.sbmember` file against the Merkle root
//!   and last key of the most recent `verify_seal` (so a coin is only reported against a verified seal).
//! Both return a pointer to a JSON result (`result_len()` bytes), `{"ok":true,…}` or
//! `{"ok":false,"error":"<ZigErrorName>"}`. Same code path as `chainproof verify-seal`/`checkMembers`.
const std = @import("std");
const sb = @import("starked_bitcoin");

const S = sb.recursion.store;
const L = sb.recursion.leaf;
const EJ = sb.recursion.epoch_join;
const CS = sb.recursion.chain_seal;
const ST = sb.recursion.set_tree;
const BT = sb.recursion.block_tree;
const SSG = sb.block.set_seg;

const gpa = std.heap.wasm_allocator;

const vk_header = @embedFile("vk:mainnet");
const vk_join = @embedFile("vk:epoch/join-935001-972500");
const vk_sealt = @embedFile("vk:epoch/sealt-935001-972500");
const vk_set = @embedFile("vk:epoch/set-l22");
const vk_trees = [_][]const u8{ @embedFile("vk:epoch/tree-935001-945000"), @embedFile("vk:epoch/tree-945001-972500") };

/// The sealed chain's epochs: (from, to). The seal's set children follow from these (`CS.nSets`).
const epochs = [_]struct { from: u32, to: u32 }{ .{ .from = 935001, .to = 945000 }, .{ .from = 945001, .to = 972500 } };
/// Core's assumeUTXO `hash_serialized` of the set after 935,000 (`chainproof.zig` `set_anchors`).
const anchor_935000 = "e4b90ef9eae834f56c4b64d2d50143cee10ad87994c614d7d04125e2a6025050";

var result: std.ArrayList(u8) = .empty;
var sealed: ?struct { root: [8]u32, last: ?[36]u8 } = null;

export fn wv_alloc(n: usize) ?[*]u8 {
    const s = gpa.alloc(u8, n) catch return null;
    return s.ptr;
}

export fn wv_free(p: [*]u8, n: usize) void {
    gpa.free(p[0..n]);
}

export fn result_len() usize {
    return result.items.len;
}

fn fail(e: anyerror) [*]const u8 {
    result.clearRetainingCapacity();
    result.writer(gpa).print("{{\"ok\":false,\"error\":\"{s}\"}}", .{@errorName(e)}) catch {};
    return result.items.ptr;
}

fn wordBytes(w: [8]u32) [32]u8 {
    var b: [32]u8 = undefined;
    for (w, 0..) |x, i| std.mem.writeInt(u32, b[4 * i ..][0..4], x, .little);
    return b;
}

export fn verify_seal(chain: [*]const u8, chain_len: usize, seal: [*]const u8, seal_len: usize) [*]const u8 {
    sealed = null;
    return verifySeal(chain[0..chain_len], seal[0..seal_len]) catch |e| fail(e);
}

fn verifySeal(chain_bytes: []const u8, seal_bytes: []const u8) ![*]const u8 {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const vk = try S.Vk.decode(a, vk_header);
    const tables = try L.Tables.init(gpa);
    defer tables.deinit(gpa);
    var c = try S.Chain.decode(gpa, a, try a.dupe(u8, chain_bytes));
    defer c.deinit();
    const jvk = try EJ.Vk.decode(a, vk_join);
    const seal_vk = try CS.Vk.decode(a, vk_sealt);
    if (seal_vk.d == 0) return error.WrongSealKind;
    // The header chain's plan and key natively; its root proof, genesis and paths in the seal (D-052).
    const ex = try S.rootExpect(a, &vk, &c);
    const tv: CS.TVerify = .{ .hhash = ex.hash, .hkey = ex.key };
    var f = try CS.File.decode(gpa, a, try a.dupe(u8, seal_bytes));
    defer f.proof.deinit();
    if (!std.mem.eql(u8, f.setvk, vk_set)) return error.VkNotPinned;
    const svk = try ST.Vk.decode(f.setvk);
    const gen = false;
    if (f.sets.len != CS.nSets(epochs.len, gen)) return error.WrongSets;
    var ins: [epochs.len]EJ.EpochIn = undefined;
    var tvks: [epochs.len]BT.Vk = undefined;
    for (epochs, &ins, &tvks, vk_trees, 0..) |ep, *in, *tvk, tb, i| {
        tvk.* = try BT.Vk.decode(tb);
        const fin = SSG.finish(f.sets[CS.endIdx(gen, i)].final).digest;
        const prev: ?[32]u8 = if (CS.hasStart(gen, i)) SSG.finish(f.sets[CS.startIdx(gen, i)].final).digest else null;
        in.* = .{ .tvk = tvk, .ep = .{ .from = ep.from, .to = ep.to, .prev = prev, .fin = fin } };
    }
    const v = try CS.verify(gpa, a, tables, &seal_vk, &jvk, &svk, &f, &ins, ex.n, null, tv);
    const t = v.open.t orelse return error.MissingHeaderChain;
    // The chain's start set is Core's assumeUTXO set after 935,000.
    const sh = v.start_hash orelse return error.AnchorMismatch;
    var want: [32]u8 = undefined;
    _ = try std.fmt.hexToBytes(&want, anchor_935000);
    if (!std.mem.eql(u8, &sh, &want)) return error.AnchorMismatch;
    // The end set's last key: in its public final state, which the seal's digest binds.
    const last = f.sets[CS.endIdx(gen, epochs.len - 1)].final.last;
    sealed = .{ .root = v.open.mroot, .last = last };

    result.clearRetainingCapacity();
    const w = result.writer(gpa);
    // Display order (as Core prints it): the words' big-endian bytes, reversed.
    var tip: [32]u8 = undefined;
    for (t.tip, 0..) |x, i| std.mem.writeInt(u32, tip[4 * i ..][0..4], x, .big);
    std.mem.reverse(u8, &tip);
    try w.print("{{\"ok\":true,\"from\":{d},\"to\":{d},\"headers\":{d},\"tip_height\":{d},\"tip_hash\":\"{x}\",\"chainwork\":\"0x{x}\",", .{ v.open.a, v.open.b, ex.n, t.height, &tip, CS.workOf(t.work) });
    try w.print("\"coins\":{d},\"amount\":\"{d}\",\"max_height\":{d},\"merkle_root\":\"{x}\",\"hash_serialized\":\"{x}\",\"start_hash\":\"{x}\"}}", .{ v.open.count, v.open.amount, v.open.max_height, &wordBytes(v.open.mroot), &v.hash, &sh });
    return result.items.ptr;
}

export fn verify_member(bytes: [*]const u8, len: usize) [*]const u8 {
    return verifyMember(bytes[0..len]) catch |e| fail(e);
}

fn verifyMember(bytes: []const u8) ![*]const u8 {
    const s = sealed orelse return error.SealNotVerified;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const a = arena.allocator();
    const ms = try ST.decodeMembers(a, try a.dupe(u8, bytes));
    result.clearRetainingCapacity();
    const w = result.writer(gpa);
    try w.writeAll("{\"ok\":true,\"coins\":[");
    for (ms, 0..) |*m, i| {
        try ST.verifyMember(m, s.root, s.last);
        var txid = m.key[0..32].*;
        std.mem.reverse(u8, &txid);
        if (i > 0) try w.writeAll(",");
        try w.print("{{\"outpoint\":\"{x}:{d}\",\"present\":{}", .{ &txid, std.mem.readInt(u32, m.key[32..36], .big), m.present });
        if (m.present) {
            const o = try ST.recordOutput(m.record);
            try w.print(",\"amount\":{d},\"height\":{d},\"coinbase\":{},\"script\":\"{x}\"", .{ o.amount, std.mem.readInt(u32, m.record[36..40], .little), m.record[40] == 1, o.script });
        }
        try w.print(",\"path\":{d}}}", .{m.path.len});
    }
    try w.writeAll("]}");
    return result.items.ptr;
}
