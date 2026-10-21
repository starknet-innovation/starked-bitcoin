//! starked-bitcoin: Stwo AIRs proving Bitcoin consensus and UTXO state.

pub const sha256 = @import("sha256/spec.zig");
pub const sha256_witness = @import("sha256/witness.zig");
pub const par = @import("par.zig");
pub const blake2s_air = @import("hash/blake2s_air.zig");
pub const header_chain = @import("btc/header_chain.zig");
pub const retarget = @import("btc/retarget.zig");
pub const work = @import("btc/work.zig");
pub const segments = @import("btc/segments.zig");
pub const header_tree = @import("btc/header_tree.zig");
pub const block = struct {
    pub const bytes = @import("block/bytes.zig");
    pub const fields = @import("block/fields.zig");
    pub const msg = @import("block/msg.zig");
    pub const sha = @import("block/sha.zig");
    pub const merkle = @import("block/merkle.zig");
    pub const checks = @import("block/checks.zig");
    pub const walk = @import("block/walk.zig");
    pub const ctx = @import("block/ctx.zig");
    pub const wmerkle = @import("block/wmerkle.zig");
    pub const anc = @import("block/anc.zig");
    pub const commit = @import("block/commit.zig");
    pub const proof_file = @import("block/proof_file.zig");
    pub const epoch_run = @import("block/epoch_run.zig");
    pub const extsum = @import("block/extsum.zig");
    pub const coin = @import("block/coin.zig");
    pub const epoch = @import("block/epoch.zig");
    pub const replay = @import("block/replay.zig");
    pub const set_file = @import("block/set_file.zig");
    pub const system = @import("block/system.zig");
    pub const negative = @import("block/negative.zig");
};
pub const recursion = struct {
    pub const plain_verifier = @import("recursion/plain_verifier.zig");
    pub const leaf = @import("recursion/leaf.zig");
    pub const node = @import("recursion/node.zig");
    pub const store = @import("recursion/store.zig");
    pub const fuzz = @import("recursion/fuzz.zig");
    pub const block_leaf = @import("recursion/block_leaf.zig");
    pub const block_rec = @import("recursion/block_rec.zig");
    pub const block_pack = @import("recursion/block_pack.zig");
    pub const block_node_k = @import("recursion/block_node_k.zig");
    pub const block_forest = @import("recursion/block_forest.zig");
    pub const block_tree = @import("recursion/block_tree.zig");
};
pub const air = struct {
    pub const ir = @import("air/ir.zig");
    pub const interp = @import("air/interp.zig");
    pub const component = @import("air/component.zig");
    pub const prove = @import("air/prove.zig");
    pub const prove_rec = @import("air/prove_rec.zig");
    pub const system = @import("air/system.zig");
    pub const stwzeva = @import("air/stwzeva.zig");
    pub const add32_chain = @import("air/gadgets/add32_chain.zig");
};

test {
    @import("std").testing.refAllDeclsRecursive(@This());
}
