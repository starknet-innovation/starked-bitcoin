//! starked-bitcoin: Stwo AIRs proving Bitcoin consensus and UTXO state.

pub const sha256 = @import("sha256/spec.zig");
pub const sha256_witness = @import("sha256/witness.zig");
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
};
pub const recursion = struct {
    pub const plain_verifier = @import("recursion/plain_verifier.zig");
    pub const leaf = @import("recursion/leaf.zig");
    pub const node = @import("recursion/node.zig");
};
pub const air = struct {
    pub const ir = @import("air/ir.zig");
    pub const interp = @import("air/interp.zig");
    pub const component = @import("air/component.zig");
    pub const prove = @import("air/prove.zig");
    pub const prove_rec = @import("air/prove_rec.zig");
    pub const system = @import("air/system.zig");
    pub const add32_chain = @import("air/gadgets/add32_chain.zig");
};

test {
    @import("std").testing.refAllDeclsRecursive(@This());
}
