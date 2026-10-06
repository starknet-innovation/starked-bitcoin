//! starked-bitcoin: Stwo AIRs proving Bitcoin consensus and UTXO state.

pub const sha256 = @import("sha256/spec.zig");
pub const sha256_witness = @import("sha256/witness.zig");
pub const header_chain = @import("btc/header_chain.zig");
pub const retarget = @import("btc/retarget.zig");
pub const air = struct {
    pub const ir = @import("air/ir.zig");
    pub const interp = @import("air/interp.zig");
    pub const component = @import("air/component.zig");
    pub const prove = @import("air/prove.zig");
    pub const add32_chain = @import("air/gadgets/add32_chain.zig");
};

test {
    @import("std").testing.refAllDeclsRecursive(@This());
}
