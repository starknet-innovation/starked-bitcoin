/-
**The coin-set pass segment system** (docs/design/set-pass.md § The segment system): the components in
proof order. Reused unchanged: `block_bytes` (0), `block_tables` (1), `block_fpwalk` (4). The Merkle root's
components (D-050) are 9–11.
-/
import StarkedAir.SetPass.Pend
import StarkedAir.SetPass.Rec
import StarkedAir.SetPass.B2w
import StarkedAir.SetPass.B2c
import StarkedAir.SetPass.TMsg
import StarkedAir.SetPass.ShaC
import StarkedAir.SetPass.LW
import StarkedAir.SetPass.LC
import StarkedAir.SetPass.MT

namespace StarkedAir.SetPass

open StarkedAir

def comps : List Comp :=
  [Block.bytes, Block.Tables.tables, Pend.pend, Rec.rec, Block.FpWalk.fpwalk, B2w.b2w, B2c.b2c, TMsg.tmsg, ShaC.shac,
    LW.lw, LC.lc, MT.mt]

end StarkedAir.SetPass
