/-
The LogUp side conditions (`LogUpSZ.StaticOk`: one arity per relation, relation ids below `P`)
for the systems we prove: the header chain with its Blake2s tree, and the block systems. With
them, `balanced_of_poly` / `balancedExt_of_poly` apply to these systems' instances.
-/
import StarkedAir.LogUpSZ
import StarkedAir.Gadgets.HeaderTreeSound
import StarkedAir.Block.Link
import StarkedAir.Block.BlockAnc

namespace StarkedAir.LogUpSZ

theorem headerTree_static : StaticOk StarkedAir.HeaderTree.sys = true := by decide

set_option maxRecDepth 100000 in
theorem hashSys_static : StaticOk StarkedAir.Block.hashSys = true := by decide

set_option maxRecDepth 100000 in
theorem blockSys_static : StaticOk StarkedAir.Block.blockSys = true := by decide

end StarkedAir.LogUpSZ
