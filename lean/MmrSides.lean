/-
Prints the canonical MMR path sides (`HTree.sides`, leaf to root; `1` = sibling on the left) for
every leaf count `n ≤ 64` and leaf `h < n`, one line `n h bits`. Zig checks
`header_tree.inclusionSides` against it (`testdata/mmr_sides.txt`).
Run: `lake env lean --run MmrSides.lean > ../testdata/mmr_sides.txt`
-/
import StarkedAir.Spec.Mmr

open StarkedAir.Spec.Mmr StarkedAir.Spec.HeaderTree

def main : IO Unit := do
  for n in List.range' 1 64 do
    let L := (List.range n).map fun i => (⟨i, 0, 0, 0, 0, 0, 0, 0⟩ : StarkedAir.Spec.Sha256.State)
    for h in List.range n do
      let bits := String.ofList (((mmr L).sides h).map fun b => if b then '1' else '0')
      IO.println s!"{n} {h} {bits}"
