/-
**Merkle leaf hashing, Lean-first (VERIFIER-LEAN step 4a).** `hashLeafM31s` in the plain verifier hashes a
queried row's values (one per committed column of a tree) before checking its Merkle path: each value
through `m31_to_u32`, then Blake2s over 4 bytes per value (the Blake2sM31 Merkle hasher's leaf).

`leaf_sound`: the result words are `blake2sWords` of the values as u32 words (from the proven gadget,
`blake2s_words`).
-/
import StarkedAir.Circuit.Gadgets
import StarkedAir.Circuit.BlakeSound

namespace StarkedAir.Circuit

open StarkedAir Spec.Blake2s Q

/-- The leaf hash of `vals` (value registers) from register `n`. -/
def leafHash (n : ℕ) (vals : List ℕ) : Out (List ℕ) :=
  let k := vals.length
  let g := blake2s (n + k) ((List.range k).map (n + ·)) (4 * k)
  ⟨(List.range k).map (fun i => Op.m2u (n + i) (vals.getD i 0)) ++ g.ops, g.res, g.next⟩

/-- **The leaf hash is Blake2s of the row's values** (each as a u32 word, little-endian bytes). -/
theorem leaf_sound {ρ : ℕ → Q} {n : ℕ} {vals : List ℕ} (h : Holds ρ (leafHash n vals).ops) (hk : 4 * vals.length < 2 ^ 32) :
    ∀ i < 8, word (ρ ((leafHash n vals).res.getD i 0)) =
      blake2sWords (vals.map fun r => BitVec.ofNat 32 (ρ r).a.val) (4 * vals.length) i := by
  simp only [leafHash] at h ⊢
  rw [holds_append] at h
  intro i hi
  rw [blake2s_words h.2 hk i hi]
  congr 1
  apply List.ext_getElem (by simp)
  intro j h1 h2
  have hj : j < vals.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, Function.comp]
  have hm := h.1 (Op.m2u (n + j) (vals.getD j 0)) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at hm
  rw [hm.2, word_m2u, List.getD_eq_getElem _ _ hj]

def leafHashJson (k : ℕ) : String :=
  let o := leafHash k (List.range k)
  let ops := [Op.hook 0 [] (List.range k)] ++ o.ops
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{",".intercalate (o.res.map toString)}]}"

end StarkedAir.Circuit
