/-
**The outer verifier's genesis checks, from Lean (proof review 2026-10-09, §5 item 1).**
`chain_from_genesis_T` assumes four facts about the root's public inputs: prev-hash 0, height 0,
the sentinel window, work 0. `genesisChecks` lists them as `(index, value)` pairs on the inputs'
canonical values; `genesis_checks_sound` proves the list implies the four hypotheses, and
`chain_from_genesis_checked` restates the root theorem with the list as its only extra hypothesis.
The list is exported (`lake env lean --run Export.lean genesis_checks`, `airs/genesis_checks.json`)
and Zig's `node.verifyRoot` checks exactly it, instead of hand-coded indices.
-/
import StarkedAir.Gadgets.AggregateTree

namespace StarkedAir.HeaderTree

open StarkedAir StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin Spec.HeaderTree

/-- The window slot `k`'s public-input index (low limb; the high limb follows). -/
def windowIndex (k : ℕ) : ℕ := if k = 0 then 44 else 48 + 2 * (k - 1)

/-- **The checks**: `(index, canonical value)`. -/
def genesisChecks : List (ℕ × ℕ) :=
  (List.range 16).map (fun k => (k, 0)) ++ [(32, 0), (33, 0)] ++
  ((List.range 11).flatMap fun k =>
    let v := if sentinel.getD k 0 = 0 then 0 else 65535
    [(windowIndex k, v), (windowIndex k + 1, v)]) ++
  (List.range 10).map (fun l => (88 + l, 0))

#guard genesisChecks.length = 16 + 2 + 22 + 10

private theorem zero_of_val {x : F} (h : x.val = 0) : x = 0 := (ZMod.val_eq_zero x).mp h

theorem genesis_checks_sound {p : ℕ → F} (h : ∀ c ∈ genesisChecks, (p c.1).val = c.2) :
    (∀ k < 16, p k = 0) ∧ (p 32 = 0 ∧ p 33 = 0) ∧ pubWindow p = sentinel ∧ (∀ l < 10, p (88 + l) = 0) := by
  have mem : ∀ c, c ∈ genesisChecks → (p c.1).val = c.2 := h
  refine ⟨fun k hk => zero_of_val (mem (k, 0) (by simp [genesisChecks]; omega)),
    ⟨zero_of_val (mem (32, 0) (by simp [genesisChecks])), zero_of_val (mem (33, 0) (by simp [genesisChecks]))⟩,
    ?_, fun l hl => zero_of_val (mem (88 + l, 0) (by simp [genesisChecks]; omega))⟩
  -- The window: each slot's two limbs are 0 or 65535, so its word is 0 or 2^32 − 1.
  have slot : ∀ k < 11, (p (windowIndex k)).val = (if sentinel.getD k 0 = 0 then 0 else 65535) ∧
      (p (windowIndex k + 1)).val = (if sentinel.getD k 0 = 0 then 0 else 65535) := fun k hk =>
    ⟨mem (windowIndex k, if sentinel.getD k 0 = 0 then 0 else 65535)
       (by simp only [genesisChecks, List.mem_append, List.mem_flatMap, List.mem_range]; exact Or.inl (Or.inr ⟨k, hk, by simp⟩)),
     mem (windowIndex k + 1, if sentinel.getD k 0 = 0 then 0 else 65535)
       (by simp only [genesisChecks, List.mem_append, List.mem_flatMap, List.mem_range]; exact Or.inl (Or.inr ⟨k, hk, by simp⟩))⟩
  have word : ∀ k < 11, leN (pubWord p (windowIndex k)) = sentinel.getD k 0 := by
    intro k hk
    obtain ⟨h1, h2⟩ := slot k hk
    simp only [pubWord, h1, h2]
    interval_cases k <;> decide
  unfold pubWindow
  apply List.ext_getElem (by simp [sentinel])
  intro i h1 h2
  simp only [List.length_cons, List.length_map, List.length_range] at h1
  rcases i with _ | i
  · have := word 0 (by norm_num)
    simp only [windowIndex, ite_true] at this
    simp only [List.getElem_cons_zero]; rw [this]; rfl
  · have := word (i + 1) (by omega)
    simp only [windowIndex, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel] at this
    simp only [List.getElem_cons_succ, List.getElem_map, List.getElem_range]
    rw [this]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **The root theorem with the exported checks.** Proven public inputs that pass
`genesisChecks` give a valid chain from genesis and a tree over its block hashes with root `T`. -/
theorem chain_from_genesis_checked {p : ℕ → F} (v : PubValidT p)
    (hc : ∀ c ∈ genesisChecks, (p c.1).val = c.2) :
    ∃ H hs, SegmentValid H hs
      ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 ∧
      ∃ t : HTree, t.leaves = (List.range H).map (fun j => sha256d (hs j)) ∧ pubT p = limbsOf t.root := by
  obtain ⟨h1, h2, h3, h4⟩ := genesis_checks_sound hc
  exact chain_from_genesis_T v h1 h2 h3 h4

/-- The checks as JSON: `[[index, value], …]`. -/
def genesisChecksJson : String :=
  "[" ++ ", ".intercalate (genesisChecks.map fun c => s!"[{c.1}, {c.2}]") ++ "]"

end StarkedAir.HeaderTree
