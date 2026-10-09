/-
**Merkle levels by index (M3a.4).** `level` pairs neighbours: entry `i` of the next level hashes
entries `2i` and `min (2i + 1) (len − 1)` (the last odd entry pairs with itself). `dupPair` is false
exactly when no pair at an even position is equal.
-/
import StarkedAir.Spec.Block

namespace StarkedAir.Spec.Block

theorem level_get : ∀ (l : List Bytes) (i : ℕ), i < (l.length + 1) / 2 →
    (level l)[i]? = some (sha256d (l.getD (2 * i) [] ++ l.getD (min (2 * i + 1) (l.length - 1)) []))
  | a :: b :: r, 0, _ => by simp [level]
  | a :: b :: r, i + 1, hi => by
    simp only [level, List.getElem?_cons_succ]
    rw [level_get r i (by simp at hi; omega)]
    have g : ∀ k, (a :: b :: r).getD (k + 2) [] = r.getD k [] := fun k => by simp
    simp only [List.length_cons] at hi ⊢
    rw [show 2 * (i + 1) = 2 * i + 2 by ring, g,
      show min (2 * i + 2 + 1) (r.length + 1 + 1 - 1) = min (2 * i + 1) (r.length - 1) + 2 by omega, g]
  | [a], 0, _ => by simp [level]
  | [a], i + 1, hi => by simp at hi
  | [], i, hi => by simp at hi

theorem dupPair_false : ∀ (l : List Bytes), dupPair l = false ↔
    ∀ i, 2 * i + 1 < l.length → l.getD (2 * i) [] ≠ l.getD (2 * i + 1) []
  | a :: b :: r => by
    simp only [dupPair, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, dupPair_false r, List.length_cons]
    constructor
    · rintro ⟨hab, hr⟩ i hi
      rcases i with _ | i
      · simpa using hab
      · have := hr i (by omega)
        simpa [show 2 * (i + 1) = 2 * i + 1 + 1 by ring] using this
    · intro h
      refine ⟨by simpa using h 0 (by omega), fun i hi => ?_⟩
      have := h (i + 1) (by omega)
      simpa [show 2 * (i + 1) = 2 * i + 1 + 1 by ring] using this
  | [a] => by simp [dupPair]
  | [] => by simp [dupPair]

/-- `merkleRoot`, one step: with at least two entries, the root is the next level's and a level is
mutated here or later. -/
theorem merkleRoot_step {l : List Bytes} (h : 1 < l.length) :
    merkleRoot l = ((merkleRoot (level l)).1, (merkleRoot (level l)).2 || dupPair l) := by
  rw [merkleRoot, dif_neg (by omega)]

theorem merkleRoot_one (a : Bytes) : merkleRoot [a] = (a, false) := by
  rw [merkleRoot]; simp

end StarkedAir.Spec.Block
