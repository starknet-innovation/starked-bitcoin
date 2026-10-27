/-
**The set tree's state vectors, by index (set-pass step 4).** `inIdx`/`outIdx` entry by entry (`fIn`,
`fOut`), and equal digests of state vectors as equal values (or a Blake2s collision).
-/
import StarkedAir.SetPass.Sound
import StarkedAir.Circuit.SetTreeSound

namespace StarkedAir.SetPass

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec StarkedAir.Circuit.SetTree
open StarkedAir.Spec.QM31 (QM)

/-! ### The state vectors' indices -/

/-- `inIdx`'s entry `t`. -/
def fIn (t : ℕ) : ℕ :=
  if t < 112 then 41 + t else if t = 112 then 1 else if t = 113 then 3 else if t < 150 then 4 + (t - 114)
  else if t = 150 then 40 else if t < 155 then 153 + (t - 151) else if t < 167 then 162 + (t - 155)
  else if t < 249 then 222 + (t - 167) else 386 + (t - 249)

/-- `outIdx`'s entry `t` (`NP` is the constant 1). -/
def fOut (t : ℕ) : ℕ :=
  if t < 112 then 41 + t else if t = 112 then 2 else if t = 113 then NP else if t < 150 then 186 + (t - 114)
  else if t = 150 then 161 else if t < 155 then 157 + (t - 151) else if t < 167 then 174 + (t - 155)
  else if t < 249 then 304 + (t - 167) else 468 + (t - 249)

set_option maxRecDepth 100000 in
theorem inIdx_get : ∀ t < NV, inIdx.getD t 0 = fIn t := by decide

set_option maxRecDepth 100000 in
theorem outIdx_get : ∀ t < NV, outIdx.getD t 0 = fOut t := by decide

theorem inIdx_length : inIdx.length = NV := by simp [inIdx, chal, NV]
theorem outIdx_length : outIdx.length = NV := by simp [outIdx, chal, NV]

/-- Equal word vectors are equal values. -/
theorem vecW_eq {p q : ℕ → F} {a b : List ℕ} (ha : a.length = NV) (hb : b.length = NV) (h : vecW p a = vecW q b) :
    ∀ t < NV, p (a.getD t 0) = q (b.getD t 0) := by
  intro t ht
  have := congrArg (fun l => l.getD t 0) h
  simp only [vecW, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (show t < a.length by omega),
    List.getElem?_eq_getElem (show t < b.length by omega), Option.map_some, Option.getD_some] at this
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact ofNat_val_inj this

/-- Equal digest limbs are equal digests. -/
theorem half_inj {a b : List Spec.Blake2s.Word} (ha : a.length = 8) (hb : b.length = 8)
    (h : ∀ j < 16, half a j = half b j) : a = b := by
  apply List.ext_getElem (by rw [ha, hb])
  intro w h1 h2
  have hw : w < 8 := by omega
  have lt : ∀ (x : Spec.Blake2s.Word) (k : ℕ), Sha256.half16 x k < P := fun x k =>
    lt_of_lt_of_le (Sha256.half16_lt x k) (by unfold P; norm_num)
  have e0 := h (2 * w) (by omega)
  have e1 := h (2 * w + 1) (by omega)
  simp only [half, show 2 * w / 2 = w by omega, show (2 * w + 1) / 2 = w by omega, show 2 * w % 2 = 0 by omega,
    show (2 * w + 1) % 2 = 1 by omega] at e0 e1
  rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0]
  exact HeaderChain.half16_inj (natCast_inj_of_lt (lt _ _) (lt _ _) e0) (natCast_inj_of_lt (lt _ _) (lt _ _) e1)

/-- Equal digest limbs of two state vectors: equal vectors, or a collision. -/
theorem vec_of_half {p q : ℕ → F} {a b : List ℕ} (ha : a.length = NV) (hb : b.length = NV)
    (h : ∀ j < 16, half (H (vecW p a)) j = half (H (vecW q b)) j) :
    (∀ t < NV, p (a.getD t 0) = q (b.getD t 0)) ∨ Collision := by
  rcases H_eq (a := vecW p a) (b := vecW q b) (by simp [vecW, ha, NV]) (by simp [vecW, hb, NV])
    (half_inj (H_length _) (H_length _) h) with e | c
  · exact Or.inl (vecW_eq ha hb e)
  · exact Or.inr c

end StarkedAir.SetPass
