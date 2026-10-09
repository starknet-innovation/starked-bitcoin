/-
**Hash messages soundness (M3a.3, message component).** Row facts first: kinds, transitions,
helpers; then a forward walk over one message.
-/
import StarkedAir.Block.Msg
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Msg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow eval_col eval_cst wrap_back)
open StarkedAir.Block.Fields (bool_val val_lt_of_eq_cast lt_P one_add_one_ne)

theorem mem_kindC {c : Expr} (h : c ∈ kindC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_transC {c : Expr} (h : c ∈ transC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_msgC {c : Expr} (h : c ∈ msgC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_padC {c : Expr} (h : c ∈ padC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto

section Rows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

omit hsat in
theorem ev_per64 {i : ℕ} {p : ℕ → Bool} (hi : preCols.getD i (.periodic [0]) = per64 p) {r : ℕ} (hr : r < n) :
    (pre i).eval n preCols pub M r = if p (r % 64) then 1 else 0 := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp only [per64, PreCol.eval, List.length_map, List.length_range, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range this, Option.map_some, Option.getD_some]
  split <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

theorem bool_of {e : ℕ} (hc : boolC (k e) ∈ constraints) {r : ℕ} (hr : r < n) : M e r = 0 ∨ M e r = 1 := by
  have := sat hsat hc hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem bool_col {e : ℕ} (he : e ∈ [D, P80, ZR, LN, NIL, FIRSTM, PC0, PC1, PC2, HDR, WTX, SEG, Z]) {r : ℕ} (hr : r < n) :
    M e r = 0 ∨ M e r = 1 := by
  have hm : boolC (k e) ∈ kindC := by
    simp only [kindC, List.mem_append, List.mem_map]
    left; exact ⟨e, Or.inl he, rfl⟩
  exact bool_of hsat (mem_kindC hm) hr

omit hsat in
theorem kinds_range : kinds = List.range 5 := rfl

/-- The kind sum, as naturals. -/
theorem kind_sumN {r : ℕ} (hr : r < n) : ∑ c ∈ Finset.range 5, (M c r).val = 1 := by
  have hs := sat hsat (mem_kindC (c := .sub (kinds.foldr (fun c acc => .add (k c) acc) (cst 0)) one)
    (by simp [kindC])) hr
  simp only [kinds, List.foldr, Expr.eval, ev_k hr, eval_cst, one, Nat.cast_zero, Nat.cast_one, sub_eq_zero] at hs
  have bv : ∀ c < 5, M c r = ((M c r).val : F) ∧ (M c r).val ≤ 1 := fun c hc => bool_val (bool_col hsat (by
    simp only [List.mem_cons]; interval_cases c <;> simp [D, P80, ZR, LN, NIL]) hr)
  have hle : ∑ c ∈ Finset.range 5, (M c r).val ≤ 5 := by
    calc _ ≤ ∑ _c ∈ Finset.range 5, 1 := Finset.sum_le_sum (fun c hc => (bv c (Finset.mem_range.mp hc)).2)
      _ = 5 := by simp
  have hcast : ((∑ c ∈ Finset.range 5, (M c r).val : ℕ) : F) = ((1 : ℕ) : F) := by
    push_cast
    rw [Finset.sum_congr rfl (fun c hc => (bv c (Finset.mem_range.mp hc)).1.symm)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [D, P80, ZR, LN, NIL] at hs
    rw [← hs]; ring
  exact natCast_inj_of_lt (lt_of_le_of_lt hle (by unfold P; norm_num)) (by unfold P; norm_num) hcast

/-- **One-hot kinds.** -/
theorem kind_unique {r : ℕ} (hr : r < n) {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : a ≠ b) (h : M a r = 1) :
    M b r = 0 := by
  have hs := kind_sumN hsat hr
  have := Finset.add_le_sum (f := fun c => (M c r).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr ha) (Finset.mem_range.mpr hb) hab
  have hb' := (bool_val (bool_col hsat (e := b) (by
    simp only [List.mem_cons]; interval_cases b <;> simp [D, P80, ZR, LN, NIL]) hr)).1
  have ha1 : (M a r).val = 1 := by rw [h]; exact ZMod.val_one P
  rw [hb', show (M b r).val = 0 by omega]; simp

theorem kind_exists {r : ℕ} (hr : r < n) : ∃ a < 5, M a r = 1 := by
  have hs := kind_sumN hsat hr
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ c ∈ Finset.range 5, (M c r).val ≠ 0)
  refine ⟨a, Finset.mem_range.mp ha, ?_⟩
  rcases bool_col hsat (e := a) (by
    have := Finset.mem_range.mp ha; simp only [List.mem_cons]; interval_cases a <;> simp [D, P80, ZR, LN, NIL]) hr with h | h
  · rw [h] at hne; simp at hne
  · exact h

end Rows

end StarkedAir.Block.Msg
