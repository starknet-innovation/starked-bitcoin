/-
**Witness tree (M3a.5e), row facts.** In a satisfied `block_wmerkle` trace, `RIX` is the row index, so
node ids `NBW + row` are distinct and at least `NBW`.
-/
import StarkedAir.Block.WMerkle
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.WMerkle

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

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
theorem ev_first {r : ℕ} (hr : r < n) : (pre FIRST).eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval, FIRST]

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

omit hsat in
theorem mem_levelC {c : Expr} (h : c ∈ levelC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-- `RIX` is the row index. -/
theorem rix_eq : ∀ r < n, M RIX r = (r : F) := by
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_levelC (c := .mul (pre FIRST) (k RIX)) (by simp [levelC])) hr
    simpa [Expr.eval, ev_first hr, ev_k hr] using this
  | succ r ih =>
    have := sat hsat (mem_levelC (c := .mul notFirst (.sub (.sub (k RIX) (kp RIX)) one)) (by simp [levelC])) hr
    simp only [Expr.eval, notFirst, om, one, eval_cst, ev_first hr, ev_k hr, ev_kp hr, Nat.cast_one,
      show r + 1 ≠ 0 by omega, if_false, sub_zero, one_mul] at this
    rw [ih (by omega)] at this; push_cast; linear_combination this

theorem kbool {c : ℕ} (hc : c ∈ [ACTN, RT, FIRSTL, ODD, L1, WON]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by
    simp only [constraints, kindC, List.mem_append, List.mem_map]; left; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

end Rows

end StarkedAir.Block.WMerkle
