/-
**Block SHA-256 soundness (M3a.3, SHA component).** Every aligned period computes the SHA-256
compression (`period_compress`, from `compress_sound`); then the period bookkeeping chains them.
-/
import StarkedAir.Block.Sha
import StarkedAir.Gadgets.HeaderChainSound

namespace StarkedAir.Block.Sha

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC limb ShaSat shaPre inputAt messageAt outputAt compress_sound)

section Period

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem sha_sat : ShaSat n preCols pub M := fun r hr c hc =>
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem pre_sha {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) :
    ∀ p < 72, ∀ i < 5, (pre i).eval n preCols pub M (s + p) = shaPre i p := by
  intro p hp i hi
  obtain ⟨vals, hv, hl⟩ := Sha256.preCols_periodic hi
  have hg : preCols.getD i (.periodic [0]) = Sha256.preCols.getD i (.periodic [0]) := by
    interval_cases i <;> rfl
  simp only [pre, Expr.eval, wrap_zero (show s + p < n by omega), shaPre]
  rw [hg, hv]
  simp only [PreCol.eval, hl, show (s + p) % 72 = p by omega, Nat.mod_eq_of_lt hp]

/-- **Each aligned period computes the SHA-256 compression.** -/
theorem period_compress {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) :
    Spec.Sha256.compress (inputAt M s) (messageAt M s) = outputAt M s :=
  compress_sound (sha_sat hsat) hsn (pre_sha hsat hs hsn)

theorem eval_per72 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per72 f) {r : ℕ} (hr : r < n) :
    (pre i).eval n preCols pub M r = ((f (r % 72) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 72 < 72 := Nat.mod_lt _ (by norm_num)
  simp [per72, PreCol.eval, Sha256.PERIOD, List.getD_eq_getElem?_getD, this]

theorem flag_sat {c : Expr} (hc : c ∈ flagC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

/-- Per-period values are constant down the period. -/
theorem per_const {X : ℕ} (hX : X = MID ∨ X = BLKI ∨ X = FST ∨ X = DBL ∨ X = NILS) {s : ℕ} (hs : s % 72 = 0) :
    ∀ p < 72, s + p < n → M X (s + p) = M X s := by
  intro p
  induction p with
  | zero => intro _ _; rfl
  | succ p ih =>
    intro hp hr
    have hc := flag_sat hsat (c := .mul (om (pre ROW0)) (.sub (k X) (kp X)))
      (by simp only [flagC, List.mem_append, List.mem_map]; right; exact ⟨X, by rcases hX with h | h | h | h | h <;> simp [h], rfl⟩) hr
    have h0 := eval_per72 hsat (i := ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hr
    rw [show (s + (p + 1)) % 72 = p + 1 by omega, if_neg (by omega)] at h0
    simp only [Expr.eval, om, one, Sha256.eval_cst, h0, k, kp, Sha256.eval_col, wrap_zero hr] at hc
    rw [show wrap n (s + (p + 1)) (-1) = s + p by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, Sha256.wrap_back (by omega) hr]; omega] at hc
    simp at hc
    rw [sub_eq_zero.mp hc, ih (by omega) (by omega)]

end Period

end StarkedAir.Block.Sha
