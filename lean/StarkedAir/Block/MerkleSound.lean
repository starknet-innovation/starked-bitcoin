/-
**Merkle tree soundness (M3a.4), row facts.** In a satisfied `block_merkle` trace: `RIX` is the row
index, so node ids `NB + row` are distinct and at least `NB`.
-/
import StarkedAir.Block.Merkle
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Merkle

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

end Rows

end StarkedAir.Block.Merkle

namespace StarkedAir.Block.Merkle

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

section Rows2

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem kbool {c : ℕ} (hc : c ∈ [ACTN, RT, FIRSTL, ODD, L1]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by
    simp only [constraints, kindC, List.mem_append, List.mem_map]; left; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hsat in
theorem mem_kindC {c : Expr} (h : c ∈ kindC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_flagC {c : Expr} (h : c ∈ flagC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_childC {c : Expr} (h : c ∈ childC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-- The is-zero flags. -/
theorem last_iff {r : ℕ} (hr : r < n) : M LAST r = 1 ↔ M I r - M CNT r + 1 = 0 := by
  have h1 := sat hsat (mem_flagC (c := .mul (k LAST) (.add (.sub (k I) (k CNT)) one)) (by simp [flagC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (om (k LAST)) (.sub (.mul (.add (.sub (k I) (k CNT)) one) (k LINV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
  constructor
  · intro h; rw [h, one_mul] at h1; exact h1
  · intro h; rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact h2.symm

theorem c1_iff {r : ℕ} (hr : r < n) : M C1 r = 1 ↔ M CNT r - 1 = 0 := by
  have h1 := sat hsat (mem_flagC (c := .mul (k C1) (.sub (k CNT) one)) (by simp [flagC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (om (k C1)) (.sub (.mul (.sub (k CNT) one) (k C1INV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
  constructor
  · intro h; rw [h, one_mul] at h1; exact h1
  · intro h; rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact h2.symm

theorem flag01 {c : ℕ} (hc : c = LAST ∨ c = C1) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  rcases hc with rfl | rfl
  · have h1 := sat hsat (mem_flagC (c := .mul (k LAST) (.add (.sub (k I) (k CNT)) one)) (by simp [flagC])) hr
    have h2 := sat hsat (mem_flagC (c := .mul (om (k LAST)) (.sub (.mul (.add (.sub (k I) (k CNT)) one) (k LINV)) one))
      (by simp [flagC])) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact Or.inr h2.symm
  · have h1 := sat hsat (mem_flagC (c := .mul (k C1) (.sub (k CNT) one)) (by simp [flagC])) hr
    have h2 := sat hsat (mem_flagC (c := .mul (om (k C1)) (.sub (.mul (.sub (k CNT) one) (k C1INV)) one))
      (by simp [flagC])) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact Or.inr h2.symm

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ constraints) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat h hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem rn_eq {r : ℕ} (hr : r < n) : M RN r = M LAST r * M C1 r := by
  rw [defn hsat (e := .mul (k LAST) (k C1)) (mem_flagC (by simp [flagC])) hr]; simp [Expr.eval, ev_k hr]

/-- Kind transitions at row `r + 1`. -/
theorem kind_next {r : ℕ} (hr : r + 1 < n) :
    M ACTN (r + 1) = M ACTN r * (1 - M RN r) ∧ M RT (r + 1) = M ACTN r * M RN r ∧
    (M ACTN (r + 1) = 1 → M FIRSTL (r + 1) = M LAST r) := by
  have c := fun (e : Expr) (h : e ∈ kindC) => sat hsat (mem_kindC h) hr
  have hnf : notFirst.eval n preCols pub M (r + 1) = 1 := by
    simp [notFirst, om, one, Expr.eval, ev_first hr, eval_cst]
  have h1 := c (.mul notFirst (.sub (k ACTN) (.mul (kp ACTN) (om (kp RN))))) (by simp [kindC])
  have h2 := c (.mul notFirst (.sub (k RT) (.mul (kp ACTN) (kp RN)))) (by simp [kindC])
  simp only [Expr.eval, hnf, one_mul, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at h1 h2
  refine ⟨h1, h2, fun ha => ?_⟩
  have h3 := sat hsat (mem_levelC (c := .mul notFirst (.mul (k ACTN) (.sub (k FIRSTL) (kp LAST)))) (by simp [levelC])) hr
  simp only [Expr.eval, hnf, one_mul, ev_k hr, ev_kp hr, ha] at h3
  exact sub_eq_zero.mp h3

theorem nf_eq {r : ℕ} (hr : r < n) : M NF r = M ACTN r * (1 - M FIRSTL r) := by
  rw [defn hsat (e := .mul (k ACTN) (om (k FIRSTL))) (mem_levelC (by simp [levelC])) hr]
  simp [Expr.eval, ev_k hr, om, one, eval_cst]

theorem fs_eq {r : ℕ} (hr : r < n) : M FS r = M ACTN r * M FIRSTL r := by
  rw [defn hsat (e := .mul (k ACTN) (k FIRSTL)) (mem_levelC (by simp [levelC])) hr]
  simp [Expr.eval, ev_k hr]

/-- A node row continuing its level. -/
theorem cont_row {r : ℕ} (hr : r + 1 < n) (ha : M ACTN (r + 1) = 1) (hf : M FIRSTL (r + 1) = 0) :
    M I (r + 1) = M I r + 1 ∧ ∀ c ∈ [CNT, PCNT, BASE, PBASE, L1], M c (r + 1) = M c r := by
  have hnf : M NF (r + 1) = 1 := by rw [nf_eq hsat hr, ha, hf]; ring
  constructor
  · have := sat hsat (mem_levelC (c := .mul (k NF) (.sub (.sub (k I) (kp I)) one)) (by simp [levelC])) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, one_mul, one, eval_cst, Nat.cast_one] at this
    linear_combination this
  · intro c hc
    have := sat hsat (mem_levelC (c := .mul (k NF) (.sub (k c) (kp c)))
      (by simp only [levelC, List.mem_append, List.mem_map]; left; right; exact ⟨c, hc, rfl⟩)) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, one_mul] at this
    exact sub_eq_zero.mp this

/-- A node row starting a level (after the first row). -/
theorem start_row {r : ℕ} (hr : r + 1 < n) (ha : M ACTN (r + 1) = 1) (hf : M FIRSTL (r + 1) = 1) :
    M I (r + 1) = 0 ∧ M PCNT (r + 1) = M CNT r ∧ M BASE (r + 1) = ((r + 1 : ℕ) : F) ∧
      M PBASE (r + 1) = M BASE r ∧ M L1 (r + 1) = 0 := by
  have hfs : M FS (r + 1) = 1 := by rw [fs_eq hsat hr, ha, hf]; ring
  have hnf : notFirst.eval n preCols pub M (r + 1) = 1 := by
    simp [notFirst, om, one, Expr.eval, ev_first hr, eval_cst]
  have e := fun (c : Expr) (h : c ∈ levelC) => sat hsat (mem_levelC h) hr
  have h0 := e (.mul (k FIRSTL) (k I)) (by simp [levelC])
  have h1 := e (.mul notFirst (.mul (k FS) (.sub (k PCNT) (kp CNT)))) (by simp [levelC])
  have h2 := e (.mul notFirst (.mul (k FS) (.sub (k BASE) (k RIX)))) (by simp [levelC])
  have h3 := e (.mul notFirst (.mul (k FS) (.sub (k PBASE) (kp BASE)))) (by simp [levelC])
  have h4 := e (.mul notFirst (.mul (k FS) (k L1))) (by simp [levelC])
  simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, hfs, hf, one_mul, sub_eq_zero] at h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2.trans (rix_eq hsat _ hr), h3, h4⟩

/-- Row 0 starts level 1 over the `pub 1` leaves (also when it is the root row). -/
theorem row0 (hn : 0 < n) : M FIRSTL 0 = 1 ∧ M L1 0 = 1 ∧ M BASE 0 = 0 ∧ M PCNT 0 = pub 1 ∧ M I 0 = 0 := by
  have e := fun (c : Expr) (h : c ∈ levelC) => sat hsat (mem_levelC h) hn
  have hf : (pre FIRST).eval n preCols pub M 0 = 1 := by simp [ev_first hn]
  have h1 := e (.mul (pre FIRST) (.sub (k FIRSTL) one)) (by simp [levelC])
  have h2 := e (.mul (pre FIRST) (.sub (k L1) one)) (by simp [levelC])
  have h3 := e (.mul (pre FIRST) (k BASE)) (by simp [levelC])
  have h4 := e (.mul (pre FIRST) (.sub (k PCNT) NTX)) (by simp [levelC])
  simp only [Expr.eval, ev_k hn, hf, one_mul, one, eval_cst, Nat.cast_one, NTX, sub_eq_zero] at h1 h2 h3 h4
  have h0 := e (.mul (k FIRSTL) (k I)) (by simp [levelC])
  simp only [Expr.eval, ev_k hn, h1, one_mul] at h0
  exact ⟨h1, h2, h3, h4, h0⟩

theorem size_eq {r : ℕ} (hr : r < n) (ha : M ACTN r = 1) :
    2 * M CNT r = M PCNT r + M ODD r ∧ M PCNT r ≠ 1 := by
  have h1 := sat hsat (mem_levelC (c := .mul (k ACTN) (.sub (.mul (cst 2) (k CNT)) (.add (k PCNT) (k ODD))))
    (by simp [levelC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (k ACTN) (.sub (.mul (.sub (k PCNT) one) (k PINV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, ha, one_mul, eval_cst, one, Nat.cast_one, Nat.cast_ofNat, sub_eq_zero] at h1 h2
  refine ⟨h1, fun h => ?_⟩
  rw [h, sub_self, zero_mul] at h2; exact zero_ne_one h2

theorem last_not_node (hn : 0 < n) : M ACTN (n - 1) = 0 := by
  have := sat hsat (mem_kindC (c := .mul (om (pre NOTLAST)) (k ACTN)) (by simp [kindC])) (show n - 1 < n by omega)
  have hnl : (pre NOTLAST).eval n preCols pub M (n - 1) = 0 := by
    simp [pre, Expr.eval, wrap_zero (show n - 1 < n by omega), preCols, PreCol.eval, NOTLAST]; omega
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, hnl, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
  exact this

end Rows2

end StarkedAir.Block.Merkle
