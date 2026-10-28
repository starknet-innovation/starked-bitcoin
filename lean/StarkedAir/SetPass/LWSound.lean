/-
**Merkle leaf messages as words, AIR soundness (`set_lw`, D-050).** In a satisfied `set_lw` trace, every on
row lies in a record's window `[st, en]` (`window`): `st` starts the record (`NEWR`), `en` ends it (`ENDR`),
the record index, start and length are constant across it and its blocks count from 0. Its active bytes
are its message positions below its length `m` (`row_fact`), it has `nbOf m` blocks, each block's first
row says whether it is the last and its counter, and `PKU` marks the first nine words.
-/
import StarkedAir.SetPass.LW
import StarkedAir.Block.B2MsgSound

namespace StarkedAir.SetPass.LW

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

section Rows

variable {n : ℕ} {pub : ℕ → F} {W : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub W r = 0)
include hsat

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub W r = W c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub W (r + 1) = W c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

omit hsat in
theorem ev_kn {c r : ℕ} (hr : r + 1 < n) : (kn c).eval n preCols pub W r = W c (r + 1) := by
  simp [kn, eval_col, wrap_one hr]

omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub W r = if r = 0 then 1 else 0 := by
  simp [first, p, pre, Expr.eval, wrap_zero hr, preCols, P_FIRST, PreCol.eval]

omit hsat in
theorem ev_notLast {r : ℕ} (hr : r < n) : (p P_NOTLAST).eval n preCols pub W r = if r + 1 < n then 1 else 0 := by
  simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_NOTLAST, PreCol.eval]

omit hsat in
theorem ev_per16 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per16 f) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub W r = ((f (r % 16) : ℕ) : F) := by
  simp only [p, pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 16 < 16 := Nat.mod_lt _ (by norm_num)
  simp [per16, PreCol.eval, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_K {r : ℕ} (hr : r < n) : (p P_K).eval n preCols pub W r = ((r % 16 : ℕ) : F) :=
  ev_per16 (f := id) rfl hr

omit hsat in
theorem ev_K0 {r : ℕ} (hr : r < n) : (p P_K0).eval n preCols pub W r = if r % 16 = 0 then 1 else 0 := by
  rw [ev_per16 (f := fun k => if k = 0 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_K15 {r : ℕ} (hr : r < n) : (p P_K15).eval n preCols pub W r = if r % 16 = 15 then 1 else 0 := by
  rw [ev_per16 (f := fun k => if k = 15 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_LT9 {r : ℕ} (hr : r < n) : (p P_LT9).eval n preCols pub W r = if r % 16 < 9 then 1 else 0 := by
  rw [ev_per16 (f := fun k => if k < 9 then 1 else 0) rfl hr]; split_ifs <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub W r = 0 :=
  hsat r hr c hc

theorem bool {c : ℕ} (hc : c ∈ boolCols) {r : ℕ} (hr : r < n) : W c r = 0 ∨ W c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by
    simp only [constraints, List.mem_append, List.mem_map]; left; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- A constraint of the main list. -/
theorem cm {c : Expr} (h : c ∈ ([ .mul first (om (k ON)), .mul isLast (k ON), .mul notFirst (.mul (k ON) (om (kp ON))),
    .mul first (om (k NEWR)), .mul (k NEWR) (om (p P_K0)), .mul (k NEWR) (om (k ON)),
    .mul notFirst (.mul (k ON) (.sub (k NEWR) (kp ENDR))),
    .sub (k SM) (.mul notFirst (.mul (k ON) (om (k NEWR)))),
    .sub (k ENDR) (.mul (p P_K15) (k LASTF)),
    .mul (k LASTF) (om (k ON)),
    .mul (k ON) (.mul (om (kn ON)) (om (k ENDR))),
    .mul first (k RI), .mul notFirst (.mul (k NEWR) (.sub (.sub (k RI) (kp RI)) one)),
    .mul (k SM) (.sub (k RI) (kp RI)), .mul (k SM) (.sub (k START) (kp START)), .mul (k SM) (.sub (k LW.M) (kp LW.M)),
    .mul (k NEWR) (k BLK),
    .mul (p P_K0) (.mul (k SM) (.sub (.sub (k BLK) (kp BLK)) one)),
    .mul (om (p P_K0)) (.mul (k SM) (.sub (k BLK) (kp BLK))),
    .sub (k F0) (.add (.mul (p P_K0) (k NEWR)) (.mul (om (p P_K0)) (kp F0))),
    .sub (k PKU) (.mul (k F0) (p P_LT9)),
    .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA),
    .mul (k SM) (.mul (k (A 0)) (om (kp (A 3)))),
    .mul (k ON) (.mul (p P_K0) (om (k (A 0)))),
    .mul (om (p P_K0)) (.mul (k SM) (.sub (k LASTF) (kp LASTF))),
    .mul (k ENDR) (.sub (k CNT) (k LW.M)),
    .sub (k T) (.add (.mul (k LASTF) (k LW.M)) (.mul (om (k LASTF)) (.add (.mul (cst 64) (k BLK)) (cst 64)))) ] : List Expr))
    {r : ℕ} (hr : r < n) : c.eval n preCols pub W r = 0 :=
  sat hsat (by simp only [constraints, List.mem_append]; left; left; left; right; exact h) hr

/-- **On rows are a prefix** `[0, e)`, with `0 < e < n`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, 0 < e ∧ e < n ∧ ∀ r < n, (W ON r = 1 ↔ r < e) := by
  have bo := fun r (hr : r < n) => bool hsat (c := ON) (by simp [boolCols]) hr
  have h0 : W ON 0 = 1 := by
    have := cm hsat (c := .mul first (om (k ON))) (by simp) hn
    simp [Expr.eval, ev_first hn, om, one, eval_cst, ev_k hn] at this
    linear_combination -this
  have hl : W ON (n - 1) = 0 := by
    have := cm hsat (c := .mul isLast (k ON)) (by simp) (show n - 1 < n by omega)
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast (show n - 1 < n by omega),
      show ¬ (n - 1 + 1 < n) by omega, if_false, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → W ON (r + 1) = 1 → W ON r = 1 := by
    intro r hr h1
    have := cm hsat (c := .mul notFirst (.mul (k ON) (om (kp ON)))) (by simp) hr
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_k hr, ev_kp hr, h1] at this
    exact (sub_eq_zero.mp this).symm
  have ex : ∃ r, r < n ∧ W ON r = 0 := ⟨n - 1, by omega, hl⟩
  obtain ⟨heN, he0⟩ := Nat.find_spec ex
  have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ W ON r = 0) := fun r h => Nat.find_min ex h
  generalize Nat.find ex = e at heN he0 hmin
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; rw [h0] at he0; exact absurd he0 one_ne_zero
    · exact h
  refine ⟨e, hepos, heN, fun r hr => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
  · by_contra hc
    push Not at hc
    have : ∀ d, r - d < n → W ON (r - d) = 1 := by
      intro d
      induction d with
      | zero => intro _; simpa using h1
      | succ d ih =>
        intro h
        by_cases hd : d < r
        · exact hstep (r - (d + 1)) (by omega) (by rw [show r - (d + 1) + 1 = r - d by omega]; exact ih (by omega))
        · rw [show r - (d + 1) = r - d by omega]; exact ih (by omega)
    have := this (r - e) (by omega)
    rw [show r - (r - e) = e by omega, he0] at this; exact zero_ne_one this
  · rcases bo r hr with h | h
    · exact absurd ⟨hr, h⟩ (hmin r hlt)
    · exact h

/-- `ENDR = K15 · LASTF`. -/
theorem endr_v {r : ℕ} (hr : r < n) : W ENDR r = if r % 16 = 15 then W LASTF r else 0 := by
  have := cm hsat (c := .sub (k ENDR) (.mul (p P_K15) (k LASTF))) (by simp) hr
  simp only [Expr.eval, ev_k hr, ev_K15 hr, sub_eq_zero] at this
  rw [this]; split_ifs <;> simp

theorem endr_bool {r : ℕ} (hr : r < n) : W ENDR r = 0 ∨ W ENDR r = 1 := by
  rw [endr_v hsat hr]; split_ifs
  · exact bool hsat (c := LASTF) (by simp [boolCols]) hr
  · exact Or.inl rfl

/-- `SM = notFirst · ON · (1 − NEWR)`. -/
theorem sm_v {r : ℕ} (hr : r < n) : W SM r = (if r = 0 then 0 else 1) * W ON r * (1 - W NEWR r) := by
  have := cm hsat (c := .sub (k SM) (.mul notFirst (.mul (k ON) (om (k NEWR))))) (by simp) hr
  simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, ev_k hr, sub_eq_zero] at this
  rw [this]; split_ifs <;> ring

/-- A record starts at a block's first row, on. -/
theorem newr_facts {r : ℕ} (hr : r < n) (h : W NEWR r = 1) : r % 16 = 0 ∧ W ON r = 1 := by
  have c1 := cm hsat (c := .mul (k NEWR) (om (p P_K0))) (by simp) hr
  have c2 := cm hsat (c := .mul (k NEWR) (om (k ON))) (by simp) hr
  simp only [Expr.eval, ev_k hr, ev_K0 hr, om, one, eval_cst, Nat.cast_one, h, one_mul] at c1 c2
  refine ⟨by by_contra hc; rw [if_neg hc, sub_zero] at c1; exact one_ne_zero c1, by linear_combination -c2⟩

/-- A later on row starts a record iff the previous row ends one. -/
theorem newr_iff {r : ℕ} (hr : r + 1 < n) (hon : W ON (r + 1) = 1) : W NEWR (r + 1) = W ENDR r := by
  have := cm hsat (c := .mul notFirst (.mul (k ON) (.sub (k NEWR) (kp ENDR)))) (by simp) hr
  simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
    sub_zero, one_mul, ev_k hr, ev_kp hr, hon] at this
  exact sub_eq_zero.mp this

/-- An on row that does not end its record continues it on the next row. -/
theorem cont {r : ℕ} (hr : r < n) (hon : W ON r = 1) (hend : W ENDR r = 0) :
    r + 1 < n ∧ W ON (r + 1) = 1 ∧ W NEWR (r + 1) = 0 ∧ W SM (r + 1) = 1 := by
  have hr1 : r + 1 < n := by
    by_contra h
    have := cm hsat (c := .mul isLast (k ON)) (by simp) hr
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast hr, if_neg h, sub_zero, one_mul,
      ev_k hr, hon] at this
    exact one_ne_zero this
  have c := cm hsat (c := .mul (k ON) (.mul (om (kn ON)) (om (k ENDR)))) (by simp) hr
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr, ev_kn hr1, hon, hend, sub_zero, mul_one,
    one_mul] at c
  have hon1 : W ON (r + 1) = 1 := by linear_combination -c
  have hnw : W NEWR (r + 1) = 0 := by rw [newr_iff hsat hr1 hon1, hend]
  refine ⟨hr1, hon1, hnw, ?_⟩
  rw [sm_v hsat hr1, if_neg (by omega), hon1, hnw]; ring

/-- On a continuing row (`SM`), the record's values carry over. -/
theorem carry {r : ℕ} (hr : r + 1 < n) (hsm : W SM (r + 1) = 1) {X : ℕ} (hX : X = RI ∨ X = START ∨ X = LW.M) :
    W X (r + 1) = W X r := by
  rcases hX with rfl | rfl | rfl
  · have := cm hsat (c := .mul (k SM) (.sub (k RI) (kp RI))) (by simp) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hsm, one_mul, sub_eq_zero] at this; exact this
  · have := cm hsat (c := .mul (k SM) (.sub (k START) (kp START))) (by simp) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hsm, one_mul, sub_eq_zero] at this; exact this
  · have := cm hsat (c := .mul (k SM) (.sub (k LW.M) (kp LW.M))) (by simp) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hsm, one_mul, sub_eq_zero] at this; exact this

/-- **A record's start**: the last `NEWR` row at or before an on row; the rows after it continue. -/
theorem rec_start : ∀ r < n, W ON r = 1 → ∃ st ≤ r, W NEWR st = 1 ∧ ∀ r', st < r' → r' ≤ r → W SM r' = 1 := by
  intro r
  induction r with
  | zero =>
    intro hr _
    have := cm hsat (c := .mul first (om (k NEWR))) (by simp) hr
    simp [Expr.eval, ev_first hr, om, one, eval_cst, ev_k hr] at this
    exact ⟨0, le_rfl, by linear_combination -this, fun r' h1 h2 => by omega⟩
  | succ r ih =>
    intro hr hon
    rcases bool hsat (c := NEWR) (by simp [boolCols]) hr with h0 | h1
    · have hsm : W SM (r + 1) = 1 := by rw [sm_v hsat hr, if_neg (by omega), hon, h0]; ring
      have hon' : W ON r = 1 := by
        have := cm hsat (c := .mul notFirst (.mul (k ON) (om (kp ON)))) (by simp) hr
        simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega,
          if_false, sub_zero, one_mul, ev_k hr, ev_kp hr, hon] at this
        exact (sub_eq_zero.mp this).symm
      obtain ⟨st, hst, hn1, hsm'⟩ := ih (by omega) hon'
      refine ⟨st, by omega, hn1, fun r' h1 h2 => ?_⟩
      rcases Nat.lt_or_ge r' (r + 1) with h | h
      · exact hsm' r' h1 (by omega)
      · rw [show r' = r + 1 by omega]; exact hsm
    · exact ⟨r + 1, le_rfl, h1, fun r' h1 h2 => by omega⟩

/-- **A record's end**: the first `ENDR` row at or after an on row; the rows after it, up to it, continue. -/
theorem rec_end : ∀ d r, n = r + d → r < n → W ON r = 1 → ∃ en, r ≤ en ∧ en < n ∧ W ENDR en = 1 ∧ W ON en = 1 ∧
    (∀ r', r ≤ r' → r' < en → W ENDR r' = 0) ∧ ∀ r', r < r' → r' ≤ en → W SM r' = 1 := by
  intro d
  induction d with
  | zero => intro r hd hr hon; exfalso; omega
  | succ d ih =>
    intro r hd hr hon
    rcases endr_bool hsat hr with h0 | h1
    · obtain ⟨hr1, hon1, -, hsm1⟩ := cont hsat hr hon h0
      obtain ⟨en, h1, h2, h3, h4, h5, h6⟩ := ih (r + 1) (by omega) hr1 hon1
      refine ⟨en, by omega, h2, h3, h4, fun r' a b => ?_, fun r' a b => ?_⟩
      · rcases Nat.eq_or_lt_of_le a with e | e
        · rw [← e]; exact h0
        · exact h5 r' (by omega) b
      · rcases Nat.eq_or_lt_of_le (show r + 1 ≤ r' by omega) with e | e
        · rw [← e]; exact hsm1
        · exact h6 r' e b
    · exact ⟨r, le_rfl, hr, h1, hon, fun r' a b => by omega, fun r' a b => by omega⟩

theorem sm_on {r : ℕ} (hr : r < n) (h : W SM r = 1) : W ON r = 1 ∧ W NEWR r = 0 := by
  rw [sm_v hsat hr] at h
  rcases bool hsat (c := ON) (by simp [boolCols]) hr with o | o <;>
    rcases bool hsat (c := NEWR) (by simp [boolCols]) hr with w | w <;>
    simp_all

/-- **A record's window** `[st, en]` around an on row. -/
theorem window {r : ℕ} (hr : r < n) (hon : W ON r = 1) : ∃ st en, st ≤ r ∧ r ≤ en ∧ en < n ∧ st % 16 = 0 ∧
    en % 16 = 15 ∧ W NEWR st = 1 ∧ W ENDR en = 1 ∧ (∀ r', st < r' → r' ≤ en → W SM r' = 1) ∧
    (∀ r', st ≤ r' → r' < en → W ENDR r' = 0) ∧ (∀ r', st ≤ r' → r' ≤ en → W ON r' = 1) := by
  obtain ⟨st, hst, hnw, hsm1⟩ := rec_start hsat r hr hon
  obtain ⟨en, hre, hen, hend, honen, hend0, hsm2⟩ := rec_end hsat (n - r) r (by omega) hr hon
  have hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1 := fun r' a b => by
    rcases Nat.lt_or_ge r r' with h | h
    · exact hsm2 r' h b
    · exact hsm1 r' a h
  have hst16 := (newr_facts hsat (show st < n by omega) hnw)
  refine ⟨st, en, hst, hre, hen, hst16.1, ?_, hnw, hend, hsm, fun r' a b => ?_, fun r' a b => ?_⟩
  · have := endr_v hsat hen; rw [hend] at this
    by_contra hc; rw [if_neg hc] at this; exact one_ne_zero this
  · have h1 := hsm (r' + 1) (by omega) (by omega)
    obtain ⟨o1, w1⟩ := sm_on hsat (show r' + 1 < n by omega) h1
    rw [← newr_iff hsat (show r' + 1 < n by omega) o1, w1]
  · rcases Nat.eq_or_lt_of_le a with e | e
    · rw [← e]; exact hst16.2
    · exact (sm_on hsat (show r' < n by omega) (hsm r' e b)).1

/-- The record's values are constant across its window. -/
theorem win_const {st en : ℕ} (hen : en < n) (hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1) {X : ℕ}
    (hX : X = RI ∨ X = START ∨ X = LW.M) : ∀ r', st ≤ r' → r' ≤ en → W X r' = W X st := by
  intro r' a b
  induction r' with
  | zero => rw [show st = 0 by omega]
  | succ r' ih =>
    rcases Nat.eq_or_lt_of_le a with e | e
    · rw [e]
    · rw [carry hsat (by omega) (hsm _ e b) hX, ih (by omega) (by omega)]

/-- Blocks count from 0 across the window. -/
theorem win_blk {st en : ℕ} (hen : en < n) (hst16 : st % 16 = 0) (hnw : W NEWR st = 1)
    (hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1) : ∀ r', st ≤ r' → r' ≤ en → W BLK r' = (((r' - st) / 16 : ℕ) : F) := by
  intro r' a b
  induction r' with
  | zero =>
    have hst : st = 0 := by omega
    subst hst
    have := cm hsat (c := .mul (k NEWR) (k BLK)) (by simp) (show 0 < n by omega)
    simp only [Expr.eval, ev_k (show 0 < n by omega), hnw, one_mul] at this
    simpa using this
  | succ r' ih =>
    rcases Nat.eq_or_lt_of_le a with e | e
    · rw [← e]
      have := cm hsat (c := .mul (k NEWR) (k BLK)) (by simp) (show st < n by omega)
      simp only [Expr.eval, ev_k (show st < n by omega), hnw, one_mul] at this
      simpa using this
    · have hr1 : r' + 1 < n := by omega
      have h1 := hsm _ e b
      have ih' := ih (by omega) (by omega)
      by_cases hk : (r' + 1) % 16 = 0
      · have := cm hsat (c := .mul (p P_K0) (.mul (k SM) (.sub (.sub (k BLK) (kp BLK)) one))) (by simp) hr1
        simp only [Expr.eval, ev_K0 hr1, if_pos hk, one_mul, ev_k hr1, ev_kp hr1, h1, one, eval_cst, Nat.cast_one,
          sub_eq_zero] at this
        rw [show (r' + 1 - st) / 16 = (r' - st) / 16 + 1 by omega]
        push_cast; rw [← ih']; linear_combination this
      · have := cm hsat (c := .mul (om (p P_K0)) (.mul (k SM) (.sub (k BLK) (kp BLK)))) (by simp) hr1
        simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K0 hr1, if_neg hk, sub_zero, one_mul, ev_k hr1,
          ev_kp hr1, h1, sub_eq_zero] at this
        rw [this, ih', show (r' + 1 - st) / 16 = (r' - st) / 16 by omega]

/-- A block's last flag: set iff the block ends the window. -/
theorem win_last {st en : ℕ} (hen : en < n) (hst16 : st % 16 = 0) (hen16 : en % 16 = 15)
    (hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1) (hend : W ENDR en = 1) (hend0 : ∀ r', st ≤ r' → r' < en → W ENDR r' = 0)
    {r0 : ℕ} (h1 : st ≤ r0) (h2 : r0 ≤ en) (h0 : r0 % 16 = 0) :
    W LASTF r0 = if r0 + 15 = en then 1 else 0 := by
  have lconst : ∀ d ≤ 15, W LASTF (r0 + d) = W LASTF r0 := by
    intro d hd
    induction d with
    | zero => rfl
    | succ d ih =>
      have hrr : r0 + d + 1 < n := by omega
      have := cm hsat (c := .mul (om (p P_K0)) (.mul (k SM) (.sub (k LASTF) (kp LASTF)))) (by simp) hrr
      simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K0 hrr, show ¬ ((r0 + d + 1) % 16 = 0) by omega,
        if_false, sub_zero, one_mul, ev_k hrr, ev_kp hrr, hsm (r0 + d + 1) (by omega) (by omega), sub_eq_zero] at this
      rw [show r0 + (d + 1) = r0 + d + 1 by ring, this, ih (by omega)]
  have he := endr_v hsat (show r0 + 15 < n by omega)
  rw [if_pos (by omega), lconst 15 le_rfl] at he
  rw [← he]
  split_ifs with h
  · rw [h]; exact hend
  · exact hend0 (r0 + 15) (by omega) (by omega)

/-- `PKU` marks the window's first nine rows. -/
theorem win_pku {st en : ℕ} (hen : en < n) (hst16 : st % 16 = 0) (hnw : W NEWR st = 1)
    (hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1) :
    ∀ r', st ≤ r' → r' ≤ en → W PKU r' = if r' - st < 9 then 1 else 0 := by
  have hf : ∀ r', st ≤ r' → r' ≤ en → W F0 r' = if r' - st < 16 then 1 else 0 := by
    intro r' a b
    induction r' with
    | zero =>
      have hst : st = 0 := by omega
      subst hst
      have := cm hsat (c := .sub (k F0) (.add (.mul (p P_K0) (k NEWR)) (.mul (om (p P_K0)) (kp F0)))) (by simp)
        (show 0 < n by omega)
      simp only [Expr.eval, ev_k (show 0 < n by omega), ev_K0 (show 0 < n by omega), Nat.zero_mod, if_true, hnw,
        om, one, eval_cst, Nat.cast_one, sub_self, zero_mul, add_zero, mul_one, sub_eq_zero] at this
      simp [this]
    | succ r' ih =>
      have hr1 : r' + 1 < n := by omega
      have c := cm hsat (c := .sub (k F0) (.add (.mul (p P_K0) (k NEWR)) (.mul (om (p P_K0)) (kp F0)))) (by simp) hr1
      rcases Nat.eq_or_lt_of_le a with e | e
      · rw [← e] at c ⊢
        simp only [Expr.eval, ev_k (show st < n by omega), ev_K0 (show st < n by omega), hst16, if_true, hnw, om, one,
          eval_cst, Nat.cast_one, sub_self, zero_mul, add_zero, mul_one, sub_eq_zero] at c
        simp [c]
      · obtain ⟨-, w1⟩ := sm_on hsat hr1 (hsm _ e b)
        simp only [Expr.eval, ev_k hr1, ev_kp hr1, ev_K0 hr1, w1, om, one, eval_cst, Nat.cast_one, mul_zero, zero_add,
          sub_eq_zero] at c
        rw [c, ih (by omega) (by omega)]
        by_cases hk : (r' + 1) % 16 = 0
        · rw [if_pos hk, sub_self, zero_mul, if_neg (by omega)]
        · rw [if_neg hk, sub_zero, one_mul]
          by_cases h16 : r' - st < 16
          · rw [if_pos h16, if_pos (by omega)]
          · rw [if_neg h16, if_neg (by omega)]
  intro r' a b
  have := cm hsat (c := .sub (k PKU) (.mul (k F0) (p P_LT9))) (by simp) (show r' < n by omega)
  simp only [Expr.eval, ev_k (show r' < n by omega), ev_LT9 (show r' < n by omega), hf r' a b, sub_eq_zero] at this
  rw [this]
  by_cases h9 : r' - st < 9
  · rw [if_pos (by omega), if_pos (by omega), if_pos h9, one_mul]
  · by_cases h16 : r' - st < 16
    · rw [if_pos h16, if_neg (by omega), if_neg h9, mul_zero]
    · rw [if_neg h16, if_neg h9, zero_mul]

theorem bA {j : ℕ} (hj : j < 4) {r : ℕ} (hr : r < n) : W (A j) r = 0 ∨ W (A j) r = 1 :=
  bool hsat (c := A j) (by interval_cases j <;> simp [boolCols, A]) hr

/-- **A record's active bytes are its message positions below its length.** -/
theorem win_count (hnP : n ≤ 2 ^ 25) {st en : ℕ} (hen : en < n) (hnw : W NEWR st = 1) (hste : st ≤ en)
    (hsm : ∀ r', st < r' → r' ≤ en → W SM r' = 1) (hend : W ENDR en = 1) :
    (W LW.M en).val ≤ 4 * (en + 1 - st) ∧
      ∀ q < 4 * (en + 1 - st), ((W (A (q % 4)) (st + q / 4)).val = 1 ↔ q < (W LW.M en).val) := by
  set L := (W LW.M en).val with hLdef
  have hsm0 : W SM st = 0 := by rw [sm_v hsat (by omega), hnw]; ring
  set a : ℕ → ℕ := fun q => (W (A (q % 4)) (st + q / 4)).val with ha
  have hb : ∀ q < 4 * (en + 1 - st), a q ≤ 1 := by
    intro q hq
    rcases bA hsat (j := q % 4) (Nat.mod_lt _ (by norm_num)) (r := st + q / 4) (by omega) with h | h <;>
      simp [ha, h, ZMod.val_one]
  have mrow : ∀ r < n, ∀ j < 3, (W (A (j + 1)) r).val ≤ (W (A j) r).val := by
    intro r hr j hj
    have := sat hsat (c := .mul (k (A (j + 1))) (om (k (A j)))) (by
      simp only [constraints, List.mem_append, List.mem_map, List.mem_range]; right; exact ⟨j, hj, rfl⟩) hr
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr] at this
    rcases bA hsat (j := j + 1) (by omega) hr with h | h <;> rcases bA hsat (j := j) (by omega) hr with g | g <;>
      simp_all [ZMod.val_one]
  have mcross : ∀ r, st < r → r ≤ en → (W (A 0) r).val ≤ (W (A 3) (r - 1)).val := by
    intro r h1 h2
    have hr : r < n := by omega
    have := cm hsat (c := .mul (k SM) (.mul (k (A 0)) (om (kp (A 3))))) (by simp) hr
    rw [show r = r - 1 + 1 by omega] at this
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k (show r - 1 + 1 < n by omega),
      ev_kp (show r - 1 + 1 < n by omega)] at this
    rw [show r - 1 + 1 = r by omega, hsm r h1 h2, one_mul] at this
    rcases bA hsat (j := 0) (by norm_num) hr with h | h <;> rcases bA hsat (j := 3) (by norm_num) (show r - 1 < n by omega) with g | g <;>
      simp_all [ZMod.val_one]
  have hm : ∀ q, q + 1 < 4 * (en + 1 - st) → a (q + 1) ≤ a q := by
    intro q hq
    simp only [ha]
    by_cases h3 : q % 4 = 3
    · rw [show (q + 1) % 4 = 0 by omega, show st + (q + 1) / 4 = (st + q / 4 + 1) by omega, h3]
      have := mcross (st + q / 4 + 1) (by omega) (by omega)
      rwa [show st + q / 4 + 1 - 1 = st + q / 4 by omega] at this
    · rw [show (q + 1) % 4 = q % 4 + 1 by omega, show (q + 1) / 4 = q / 4 by omega]
      exact mrow (st + q / 4) (by omega) (q % 4) (by omega)
  have hcnt : ∀ d, st + d ≤ en → W CNT (st + d) = ((∑ q ∈ Finset.range (4 * (d + 1)), a q : ℕ) : F) := by
    have rowsum : ∀ r < n, sumA.eval n preCols pub W r =
        (((W (A 0) r).val + (W (A 1) r).val + (W (A 2) r).val + (W (A 3) r).val : ℕ) : F) := by
      intro r hr
      simp only [sumA, Expr.eval, ev_k hr]; push_cast; simp only [ZMod.natCast_zmod_val]; ring
    have blk : ∀ d, ∑ q ∈ Finset.Ico (4 * d) (4 * (d + 1)), a q =
        (W (A 0) (st + d)).val + (W (A 1) (st + d)).val + (W (A 2) (st + d)).val + (W (A 3) (st + d)).val := by
      intro d
      rw [show 4 * (d + 1) = 4 * d + 4 by ring, Finset.sum_Ico_eq_sum_range]
      simp [Finset.sum_range_succ, ha, show ∀ i < 4, (4 * d + i) / 4 = d from fun i hi => by omega,
        show ∀ i < 4, (4 * d + i) % 4 = i from fun i hi => by omega]
    intro d
    induction d with
    | zero =>
      intro h
      have hr : st < n := by omega
      have := cm hsat (c := .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA)) (by simp) hr
      simp only [Expr.eval, ev_k hr, sub_eq_zero] at this
      rw [Nat.add_zero, this, hsm0, zero_mul, zero_add, rowsum st hr]
      congr 1
      have b0 := blk 0
      rw [mul_zero, Nat.add_zero, ← Finset.range_eq_Ico] at b0
      exact b0.symm
    | succ d ih =>
      intro h
      have hr : st + d + 1 < n := by omega
      have := cm hsat (c := .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA)) (by simp) hr
      simp only [Expr.eval, ev_k hr, ev_kp hr, sub_eq_zero] at this
      rw [show st + (d + 1) = st + d + 1 by ring, this, hsm _ (by omega) (by omega), one_mul, ih (by omega),
        rowsum _ hr, ← Finset.sum_range_add_sum_Ico _ (show 4 * (d + 1) ≤ 4 * (d + 1 + 1) by omega),
        show st + d + 1 = st + (d + 1) by ring, ← blk (d + 1)]
      push_cast; ring
  have he := cm hsat (c := .mul (k ENDR) (.sub (k CNT) (k LW.M))) (by simp) hen
  simp only [Expr.eval, ev_k hen, hend, one_mul, sub_eq_zero] at he
  have hc := hcnt (en - st) (by omega)
  rw [show st + (en - st) = en by omega, show en - st + 1 = en + 1 - st by omega, he] at hc
  have hsumle : ∑ q ∈ Finset.range (4 * (en + 1 - st)), a q ≤ 4 * (en + 1 - st) := by
    calc _ ≤ ∑ q ∈ Finset.range (4 * (en + 1 - st)), 1 := Finset.sum_le_sum (fun q hq => hb q (by simpa using hq))
      _ = 4 * (en + 1 - st) := by simp
  have hLv : W LW.M en = (L : F) := by rw [hLdef, ZMod.natCast_zmod_val]
  rw [hLv] at hc
  have hsum := natCast_inj_of_lt (Block.Fields.lt_P (by omega)) (ZMod.val_lt _) hc.symm
  exact Block.B2Msg.prefix_of_count hb hm hsum

/-- **An on row of the walker**: in its record's window `[st, en]`, with the record's values, block, active
bytes (its message positions below `m`), last flag and counter, and `PKU` on the first nine rows. -/
theorem row_fact (hnP : n ≤ 2 ^ 25) {r : ℕ} (hr : r < n) (hon : W ON r = 1) :
    ∃ st, st ≤ r ∧ st % 16 = 0 ∧ W NEWR st = 1 ∧ r - st < 16 * Block.B2Msg.nbOf (W LW.M st).val ∧
      (∀ X, X = RI ∨ X = START ∨ X = LW.M → W X r = W X st) ∧ 1 ≤ (W LW.M st).val ∧
      W BLK r = (((r - st) / 16 : ℕ) : F) ∧
      (∀ j < 4, ((W (A j) r).val = 1 ↔ 4 * (r - st) + j < (W LW.M st).val) ∧ (W (A j) r = 0 ∨ W (A j) r = 1)) ∧
      (∀ j < 4, W (A j) r = 0 → W (B j) r = 0) ∧
      (r % 16 = 0 → (W LASTF r = 1 ↔ (r - st) / 16 + 1 = Block.B2Msg.nbOf (W LW.M st).val) ∧
        (W LASTF r = 0 ∨ W LASTF r = 1) ∧
        W T r = ((if (r - st) / 16 + 1 = Block.B2Msg.nbOf (W LW.M st).val then (W LW.M st).val
          else 64 * ((r - st) / 16 + 1) : ℕ) : F)) ∧
      W PKU r = if r - st < 9 then 1 else 0 := by
  obtain ⟨st, en, hst, hre, hen, hst16, hen16, hnw, hend, hsm, hend0, hon'⟩ := window hsat hr hon
  have hcst := fun X hX r' a b => win_const hsat (st := st) (en := en) hen hsm (X := X) hX r' a b
  have hMen : W LW.M en = W LW.M st := hcst LW.M (Or.inr (Or.inr rfl)) en (by omega) le_rfl
  obtain ⟨hLle, hpre⟩ := win_count hsat hnP hen hnw (by omega) hsm hend
  rw [hMen] at hLle hpre
  set m := (W LW.M st).val with hm
  set nbr := (en + 1 - st) / 16 with hnbr
  have hrows : en + 1 - st = 16 * nbr := by omega
  -- every block starts active
  have act : ∀ i < nbr, 64 * i < m := by
    intro i hi
    have hr0 : st + 16 * i < n := by omega
    have := cm hsat (c := .mul (k ON) (.mul (p P_K0) (om (k (A 0))))) (by simp) hr0
    simp only [Expr.eval, ev_k hr0, ev_K0 hr0, show (st + 16 * i) % 16 = 0 by omega, if_true, one_mul, om, one,
      eval_cst, Nat.cast_one, hon' (st + 16 * i) (by omega) (by omega)] at this
    have hA : W (A 0) (st + 16 * i) = 1 := by linear_combination -this
    exact (hpre (64 * i) (by omega)).mp (by
      rw [show 64 * i % 4 = 0 by omega, show st + 64 * i / 4 = st + 16 * i by omega, hA, ZMod.val_one])
  have hnb : nbr = Block.B2Msg.nbOf m := by
    have h1 : 1 ≤ nbr := by omega
    have := act (nbr - 1) (by omega)
    unfold Block.B2Msg.nbOf; omega
  have hm1 : 1 ≤ m := by have := act 0 (by omega); omega
  refine ⟨st, hst, hst16, hnw, by rw [← hnb]; omega, fun X hX => hcst X hX r hst hre, hm1,
    win_blk hsat hen hst16 hnw hsm r hst hre, fun j hj => ⟨?_, bA hsat hj hr⟩, fun j hj h0 => ?_, fun hk0 => ?_,
    win_pku hsat hen hst16 hnw hsm r hst hre⟩
  · have := hpre (4 * (r - st) + j) (by omega)
    rwa [show (4 * (r - st) + j) % 4 = j by omega, show st + (4 * (r - st) + j) / 4 = r by omega] at this
  · have := sat hsat (c := .mul (k (B j)) (om (k (A j)))) (by
      simp only [constraints, List.mem_append, List.mem_map, List.mem_range]; left; left; right; exact ⟨j, hj, rfl⟩) hr
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr, h0, sub_zero, mul_one] at this
    exact this
  · simp only [← hm]
    have hl := win_last hsat hen hst16 hen16 hsm hend hend0 hst hre hk0
    have hiff : r + 15 = en ↔ (r - st) / 16 + 1 = Block.B2Msg.nbOf m := by rw [← hnb]; omega
    have hLv : W LASTF r = if (r - st) / 16 + 1 = Block.B2Msg.nbOf m then 1 else 0 := by
      rw [hl]; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)
    refine ⟨by rw [hLv]; split_ifs with h <;> simp [h], by rw [hLv]; split_ifs <;> simp, ?_⟩
    have := cm hsat (c := .sub (k T) (.add (.mul (k LASTF) (k LW.M)) (.mul (om (k LASTF))
      (.add (.mul (cst 64) (k BLK)) (cst 64))))) (by simp) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, win_blk hsat hen hst16 hnw hsm r hst hre,
      hcst LW.M (Or.inr (Or.inr rfl)) r hst hre, sub_eq_zero, hLv] at this
    rw [this]
    split_ifs
    · rw [hm, ZMod.natCast_zmod_val]; ring
    · push_cast; ring

end Rows

end StarkedAir.SetPass.LW
