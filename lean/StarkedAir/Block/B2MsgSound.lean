/-
**Blake2s message words, soundness (M3a.6).** In a satisfied `block_b2msg` trace with its byte reads
answered by the undo table, the on rows are the stream's blocks; the active bytes are exactly its
positions below the length; so each row's word is the stream's little-endian word (zero past the end),
the stream has `max 1 ⌈len / 64⌉` blocks, and each block's `last` and `t` are Blake2s's.
-/
import StarkedAir.Block.B2Msg
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.B2Msg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

/-- **Monotone flags with a known count are a prefix.** -/
theorem prefix_of_count {a : ℕ → ℕ} {N c : ℕ} (hb : ∀ q < N, a q ≤ 1) (hm : ∀ q, q + 1 < N → a (q + 1) ≤ a q)
    (hc : ∑ q ∈ Finset.range N, a q = c) : c ≤ N ∧ ∀ q < N, (a q = 1 ↔ q < c) := by
  -- the ones are an initial segment: `a q = 1` for `q < m`, `0` after
  obtain ⟨m, hmN, hpre⟩ : ∃ m ≤ N, ∀ q < N, (a q = 1 ↔ q < m) := by
    by_cases hall : ∀ q < N, a q = 1
    · exact ⟨N, le_rfl, fun q hq => ⟨fun _ => hq, fun _ => hall q hq⟩⟩
    · push Not at hall
      obtain ⟨q0, hq0, hne⟩ := hall
      have ex : ∃ q, q < N ∧ a q ≠ 1 := ⟨q0, hq0, hne⟩
      obtain ⟨hfN, hf1⟩ := Nat.find_spec ex
      have hmin : ∀ q < Nat.find ex, ¬ (q < N ∧ a q ≠ 1) := fun q h => Nat.find_min ex h
      generalize Nat.find ex = f at hfN hf1 hmin
      have hf0 : a f = 0 := by have := hb f hfN; omega
      have hz : ∀ d, f + d < N → a (f + d) = 0 := by
        intro d
        induction d with
        | zero => intro _; simpa using hf0
        | succ d ih =>
          intro h; rw [show f + (d + 1) = f + d + 1 by ring]
          have := hm (f + d) (by omega); have := ih (by omega); omega
      refine ⟨f, hfN.le, fun q hq => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
      · by_contra hc
        push Not at hc
        have := hz (q - f) (by omega)
        rw [show f + (q - f) = q by omega] at this; omega
      · have := hmin q hlt
        push Not at this
        exact this hq
  have hsum : ∑ q ∈ Finset.range N, a q = m := by
    rw [← Finset.sum_range_add_sum_Ico _ hmN]
    have h1 : ∑ q ∈ Finset.range m, a q = m := by
      rw [Finset.sum_congr rfl (fun q hq => (hpre q (by simp at hq; omega)).mpr (by simpa using hq))]; simp
    have h2 : ∑ q ∈ Finset.Ico m N, a q = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hq
      have := hb q h2
      have := (hpre q h2).not.mpr (by omega)
      omega
    rw [h1, h2, add_zero]
  rw [hsum] at hc
  subst hc
  exact ⟨hmN, hpre⟩

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
theorem ev_kn {c r : ℕ} (hr : r + 1 < n) : (kn c).eval n preCols pub M r = M c (r + 1) := by
  simp [kn, eval_col, wrap_one hr]

omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, p, pre, Expr.eval, wrap_zero hr, preCols, P_FIRST, PreCol.eval]

omit hsat in
theorem ev_notLast {r : ℕ} (hr : r < n) : (p P_NOTLAST).eval n preCols pub M r = if r + 1 < n then 1 else 0 := by
  simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_NOTLAST, PreCol.eval]

omit hsat in
theorem ev_per16 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per16 f) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub M r = ((f (r % 16) : ℕ) : F) := by
  simp only [p, pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 16 < 16 := Nat.mod_lt _ (by norm_num)
  simp [per16, PreCol.eval, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_K {r : ℕ} (hr : r < n) : (p P_K).eval n preCols pub M r = ((r % 16 : ℕ) : F) :=
  ev_per16 (f := id) rfl hr

omit hsat in
theorem ev_K0 {r : ℕ} (hr : r < n) : (p P_K0).eval n preCols pub M r = if r % 16 = 0 then 1 else 0 := by
  rw [ev_per16 (f := fun k => if k = 0 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_K15 {r : ℕ} (hr : r < n) : (p P_K15).eval n preCols pub M r = if r % 16 = 15 then 1 else 0 := by
  rw [ev_per16 (f := fun k => if k = 15 then 1 else 0) rfl hr]; split_ifs <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

theorem bool {c : ℕ} (hc : c ∈ boolCols) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by
    simp only [constraints, List.mem_append, List.mem_map]; left; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hsat in
theorem mem_main {c : Expr} (h : c ∈ [ .mul first (om (k ON)), .mul first (k BLK),
    .mul isLast (k ON),
    .mul notFirst (.mul (k ON) (om (kp ON))),
    .sub (k SM) (.mul notFirst (k ON)),
    .mul (p P_K0) (.sub (k BLK) (.mul (k SM) (.add (kp BLK) one))),
    .mul (om (p P_K0)) (.sub (k BLK) (kp BLK)),
    .sub (k POS) (.add (.mul (cst 64) (k BLK)) (.mul (cst 4) (p P_K))),
    .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA),
    .mul (k SM) (.mul (k (A 0)) (om (kp (A 3)))),
    .mul (p P_K0) (.mul (om (k (A 0))) (k BLK)),
    .sub (k END) (.mul (p P_NOTLAST) (.sub (k ON) (kn ON))),
    .mul (om (p P_K15)) ends,
    .mul (p P_K15) (.sub (k LASTF) ends),
    .mul (om (p P_K0)) (.sub (k LASTF) (kp LASTF)),
    .mul ends (.sub (k CNT) lenS),
    .sub (k T) (.add (.mul (k LASTF) lenS) (.mul (om (k LASTF)) (.add (.mul (cst 64) (k BLK)) (cst 64)))) ]) :
    c ∈ constraints := by
  simp only [constraints, List.mem_append]; left; left; left; right; exact h

/-- **On rows are a prefix** `[0, e)`, with `0 < e < n`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, 0 < e ∧ e < n ∧ ∀ r < n, (M ON r = 1 ↔ r < e) := by
  have bo := fun r (hr : r < n) => bool hsat (c := ON) (by simp [boolCols]) hr
  have h0 : M ON 0 = 1 := by
    have := sat hsat (mem_main (c := .mul first (om (k ON))) (by simp)) hn
    simp [Expr.eval, ev_first hn, om, one, eval_cst, ev_k hn] at this
    linear_combination -this
  have hl : M ON (n - 1) = 0 := by
    have := sat hsat (mem_main (c := .mul isLast (k ON)) (by simp)) (show n - 1 < n by omega)
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast (show n - 1 < n by omega),
      show ¬ (n - 1 + 1 < n) by omega, if_false, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → M ON (r + 1) = 1 → M ON r = 1 := by
    intro r hr h1
    have := sat hsat (mem_main (c := .mul notFirst (.mul (k ON) (om (kp ON)))) (by simp)) hr
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_k hr, ev_kp hr, h1] at this
    exact (sub_eq_zero.mp this).symm
  have ex : ∃ r, r < n ∧ M ON r = 0 := ⟨n - 1, by omega, hl⟩
  obtain ⟨heN, he0⟩ := Nat.find_spec ex
  have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ M ON r = 0) := fun r h => Nat.find_min ex h
  generalize Nat.find ex = e at heN he0 hmin
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; rw [h0] at he0; exact absurd he0 one_ne_zero
    · exact h
  refine ⟨e, hepos, heN, fun r hr => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
  · by_contra hc
    push Not at hc
    -- on at `r ≥ e` forces on at `e`
    have : ∀ d, r - d < n → M ON (r - d) = 1 := by
      intro d
      induction d with
      | zero => intro _; simpa using h1
      | succ d ih =>
        intro h
        by_cases hd : d < r
        · have := hstep (r - (d + 1)) (by omega) (by rw [show r - (d + 1) + 1 = r - d by omega]; exact ih (by omega))
          exact this
        · rw [show r - (d + 1) = r - d by omega]; exact ih (by omega)
    have := this (r - e) (by omega)
    rw [show r - (r - e) = e by omega, he0] at this; exact zero_ne_one this
  · rcases bo r hr with h | h
    · exact absurd ⟨hr, h⟩ (hmin r hlt)
    · exact h

/-- **Layout**: `SM`, `END`, block numbers and positions, given the on prefix. -/
theorem layout (hn : 0 < n) {e : ℕ} (he0 : 0 < e) (hen : e < n) (hon : ∀ r < n, (M ON r = 1 ↔ r < e)) :
    (∀ r < n, M SM r = if 0 < r ∧ r < e then 1 else 0) ∧
    (∀ r < n, M END r = if r + 1 = e then 1 else 0) ∧ e % 16 = 0 ∧
    (∀ r < e, M BLK r = ((r / 16 : ℕ) : F) ∧ M POS r = ((4 * r : ℕ) : F)) := by
  have onv : ∀ r < n, M ON r = if r < e then 1 else 0 := by
    intro r hr
    split_ifs with h
    · exact (hon r hr).mpr h
    · rcases bool hsat (c := ON) (by simp [boolCols]) hr with g | g
      · exact g
      · exact absurd ((hon r hr).mp g) h
  have hSM : ∀ r < n, M SM r = if 0 < r ∧ r < e then 1 else 0 := by
    intro r hr
    have := sat hsat (mem_main (c := .sub (k SM) (.mul notFirst (k ON))) (by simp)) hr
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, ev_k hr, onv r hr,
      sub_eq_zero] at this
    rw [this]
    by_cases h0 : r = 0
    · subst h0; simp
    · by_cases h2 : r < e <;> simp [h0, h2] <;> omega
  have hEND : ∀ r < n, M END r = if r + 1 = e then 1 else 0 := by
    intro r hr
    have := sat hsat (mem_main (c := .sub (k END) (.mul (p P_NOTLAST) (.sub (k ON) (kn ON)))) (by simp)) hr
    simp only [Expr.eval, ev_k hr, ev_notLast hr, sub_eq_zero] at this
    rw [this]
    by_cases hl : r + 1 < n
    · rw [if_pos hl, one_mul, ev_kn hl, onv r hr, onv (r + 1) hl]
      split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [if_neg hl, zero_mul, if_neg (by omega)]
  have endK : ∀ r < n, M END r = 1 → r % 16 = 15 := by
    intro r hr h
    have := sat hsat (mem_main (c := .mul (om (p P_K15)) ends) (by simp)) hr
    simp only [ends, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K15 hr, ev_k hr, h, mul_one] at this
    by_contra hc; rw [if_neg hc, sub_zero] at this; exact one_ne_zero this
  have he16 : e % 16 = 0 := by
    have := endK (e - 1) (by omega) (by rw [hEND (e - 1) (by omega), if_pos (by omega)])
    omega
  refine ⟨hSM, hEND, he16, fun r hr => ?_⟩
  have hBLK : ∀ r < e, M BLK r = ((r / 16 : ℕ) : F) := by
    intro r hr
    induction r with
    | zero =>
      have := sat hsat (mem_main (c := .mul first (k BLK)) (by simp)) (show 0 < n by omega)
      simpa [Expr.eval, ev_first (show 0 < n by omega), ev_k (show 0 < n by omega)] using this
    | succ r ih =>
      have hr1 : r + 1 < n := by omega
      have ih' := ih (by omega)
      by_cases hk : (r + 1) % 16 = 0
      · have := sat hsat (mem_main (c := .mul (p P_K0) (.sub (k BLK) (.mul (k SM) (.add (kp BLK) one)))) (by simp)) hr1
        simp only [Expr.eval, ev_K0 hr1, if_pos hk, one_mul, ev_k hr1, ev_kp hr1, hSM (r + 1) hr1, one, eval_cst,
          Nat.cast_one, sub_eq_zero] at this
        rw [this, if_pos ⟨by omega, hr⟩, one_mul, ih', show (r + 1) / 16 = r / 16 + 1 by omega]
        push_cast; ring
      · have := sat hsat (mem_main (c := .mul (om (p P_K0)) (.sub (k BLK) (kp BLK))) (by simp)) hr1
        simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K0 hr1, if_neg hk, sub_zero, one_mul, ev_k hr1,
          ev_kp hr1, sub_eq_zero] at this
        rw [this, ih', show (r + 1) / 16 = r / 16 by omega]
  refine ⟨hBLK r hr, ?_⟩
  have hrn : r < n := by omega
  have := sat hsat (mem_main (c := .sub (k POS) (.add (.mul (cst 64) (k BLK)) (.mul (cst 4) (p P_K)))) (by simp)) hrn
  simp only [Expr.eval, ev_k hrn, eval_cst, ev_K hrn, hBLK r hr, sub_eq_zero] at this
  rw [this, show 4 * r = 64 * (r / 16) + 4 * (r % 16) by omega]
  push_cast; ring

/-- **A stream's active bytes are its positions below its length.** -/
theorem stream_count (hnP : n ≤ 2 ^ 25) {st en : ℕ} (hst : st < en) (hen : en ≤ n) (hsm0 : M SM st = 0)
    (hsm : ∀ r, st < r → r < en → M SM r = 1) (hend : M END (en - 1) = 1) {L : ℕ}
    (hL : lenS.eval n preCols pub M (en - 1) = (L : F)) (hLP : L < P) :
    L ≤ 4 * (en - st) ∧ ∀ q < 4 * (en - st), ((M (A (q % 4)) (st + q / 4)).val = 1 ↔ q < L) := by
  set a : ℕ → ℕ := fun q => (M (A (q % 4)) (st + q / 4)).val with ha
  have bA : ∀ j < 4, ∀ r < n, M (A j) r = 0 ∨ M (A j) r = 1 := fun j hj r hr =>
    bool hsat (c := A j) (by interval_cases j <;> simp [boolCols, A]) hr
  have hb : ∀ q < 4 * (en - st), a q ≤ 1 := by
    intro q hq
    rcases bA (q % 4) (Nat.mod_lt _ (by norm_num)) (st + q / 4) (by omega) with h | h <;> simp [ha, h, ZMod.val_one]
  -- monotone within a row and across rows
  have mrow : ∀ r < n, ∀ j < 3, (M (A (j + 1)) r).val ≤ (M (A j) r).val := by
    intro r hr j hj
    have := sat hsat (c := .mul (k (A (j + 1))) (om (k (A j)))) (by
      simp only [constraints, List.mem_append, List.mem_map, List.mem_range]; right; exact ⟨j, hj, rfl⟩) hr
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr] at this
    rcases bA (j + 1) (by omega) r hr with h | h <;> rcases bA j (by omega) r hr with g | g <;>
      simp_all [ZMod.val_one]
  have mcross : ∀ r, st < r → r < en → (M (A 0) r).val ≤ (M (A 3) (r - 1)).val := by
    intro r h1 h2
    have hr : r < n := by omega
    have := sat hsat (mem_main (c := .mul (k SM) (.mul (k (A 0)) (om (kp (A 3))))) (by simp)) hr
    rw [show r = r - 1 + 1 by omega] at this
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k (show r - 1 + 1 < n by omega),
      ev_kp (show r - 1 + 1 < n by omega)] at this
    rw [show r - 1 + 1 = r by omega, hsm r h1 h2, one_mul] at this
    rcases bA 0 (by norm_num) r hr with h | h <;> rcases bA 3 (by norm_num) (r - 1) (by omega) with g | g <;>
      simp_all [ZMod.val_one]
  have hm : ∀ q, q + 1 < 4 * (en - st) → a (q + 1) ≤ a q := by
    intro q hq
    simp only [ha]
    by_cases h3 : q % 4 = 3
    · rw [show (q + 1) % 4 = 0 by omega, show st + (q + 1) / 4 = (st + q / 4 + 1) by omega, h3]
      have := mcross (st + q / 4 + 1) (by omega) (by omega)
      rwa [show st + q / 4 + 1 - 1 = st + q / 4 by omega] at this
    · rw [show (q + 1) % 4 = q % 4 + 1 by omega, show (q + 1) / 4 = q / 4 by omega]
      exact mrow (st + q / 4) (by omega) (q % 4) (by omega)
  -- the count
  have hcnt : ∀ d, st + d < en → M CNT (st + d) = ((∑ q ∈ Finset.range (4 * (d + 1)), a q : ℕ) : F) := by
    have rowsum : ∀ r < n, sumA.eval n preCols pub M r =
        (((M (A 0) r).val + (M (A 1) r).val + (M (A 2) r).val + (M (A 3) r).val : ℕ) : F) := by
      intro r hr
      simp only [sumA, Expr.eval, ev_k hr]; push_cast; simp only [ZMod.natCast_zmod_val]; ring
    have blk : ∀ d, ∑ q ∈ Finset.Ico (4 * d) (4 * (d + 1)), a q =
        (M (A 0) (st + d)).val + (M (A 1) (st + d)).val + (M (A 2) (st + d)).val + (M (A 3) (st + d)).val := by
      intro d
      rw [show 4 * (d + 1) = 4 * d + 4 by ring, Finset.sum_Ico_eq_sum_range]
      simp [Finset.sum_range_succ, ha, show ∀ i < 4, (4 * d + i) / 4 = d from fun i hi => by omega,
        show ∀ i < 4, (4 * d + i) % 4 = i from fun i hi => by omega]
    intro d
    induction d with
    | zero =>
      intro h
      have hr : st < n := by omega
      have := sat hsat (mem_main (c := .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA)) (by simp)) hr
      simp only [Expr.eval, ev_k hr, sub_eq_zero] at this
      rw [Nat.add_zero, this, hsm0, zero_mul, zero_add, rowsum st hr]
      congr 1
      have b0 := blk 0
      rw [mul_zero, Nat.add_zero, ← Finset.range_eq_Ico] at b0
      exact b0.symm
    | succ d ih =>
      intro h
      have hr : st + d + 1 < n := by omega
      have := sat hsat (mem_main (c := .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA)) (by simp)) hr
      simp only [Expr.eval, ev_k hr, ev_kp hr, sub_eq_zero] at this
      rw [show st + (d + 1) = st + d + 1 by ring, this, hsm _ (by omega) (by omega), one_mul, ih (by omega),
        rowsum _ hr, ← Finset.sum_range_add_sum_Ico _ (show 4 * (d + 1) ≤ 4 * (d + 1 + 1) by omega),
        show st + d + 1 = st + (d + 1) by ring, ← blk (d + 1)]
      push_cast; ring
  -- at the stream's end the count is the length
  have he := sat hsat (mem_main (c := .mul ends (.sub (k CNT) lenS)) (by simp)) (show en - 1 < n by omega)
  simp only [ends, Expr.eval, ev_k (show en - 1 < n by omega), hend, one_mul, hL, sub_eq_zero] at he
  have hc := hcnt (en - 1 - st) (by omega)
  rw [show st + (en - 1 - st) = en - 1 by omega, show en - 1 - st + 1 = en - st by omega, he] at hc
  have hsumle : ∑ q ∈ Finset.range (4 * (en - st)), a q ≤ 4 * (en - st) := by
    calc _ ≤ ∑ q ∈ Finset.range (4 * (en - st)), 1 := Finset.sum_le_sum (fun q hq => hb q (by simpa using hq))
      _ = 4 * (en - st) := by simp
  have hsum := natCast_inj_of_lt (Fields.lt_P (by omega)) hLP hc.symm
  obtain ⟨hle, hpre⟩ := prefix_of_count hb hm hsum
  exact ⟨hle, hpre⟩

/-- Blake2s's block count for a stream of `L` bytes. -/
def nbOf (L : ℕ) : ℕ := max 1 ((L + 63) / 64)

/-- A stream's byte `i`, or 0 past its end. -/
def sbyte (S : Spec.Block.Bytes) (i : ℕ) : ℕ := (S.getD i 0).toNat

/-- **Walker soundness.** With the byte reads answered by the stream `S` (`pub 8` bytes): every on row of
block `b < nbOf len` holds, as limbs, the stream's little-endian word at `64·b + 4·(r mod 16)` (zero past
the end); a block's first row says whether it is the last block and its counter. -/
theorem walker_sound (hn : 0 < n) (hnP : n ≤ 2 ^ 25) (S : Spec.Block.Bytes)
    (hl : pub Undo.PUB_LEN = (S.length : F)) (hS : S.length < P)
    (hrd : ∀ r < n, ∀ j < 4, M (A j) r = 1 → ∃ q : ℕ, M POS r + (j : F) = (q : F) ∧
      q < S.length ∧ (M (B j) r).val = sbyte S q) :
    ∀ r < n, M ON r = 1 → ∃ b : ℕ, M BLK r = (b : F) ∧ b < nbOf S.length ∧
      (∀ j < 4, (M (B j) r).val = sbyte S (64 * b + 4 * (r % 16) + j)) ∧
      (r % 16 = 0 → (M LASTF r = 1 ↔ b + 1 = nbOf S.length) ∧ (M LASTF r = 0 ∨ M LASTF r = 1) ∧
        M T r = ((if b + 1 = nbOf S.length then S.length else 64 * (b + 1) : ℕ) : F)) := by
  obtain ⟨e, he0, hen, hon⟩ := on_prefix hsat hn
  obtain ⟨hSM, hEND, he16, hBP⟩ := layout hsat hn he0 hen hon
  intro r hr hon_r
  have hre : r < e := (hon r hr).mp hon_r
  have hlen : ∀ r', r' < n → lenS.eval n preCols pub M r' = (S.length : F) := by
    intro r' _; simp only [lenS, Expr.eval, hl]
  obtain ⟨hLle, hpre⟩ := stream_count hsat hnP (st := 0) (en := e) he0 (by omega)
    (by rw [hSM 0 (by omega), if_neg (by omega)])
    (fun r' h1 h2 => by rw [hSM r' (by omega), if_pos (by omega)])
    (by rw [hEND (e - 1) (by omega), if_pos (by omega)])
    (hlen (e - 1) (by omega)) hS
  simp only [Nat.sub_zero, Nat.zero_add] at hLle hpre
  -- the block count
  set nbr := e / 16 with hnbr
  have hrows : e = 16 * nbr := by omega
  have hnb : nbr = nbOf S.length := by
    have hge : nbr ≥ 1 := by omega
    have hlast : 2 ≤ nbr → 64 * (nbr - 1) < S.length := by
      intro h2
      set r1 := 16 * (nbr - 1)
      have hr1 : r1 < e := by omega
      have hk := sat hsat (mem_main (c := .mul (p P_K0) (.mul (om (k (A 0))) (k BLK))) (by simp)) (show r1 < n by omega)
      simp only [Expr.eval, ev_K0 (show r1 < n by omega), show r1 % 16 = 0 by omega, if_true, one_mul, om, one, eval_cst,
        Nat.cast_one, ev_k (show r1 < n by omega), (hBP r1 hr1).1] at hk
      rw [show r1 / 16 = nbr - 1 by omega] at hk
      have hb0 : ((nbr - 1 : ℕ) : F) ≠ 0 := by
        intro h0
        have hnb' : nbr - 1 ≤ 2 ^ 30 := by omega
        have := natCast_inj_of_lt (a := nbr - 1) (b := 0) (Fields.lt_P hnb') (Fields.lt_P (by norm_num)) (by simpa using h0)
        omega
      have hA : M (A 0) r1 = 1 := by
        rcases mul_eq_zero.mp hk with h | h
        · exact (sub_eq_zero.mp h).symm
        · exact absurd h hb0
      exact (hpre (64 * (nbr - 1)) (by omega)).mp (by
        rw [show 64 * (nbr - 1) % 4 = 0 by omega, show 64 * (nbr - 1) / 4 = r1 by omega, hA, ZMod.val_one])
    unfold nbOf
    rcases Nat.lt_or_ge nbr 2 with h | h
    · have : nbr = 1 := by omega
      rw [this]; omega
    · have := hlast h; omega
  have hb : r / 16 < nbOf S.length := by rw [← hnb]; omega
  have hpos16 : 64 * (r / 16) + 4 * (r % 16) = 4 * r := by omega
  refine ⟨r / 16, (hBP r hre).1, hb, fun j hj => ?_, fun hk0 => ?_⟩
  · -- the bytes
    rw [hpos16]
    have aiff := hpre (4 * r + j) (by omega)
    rw [show (4 * r + j) % 4 = j by omega, show (4 * r + j) / 4 = r by omega] at aiff
    have hbA := bool hsat (c := A j) (by interval_cases j <;> simp [boolCols, A]) hr
    by_cases hlt : 4 * r + j < S.length
    · have hA1 : M (A j) r = 1 := by
        rcases hbA with h | h
        · exfalso; rw [h, ZMod.val_zero] at aiff; exact absurd (aiff.mpr hlt) (by decide)
        · exact h
      obtain ⟨q, hq1, hq2, hq3⟩ := hrd r hr j hj hA1
      rw [(hBP r hre).2] at hq1
      have : 4 * r + j = q := by
        apply natCast_inj_of_lt (Fields.lt_P (by omega)) (by omega)
        push_cast; push_cast at hq1; exact hq1
      rw [hq3, this]
    · have hA0 : M (A j) r = 0 := by
        rcases hbA with h | h
        · exact h
        · exfalso; rw [h, ZMod.val_one] at aiff; exact hlt (aiff.mp rfl)
      have := sat hsat (c := .mul (k (B j)) (om (k (A j)))) (by
        simp only [constraints, List.mem_append, List.mem_map, List.mem_range]; left; left; right; exact ⟨j, hj, rfl⟩) hr
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr, hA0, sub_zero, mul_one] at this
      rw [this, ZMod.val_zero, sbyte, List.getD_eq_default _ _ (by omega)]; rfl
  · -- a block's first row: the last flag and the counter
    have hr15 : r + 15 < e := by omega
    have lconst : ∀ d ≤ 15, M LASTF (r + d) = M LASTF r := by
      intro d hd
      induction d with
      | zero => rfl
      | succ d ih =>
        have hrr : r + d + 1 < n := by omega
        have := sat hsat (mem_main (c := .mul (om (p P_K0)) (.sub (k LASTF) (kp LASTF))) (by simp)) hrr
        simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K0 hrr, show ¬ ((r + d + 1) % 16 = 0) by omega,
          if_false, sub_zero, one_mul, ev_k hrr, ev_kp hrr, sub_eq_zero] at this
        rw [show r + (d + 1) = r + d + 1 by ring, this, ih (by omega)]
    have hK15 := sat hsat (mem_main (c := .mul (p P_K15) (.sub (k LASTF) ends)) (by simp)) (show r + 15 < n by omega)
    simp only [ends, Expr.eval, ev_K15 (show r + 15 < n by omega), show (r + 15) % 16 = 15 by omega, if_true, one_mul,
      ev_k (show r + 15 < n by omega), hEND (r + 15) (by omega), sub_eq_zero, lconst 15 le_rfl] at hK15
    have hlastiff : (r + 15 + 1 = e) ↔ r / 16 + 1 = nbOf S.length := by
      rw [← hnb]; omega
    have hLv : M LASTF r = if r / 16 + 1 = nbOf S.length then 1 else 0 := by
      rw [hK15]; split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; tauto)
    refine ⟨by rw [hLv]; split_ifs with h <;> simp [h], by rw [hLv]; split_ifs <;> simp, ?_⟩
    have := sat hsat (mem_main (c := .sub (k T) (.add (.mul (k LASTF) lenS) (.mul (om (k LASTF))
      (.add (.mul (cst 64) (k BLK)) (cst 64))))) (by simp)) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, hlen r hr, (hBP r hre).1, sub_eq_zero, hLv] at this
    rw [this]
    split_ifs <;> push_cast <;> ring

end Rows

end StarkedAir.Block.B2Msg
