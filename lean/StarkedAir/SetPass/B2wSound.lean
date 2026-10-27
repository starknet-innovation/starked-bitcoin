/-
**A segment's Blake2s message words, soundness (`set_b2w`).** In a satisfied trace whose byte reads are
answered by the incoming pending bytes, the segment bytes `S` and the outgoing pending bytes: the on rows
are blocks `0 … m` (`m ≥ 1`, from the public block counts); the stream is `xb` (the `plen_in ≤ 64`
incoming pending bytes, then `S`), `64·m + plen_out = plen_in + len` with `1 ≤ plen_out ≤ 64`; the rows of
blocks below `m` yield their words (`UW`) and hold the stream's bytes; the outgoing pending bytes are the
stream's bytes from `64·m`.
-/
import StarkedAir.SetPass.B2w
import StarkedAir.Block.B2MsgSound

namespace StarkedAir.SetPass.B2w

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

/-- The stream `P_in ‖ S`: incoming pending byte `i` below `plen_in`, else segment byte `i − plen_in`. -/
def xb (pub : ℕ → F) (S : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < (pub (H_PLEN B2_IN)).val then (pub (H_PEND B2_IN i)).val else S (i - (pub (H_PLEN B2_IN)).val)

/-- **Sixteen rows of monotone flags, counted.** Four flag columns over the rows `st … st + 15`, monotone
in stream order (`q ↦ X (q mod 4)` at row `st + q / 4`), with a running count: the count at the last row is
`v ≤ 64` and the flags are the positions below `v`. -/
theorem count16 {M : ℕ → ℕ → F} {X : ℕ → ℕ} {CN st : ℕ}
    (hb : ∀ j < 4, ∀ d < 16, M (X j) (st + d) = 0 ∨ M (X j) (st + d) = 1)
    (hrow : ∀ j < 3, ∀ d < 16, M (X (j + 1)) (st + d) = 1 → M (X j) (st + d) = 1)
    (hcross : ∀ d, 0 < d → d < 16 → M (X 0) (st + d) = 1 → M (X 3) (st + (d - 1)) = 1)
    (hcnt0 : M CN st = M (X 0) st + M (X 1) st + (M (X 2) st + M (X 3) st))
    (hcnt : ∀ d, 0 < d → d < 16 → M CN (st + d) = M CN (st + (d - 1)) +
      (M (X 0) (st + d) + M (X 1) (st + d) + (M (X 2) (st + d) + M (X 3) (st + d)))) :
    ∃ v : ℕ, v ≤ 64 ∧ M CN (st + 15) = (v : F) ∧ ∀ q < 64, (M (X (q % 4)) (st + q / 4) = 1 ↔ q < v) := by
  set a : ℕ → ℕ := fun q => (M (X (q % 4)) (st + q / 4)).val with ha
  have hab : ∀ q < 64, a q ≤ 1 := by
    intro q hq
    rcases hb (q % 4) (Nat.mod_lt _ (by norm_num)) (q / 4) (by omega) with h | h <;> simp [ha, h, ZMod.val_one]
  have aiff : ∀ q < 64, (a q = 1 ↔ M (X (q % 4)) (st + q / 4) = 1) := by
    intro q hq
    rcases hb (q % 4) (Nat.mod_lt _ (by norm_num)) (q / 4) (by omega) with h | h <;> simp [ha, h, ZMod.val_one]
  have hm : ∀ q, q + 1 < 64 → a (q + 1) ≤ a q := by
    intro q hq
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hab (q + 1) hq) with h0 | h1
    · rw [h0]; exact Nat.zero_le _
    · have h1' := (aiff (q + 1) hq).mp h1
      have : M (X (q % 4)) (st + q / 4) = 1 := by
        by_cases h3 : q % 4 = 3
        · rw [show (q + 1) % 4 = 0 by omega, show (q + 1) / 4 = q / 4 + 1 by omega] at h1'
          have := hcross (q / 4 + 1) (by omega) (by omega) h1'
          rw [show q / 4 + 1 - 1 = q / 4 by omega] at this
          rw [h3]; exact this
        · rw [show (q + 1) % 4 = q % 4 + 1 by omega, show (q + 1) / 4 = q / 4 by omega] at h1'
          exact hrow (q % 4) (by omega) (q / 4) (by omega) h1'
      have := (aiff q (by omega)).mpr this
      omega
  have rowsum : ∀ d < 16, M (X 0) (st + d) + M (X 1) (st + d) + (M (X 2) (st + d) + M (X 3) (st + d)) =
      ((a (4 * d) + a (4 * d + 1) + a (4 * d + 2) + a (4 * d + 3) : ℕ) : F) := by
    intro d hd
    simp only [ha, show (4 * d) % 4 = 0 by omega, show (4 * d + 1) % 4 = 1 by omega, show (4 * d + 2) % 4 = 2 by omega,
      show (4 * d + 3) % 4 = 3 by omega, show 4 * d / 4 = d by omega, show (4 * d + 1) / 4 = d by omega,
      show (4 * d + 2) / 4 = d by omega, show (4 * d + 3) / 4 = d by omega]
    push_cast; simp only [ZMod.natCast_zmod_val]; ring
  have blk : ∀ d, ∑ q ∈ Finset.Ico (4 * d) (4 * (d + 1)), a q = a (4 * d) + a (4 * d + 1) + a (4 * d + 2) + a (4 * d + 3) := by
    intro d
    rw [show 4 * (d + 1) = 4 * d + 4 by ring, Finset.sum_Ico_eq_sum_range]
    simp [Finset.sum_range_succ, add_assoc]
  have hsum : ∀ d < 16, M CN (st + d) = ((∑ q ∈ Finset.range (4 * (d + 1)), a q : ℕ) : F) := by
    intro d
    induction d with
    | zero =>
      intro _
      have b0 := blk 0
      rw [Nat.mul_zero, show 4 * (0 + 1) = 4 by rfl, ← Finset.range_eq_Ico] at b0
      rw [Nat.add_zero, hcnt0, show 4 * (0 + 1) = 4 by rfl, b0]
      simpa using rowsum 0 (by norm_num)
    | succ d ih =>
      intro h
      rw [hcnt (d + 1) (by omega) h, show d + 1 - 1 = d by omega, ih (by omega), rowsum (d + 1) h,
        ← Finset.sum_range_add_sum_Ico _ (show 4 * (d + 1) ≤ 4 * (d + 1 + 1) by omega), blk (d + 1)]
      push_cast; ring
  have hle : ∑ q ∈ Finset.range 64, a q ≤ 64 := by
    calc _ ≤ ∑ q ∈ Finset.range 64, 1 := Finset.sum_le_sum (fun q hq => hab q (by simpa using hq))
      _ = 64 := by simp
  obtain ⟨-, hpre⟩ := Block.B2Msg.prefix_of_count hab hm rfl
  exact ⟨_, hle, hsum 15 (by norm_num), fun q hq => (aiff q hq).symm.trans (hpre q hq)⟩

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

omit hsat in
theorem ev_row15 {r : ℕ} (hr : r < n) : row15.eval n preCols pub M r = if r = 15 then 1 else 0 := by
  have e1 : (p P_LT16).eval n preCols pub M r = if r < 16 then 1 else 0 := by
    simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_LT16, PreCol.eval]
  have e2 : (p P_LT15).eval n preCols pub M r = if r < 15 then 1 else 0 := by
    simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_LT15, PreCol.eval]
  simp only [row15, Expr.eval, e1, e2]
  split_ifs <;> first | (exfalso; omega) | norm_num

theorem bool {c : ℕ} (hc : c ∈ boolCols) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := hsat r hr (boolC (k c)) (by
    unfold constraints
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hsat in
theorem mem_uw {j : ℕ} (hj : j < 4) : Expr.mul (k UW) (om (k (A j))) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_aon {j : ℕ} (hj : j < 4) : Expr.mul (k (A j)) (om (k ON)) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_bz {j : ℕ} (hj : j < 4) : Expr.mul (k (B j)) (om (k (A j))) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_amono {j : ℕ} (hj : j < 3) : Expr.mul (k (A (j + 1))) (om (k (A j))) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_nblk {j : ℕ} (hj : j < 4) : Expr.mul (k (N j)) (k BLK) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left; apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_na {j : ℕ} (hj : j < 4) : Expr.mul (k (N j)) (om (k (A j))) ∈ constraints := by
  unfold constraints
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
theorem mem_nmono {j : ℕ} (hj : j < 3) : Expr.mul (k (N (j + 1))) (om (k (N j))) ∈ constraints := by
  unfold constraints
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

omit hsat in
/-- `x · (1 − y) = 0` with `x = 1` gives `y = 1`. -/
theorem one_of_imp {x y : F} (h : x * (1 - y) = 0) (hx : x = 1) : y = 1 := by
  rw [hx, one_mul] at h; exact (sub_eq_zero.mp h).symm

/-- **On rows are a prefix** `[0, e)`, with `0 < e < n`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, 0 < e ∧ e < n ∧ ∀ r < n, (M ON r = 1 ↔ r < e) := by
  have bo := fun r (hr : r < n) => bool hsat (c := ON) (by simp [boolCols]) hr
  have h0 : M ON 0 = 1 := by
    have := hsat 0 hn (.mul first (om (k ON))) (by simp [constraints])
    simp [Expr.eval, ev_first hn, om, one, eval_cst, ev_k hn] at this
    linear_combination -this
  have hl : M ON (n - 1) = 0 := by
    have := hsat (n - 1) (by omega) (.mul isLast (k ON)) (by simp [constraints])
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast (show n - 1 < n by omega),
      show ¬ (n - 1 + 1 < n) by omega, if_false, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → M ON (r + 1) = 1 → M ON r = 1 := by
    intro r hr h1
    have := hsat (r + 1) hr (.mul notFirst (.mul (k ON) (om (kp ON)))) (by simp [constraints])
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
    have : ∀ d, r - d < n → M ON (r - d) = 1 := by
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

/-- **Layout**: `SM`, `END`, block numbers and positions, given the on prefix. -/
theorem layout (hn : 0 < n) {e : ℕ} (_he0 : 0 < e) (hen : e < n) (hon : ∀ r < n, (M ON r = 1 ↔ r < e)) :
    (∀ r < n, M ON r = if r < e then 1 else 0) ∧
    (∀ r < n, M END r = if r + 1 = e then 1 else 0) ∧
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
    have := hsat r hr (.sub (k SM) (.mul notFirst (k ON))) (by simp [constraints])
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, ev_k hr, onv r hr,
      sub_eq_zero] at this
    rw [this]
    by_cases h0 : r = 0
    · subst h0; simp
    · by_cases h2 : r < e <;> simp [h0, h2]
  have hEND : ∀ r < n, M END r = if r + 1 = e then 1 else 0 := by
    intro r hr
    have := hsat r hr (.sub (k END) (.mul (k ON) (om (kn ON)))) (by simp [constraints])
    simp only [Expr.eval, ev_k hr, sub_eq_zero, om, one, eval_cst, Nat.cast_one] at this
    rw [this]
    by_cases hl : r + 1 < n
    · rw [ev_kn hl, onv r hr, onv (r + 1) hl]
      split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [onv r hr, if_neg (by omega), if_neg (by omega), zero_mul]
  refine ⟨onv, hEND, fun r hr => ?_⟩
  have hBLK : ∀ r < e, M BLK r = ((r / 16 : ℕ) : F) := by
    intro r hr
    induction r with
    | zero =>
      have := hsat 0 hn (.mul first (k BLK)) (by simp [constraints])
      simpa [Expr.eval, ev_first hn, ev_k hn] using this
    | succ r ih =>
      have hr1 : r + 1 < n := by omega
      have ih' := ih (by omega)
      by_cases hk : (r + 1) % 16 = 0
      · have := hsat (r + 1) hr1 (.mul (p P_K0) (.sub (k BLK) (.mul (k SM) (.add (kp BLK) one)))) (by simp [constraints])
        simp only [Expr.eval, ev_K0 hr1, if_pos hk, one_mul, ev_k hr1, ev_kp hr1, hSM (r + 1) hr1, one, eval_cst,
          Nat.cast_one, sub_eq_zero] at this
        rw [this, if_pos ⟨by omega, hr⟩, one_mul, ih', show (r + 1) / 16 = r / 16 + 1 by omega]
        push_cast; ring
      · have := hsat (r + 1) hr1 (.mul (om (p P_K0)) (.sub (k BLK) (kp BLK))) (by simp [constraints])
        simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_K0 hr1, if_neg hk, sub_zero, one_mul, ev_k hr1,
          ev_kp hr1, sub_eq_zero] at this
        rw [this, ih', show (r + 1) / 16 = r / 16 by omega]
  refine ⟨hBLK r hr, ?_⟩
  have hrn : r < n := by omega
  have := hsat r hrn (.sub (k POS) (.add (.mul (cst 64) (k BLK)) (.mul (cst 4) (p P_K)))) (by simp [constraints])
  simp only [Expr.eval, ev_k hrn, eval_cst, ev_K hrn, hBLK r hr, sub_eq_zero] at this
  rw [this, show 4 * r = 64 * (r / 16) + 4 * (r % 16) by omega]
  push_cast; ring

/-- **The message words of a segment's stream.** With byte reads answered by the incoming pending bytes
(`N` rows), the segment bytes `S` (other active bytes, at `x − plen_in`) and the outgoing pending bytes
(the held block's active bytes): the stream `xb` has `64·m + plen_out = plen_in + len` bytes, `m ≥ 1`
whole blocks yield their words and hold the stream's bytes, and the outgoing pending bytes are the
stream's from `64·m`. -/
theorem b2w_sound (hn : 0 < n) (hn2 : n ≤ 2 ^ 25) (S : ℕ → ℕ) (hLEN : (pub PUB_LEN).val < 2 ^ 30)
    (hrN : ∀ r < n, ∀ j < 4, M (N j) r = 1 → ∃ q : ℕ, q < 64 ∧ M POS r + (j : F) = (q : F) ∧ M (B j) r = pub (H_PEND B2_IN q))
    (hrS : ∀ r < n, ∀ j < 4, M (A j) r - M (N j) r = 1 → ∃ q < (pub PUB_LEN).val,
      M POS r + (j : F) - pub (H_PLEN B2_IN) = (q : F) ∧ (M (B j) r).val = S q)
    (hrO : ∀ r < n, ∀ j < 4, M HELD r * M (A j) r = 1 → ∃ q : ℕ, q < 64 ∧
      4 * ((r % 16 : ℕ) : F) + (j : F) = (q : F) ∧ M (B j) r = pub (H_PEND B2_OUT q)) :
    ∃ m : ℕ, 1 ≤ m ∧ 16 * (m + 1) < n ∧ pub (H_NB B2_OUT) - pub (H_NB B2_IN) = (m : F) ∧
      (pub (H_PLEN B2_IN)).val ≤ 64 ∧ 1 ≤ (pub (H_PLEN B2_OUT)).val ∧ (pub (H_PLEN B2_OUT)).val ≤ 64 ∧
      64 * m + (pub (H_PLEN B2_OUT)).val = (pub (H_PLEN B2_IN)).val + (pub PUB_LEN).val ∧
      (∀ r < n, M UW r = if r < 16 * m then 1 else 0) ∧
      (∀ r < 16 * m, M BLK r = ((r / 16 : ℕ) : F) ∧ ∀ j < 4, M (B j) r = ((xb pub S (4 * r + j) : ℕ) : F)) ∧
      (∀ q < (pub (H_PLEN B2_OUT)).val, pub (H_PEND B2_OUT q) = ((xb pub S (64 * m + q) : ℕ) : F)) := by
  have hPv : ∀ x : ℕ, x ≤ 2 ^ 30 → x < P := fun x hx => Block.Fields.lt_P hx
  obtain ⟨e, he0, hen, hon⟩ := on_prefix hsat hn
  obtain ⟨onv, hEND, hBP⟩ := layout hsat hn he0 hen hon
  set mF := pub (H_NB B2_OUT) - pub (H_NB B2_IN) with hmF
  have mev : ∀ r, (B2w.m).eval n preCols pub M r = mF := fun r => by simp [B2w.m, Expr.eval, hmF]
  have bA : ∀ j < 4, ∀ r < n, M (A j) r = 0 ∨ M (A j) r = 1 := fun j hj r hr =>
    bool hsat (c := A j) (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))) hr
  have bN : ∀ j < 4, ∀ r < n, M (N j) r = 0 ∨ M (N j) r = 1 := fun j hj r hr =>
    bool hsat (c := N j) (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) hr
  -- the stream's last row ends the held block `m`
  have hl1 : e - 1 < n := by omega
  have hend1 : M END (e - 1) = 1 := by rw [hEND _ hl1, if_pos (by omega)]
  have hheld1 : M HELD (e - 1) = 1 := by
    have := hsat _ hl1 (.mul (k END) (om (k HELD))) (by simp [constraints])
    simp only [Expr.eval, ev_k hl1, om, one, eval_cst, Nat.cast_one] at this
    exact one_of_imp this hend1
  have he16 : (e - 1) % 16 = 15 := by
    have := hsat _ hl1 (.mul (k END) (om (p P_K15))) (by simp [constraints])
    simp only [Expr.eval, ev_k hl1, om, one, eval_cst, Nat.cast_one, ev_K15 hl1, hend1, one_mul] at this
    by_contra hc; rw [if_neg hc, sub_zero] at this; exact one_ne_zero this
  set mm := (e - 1) / 16 with hmm
  have hee : e = 16 * (mm + 1) := by omega
  have hblkm : mF = ((mm : ℕ) : F) := by
    have := hsat _ hl1 (.mul (k HELD) (.sub (k BLK) B2w.m)) (by simp [constraints])
    simp only [Expr.eval, ev_k hl1, mev, hheld1, one_mul, sub_eq_zero] at this
    rw [← this, (hBP (e - 1) (by omega)).1]
  have hmm1 : 1 ≤ mm := by
    have h0 := hsat 0 hn (.mul first (k HELD)) (by simp [constraints])
    simp only [Expr.eval, ev_first hn, if_true, one_mul, ev_k hn] at h0
    have := hsat 0 hn (.sub (.mul (.sub (k BLK) B2w.m) (k HINV)) (om (k HELD))) (by simp [constraints])
    simp only [Expr.eval, ev_k hn, mev, om, one, eval_cst, Nat.cast_one, h0, sub_zero, (hBP 0 he0).1] at this
    by_contra hc
    rw [hblkm, show mm = 0 by omega] at this
    simp at this
  have hmmP : ∀ x, x ≤ mm → x < P := fun x hx => hPv x (by omega)
  -- the held flag: block `m`
  have hHELD : ∀ r < e, M HELD r = if 16 * mm ≤ r then 1 else 0 := by
    intro r hr
    have hrn : r < n := by omega
    split_ifs with h
    · have := hsat r hrn (.sub (.mul (.sub (k BLK) B2w.m) (k HINV)) (om (k HELD))) (by simp [constraints])
      simp only [Expr.eval, ev_k hrn, mev, om, one, eval_cst, Nat.cast_one, (hBP r hr).1, hblkm,
        show r / 16 = mm by omega, sub_self, zero_mul, zero_sub, neg_eq_zero, sub_eq_zero] at this
      exact this.symm
    · have := hsat r hrn (.mul (k HELD) (.sub (k BLK) B2w.m)) (by simp [constraints])
      simp only [Expr.eval, ev_k hrn, mev, (hBP r hr).1, hblkm] at this
      rcases mul_eq_zero.mp this with g | g
      · exact g
      · exfalso
        have := natCast_inj_of_lt (hmmP _ (by omega)) (hmmP mm le_rfl) (sub_eq_zero.mp g)
        omega
  have hUW : ∀ r < n, M UW r = if r < 16 * mm then 1 else 0 := by
    intro r hr
    have := hsat r hr (.sub (k UW) (.mul (k ON) (om (k HELD)))) (by simp [constraints])
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, onv r hr, sub_eq_zero] at this
    rw [this]
    by_cases h : r < e
    · rw [if_pos h, hHELD r h]; split_ifs <;> first | (exfalso; omega) | norm_num
    · rw [if_neg h, zero_mul, if_neg (by omega)]
  -- active bytes: whole blocks below `m`; nothing off the stream
  have hAfull : ∀ r < 16 * mm, ∀ j < 4, M (A j) r = 1 := by
    intro r hr j hj
    have hrn : r < n := by omega
    have := hsat r hrn _ (mem_uw hj)
    simp only [Expr.eval, ev_k hrn, om, one, eval_cst, Nat.cast_one] at this
    exact one_of_imp this (by rw [hUW r hrn, if_pos hr])
  have hAoff : ∀ r < n, e ≤ r → ∀ j < 4, M (A j) r = 0 := by
    intro r hr her j hj
    have := hsat r hr _ (mem_aon hj)
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, onv r hr, if_neg (show ¬ r < e by omega),
      sub_zero, mul_one] at this
    exact this
  have hNA : ∀ r < n, ∀ j < 4, M (N j) r = 1 → M (A j) r = 1 := by
    intro r hr j hj h
    have := hsat r hr _ (mem_na hj)
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at this
    exact one_of_imp this h
  -- the pending bytes: a prefix of block 0, `plen_in` of them
  have hst0 : ∀ d < 16, d < n := fun d hd => by omega
  obtain ⟨vin, hvin, hpc, hNiff⟩ := count16 (M := M) (X := N) (CN := PCNT) (st := 0)
    (fun j hj d hd => bN j hj (0 + d) (by omega))
    (fun j hj d hd h => by
      have hr : 0 + d < n := by omega
      have := hsat _ hr _ (mem_nmono hj)
      simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at this
      exact one_of_imp this h)
    (fun d hd0 hd h => by
      have hr : 0 + (d - 1) + 1 < n := by omega
      have := hsat _ hr (.mul (om (p P_K0)) (.mul (k (N 0)) (om (kp (N 3))))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, ev_k hr, ev_kp hr,
        if_neg (show ¬ (0 + (d - 1) + 1) % 16 = 0 by omega), sub_zero, one_mul] at this
      rw [show 0 + (d - 1) + 1 = 0 + d by omega] at this
      exact one_of_imp this h)
    (by
      have := hsat 0 hn (.sub (k PCNT) (.add (.mul (om (p P_K0)) (kp PCNT)) (sum4 N))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hn, Nat.zero_mod, if_true, sub_self, zero_mul,
        zero_add, sum4, ev_k hn, sub_eq_zero] at this
      exact this)
    (fun d hd0 hd => by
      have hr : 0 + (d - 1) + 1 < n := by omega
      have := hsat _ hr (.sub (k PCNT) (.add (.mul (om (p P_K0)) (kp PCNT)) (sum4 N))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, ev_k hr, ev_kp hr, sum4,
        if_neg (show ¬ (0 + (d - 1) + 1) % 16 = 0 by omega), sub_zero, one_mul, sub_eq_zero] at this
      rw [show 0 + (d - 1) + 1 = 0 + d by omega] at this
      exact this)
  have hpl : pub (H_PLEN B2_IN) = (vin : F) := by
    have := hsat 15 (by omega) (.mul row15 (.sub (k PCNT) plenIn)) (by simp [constraints])
    simp only [Expr.eval, ev_row15 (show 15 < n by omega), if_true, one_mul, ev_k (show 15 < n by omega), plenIn,
      sub_eq_zero] at this
    rw [← this, ← hpc]
  set pl := (pub (H_PLEN B2_IN)).val with hpldef
  have hplv : pl = vin := by rw [hpldef, hpl, ZMod.val_natCast_of_lt (hPv _ (by omega))]
  have hNall : ∀ r < n, ∀ j < 4, (M (N j) r = 1 ↔ 4 * r + j < pl) := by
    intro r hr j hj
    by_cases h16 : r < 16
    · have := hNiff (4 * r + j) (by omega)
      rw [show (4 * r + j) % 4 = j by omega, show (4 * r + j) / 4 = r by omega, Nat.zero_add] at this
      rw [this, hplv]
    · have hN0 : M (N j) r = 0 := by
        by_cases hre : r < e
        · have := hsat r hr _ (mem_nblk hj)
          simp only [Expr.eval, ev_k hr, (hBP r hre).1] at this
          rcases mul_eq_zero.mp this with g | g
          · exact g
          · exfalso
            have := natCast_inj_of_lt (a := r / 16) (b := 0) (hPv _ (by omega)) (hPv _ (by omega)) (by simpa using g)
            omega
        · rcases bN j hj r hr with g | g
          · exact g
          · exact absurd (hAoff r hr (by omega) j hj) (by rw [hNA r hr j hj g]; exact one_ne_zero)
      rw [hN0]
      constructor
      · intro h; exact absurd h zero_ne_one
      · intro h; omega
  -- the held block's active bytes: a nonempty prefix, `plen_out` of them
  have hst : ∀ d < 16, 16 * mm + d < n := fun d hd => by omega
  obtain ⟨vout, hvout, hcc, hAiff⟩ := count16 (M := M) (X := A) (CN := CNT) (st := 16 * mm)
    (fun j hj d hd => bA j hj _ (hst d hd))
    (fun j hj d hd h => by
      have hr := hst d hd
      have := hsat _ hr _ (mem_amono hj)
      simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at this
      exact one_of_imp this h)
    (fun d hd0 hd h => by
      have hr : 16 * mm + (d - 1) + 1 < n := by omega
      have := hsat _ hr (.mul (om (p P_K0)) (.mul (k (A 0)) (om (kp (A 3))))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, ev_k hr, ev_kp hr,
        if_neg (show ¬ (16 * mm + (d - 1) + 1) % 16 = 0 by omega), sub_zero, one_mul] at this
      rw [show 16 * mm + (d - 1) + 1 = 16 * mm + d by omega] at this
      exact one_of_imp this h)
    (by
      have hr : 16 * mm < n := by omega
      have := hsat _ hr (.sub (k CNT) (.add (.mul (om (p P_K0)) (kp CNT)) (sum4 A))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, show 16 * mm % 16 = 0 by omega,
        if_true, sub_self, zero_mul, zero_add, sum4, ev_k hr, sub_eq_zero] at this
      exact this)
    (fun d hd0 hd => by
      have hr : 16 * mm + (d - 1) + 1 < n := by omega
      have := hsat _ hr (.sub (k CNT) (.add (.mul (om (p P_K0)) (kp CNT)) (sum4 A))) (by simp [constraints])
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, ev_k hr, ev_kp hr, sum4,
        if_neg (show ¬ (16 * mm + (d - 1) + 1) % 16 = 0 by omega), sub_zero, one_mul, sub_eq_zero] at this
      rw [show 16 * mm + (d - 1) + 1 = 16 * mm + d by omega] at this
      exact this)
  have hplo : pub (H_PLEN B2_OUT) = (vout : F) := by
    have := hsat _ hl1 (.mul (k END) (.sub (k CNT) plenOut)) (by simp [constraints])
    simp only [Expr.eval, ev_k hl1, hend1, one_mul, plenOut, sub_eq_zero] at this
    rw [← this, show e - 1 = 16 * mm + 15 by omega, hcc]
  set plo := (pub (H_PLEN B2_OUT)).val with hplodef
  have hplov : plo = vout := by rw [hplodef, hplo, ZMod.val_natCast_of_lt (hPv _ (by omega))]
  have hplo1 : 1 ≤ plo := by
    have hr : 16 * mm < n := by omega
    have := hsat _ hr (.mul (k HELD) (.mul (p P_K0) (om (k (A 0))))) (by simp [constraints])
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_K0 hr, show 16 * mm % 16 = 0 by omega,
      if_true, one_mul, ev_k hr, hHELD _ (show 16 * mm < e by omega), le_refl] at this
    have hA0 : M (A 0) (16 * mm) = 1 := (sub_eq_zero.mp this).symm
    have := (hAiff 0 (by norm_num)).mp (by simpa using hA0)
    omega
  have hAall : ∀ r < e, ∀ j < 4, (M (A j) r = 1 ↔ 4 * r + j < 64 * mm + plo) := by
    intro r hr j hj
    by_cases h : r < 16 * mm
    · exact ⟨fun _ => by omega, fun _ => hAfull r h j hj⟩
    · have := hAiff (4 * (r - 16 * mm) + j) (by omega)
      rw [show (4 * (r - 16 * mm) + j) % 4 = j by omega, show 16 * mm + (4 * (r - 16 * mm) + j) / 4 = r by omega] at this
      rw [this, hplov]; omega
  -- the lengths
  have heq : 64 * mm + plo = pl + (pub PUB_LEN).val := by
    obtain ⟨LV, hLV⟩ : ∃ LV, LV = (pub PUB_LEN).val := ⟨_, rfl⟩
    have hLVlt : LV < 2 ^ 30 := by rw [hLV]; exact hLEN
    have hLc : pub PUB_LEN = (LV : F) := by rw [hLV, ZMod.natCast_zmod_val]
    have := hsat 0 hn (.mul first (.sub (.add plenOut (.mul (cst 64) B2w.m)) (.add plenIn (.pub PUB_LEN))))
      (by simp [constraints])
    simp only [Expr.eval, ev_first hn, if_true, one_mul, plenOut, plenIn, eval_cst, mev, hblkm,
      sub_eq_zero] at this
    rw [hplo, hpl, hLc] at this
    have e2 : (((64 * mm + vout : ℕ)) : F) = ((vin + LV : ℕ) : F) := by push_cast; linear_combination this
    have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e2
    rw [hplov, hplv, ← hLV]; exact this
  -- the bytes of active positions
  have hbyte : ∀ r < e, ∀ j < 4, M (A j) r = 1 → M (B j) r = ((xb pub S (4 * r + j) : ℕ) : F) := by
    intro r hr j hj ha
    have hrn : r < n := by omega
    have hpos := (hBP r hr).2
    by_cases hN : M (N j) r = 1
    · obtain ⟨q, hq, hqp, hqb⟩ := hrN r hrn j hj hN
      rw [hpos] at hqp
      have hq' : 4 * r + j = q := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) (by exact_mod_cast hqp)
      have hlt := (hNall r hrn j hj).mp hN
      have hx : xb pub S (4 * r + j) = (pub (H_PEND B2_IN (4 * r + j))).val := if_pos hlt
      rw [hqb, hx, ← hq', ZMod.natCast_zmod_val]
    · have hN0 : M (N j) r = 0 := (bN j hj r hrn).resolve_right hN
      obtain ⟨q, hq, hqp, hqb⟩ := hrS r hrn j hj (by rw [ha, hN0, sub_zero])
      rw [hpos, hpl] at hqp
      have hge : ¬ (4 * r + j < pl) := fun h => hN ((hNall r hrn j hj).mpr h)
      have e2 : ((4 * r + j : ℕ) : F) = ((q + vin : ℕ) : F) := by push_cast at hqp ⊢; linear_combination hqp
      have hq' := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) e2
      have hx : xb pub S (4 * r + j) = S (4 * r + j - pl) := if_neg hge
      rw [hx, show 4 * r + j - pl = q by omega, ← hqb, ZMod.natCast_zmod_val]
  refine ⟨mm, hmm1, by omega, hblkm, by omega, hplo1, by omega, heq, hUW, fun r hr => ⟨(hBP r (by omega)).1,
    fun j hj => hbyte r (by omega) j hj (hAfull r hr j hj)⟩, fun q hq => ?_⟩
  -- the outgoing pending bytes
  set r := 16 * mm + q / 4 with hr
  have hre : r < e := by omega
  have hrn : r < n := by omega
  have ha : M (A (q % 4)) r = 1 := (hAall r hre (q % 4) (by omega)).mpr (by omega)
  have hh : M HELD r = 1 := by rw [hHELD r hre, if_pos (by omega)]
  obtain ⟨q', hq', hqq, hqb⟩ := hrO r hrn (q % 4) (by omega) (by rw [hh, ha, one_mul])
  have : q = q' := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) (by
    rw [← hqq, show r % 16 = q / 4 by omega]
    conv_lhs => rw [← Nat.div_add_mod q 4]
    push_cast; ring)
  rw [show pub (H_PEND B2_OUT q) = M (B (q % 4)) r from by rw [hqb, this],
    hbyte r hre (q % 4) (by omega) ha, show 4 * r + q % 4 = 64 * mm + q by omega]

end Rows

end StarkedAir.SetPass.B2w
