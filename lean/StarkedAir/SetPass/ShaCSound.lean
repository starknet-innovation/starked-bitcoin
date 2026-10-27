/-
**SHA-256 compressions, soundness (`set_shac`).** In a satisfied `set_shac` trace whose message-word uses
are answered with words `wd b t` of blocks `b < m` (`m = nb_out − nb_in`) and whose end token is yielded
(a row `≡ 71 mod 72` with `LASTS`), period `q` of a used prefix is block `q`; period 0 starts from the
public `H_in`, each next one from the previous output; the last block's output is the public `H_out`:
`H_out = wfold H_in wd m` (`shac_sound`). The token on the period's last row makes that period whole.
-/
import StarkedAir.SetPass.ShaC
import StarkedAir.SetPass.ShaSpec

namespace StarkedAir.SetPass.ShaC

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC limb ShaSat shaPre inputAt messageAt outputAt compress_sound eval_col
  eval_cst wrap_back half16 word)
open StarkedAir.HeaderChain (eqLimbs pubWord pubState)

theorem ltP {m : ℕ} (h : m ≤ 1073741824) : m < P := lt_of_le_of_lt h (by unfold P; norm_num)

theorem ceq {a b : ℕ} (ha : a ≤ 1073741824) (hb : b ≤ 1073741824) (h : (a : F) = (b : F)) : a = b :=
  natCast_inj_of_lt (ltP ha) (ltP hb) h

section Period

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem sha_sat : ShaSat n preCols pub M := fun r hr c hc =>
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

omit hsat in
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
  compress_sound (sha_sat hsat) hsn (pre_sha hs hsn)

omit hsat in
theorem eval_per72 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = Block.Sha.per72 f) {r : ℕ}
    (hr : r < n) : (pre i).eval n preCols pub M r = ((f (r % 72) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 72 < 72 := Nat.mod_lt _ (by norm_num)
  simp [Block.Sha.per72, PreCol.eval, Sha256.PERIOD, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_row0 {r : ℕ} (hr : r < n) : (pre ROW0).eval n preCols pub M r = if r % 72 = 0 then 1 else 0 := by
  rw [eval_per72 (f := fun q => if q = 0 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_init {r : ℕ} (hr : r < n) : (pre INIT).eval n preCols pub M r = if r % 72 < 4 then 1 else 0 := by
  rw [eval_per72 (f := fun q => if q < 4 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_fin3 {r : ℕ} (hr : r < n) : (pre FIN3).eval n preCols pub M r = if r % 72 = 71 then 1 else 0 := by
  rw [eval_per72 (f := fun q => if q = 71 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_iq {j r : ℕ} (hj : j < 4) (hr : r < n) :
    (pre (IQ j)).eval n preCols pub M r = if r % 72 = j then 1 else 0 := by
  have hg : preCols.getD (IQ j) (.periodic [0]) = Block.Sha.per72 (fun q => if q = j then 1 else 0) := by
    interval_cases j <;> rfl
  rw [eval_per72 hg hr]; split_ifs <;> simp

omit hsat in
theorem ev_p0 {r : ℕ} (hr : r < n) : (pre P0).eval n preCols pub M r = if r < 72 then 1 else 0 := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [show preCols.getD P0 (.periodic [0]) = .rowLt 72 from rfl]
  simp [PreCol.eval]

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

theorem flag_sat {c : Expr} (hc : c ∈ flagC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem chain_sat {c : Expr} (hc : c ∈ chainC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem init_sat {c : Expr} (hc : c ∈ initC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem out_sat {c : Expr} (hc : c ∈ outC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

/-- Per-period values are constant down the period. -/
theorem per_const {X : ℕ} (hX : X ∈ [BLKI, NIL, LASTS]) {s : ℕ} (hs : s % 72 = 0) :
    ∀ p < 72, s + p < n → M X (s + p) = M X s := by
  intro p
  induction p with
  | zero => intro _ _; rfl
  | succ p ih =>
    intro hp hr
    rw [show s + (p + 1) = s + p + 1 by ring] at hr ⊢
    have hc := flag_sat hsat (c := .mul (om (pre ROW0)) (.sub (k X) (kp X)))
      (by simp only [flagC, List.mem_append, List.mem_map]; right; exact ⟨X, hX, rfl⟩) hr
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_row0 hr, show (s + p + 1) % 72 ≠ 0 by omega,
      if_false, sub_zero, one_mul, ev_k hr, kp, eval_col] at hc
    rw [show wrap n (s + p + 1) (-1) = s + p by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; omega] at hc
    rw [sub_eq_zero.mp hc, ih (by omega) (by omega)]

theorem nil_bool {r : ℕ} (hr : r < n) : M NIL r = 0 ∨ M NIL r = 1 := by
  have h := flag_sat hsat (c := boolC (k NIL)) (by simp [flagC]) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem usew_eq {r : ℕ} (hr : r < n) : M USEW r = 1 - M NIL r := by
  have h := flag_sat hsat (c := .sub (k USEW) (om (k NIL))) (by simp [flagC]) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h
  exact sub_eq_zero.mp h

theorem chn_eq {r : ℕ} (hr : r < n) : M CHN r = M USEW r * (1 - if r < 72 then 1 else 0) := by
  have h := flag_sat hsat (c := .sub (k CHN) (.mul (k USEW) (om (pre P0)))) (by simp [flagC]) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, ev_p0 hr] at h
  exact sub_eq_zero.mp h

theorem p0_nil (hn : 0 < n) : M NIL 0 = 0 := by
  have h := flag_sat hsat (c := .mul (pre P0) (k NIL)) (by simp [flagC]) hn
  simpa only [Expr.eval, ev_p0 hn, ev_k hn, show (0 : ℕ) < 72 by norm_num, if_true, one_mul] using h

theorem lasts_blki {r : ℕ} (hr : r < n) (h : M LASTS r = 1) :
    M BLKI r = pub (H_NB SHA_OUT) - pub (H_NB SHA_IN) - 1 ∧ M NIL r = 0 := by
  have h1 := flag_sat hsat (c := .mul (k LASTS) (.sub (k BLKI) mLast)) (by simp [flagC]) hr
  have h2 := flag_sat hsat (c := .mul (k LASTS) (k NIL)) (by simp [flagC]) hr
  simp only [Expr.eval, ev_k hr, mLast, one, eval_cst, Nat.cast_one, h, one_mul] at h1 h2
  exact ⟨sub_eq_zero.mp h1, h2⟩

theorem p0_blki (hn : 0 < n) : M BLKI 0 = 0 := by
  have h := chain_sat hsat (c := .mul (pre P0) (k BLKI)) (by simp [chainC]) hn
  simpa only [Expr.eval, ev_p0 hn, ev_k hn, show (0 : ℕ) < 72 by norm_num, if_true, one_mul] using h

/-- A used period after period 0 continues: the previous period is used, one block back. -/
theorem prev_period {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s < n) (hnil : M NIL s = 0) :
    M CHN s = 1 ∧ M BLKI s = M BLKI (s - 72) + 1 ∧ M NIL (s - 72) = 0 := by
  have hchn : M CHN s = 1 := by
    rw [chn_eq hsat hsn, usew_eq hsat hsn, hnil, if_neg (by omega)]; ring
  have hw : wrap n s (-72) = s - 72 := by
    rw [show (-72 : ℤ) = -((72 : ℕ) : ℤ) by simp, wrap_back (by omega) hsn]
  have h1 := chain_sat hsat (c := .mul (pre ROW0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)))
    (by simp [chainC]) hsn
  have h2 := chain_sat hsat (c := .mul (pre ROW0) (.mul (k CHN) (kq NIL))) (by simp [chainC]) hsn
  simp only [Expr.eval, ev_row0 hsn, hs, if_true, one_mul, ev_k hsn, hchn, kq, eval_col, hw, one, eval_cst,
    Nat.cast_one] at h1 h2
  exact ⟨hchn, by linear_combination h1, h2⟩

/-- **The used periods' blocks**: a whole used period `q` is block `q`, after used periods. -/
theorem blki_q (hn : 0 < n) : ∀ q, 72 * q + 72 ≤ n → M NIL (72 * q) = 0 →
    M BLKI (72 * q) = (q : F) ∧ ∀ j ≤ q, M NIL (72 * j) = 0 := by
  intro q
  induction q with
  | zero => intro _ h; exact ⟨by simpa using p0_blki hsat hn, fun j hj => by
      rw [show j = 0 by omega]; simpa using h⟩
  | succ q ih =>
    intro hsn hnil
    obtain ⟨-, hb, hnp⟩ := prev_period hsat (s := 72 * (q + 1)) (by omega) (by omega) (by omega) hnil
    rw [show 72 * (q + 1) - 72 = 72 * q by omega] at hb hnp
    obtain ⟨ihb, ihn⟩ := ih (by omega) hnp
    refine ⟨by rw [hb, ihb]; push_cast; ring, fun j hj => ?_⟩
    rcases Nat.lt_or_ge j (q + 1) with h | h
    · exact ihn j (by omega)
    · rw [show j = q + 1 by omega]; exact hnil

theorem abits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.A + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.A]; omega)

theorem ebits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.E + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.E]; omega)

theorem wbits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.W + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.W]; omega)

/-- **Period 0 starts from the public `H_in`.** -/
theorem input_pub (h72 : 72 ≤ n) : inputAt M 0 = pubState pub SHA_IN := by
  have row : ∀ q < 4, word M Sha256.A q = pubWord pub (SHA_IN + 2 * (3 - q)) ∧
      word M Sha256.E q = pubWord pub (SHA_IN + 2 * (7 - q)) := by
    intro q hq
    have hr : q < n := by omega
    have hsel : (Expr.mul (pre P0) (pre (IQ q))).eval n preCols pub M q = 1 := by
      simp only [Expr.eval, ev_p0 hr, ev_iq hq hr, show q < 72 by omega, Nat.mod_eq_of_lt (show q < 72 by omega),
        if_true, one_mul]
    have hfA : (fun h => Expr.pub (H_LIMB SHA_IN (2 * (3 - q) + h))) =
        (fun h => Expr.pub (SHA_IN + 2 * (3 - q) + h)) := by funext h; simp [H_LIMB, Nat.add_assoc]
    have hfE : (fun h => Expr.pub (H_LIMB SHA_IN (2 * (7 - q) + h))) =
        (fun h => Expr.pub (SHA_IN + 2 * (7 - q) + h)) := by funext h; simp [H_LIMB, Nat.add_assoc]
    constructor
    · refine HeaderChain.eqLimbs_pub (fun c hc => init_sat hsat ?_ hr) hsel hr rfl (abits hsat hr)
      simp only [initC, List.mem_append, List.mem_flatMap, List.mem_range]
      left; left; refine ⟨q, hq, ?_⟩; left; rw [hfA]; exact hc
    · refine HeaderChain.eqLimbs_pub (fun c hc => init_sat hsat ?_ hr) hsel hr rfl (ebits hsat hr)
      simp only [initC, List.mem_append, List.mem_flatMap, List.mem_range]
      left; left; refine ⟨q, hq, ?_⟩; right; rw [hfE]; exact hc
  obtain ⟨a0, e0⟩ := row 0 (by norm_num)
  obtain ⟨a1, e1⟩ := row 1 (by norm_num)
  obtain ⟨a2, e2⟩ := row 2 (by norm_num)
  obtain ⟨a3, e3⟩ := row 3 (by norm_num)
  simp only [inputAt, Sha256.stAt, pubState]
  norm_num at a0 e0 a1 e1 a2 e2 a3 e3 ⊢
  rw [a0, e0, a1, e1, a2, e2, a3, e3]
  simp

/-- **A continuing period starts from the previous period's output.** -/
theorem input_chain {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (hc : M CHN s = 1) :
    inputAt M s = outputAt M (s - 72) := by
  have row : ∀ q < 4, word M Sha256.A (s + q) = word M Sha256.A (s - 4 + q) ∧
      word M Sha256.E (s + q) = word M Sha256.E (s - 4 + q) := by
    intro q hq
    have hr : s + q < n := by omega
    have hcq : M CHN (s + q) = 1 := by
      have h0 := hc
      rw [chn_eq hsat (by omega), usew_eq hsat (by omega), if_neg (by omega)] at h0
      rw [chn_eq hsat hr, usew_eq hsat hr, per_const hsat (X := NIL) (by simp) hs q (by omega) hr,
        if_neg (by omega), h0]
    have hsel : (Expr.mul (pre INIT) (k CHN)).eval n preCols pub M (s + q) = 1 := by
      simp only [Expr.eval, ev_init hr, show (s + q) % 72 < 4 by omega, if_true, ev_k hr, hcq, one_mul]
    have hw : wrap n (s + q) (-4) = s - 4 + q := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; omega
    constructor
    · exact HeaderChain.eqLimbs_word _ (fun c hc => init_sat hsat (by simp only [initC, List.mem_append]; tauto) hr)
        hsel (wrap_zero hr) (abits hsat hr) (fun hh hhh => Sha256.eval_limb hw (abits hsat (by omega)) hhh)
    · exact HeaderChain.eqLimbs_word _ (fun c hc => init_sat hsat (by simp only [initC, List.mem_append]; tauto) hr)
        hsel (wrap_zero hr) (ebits hsat hr) (fun hh hhh => Sha256.eval_limb hw (ebits hsat (by omega)) hhh)
  obtain ⟨a0, e0⟩ := row 0 (by norm_num)
  obtain ⟨a1, e1⟩ := row 1 (by norm_num)
  obtain ⟨a2, e2⟩ := row 2 (by norm_num)
  obtain ⟨a3, e3⟩ := row 3 (by norm_num)
  simp only [inputAt, outputAt, Sha256.stAt]
  simp only [Nat.add_zero, show s + 3 - 1 = s + 2 by omega, show s + 3 - 2 = s + 1 by omega, show s + 3 - 3 = s by omega,
    show s - 72 + 71 = s - 1 by omega, show s - 1 - 1 = s - 2 by omega, show s - 1 - 2 = s - 3 by omega,
    show s - 1 - 3 = s - 4 by omega] at *
  rw [a0, e0, a1, e1, a2, e2, a3, e3, show s - 4 + 1 = s - 3 by omega, show s - 4 + 2 = s - 2 by omega,
    show s - 4 + 3 = s - 1 by omega]

/-- **The last block's output is `H_out`**, at a period whose last row holds `LASTS`. -/
theorem out_word {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) (hl : M LASTS (s + 71) = 1) :
    ∀ w < 8, ∀ h ≤ 1, (pub (H_LIMB SHA_OUT (2 * w + h))).val =
      half16 (Spec.Bitcoin.stateWord (outputAt M s) w) h := by
  intro w hw h hh
  have hr : s + 71 < n := by omega
  have hP : ∀ y : Spec.Sha256.Word, half16 y h < P := fun y => lt_trans (Sha256.half16_lt _ _) (by unfold P; norm_num)
  have hsel : (Expr.mul (k LASTS) (pre FIN3)).eval n preCols pub M (s + 71) = 1 := by
    simp only [Expr.eval, ev_k hr, hl, ev_fin3 hr, if_pos (show (s + 71) % 72 = 71 by omega), one_mul]
  rw [outputAt, HeaderChain.stAt_word _ _ hw]
  by_cases h4 : w < 4
  · rw [if_pos h4]
    have hc := out_sat hsat (c := .mul (.mul (k LASTS) (pre FIN3))
      (.sub (limb Sha256.A h (-((w : ℕ) : ℤ))) (.pub (H_LIMB SHA_OUT (2 * w + h))))) (by
        simp only [outC, List.mem_flatMap, List.mem_range, List.mem_append]
        refine ⟨w, h4, Or.inl (List.mem_map.mpr ⟨h, by simp; omega, rfl⟩)⟩) hr
    rw [Expr.eval, hsel, one_mul, Expr.eval, Sha256.limbs_back (sha_sat hsat) hr (show w ≤ s + 71 by omega)
      (by simp [Sha256.A]) hh, Expr.eval, sub_eq_zero] at hc
    rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt (hP _)]
  · rw [if_neg h4]
    obtain ⟨i, rfl⟩ : ∃ i, w = 4 + i := ⟨w - 4, by omega⟩
    have hc := out_sat hsat (c := .mul (.mul (k LASTS) (pre FIN3))
      (.sub (limb Sha256.E h (-((i : ℕ) : ℤ))) (.pub (H_LIMB SHA_OUT (2 * (4 + i) + h))))) (by
        simp only [outC, List.mem_flatMap, List.mem_range, List.mem_append]
        refine ⟨i, by omega, Or.inr (List.mem_map.mpr ⟨h, by simp; omega, rfl⟩)⟩) hr
    rw [Expr.eval, hsel, one_mul, Expr.eval, Sha256.limbs_back (sha_sat hsat) hr (show i ≤ s + 71 by omega)
      (by simp [Sha256.E]) hh, Expr.eval, sub_eq_zero] at hc
    rw [← hc, ZMod.val_natCast, Nat.mod_eq_of_lt (hP _), show 4 + i - 4 = i by omega]

/-- **`set_shac` is sound.** If every used period's message-word uses read words `wd b t` of blocks
`b < m` (`m = nb_out − nb_in`), and the end token is yielded on some period's last row, then `m ≥ 1` and
`H_out` (16-bit limbs) is the chaining value after compressing blocks `0 … m − 1` from `H_in`. -/
theorem shac_sound (hn : 0 < n) (hnP : n ≤ 1073741824) (wd : ℕ → ℕ → Spec.Sha256.Word)
    (hmsg : ∀ s t, s % 72 = 0 → t < 16 → s + 4 + t < n → M USEW s = 1 →
      ∃ b : ℕ, M BLKI s = (b : F) ∧ b < (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val ∧
        ∀ h ≤ 1, (limb Sha256.W h).eval n preCols pub M (s + 4 + t) = ((half16 (wd b t) h : ℕ) : F))
    (htok : ∃ r < n, r % 72 = 71 ∧ M LASTS r = 1) :
    1 ≤ (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val ∧
    ∀ w < 8, ∀ h ≤ 1, (pub (H_LIMB SHA_OUT (2 * w + h))).val =
      half16 (Spec.Bitcoin.stateWord (wfold (pubState pub SHA_IN) wd
        (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val) w) h := by
  obtain ⟨r, hr, hr71, hlast⟩ := htok
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 71 := ⟨r - 71, by omega⟩
  have hs : s % 72 = 0 := by omega
  have hsn : s + 72 ≤ n := by omega
  have hls : M LASTS s = 1 := by
    rw [← per_const hsat (X := LASTS) (by simp) hs 71 (by omega) hr, hlast]
  obtain ⟨hbl, hnil⟩ := lasts_blki hsat (by omega) hls
  obtain ⟨hq, -⟩ := blki_q hsat hn (s / 72) (by omega) (by rw [show 72 * (s / 72) = s by omega]; exact hnil)
  rw [show 72 * (s / 72) = s by omega] at hq
  have hm : (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val = s / 72 + 1 := by
    have : pub (H_NB SHA_OUT) - pub (H_NB SHA_IN) = ((s / 72 + 1 : ℕ) : F) := by
      push_cast; rw [← hq, hbl]; ring
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (ltP (by omega))]
  -- a used whole period's message is its block's words
  have msg : ∀ q, 72 * q + 72 ≤ n → M NIL (72 * q) = 0 → ∀ t < 16, messageAt M (72 * q) t = wd q t := by
    intro q hqn hnq t ht
    have hrt : 72 * q + 4 + t < n := by omega
    obtain ⟨b, hb, hbm, hl⟩ := hmsg (72 * q) t (by omega) ht hrt
      (by rw [usew_eq hsat (by omega), hnq, sub_zero])
    have hbq : b = q := ceq (by omega) (by omega) (by rw [← hb, (blki_q hsat hn q hqn hnq).1])
    subst hbq
    have hw : ∀ h ≤ 1, half16 (word M Sha256.W (72 * b + 4 + t)) h = half16 (wd b t) h := fun h hh => by
      have e1 := Sha256.eval_limb (n := n) (pc := preCols) (pub := pub) (main := M) (r := 72 * b + 4 + t)
        (base := Sha256.W) (off := 0) (wrap_zero hrt) (wbits hsat hrt) hh
      exact natCast_inj_of_lt (lt_trans (Sha256.half16_lt _ _) (by unfold P; norm_num))
        (lt_trans (Sha256.half16_lt _ _) (by unfold P; norm_num)) (e1.symm.trans (hl h hh))
    exact HeaderChain.half16_inj (hw 0 (by norm_num)) (hw 1 (by norm_num))
  -- the used periods' outputs chain
  have hout : ∀ q, 72 * q + 72 ≤ n → M NIL (72 * q) = 0 →
      outputAt M (72 * q) = wfold (pubState pub SHA_IN) wd (q + 1) := by
    intro q
    induction q with
    | zero =>
      intro hqn hnq
      rw [← period_compress hsat (s := 72 * 0) (by omega) hqn, show 72 * 0 = 0 by rfl, input_pub hsat (by omega)]
      exact HeaderChain.compress_congr _ (fun t ht => msg 0 hqn hnq t ht)
    | succ q ih =>
      intro hqn hnq
      obtain ⟨hchn, -, hnp⟩ := prev_period hsat (s := 72 * (q + 1)) (by omega) (by omega) (by omega) hnq
      rw [show 72 * (q + 1) - 72 = 72 * q by omega] at hnp
      rw [← period_compress hsat (s := 72 * (q + 1)) (by omega) hqn,
        input_chain hsat (by omega) (by omega) hqn hchn, show 72 * (q + 1) - 72 = 72 * q by omega,
        ih (by omega) hnp, wfold]
      exact HeaderChain.compress_congr _ (fun t ht => msg (q + 1) hqn hnq t ht)
  refine ⟨by omega, fun w hw h hh => ?_⟩
  rw [out_word hsat hs hsn hlast w hw h hh, hm, ← hout (s / 72) (by omega)
    (by rw [show 72 * (s / 72) = s by omega]; exact hnil), show 72 * (s / 72) = s by omega]

end Period

end StarkedAir.SetPass.ShaC

