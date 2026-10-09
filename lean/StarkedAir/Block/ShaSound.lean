/-
**Block SHA-256 soundness (M3a.3, SHA component).** Every aligned period computes the SHA-256
compression (`period_compress`, from `compress_sound`); then the period bookkeeping chains them.
-/
import StarkedAir.Block.Sha
import StarkedAir.Gadgets.HeaderChainSound

namespace StarkedAir.Block.Sha

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC limb ShaSat shaPre inputAt messageAt outputAt compress_sound)

/-- The chaining value after `j` blocks of a message whose periods start at `s0`. -/
def fold (M : ℕ → ℕ → F) (s0 : ℕ) : ℕ → Spec.Sha256.State
  | 0 => Spec.Sha256.IV
  | j + 1 => Spec.Sha256.compress (fold M s0 j) (messageAt M (s0 + 72 * j))

/-- The second hash's message block over a digest `d`. -/
def dblBlock (d : Spec.Sha256.State) (t : ℕ) : Spec.Sha256.Word :=
  if t < 8 then Spec.Bitcoin.stateWord d t else BitVec.ofNat 32 (dblWord t)

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

theorem init_sat {c : Expr} (hc : c ∈ initC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem abits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.A + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.A]; omega)

theorem ebits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.E + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.E]; omega)

theorem init_row {s q : ℕ} (hs : s % 72 = 0) (hq : q < 4) (hr : s + q < n) :
    (pre INIT).eval n preCols pub M (s + q) = 1 := by
  rw [eval_per72 hsat (i := INIT) (f := fun q => if q < 4 then 1 else 0) rfl hr, show (s + q) % 72 = q by omega]
  simp [hq]

/-- **A first block or a second hash starts from the IV.** -/
theorem input_iv {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) (h : M FST s + M DBL s = 1) :
    inputAt M s = Spec.Sha256.IV := by
  have row : ∀ q < 4, Sha256.word M Sha256.A (s + q) = BitVec.ofNat 32 (HeaderChain.ivWords.getD (3 - q) 0) ∧
      Sha256.word M Sha256.E (s + q) = BitVec.ofNat 32 (HeaderChain.ivWords.getD (7 - q) 0) := by
    intro q hq
    have hr : s + q < n := by omega
    have hsel : (Expr.mul (pre INIT) (.add (k FST) (k DBL))).eval n preCols pub M (s + q) = 1 := by
      simp only [Expr.eval, init_row hsat hs hq hr, k, Sha256.eval_col, wrap_zero hr, one_mul,
        per_const hsat (X := FST) (by simp) hs q (by omega) hr, per_const hsat (X := DBL) (by simp) hs q (by omega) hr, h]
    have ev := fun (i : ℕ) (f : ℕ → ℕ) (hi : preCols.getD i (.periodic [0]) = per72 f) => eval_per72 hsat hi hr
    constructor
    · refine HeaderChain.eqLimbs_word _ (fun c hc => init_sat hsat (by simp only [initC, List.mem_append]; tauto) hr)
        hsel (wrap_zero hr) (abits hsat hr) ?_
      intro hh hhh
      interval_cases hh
      · rw [ev _ _ rfl, show (s + q) % 72 = q by omega, if_pos hq, HeaderChain.half16_ofNat (HeaderChain.ivWords_lt _) 0 (by norm_num)]; rfl
      · rw [ev _ _ rfl, show (s + q) % 72 = q by omega, if_pos hq, HeaderChain.half16_ofNat (HeaderChain.ivWords_lt _) 1 (by norm_num)]; rfl
    · refine HeaderChain.eqLimbs_word _ (fun c hc => init_sat hsat (by simp only [initC, List.mem_append]; tauto) hr)
        hsel (wrap_zero hr) (ebits hsat hr) ?_
      intro hh hhh
      interval_cases hh
      · rw [ev _ _ rfl, show (s + q) % 72 = q by omega, if_pos hq, HeaderChain.half16_ofNat (HeaderChain.ivWords_lt _) 0 (by norm_num)]; rfl
      · rw [ev _ _ rfl, show (s + q) % 72 = q by omega, if_pos hq, HeaderChain.half16_ofNat (HeaderChain.ivWords_lt _) 1 (by norm_num)]; rfl
  obtain ⟨a0, e0⟩ := row 0 (by norm_num)
  obtain ⟨a1, e1⟩ := row 1 (by norm_num)
  obtain ⟨a2, e2⟩ := row 2 (by norm_num)
  obtain ⟨a3, e3⟩ := row 3 (by norm_num)
  simp only [Nat.add_zero] at a0 e0
  simp only [inputAt, Sha256.stAt, show s + 3 - 1 = s + 2 by omega, show s + 3 - 2 = s + 1 by omega,
    show s + 3 - 3 = s by omega, a0, e0, a1, e1, a2, e2, a3, e3]
  rfl

theorem chn_eq {r : ℕ} (hr : r < n) : M CHN r = 1 - (M FST r + (M DBL r + M NILS r)) := by
  have := flag_sat hsat (c := .sub (k CHN) (om (.add (k FST) (.add (k DBL) (k NILS))))) (by simp [flagC]) hr
  simp only [Expr.eval, om, one, Sha256.eval_cst, k, Sha256.eval_col, wrap_zero hr, Nat.cast_one] at this
  linear_combination this

theorem usew_eq {r : ℕ} (hr : r < n) : M USEW r = 1 - (M DBL r + M NILS r) := by
  have := flag_sat hsat (c := .sub (k USEW) (om (.add (k DBL) (k NILS)))) (by simp [flagC]) hr
  simp only [Expr.eval, om, one, Sha256.eval_cst, k, Sha256.eval_col, wrap_zero hr, Nat.cast_one] at this
  linear_combination this

/-- **A continuation starts from the previous period's output.** -/
theorem input_chain {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (h : M CHN s = 1) :
    inputAt M s = outputAt M (s - 72) := by
  have row : ∀ q < 4, Sha256.word M Sha256.A (s + q) = Sha256.word M Sha256.A (s - 4 + q) ∧
      Sha256.word M Sha256.E (s + q) = Sha256.word M Sha256.E (s - 4 + q) := by
    intro q hq
    have hr : s + q < n := by omega
    have hc : M CHN (s + q) = 1 := by
      rw [chn_eq hsat hr, per_const hsat (X := FST) (by simp) hs q (by omega) hr,
        per_const hsat (X := DBL) (by simp) hs q (by omega) hr, per_const hsat (X := NILS) (by simp) hs q (by omega) hr,
        ← chn_eq hsat (by omega), h]
    have hsel : (Expr.mul (pre INIT) (k CHN)).eval n preCols pub M (s + q) = 1 := by
      simp only [Expr.eval, init_row hsat hs hq hr, k, Sha256.eval_col, wrap_zero hr, one_mul, hc]
    have hw : wrap n (s + q) (-4) = s - 4 + q := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by simp, Sha256.wrap_back (by omega) hr]; omega
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

theorem dbl_sat {c : Expr} (hc : c ∈ dblC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem wbits {r : ℕ} (hr : r < n) : ∀ i < 32, (M (Sha256.W + i) r).val ≤ 1 :=
  fun i hi => Sha256.bool_val (sha_sat hsat) hr (by simp [Sha256.W]; omega)

/-- **The second hash's message**: the previous period's digest words, then `dblWord`. -/
theorem dbl_message {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (h : M DBL s = 1) :
    ∀ t < 16, messageAt M s t =
      if t < 8 then Spec.Bitcoin.stateWord (outputAt M (s - 72)) t else BitVec.ofNat 32 (dblWord t) := by
  intro t ht
  have hr : s + 4 + t < n := by omega
  have hd : M DBL (s + 4 + t) = 1 := by
    rw [show s + 4 + t = s + (4 + t) by ring, per_const hsat (X := DBL) (by simp) hs (4 + t) (by omega) (by omega), h]
  have ev := fun (i : ℕ) (f : ℕ → ℕ) (hi : preCols.getD i (.periodic [0]) = per72 f) => eval_per72 hsat hi hr
  have hq : (s + 4 + t) % 72 = 4 + t := by omega
  simp only [messageAt]
  split_ifs with h8
  · -- Digest words.
    have hsel : (Expr.mul (k DBL) (pre (DMSG t))).eval n preCols pub M (s + 4 + t) = 1 := by
      simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr, hd, one_mul]
      have hg : preCols.getD (DMSG t) (.periodic [0]) = per72 (fun q => if q = 4 + t then 1 else 0) := by
        interval_cases t <;> rfl
      rw [eval_per72 hsat hg hr, hq]; simp
    simp only [outputAt, show s - 72 + 71 = s - 1 by omega]
    rw [HeaderChain.stAt_word _ _ h8]
    have hsrc : ((HeaderChain.msgSrc t).2 : ℤ) = -((((if t < 4 then 5 + 2 * t else 9 + 2 * (t - 4)) : ℕ)) : ℤ) := by
      unfold HeaderChain.msgSrc; split_ifs <;> rfl
    have hw : wrap n (s + 4 + t) (HeaderChain.msgSrc t).2 =
        if t < 4 then s - 1 - t else s - 1 - (t - 4) := by
      rw [hsrc, Sha256.wrap_back (by split_ifs <;> omega) hr]; split_ifs <;> omega
    have hX : (HeaderChain.msgSrc t).1 = if t < 4 then Sha256.A else Sha256.E := by
      unfold HeaderChain.msgSrc; split_ifs <;> rfl
    have hsrcb : ∀ i < 32, (M ((HeaderChain.msgSrc t).1 + i) (if t < 4 then s - 1 - t else s - 1 - (t - 4))).val ≤ 1 := by
      rw [hX]; split_ifs
      · exact abits hsat (by omega)
      · exact ebits hsat (by omega)
    have key := HeaderChain.eqLimbs_word (n := n) (pc := preCols) (pub := pub) (main := M) (r := s + 4 + t)
      (Y := Sha256.word M (HeaderChain.msgSrc t).1 (if t < 4 then s - 1 - t else s - 1 - (t - 4))) (X := Sha256.W)
      (off := 0) (sel := .mul (k DBL) (pre (DMSG t)))
      (rhs := fun h => limb (HeaderChain.msgSrc t).1 h (HeaderChain.msgSrc t).2)
      (fun c hc => dbl_sat hsat (by
        simp only [dblC, List.mem_append, List.mem_flatMap, List.mem_range]; left; exact ⟨t, h8, hc⟩) hr)
      hsel (wrap_zero hr) (wbits hsat hr) (fun hh hhh => Sha256.eval_limb hw hsrcb hhh)
    rw [key, hX]; split_ifs <;> rfl
  · -- Constant words.
    have hsel : (Expr.mul (k DBL) (pre DCONST)).eval n preCols pub M (s + 4 + t) = 1 := by
      simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr, hd, one_mul]
      rw [ev DCONST (fun q => if 12 ≤ q ∧ q < 20 then 1 else 0) rfl, hq]; simp; omega
    refine HeaderChain.eqLimbs_word _ (fun c hc => dbl_sat hsat (by
        simp only [dblC, List.mem_append]; right; exact hc) hr)
      hsel (wrap_zero hr) (wbits hsat hr) (fun hh hhh => ?_)
    have hlt : dblWord t < 2 ^ 32 := by unfold dblWord; split_ifs <;> norm_num
    interval_cases hh
    · rw [ev (DC_LO + 0) (fun q => if 12 ≤ q ∧ q < 20 then dblWord (q - 4) % 2 ^ 16 else 0) rfl, hq,
        if_pos (by omega), show 4 + t - 4 = t by omega, HeaderChain.half16_ofNat hlt 0 (by norm_num)]; simp
    · rw [ev (DC_LO + 1) (fun q => if 12 ≤ q ∧ q < 20 then dblWord (q - 4) / 2 ^ 16 else 0) rfl, hq,
        if_pos (by omega), show 4 + t - 4 = t by omega, HeaderChain.half16_ofNat hlt 1 (by norm_num)]; simp

theorem flags_excl {r : ℕ} (hr : r < n) : M FST r * M DBL r = 0 ∧ M FST r * M NILS r = 0 ∧ M DBL r * M NILS r = 0 := by
  have e := fun (c : Expr) (h : c ∈ flagC) => flag_sat hsat h hr
  have h1 := e (.mul (k FST) (k DBL)) (by simp [flagC])
  have h2 := e (.mul (k FST) (k NILS)) (by simp [flagC])
  have h3 := e (.mul (k DBL) (k NILS)) (by simp [flagC])
  simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **A message's blocks**: from a first block through continuations, the outputs chain. -/
theorem chain_out {s0 b : ℕ} (hs0 : s0 % 72 = 0) (hn : s0 + 72 * b ≤ n) (hf : M FST s0 = 1)
    (hc : ∀ j, 1 ≤ j → j < b → M CHN (s0 + 72 * j) = 1) :
    ∀ j, 1 ≤ j → j ≤ b → outputAt M (s0 + 72 * (j - 1)) = fold M s0 j := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · have hd : M DBL s0 = 0 := by
        have := (flags_excl hsat (show s0 < n by omega)).1; rw [hf, one_mul] at this; exact this
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.add_zero, fold]
      rw [← period_compress hsat hs0 (by omega), input_iv hsat hs0 (by omega) (by rw [hf, hd, add_zero])]
    · have hs : (s0 + 72 * j) % 72 = 0 := by omega
      rw [show j + 1 - 1 = j by omega, ← period_compress hsat hs (by omega),
        input_chain hsat hs (by omega) (by omega) (hc j hj0 (by omega)),
        show s0 + 72 * j - 72 = s0 + 72 * (j - 1) by omega, ih (by omega) (by omega), fold]

/-- **The second hash**: its output is the compression of the IV with the previous digest and the
constant padding, i.e. SHA-256 of that digest. -/
theorem dbl_out {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (h : M DBL s = 1) :
    outputAt M s = Spec.Sha256.compress Spec.Sha256.IV (dblBlock (outputAt M (s - 72))) := by
  have hf : M FST s = 0 := by
    have := (flags_excl hsat (show s < n by omega)).1; rw [h, mul_one] at this; exact this
  rw [← period_compress hsat hs hsn, input_iv hsat hs hsn (by rw [hf, h, zero_add])]
  exact HeaderChain.compress_congr _ (fun t ht => by rw [dbl_message hsat hs h72 hsn h t ht]; rfl)

end Period

end StarkedAir.Block.Sha
