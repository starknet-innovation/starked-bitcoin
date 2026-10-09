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

theorem one_add_one_ne : (1 : F) + 1 ≠ 0 := by
  intro e
  have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num)
    (by push_cast; linear_combination e)
  omega

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
theorem nflag_sat {c : Expr} (hc : c ∈ nodeFlagC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem per_const {X : ℕ} (hX : X ∈ [MID, BLKI, FST, DBL, NILS, NODE, NPAD, LID, RID, NDUP]) {s : ℕ} (hs : s % 72 = 0) :
    ∀ p < 72, s + p < n → M X (s + p) = M X s := by
  intro p
  induction p with
  | zero => intro _ _; rfl
  | succ p ih =>
    intro hp hr
    have hc : (Expr.mul (om (pre ROW0)) (.sub (k X) (kp X))).eval n preCols pub M (s + (p + 1)) = 0 := by
      have h5 : X ∈ [MID, BLKI, FST, DBL, NILS] ∨ X ∈ [NODE, NPAD, LID, RID, NDUP] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hX ⊢; tauto
      rcases h5 with h5 | h5
      · exact flag_sat hsat (by simp only [flagC, List.mem_append, List.mem_map]; right; exact ⟨X, h5, rfl⟩) hr
      · exact nflag_sat hsat (by simp only [nodeFlagC, List.mem_append, List.mem_map]; right; exact ⟨X, h5, rfl⟩) hr
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
theorem input_iv {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) (h : M FST s + (M DBL s + M NODE s) = 1) :
    inputAt M s = Spec.Sha256.IV := by
  have row : ∀ q < 4, Sha256.word M Sha256.A (s + q) = BitVec.ofNat 32 (HeaderChain.ivWords.getD (3 - q) 0) ∧
      Sha256.word M Sha256.E (s + q) = BitVec.ofNat 32 (HeaderChain.ivWords.getD (7 - q) 0) := by
    intro q hq
    have hr : s + q < n := by omega
    have hsel : (Expr.mul (pre INIT) (.add (k FST) (.add (k DBL) (k NODE)))).eval n preCols pub M (s + q) = 1 := by
      simp only [Expr.eval, init_row hsat hs hq hr, k, Sha256.eval_col, wrap_zero hr, one_mul,
        per_const hsat (X := FST) (by simp) hs q (by omega) hr, per_const hsat (X := DBL) (by simp) hs q (by omega) hr,
        per_const hsat (X := NODE) (by simp) hs q (by omega) hr, h]
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

theorem chn_eq {r : ℕ} (hr : r < n) :
    M CHN r = 1 - (M FST r + (M DBL r + (M NILS r + (M NODE r + M NPAD r)))) := by
  have := flag_sat hsat (c := .sub (k CHN) (om (.add (k FST) (.add (k DBL) (.add (k NILS) (.add (k NODE) (k NPAD)))))))
    (by simp [flagC]) hr
  simp only [Expr.eval, om, one, Sha256.eval_cst, k, Sha256.eval_col, wrap_zero hr, Nat.cast_one] at this
  linear_combination this

theorem usew_eq {r : ℕ} (hr : r < n) : M USEW r = 1 - (M DBL r + (M NILS r + (M NODE r + M NPAD r))) := by
  have := flag_sat hsat (c := .sub (k USEW) (om (.add (k DBL) (.add (k NILS) (.add (k NODE) (k NPAD)))))) (by simp [flagC]) hr
  simp only [Expr.eval, om, one, Sha256.eval_cst, k, Sha256.eval_col, wrap_zero hr, Nat.cast_one] at this
  linear_combination this

theorem kbool {c : ℕ} (hc : c ∈ [FST, DBL, NILS, NODE, NPAD, NDUP]) {r : ℕ} (hr : r < n) :
    M c r = 0 ∨ M c r = 1 := by
  have e : (boolC (k c)).eval n preCols pub M r = 0 := by
    have h3 : c ∈ [FST, DBL, NILS] ∨ c ∈ [NODE, NPAD, NDUP] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; tauto
    rcases h3 with h3 | h3
    · exact flag_sat hsat (by simp only [flagC, List.mem_append, List.mem_map]; left; left; exact ⟨c, h3, rfl⟩) hr
    · exact nflag_sat hsat (by simp only [nodeFlagC, List.mem_append, List.mem_map]; left; left; exact ⟨c, h3, rfl⟩) hr
  simp only [boolC, Expr.eval, k, Sha256.eval_col, Sha256.eval_cst, wrap_zero hr, Nat.cast_one] at e
  rcases mul_eq_zero.mp e with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The period kinds `FST`, `DBL`, `NILS`, `NODE`, `NPAD` exclude each other. -/
theorem kinds_excl {r : ℕ} (hr : r < n) :
    M FST r * M DBL r = 0 ∧ M FST r * M NILS r = 0 ∧ M DBL r * M NILS r = 0 ∧
    M NODE r * M FST r = 0 ∧ M NODE r * M DBL r = 0 ∧ M NODE r * M NILS r = 0 ∧ M NODE r * M NPAD r = 0 ∧
    M NPAD r * M FST r = 0 ∧ M NPAD r * M DBL r = 0 ∧ M NPAD r * M NILS r = 0 := by
  have e := fun (c : Expr) (h : c ∈ flagC) => flag_sat hsat h hr
  have f := fun (c : Expr) (h : c ∈ nodeFlagC) => nflag_sat hsat h hr
  have h1 := e (.mul (k FST) (k DBL)) (by simp [flagC])
  have h2 := e (.mul (k FST) (k NILS)) (by simp [flagC])
  have h3 := e (.mul (k DBL) (k NILS)) (by simp [flagC])
  have h4 := f (.mul (k NODE) (k FST)) (by simp [nodeFlagC])
  have h5 := f (.mul (k NODE) (k DBL)) (by simp [nodeFlagC])
  have h6 := f (.mul (k NODE) (k NILS)) (by simp [nodeFlagC])
  have h7 := f (.mul (k NODE) (k NPAD)) (by simp [nodeFlagC])
  have h8 := f (.mul (k NPAD) (k FST)) (by simp [nodeFlagC])
  have h9 := f (.mul (k NPAD) (k DBL)) (by simp [nodeFlagC])
  have h10 := f (.mul (k NPAD) (k NILS)) (by simp [nodeFlagC])
  simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

/-- A continuation is no other kind. -/
theorem chn_one {r : ℕ} (hr : r < n) (h : M CHN r = 1) :
    M FST r = 0 ∧ M DBL r = 0 ∧ M NILS r = 0 ∧ M NODE r = 0 ∧ M NPAD r = 0 := by
  have hc := chn_eq hsat hr
  rw [h] at hc
  have bv : ∀ {x : F}, x = 0 ∨ x = 1 → x = ((x.val : ℕ) : F) ∧ x.val ≤ 1 := fun hx => by
    rcases hx with rfl | rfl
    · simp
    · rw [ZMod.val_one]; simp
  have b1 := bv (kbool hsat (c := FST) (by simp) hr)
  have b2 := bv (kbool hsat (c := DBL) (by simp) hr)
  have b3 := bv (kbool hsat (c := NILS) (by simp) hr)
  have b4 := bv (kbool hsat (c := NODE) (by simp) hr)
  have b5 := bv (kbool hsat (c := NPAD) (by simp) hr)
  have hs : (M FST r).val + (M DBL r).val + (M NILS r).val + (M NODE r).val + (M NPAD r).val = 0 := by
    refine natCast_inj_of_lt (a := (M FST r).val + (M DBL r).val + (M NILS r).val + (M NODE r).val + (M NPAD r).val)
      (b := 0) (lt_of_le_of_lt (show _ ≤ 5 by omega) (by unfold P; norm_num)) (by unfold P; norm_num) ?_
    push_cast; rw [← b1.1, ← b2.1, ← b3.1, ← b4.1, ← b5.1]; linear_combination hc
  refine ⟨(ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega),
    (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega)⟩

theorem usew_bool {r : ℕ} (hr : r < n) : M USEW r = 0 ∨ M USEW r = 1 := by
  obtain ⟨-, -, e3, -, e5, e6, e7, -, e9, e10⟩ := kinds_excl hsat hr
  rcases kbool hsat (c := DBL) (by simp) hr with a | a <;> rcases kbool hsat (c := NILS) (by simp) hr with b | b <;>
    rcases kbool hsat (c := NODE) (by simp) hr with c | c <;> rcases kbool hsat (c := NPAD) (by simp) hr with d | d <;>
    simp only [usew_eq hsat hr, a, b, c, d] at e3 e5 e6 e7 e9 e10 ⊢ <;>
    first | (norm_num; done) | (norm_num at e3; done) | (norm_num at e5; done) | (norm_num at e6; done) |
      (norm_num at e7; done) | (norm_num at e9; done) | (norm_num at e10; done)

/-- **A continuation starts from the previous period's output.** -/
theorem input_chain' {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (h : M CHN s + M NPAD s = 1) :
    inputAt M s = outputAt M (s - 72) := by
  have row : ∀ q < 4, Sha256.word M Sha256.A (s + q) = Sha256.word M Sha256.A (s - 4 + q) ∧
      Sha256.word M Sha256.E (s + q) = Sha256.word M Sha256.E (s - 4 + q) := by
    intro q hq
    have hr : s + q < n := by omega
    have hc : M CHN (s + q) = M CHN s := by
      rw [chn_eq hsat hr, per_const hsat (X := FST) (by simp) hs q (by omega) hr,
        per_const hsat (X := DBL) (by simp) hs q (by omega) hr, per_const hsat (X := NILS) (by simp) hs q (by omega) hr,
        per_const hsat (X := NODE) (by simp) hs q (by omega) hr, per_const hsat (X := NPAD) (by simp) hs q (by omega) hr,
        ← chn_eq hsat (by omega)]
    have hnp : M NPAD (s + q) = M NPAD s := per_const hsat (X := NPAD) (by simp) hs q (by omega) hr
    have hsel : (Expr.mul (pre INIT) (.add (k CHN) (k NPAD))).eval n preCols pub M (s + q) = 1 := by
      simp only [Expr.eval, init_row hsat hs hq hr, k, Sha256.eval_col, wrap_zero hr, one_mul, hc, hnp, h]
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

theorem input_chain {s : ℕ} (hs : s % 72 = 0) (h72 : 72 ≤ s) (hsn : s + 72 ≤ n) (h : M CHN s = 1) :
    inputAt M s = outputAt M (s - 72) :=
  input_chain' hsat hs h72 hsn (by rw [h, (chn_one hsat (by omega) h).2.2.2.2, add_zero])

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
      have hno : M NODE s0 = 0 := by
        have := (kinds_excl hsat (show s0 < n by omega)).2.2.2.1; rw [hf, mul_one] at this; exact this
      simp only [Nat.zero_add, Nat.sub_self, Nat.mul_zero, Nat.add_zero, fold]
      rw [← period_compress hsat hs0 (by omega), input_iv hsat hs0 (by omega) (by rw [hf, hd, hno]; ring)]
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
  have hno : M NODE s = 0 := by
    have := (kinds_excl hsat (show s < n by omega)).2.2.2.2.1; rw [h, mul_one] at this; exact this
  rw [← period_compress hsat hs hsn, input_iv hsat hs hsn (by rw [hf, h, hno]; ring)]
  exact HeaderChain.compress_congr _ (fun t ht => by rw [dbl_message hsat hs h72 hsn h t ht]; rfl)

theorem order_sat {c : Expr} (hc : c ∈ orderC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem fbool {c : ℕ} (hc : c = FST ∨ c = DBL ∨ c = NILS) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have hm : boolC (k c) ∈ flagC := by rcases hc with rfl | rfl | rfl <;> simp [flagC]
  have := flag_sat hsat hm hr
  simp only [boolC, Expr.eval, k, Sha256.eval_col, Sha256.eval_cst, wrap_zero hr, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem row0_at {q : ℕ} (hr : 72 * q < n) : (pre ROW0).eval n preCols pub M (72 * q) = 1 := by
  rw [eval_per72 hsat (i := ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hr]; simp

/-- What a period start says about the previous period. -/
theorem prev_facts {q : ℕ} (hq : 1 ≤ q) (hn : 72 * q + 72 ≤ n) :
    (M CHN (72 * q) = 1 → M MID (72 * q) = M MID (72 * (q - 1)) ∧
      M BLKI (72 * q) = M BLKI (72 * (q - 1)) + 1 ∧ M DBL (72 * (q - 1)) + M NILS (72 * (q - 1)) = 0 ∧
      M NODE (72 * (q - 1)) + M NPAD (72 * (q - 1)) = 0) ∧
    (M DBL (72 * q) = 1 → M MID (72 * q) = M MID (72 * (q - 1)) ∧
      M DBL (72 * (q - 1)) + M NILS (72 * (q - 1)) = 0) := by
  have hr : 72 * q < n := by omega
  have r0 := row0_at hsat hr
  have hw : wrap n (72 * q) (-1) = 72 * (q - 1) + 71 := by
    rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, Sha256.wrap_back (by omega) hr]; omega
  have pc := fun (X : ℕ) (hX : X ∈ [MID, BLKI, FST, DBL, NILS, NODE, NPAD, LID, RID, NDUP]) =>
    per_const hsat hX (s := 72 * (q - 1)) (by omega) 71 (by norm_num) (by omega)
  have e := fun (c : Expr) (h : c ∈ orderC) => order_sat hsat h hr
  have ev : ∀ X, (kp X).eval n preCols pub M (72 * q) = M X (72 * (q - 1) + 71) := fun X => by
    simp [kp, Sha256.eval_col, hw]
  refine ⟨fun hc => ⟨?_, ?_, ?_, ?_⟩, fun hd => ⟨?_, ?_⟩⟩
  · have := e _ (show Expr.mul (pre ROW0) (.mul (k CHN) (.sub (k MID) (kp MID))) ∈ orderC by simp [orderC])
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hc, ev, pc MID (by simp)] at this
    exact sub_eq_zero.mp this
  · have := e _ (show Expr.mul (pre ROW0) (.mul (k CHN) (.sub (.sub (k BLKI) (kp BLKI)) one)) ∈ orderC by simp [orderC])
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hc, ev, pc BLKI (by simp), one,
      Sha256.eval_cst, Nat.cast_one] at this
    linear_combination this
  · have := e _ (show Expr.mul (pre ROW0) (.mul (k CHN) (.add (kp DBL) (kp NILS))) ∈ orderC by simp [orderC])
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hc, ev, pc DBL (by simp), pc NILS (by simp)] at this
    exact this
  · have hm : Expr.mul (pre ROW0) (.mul (k CHN) (.add (kp NODE) (kp NPAD))) ∈ nodeOrderC := by simp [nodeOrderC]
    have := hsat _ hr (Expr.mul (pre ROW0) (.mul (k CHN) (.add (kp NODE) (kp NPAD))))
      (by simp only [constraints, List.mem_append]; tauto)
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hc, ev, pc NODE (by simp), pc NPAD (by simp)] at this
    exact this
  · have := e _ (show Expr.mul (pre ROW0) (.mul (k DBL) (.sub (k MID) (kp MID))) ∈ orderC by simp [orderC])
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hd, ev, pc MID (by simp)] at this
    exact sub_eq_zero.mp this
  · have := e _ (show Expr.mul (pre ROW0) (.mul (k DBL) (.add (kp DBL) (kp NILS))) ∈ orderC by simp [orderC])
    simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hd, ev, pc DBL (by simp), pc NILS (by simp)] at this
    exact this

theorem not_dn {r : ℕ} (hr : r < n) (h : M DBL r + M NILS r = 0) : M DBL r = 0 ∧ M NILS r = 0 := by
  rcases fbool hsat (c := DBL) (by simp) hr with a | a <;> rcases fbool hsat (c := NILS) (by simp) hr with b | b <;>
    rw [a, b] at h <;> simp_all
  exact absurd h one_add_one_ne

theorem not_np {r : ℕ} (hr : r < n) (h : M NODE r + M NPAD r = 0) : M NODE r = 0 ∧ M NPAD r = 0 := by
  rcases kbool hsat (c := NODE) (by simp) hr with a | a <;> rcases kbool hsat (c := NPAD) (by simp) hr with b | b <;>
    rw [a, b] at h <;> simp_all
  exact absurd h one_add_one_ne

theorem fst_or_chn {r : ℕ} (hr : r < n) (hd : M DBL r = 0) (hn : M NILS r = 0) (ho : M NODE r = 0)
    (hp : M NPAD r = 0) : M FST r = 1 ∨ M CHN r = 1 := by
  rcases fbool hsat (c := FST) (by simp) hr with a | a
  · right; rw [chn_eq hsat hr, a, hd, hn, ho, hp]; ring
  · left; exact a

/-- **Back to the first block.** From a period that is a first block or a continuation, the walk
back through continuations reaches its message's first block; message id constant, block indices
counting from 0. -/
theorem walk : ∀ q, 72 * q + 72 ≤ n → (M FST (72 * q) = 1 ∨ M CHN (72 * q) = 1) →
    ∃ q0 ≤ q, M FST (72 * q0) = 1 ∧ (∀ j, q0 < j → j ≤ q → M CHN (72 * j) = 1) ∧
      (∀ j, q0 ≤ j → j ≤ q → M MID (72 * j) = M MID (72 * q) ∧ M BLKI (72 * j) = ((j - q0 : ℕ) : F)) := by
  intro q
  induction q with
  | zero =>
    intro hn h
    have hr : 72 * 0 < n := by omega
    have hf : M FST 0 = 1 := by
      rcases h with h | h
      · exact h
      · exfalso
        have := order_sat hsat (c := .mul (pre FIRST) (.add (k CHN) (k DBL))) (by simp [orderC]) (show 0 < n by omega)
        have hfirst : (pre FIRST).eval n preCols pub M 0 = 1 := by
          simp only [pre, Expr.eval, wrap_zero (show 0 < n by omega)]
          rw [show preCols.getD FIRST (.periodic [0]) = .isFirst from rfl]; simp [PreCol.eval]
        simp only [Expr.eval, hfirst, one_mul, k, Sha256.eval_col, wrap_zero (show 0 < n by omega)] at this
        simp only [Nat.mul_zero] at h
        have hc := chn_eq hsat (show 0 < n by omega)
        rw [h] at this hc
        rcases fbool hsat (c := DBL) (by simp) (show 0 < n by omega) with d | d
        · rw [d] at this; simp at this
        · rw [d] at hc this; exact one_add_one_ne this
    refine ⟨0, le_rfl, by simpa using hf, fun j h1 h2 => by omega, fun j h1 h2 => ?_⟩
    obtain rfl : j = 0 := by omega
    refine ⟨rfl, ?_⟩
    have := order_sat hsat (c := .mul (k FST) (k BLKI)) (by simp [orderC]) (show 0 < n by omega)
    simp only [Expr.eval, k, Sha256.eval_col, wrap_zero (show 0 < n by omega), hf, one_mul] at this
    simpa using this
  | succ q ih =>
    intro hn h
    have hr : 72 * (q + 1) < n := by omega
    rcases fbool hsat (c := FST) (by simp) hr with hf | hf
    · -- A continuation: step back.
      have hc : M CHN (72 * (q + 1)) = 1 := by rcases h with h | h; rw [hf] at h; exact absurd h zero_ne_one; exact h
      obtain ⟨hm, hb, hdn, hnp⟩ := (prev_facts hsat (q := q + 1) (by omega) (by omega)).1 hc
      simp only [Nat.add_sub_cancel] at hm hb hdn hnp
      obtain ⟨hd, hnl⟩ := not_dn hsat (by omega) hdn
      obtain ⟨ho, hp⟩ := not_np hsat (by omega) hnp
      obtain ⟨q0, hq0, f0, c0, v0⟩ := ih (by omega) (fst_or_chn hsat (by omega) hd hnl ho hp)
      refine ⟨q0, by omega, f0, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge j (q + 1) with hj | hj
        · exact c0 j h1 (by omega)
        · obtain rfl : j = q + 1 := by omega
          exact hc
      · rcases Nat.lt_or_ge j (q + 1) with hj | hj
        · obtain ⟨a, b⟩ := v0 j h1 (by omega); exact ⟨a.trans hm.symm, b⟩
        · obtain rfl : j = q + 1 := by omega
          refine ⟨rfl, ?_⟩
          rw [hb, (v0 q hq0 le_rfl).2, show q + 1 - q0 = (q - q0) + 1 by omega]
          push_cast; ring
    · -- A first block.
      refine ⟨q + 1, le_rfl, hf, fun j h1 h2 => by omega, fun j h1 h2 => ?_⟩
      obtain rfl : j = q + 1 := by omega
      refine ⟨rfl, ?_⟩
      have := order_sat hsat (c := .mul (k FST) (k BLKI)) (by simp [orderC]) hr
      simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr, hf, one_mul] at this
      simpa using this

/-- A node's padding block follows its first block, with the same id. -/
theorem npad_prev {q : ℕ} (hn : 72 * q + 72 ≤ n) (hp : M NPAD (72 * q) = 1) :
    1 ≤ q ∧ M NODE (72 * (q - 1)) = 1 ∧ M MID (72 * (q - 1)) = M MID (72 * q) := by
  have hr : 72 * q < n := by omega
  have hq : 1 ≤ q := by
    by_contra h
    have e : q = 0 := by omega
    subst e
    have := hsat _ hr (Expr.mul (pre FIRST) (k NPAD)) (by
      have hm : Expr.mul (pre FIRST) (k NPAD) ∈ nodeOrderC := by simp [nodeOrderC]
      simp only [constraints, List.mem_append]; tauto)
    have hfirst : (pre FIRST).eval n preCols pub M 0 = 1 := by
      simp only [pre, Expr.eval, wrap_zero (show 0 < n by omega)]
      rw [show preCols.getD FIRST (.periodic [0]) = .isFirst from rfl]; simp [PreCol.eval]
    simp only [Nat.mul_zero] at this hp
    simp only [Expr.eval, hfirst, one_mul, k, Sha256.eval_col, wrap_zero (show 0 < n by omega), hp] at this
    exact one_ne_zero this
  have r0 := row0_at hsat hr
  have hw : wrap n (72 * q) (-1) = 72 * (q - 1) + 71 := by
    rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, Sha256.wrap_back (by omega) hr]; omega
  have pc := fun (X : ℕ) (hX : X ∈ [MID, BLKI, FST, DBL, NILS, NODE, NPAD, LID, RID, NDUP]) =>
    per_const hsat hX (s := 72 * (q - 1)) (by omega) 71 (by norm_num) (by omega)
  have ev : ∀ X, (kp X).eval n preCols pub M (72 * q) = M X (72 * (q - 1) + 71) := fun X => by
    simp [kp, Sha256.eval_col, hw]
  have e := fun (c : Expr) (h : c ∈ nodeOrderC) =>
    hsat _ hr c (by simp only [constraints, List.mem_append]; tauto)
  have h1 := e (.mul (pre ROW0) (.mul (k NPAD) (.sub (k MID) (kp MID)))) (by simp [nodeOrderC])
  have h2 := e (.mul (pre ROW0) (.mul (k NPAD) (om (kp NODE)))) (by simp [nodeOrderC])
  simp only [Expr.eval, r0, one_mul, k, Sha256.eval_col, wrap_zero hr, hp, ev, pc MID (by simp), pc NODE (by simp),
    om, one, Sha256.eval_cst, Nat.cast_one] at h1 h2
  exact ⟨hq, (sub_eq_zero.mp h2).symm, (sub_eq_zero.mp h1).symm⟩

/-- **The SHA component's digest.** A second-hash period `q` hashes the digest of its message's
blocks: periods `q0 … q − 1` (`b = q − q0 ≥ 1` blocks, the first a first block, the rest
continuations, all with the same id), and its output is
`compress IV (dblBlock (fold over those blocks))`, i.e. SHA256d of the blocks' words. -/
theorem digest_sound {q : ℕ} (hq : 1 ≤ q) (hn : 72 * q + 72 ≤ n) (hd : M DBL (72 * q) = 1)
    (hpo : M NODE (72 * (q - 1)) = 0) (hpp : M NPAD (72 * (q - 1)) = 0) :
    ∃ q0 < q, M FST (72 * q0) = 1 ∧ (∀ j, q0 < j → j < q → M CHN (72 * j) = 1) ∧
      (∀ j, q0 ≤ j → j < q → M MID (72 * j) = M MID (72 * q) ∧ M BLKI (72 * j) = ((j - q0 : ℕ) : F)) ∧
      outputAt M (72 * q) =
        Spec.Sha256.compress Spec.Sha256.IV (dblBlock (fold M (72 * q0) (q - q0))) := by
  obtain ⟨hm, hdn⟩ := (prev_facts hsat hq hn).2 hd
  obtain ⟨hpd, hpn⟩ := not_dn hsat (by omega) hdn
  obtain ⟨q0, hq0, f0, c0, v0⟩ := walk hsat (q - 1) (by omega) (fst_or_chn hsat (by omega) hpd hpn hpo hpp)
  refine ⟨q0, by omega, f0, fun j h1 h2 => c0 j h1 (by omega),
    fun j h1 h2 => ⟨(v0 j h1 (by omega)).1.trans hm.symm, (v0 j h1 (by omega)).2⟩, ?_⟩
  have hb := chain_out hsat (s0 := 72 * q0) (b := q - q0) (by omega) (by omega) f0
    (fun j h1 h2 => by rw [show 72 * q0 + 72 * j = 72 * (q0 + j) by ring]; exact c0 _ (by omega) (by omega))
    (q - q0) (by omega) le_rfl
  rw [dbl_out hsat (by omega) (by omega) hn hd, show 72 * q - 72 = 72 * q0 + 72 * (q - q0 - 1) by omega, hb]

theorem npad_sat {c : Expr} (hc : c ∈ npadC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

/-- **A node's padding block** is the constant padding of a 64-byte message. -/
theorem npad_message {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) (h : M NPAD s = 1) :
    ∀ t < 16, messageAt M s t = BitVec.ofNat 32 (npadWord t) := by
  intro t ht
  have hr : s + 4 + t < n := by omega
  have hd : M NPAD (s + 4 + t) = 1 := by
    rw [show s + 4 + t = s + (4 + t) by ring, per_const hsat (X := NPAD) (by simp) hs (4 + t) (by omega) (by omega), h]
  have ev := fun (i : ℕ) (f : ℕ → ℕ) (hi : preCols.getD i (.periodic [0]) = per72 f) => eval_per72 hsat hi hr
  have hq : (s + 4 + t) % 72 = 4 + t := by omega
  have hsel : (Expr.mul (k NPAD) (pre MSGROW)).eval n preCols pub M (s + 4 + t) = 1 := by
    simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr, hd, one_mul]
    rw [ev MSGROW (fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) rfl, hq]; simp; omega
  simp only [messageAt]
  refine HeaderChain.eqLimbs_word _ (fun c hc => npad_sat hsat (by simpa [npadC] using hc) hr)
    hsel (wrap_zero hr) (wbits hsat hr) (fun hh hhh => ?_)
  have hlt : npadWord t < 2 ^ 32 := by unfold npadWord; split_ifs <;> norm_num
  interval_cases hh
  · rw [ev (NP_LO + 0) (fun q => if 4 ≤ q ∧ q < 20 then npadWord (q - 4) % 2 ^ 16 else 0) rfl, hq,
      if_pos (by omega), show 4 + t - 4 = t by omega, HeaderChain.half16_ofNat hlt 0 (by norm_num)]; simp
  · rw [ev (NP_LO + 1) (fun q => if 4 ≤ q ∧ q < 20 then npadWord (q - 4) / 2 ^ 16 else 0) rfl, hq,
      if_pos (by omega), show 4 + t - 4 = t by omega, HeaderChain.half16_ofNat hlt 1 (by norm_num)]; simp

/-- The padding block of a 64-byte message, as words. -/
def npadBlock (t : ℕ) : Spec.Sha256.Word := BitVec.ofNat 32 (npadWord t)

/-- **A node's digest.** A second hash at period `q` after a padding block (period `q − 1`) after a node
block (period `q − 2`): SHA256d of the node block's 16 words. -/
theorem node_out {q : ℕ} (hq : 2 ≤ q) (hn : 72 * q + 72 ≤ n) (hd : M DBL (72 * q) = 1)
    (hp : M NPAD (72 * (q - 1)) = 1) (ho : M NODE (72 * (q - 2)) = 1) :
    outputAt M (72 * q) = Spec.Sha256.compress Spec.Sha256.IV (dblBlock
      (Spec.Sha256.compress (Spec.Sha256.compress Spec.Sha256.IV (messageAt M (72 * (q - 2)))) npadBlock)) := by
  have s2 : (72 * (q - 2)) % 72 = 0 := by omega
  have s1 : (72 * (q - 1)) % 72 = 0 := by omega
  -- the node block starts from the IV
  have hf0 : M FST (72 * (q - 2)) = 0 := by
    have := (kinds_excl hsat (show 72 * (q - 2) < n by omega)).2.2.2.1; rw [ho, one_mul] at this; exact this
  have hd0 : M DBL (72 * (q - 2)) = 0 := by
    have := (kinds_excl hsat (show 72 * (q - 2) < n by omega)).2.2.2.2.1; rw [ho, one_mul] at this; exact this
  have o2 : outputAt M (72 * (q - 2)) = Spec.Sha256.compress Spec.Sha256.IV (messageAt M (72 * (q - 2))) := by
    rw [← period_compress hsat s2 (by omega), input_iv hsat s2 (by omega) (by rw [hf0, hd0, ho]; ring)]
  -- the padding block continues it
  have hc0 : M CHN (72 * (q - 1)) = 0 := by
    have hr : 72 * (q - 1) < n := by omega
    obtain ⟨-, -, -, -, -, -, -, e8, e9, e10⟩ := kinds_excl hsat hr
    rw [hp, one_mul] at e8 e9 e10
    have e7 := (kinds_excl hsat hr).2.2.2.2.2.2.1
    rw [hp, mul_one] at e7
    rw [chn_eq hsat hr, e8, e9, e10, e7, hp]; ring
  have o1 : outputAt M (72 * (q - 1)) = Spec.Sha256.compress (outputAt M (72 * (q - 2))) npadBlock := by
    rw [← period_compress hsat s1 (by omega), input_chain' hsat s1 (by omega) (by omega) (by rw [hc0, hp]; ring),
      show 72 * (q - 1) - 72 = 72 * (q - 2) by omega]
    exact HeaderChain.compress_congr _ (fun t ht => npad_message hsat s1 (by omega) hp t ht)
  rw [dbl_out hsat (by omega) (by omega) hn hd, show 72 * q - 72 = 72 * (q - 1) by omega, o1, o2]

theorem mut_sat {c : Expr} (hc : c ∈ mutC) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

/-- **The mutation check.** A node block that does not duplicate its child has two different halves. -/
theorem node_distinct {s : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ n) (ho : M NODE s = 1) (hd : M NDUP s = 0) :
    ∃ t < 8, messageAt M s t ≠ messageAt M s (t + 8) := by
  by_contra hne
  push Not at hne
  -- every compared limb pair is equal, so each is-zero flag is 1
  have flags : ∀ t < 8, M ZZ (s + 12 + t) = 1 := by
    intro t ht
    have hr : s + 12 + t < n := by omega
    have dl : ∀ h ≤ 1, (dLimb h).eval n preCols pub M (s + 12 + t) = 0 := by
      intro h hh
      simp only [dLimb, Expr.eval]
      rw [show (-8 : ℤ) = -((8 : ℕ) : ℤ) by simp, Sha256.limbs_back (sha_sat hsat) hr (by omega) (by simp [Sha256.W]) hh,
        show (0 : ℤ) = -((0 : ℕ) : ℤ) by simp, Sha256.limbs_back (sha_sat hsat) hr (by omega) (by simp [Sha256.W]) hh]
      have e := hne t ht
      simp only [messageAt] at e
      rw [show s + 12 + t - 0 = s + 4 + (t + 8) by omega, show s + 12 + t - 8 = s + 4 + t by omega, e, sub_self]
    have zf : ∀ (Z IV : ℕ) (h : ℕ), h ≤ 1 →
        Expr.mul (om (k Z)) (.sub (.mul (dLimb h) (k IV)) one) ∈ mutC → M Z (s + 12 + t) = 1 := by
      intro Z IV h hh hm
      have := mut_sat hsat hm hr
      simp only [Expr.eval, om, one, Sha256.eval_cst, k, Sha256.eval_col, wrap_zero hr, dl h hh, zero_mul, zero_sub,
        Nat.cast_one, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at this
      exact this.symm
    have zl := zf ZL IL 0 (by norm_num) (by simp [mutC])
    have zh := zf ZH IH 1 (by norm_num) (by simp [mutC])
    have := mut_sat hsat (c := .sub (k ZZ) (.mul (k ZL) (k ZH))) (by simp [mutC]) hr
    simp only [Expr.eval, k, Sha256.eval_col, wrap_zero hr, zl, zh, mul_one, sub_eq_zero] at this
    exact this
  -- so `ALLEQ` is 1 through row 19
  have alleq : ∀ t < 8, M ALLEQ (s + 12 + t) = 1 := by
    intro t ht
    induction t with
    | zero =>
      have hr : s + 12 < n := by omega
      have := mut_sat hsat (c := .mul (pre CMPF) (.sub (k ALLEQ) (k ZZ))) (by simp [mutC]) hr
      rw [show Expr.eval n preCols pub M (s + 12) (.mul (pre CMPF) (.sub (k ALLEQ) (k ZZ))) =
        (pre CMPF).eval n preCols pub M (s + 12) * (M ALLEQ (s + 12) - M ZZ (s + 12)) by
          simp [Expr.eval, k, Sha256.eval_col, wrap_zero hr],
        eval_per72 hsat (i := CMPF) (f := fun q => if q = 12 then 1 else 0) rfl hr,
        show (s + 12) % 72 = 12 by omega] at this
      have z := flags 0 (by norm_num)
      simp only [Nat.add_zero] at z ⊢
      simp only [if_true, Nat.cast_one, one_mul, sub_eq_zero, z] at this; exact this
    | succ t ih =>
      have hr : s + 12 + t + 1 < n := by omega
      have := mut_sat hsat (c := .mul (pre CMPR) (.sub (k ALLEQ) (.mul (kp ALLEQ) (k ZZ)))) (by simp [mutC]) hr
      rw [show Expr.eval n preCols pub M (s + 12 + t + 1) (.mul (pre CMPR) (.sub (k ALLEQ) (.mul (kp ALLEQ) (k ZZ)))) =
        (pre CMPR).eval n preCols pub M (s + 12 + t + 1) *
          (M ALLEQ (s + 12 + t + 1) - M ALLEQ (s + 12 + t) * M ZZ (s + 12 + t + 1)) by
          simp only [Expr.eval, k, kp, Sha256.eval_col, wrap_zero hr]
          rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, Sha256.wrap_back (by omega) hr]; rfl,
        eval_per72 hsat (i := CMPR) (f := fun q => if 13 ≤ q ∧ q < 20 then 1 else 0) rfl hr,
        show (s + 12 + t + 1) % 72 = 13 + t by omega] at this
      have z := flags (t + 1) ht
      rw [show s + 12 + (t + 1) = s + 12 + t + 1 by ring] at z ⊢
      rw [if_pos (by omega), Nat.cast_one, one_mul, ih (by omega), z, one_mul, sub_eq_zero] at this
      exact this
  -- row 19 forbids it
  have hr : s + 19 < n := by omega
  have := mut_sat hsat (c := .mul (pre DRR) (.mul (k NNE) (k ALLEQ))) (by simp [mutC]) hr
  have hnne : M NNE (s + 19) = 1 := by
    have e := nflag_sat hsat (c := .sub (k NNE) (.mul (k NODE) (om (k NDUP)))) (by simp [nodeFlagC]) hr
    simp only [Expr.eval, k, om, one, Sha256.eval_col, Sha256.eval_cst, wrap_zero hr, Nat.cast_one, sub_eq_zero] at e
    rw [e, show s + 19 = s + 19 by rfl, per_const hsat (X := NODE) (by simp) hs 19 (by norm_num) hr,
      per_const hsat (X := NDUP) (by simp) hs 19 (by norm_num) hr, ho, hd]; ring
  have a19 := alleq 7 (by norm_num)
  rw [show s + 12 + 7 = s + 19 by ring] at a19
  rw [show Expr.eval n preCols pub M (s + 19) (.mul (pre DRR) (.mul (k NNE) (k ALLEQ))) =
    (pre DRR).eval n preCols pub M (s + 19) * (M NNE (s + 19) * M ALLEQ (s + 19)) by
      simp [Expr.eval, k, Sha256.eval_col, wrap_zero hr],
    eval_per72 hsat (i := DRR) (f := fun q => if q = 19 then 1 else 0) rfl hr, show (s + 19) % 72 = 19 by omega,
    hnne, a19] at this
  simp at this

/-- **The digest tuple** at a second hash's last row is the output state's words, 16-bit limbs. -/
theorem digest_tuple {s : ℕ} (hsn : s + 72 ≤ n) {j : ℕ} (hj : j < 16) :
    (digestLimbs.getD j (cst 0)).eval n preCols pub M (s + 71) =
      ((Sha256.half16 (Spec.Bitcoin.stateWord (outputAt M s) (j / 2)) (j % 2) : ℕ) : F) := by
  have hr : s + 71 < n := by omega
  have hw : j / 2 < 8 := by omega
  have hh : j % 2 ≤ 1 := by omega
  simp only [digestLimbs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, outputAt]
  rw [HeaderChain.stAt_word _ _ hw]
  split_ifs with h4
  · rw [Sha256.limbs_back (sha_sat hsat) hr (by omega) (by simp [Sha256.A]) hh]
  · rw [Sha256.limbs_back (sha_sat hsat) hr (by omega) (by simp [Sha256.E]) hh]

/-- **A node block's word tuples** (rows 11 and 19): message words `0..7` and `8..15`, limbs. -/
theorem node_tuple {s : ℕ} (hsn : s + 72 ≤ n) {j : ℕ} (hj : j < 16) (half : ℕ) (hhalf : half ≤ 1) :
    (nodeWordLimbs.getD j (cst 0)).eval n preCols pub M (s + 11 + 8 * half) =
      ((Sha256.half16 (messageAt M s (8 * half + j / 2)) (j % 2) : ℕ) : F) := by
  have hr : s + 11 + 8 * half < n := by omega
  have hh : j % 2 ≤ 1 := by omega
  simp only [nodeWordLimbs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some, messageAt]
  rw [show (((j / 2 : ℕ) : ℤ) - 7) = -((7 - j / 2 : ℕ) : ℤ) by omega,
    Sha256.limbs_back (sha_sat hsat) hr (by omega) (by simp [Sha256.W]) hh,
    show s + 11 + 8 * half - (7 - j / 2) = s + 4 + (8 * half + j / 2) by omega]

end Period

end StarkedAir.Block.Sha
