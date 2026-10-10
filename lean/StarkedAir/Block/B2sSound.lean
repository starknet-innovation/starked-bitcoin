/-
**Block Blake2s soundness, per period (M3a.6).** In a satisfied `block_b2s` trace, every aligned period
computes the Blake2s compression of its chaining value, message words, counter and flag
(`period_compress`, from the gadget's `compress_sound`); a first block's chaining value is `h0`; a
continuing period's is the previous period's output; the counter and flag are `T` and `LASTF`; the
message limbs are the words read at rows 0–15.
-/
import StarkedAir.Block.B2Bridge

namespace StarkedAir.Block.B2s

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back word bit eq_bit word_getLsbD)
open StarkedAir.Blake2s (BlakeSat diagSlot msgWord inT fBit outWord rw4 compress_sound P_INIT P_FIN)

theorem preCols_assoc : preCols = Blake2s.preCols ++
    ([ .rowLt 8, per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
      per88 (fun r => if r < 16 then r else 0) ] ++
    (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))) := by
  simp [preCols, List.append_assoc]

theorem gadget_len : Blake2s.preCols.length = 50 := by simp [Blake2s.preCols]

/-- A gadget constraint evaluates the same with the block component's preprocessed columns. -/
theorem eval_gadget {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r : ℕ} {c : Expr} (hc : c ∈ Blake2s.constraints) :
    c.eval n preCols pub M r = c.eval n Blake2s.preCols pub M r := by
  rw [preCols_assoc]
  apply Expr.eval_pre_append
  rw [gadget_len]
  exact List.all_eq_true.mp gadget_pre c hc

theorem eval_pre_gadget {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r i : ℕ} (hi : i < 50) :
    (pre i).eval n preCols pub M r = (pre i).eval n Blake2s.preCols pub M r := by
  rw [preCols_assoc]
  apply Expr.eval_pre_append
  simp [pre, Expr.preBelow, gadget_len, hi]

theorem word_of_vals {M : ℕ → ℕ → F} {w r : ℕ} {Y : Spec.Blake2s.Word}
    (hbits : ∀ i < 32, (M (32 * w + i) r).val ≤ 1)
    (h : ∀ i < 32, M (32 * w + i) r = ((Y.getLsbD i).toNat : F)) : word M (32 * w) r = Y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc := h i hi
  rw [eq_bit (hbits i hi)] at hc
  rw [word_getLsbD _ _ hi]
  have := congrArg ZMod.val hc
  cases hb : bit M (32 * w + i) r <;> cases hy : Y.getLsbD i <;> simp_all

section Period

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem gadget_sat : BlakeSat n Blake2s.preCols pub M := fun r hr c hc => by
  rw [← eval_gadget hc]
  exact hsat r hr c (by simp only [constraints, List.mem_append]; tauto)

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_per88 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per88 f) {r : ℕ} (hr : r < n) :
    (pre i).eval n preCols pub M r = ((f (r % 88) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 88 < 88 := Nat.mod_lt _ (by norm_num)
  simp [per88, PreCol.eval, Blake2s.PERIOD, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_out8 {r : ℕ} (hr : r < n) : (p P_OUT8).eval n preCols pub M r = if r < 8 then 1 else 0 := by
  simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_OUT8, PreCol.eval, List.getD_append, Blake2s.preCols]

omit hsat in
theorem ev_r0 {r : ℕ} (hr : r < n) : (p P_R0).eval n preCols pub M r = if r % 88 = 0 then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r = 0 then 1 else 0) (by simp [preCols, P_R0, Blake2s.preCols]) hr]
  split_ifs <;> simp

omit hsat in
theorem ev_lt16 {r : ℕ} (hr : r < n) : (p P_LT16).eval n preCols pub M r = if r % 88 < 16 then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r < 16 then 1 else 0) (by simp [preCols, P_LT16, Blake2s.preCols]) hr]
  split_ifs <;> simp

omit hsat in
theorem ev_rk {j r : ℕ} (hj : j < 16) (hr : r < n) :
    (p (P_RK j)).eval n preCols pub M r = if r % 88 = j then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r = j then 1 else 0) (by
    rw [preCols_assoc, P_RK, List.getD_append_right _ _ _ _ (by rw [gadget_len]; omega), gadget_len,
      List.getD_append_right _ _ _ _ (by simp; omega), List.length_cons, List.length_cons, List.length_cons,
      List.length_cons, List.length_nil, show 54 + j - 50 - (0 + 1 + 1 + 1 + 1) = j by omega]
    simp [List.getD_eq_getElem?_getD, hj]) hr]
  split_ifs <;> simp

end Period

section Period2

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem mem_flag {c : Expr} (h : c ∈ flagC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_chain {c : Expr} (h : c ∈ chainC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_init {c : Expr} (h : c ∈ initC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_tf {c : Expr} (h : c ∈ tfC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_word {c : Expr} (h : c ∈ wordC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

theorem bool_flag {c : ℕ} (hc : c ∈ [FST, NIL, LASTF, MU0, MU1]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (mem_flag (c := boolC (k c)) (by
    simp only [flagC, List.mem_append, List.mem_map]; left; left; exact ⟨c, hc, rfl⟩)) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ flagC) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat (mem_flag h) hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

/-- Per-period values are constant down the period. -/
theorem per_const {X : ℕ} (hX : X ∈ perConst) {s : ℕ} (hs : s % 88 = 0) :
    ∀ q < 88, s + q < n → M X (s + q) = M X s := by
  intro q
  induction q with
  | zero => intro _ _; rfl
  | succ q ih =>
    intro hq hr
    have := sat hsat (mem_flag (c := .mul (om (p P_R0)) (.sub (k X) (kp X)))
      (by simp only [flagC, List.mem_append, List.mem_map]; right; exact ⟨X, hX, rfl⟩)) hr
    rw [show s + (q + 1) = s + q + 1 by ring] at this hr ⊢
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_r0 hr, ev_k hr, ev_kp hr,
      show ¬ ((s + q + 1) % 88 = 0) by omega, if_false, sub_zero, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega) (by omega)]

/-- **Each aligned period computes the Blake2s compression.** -/
theorem period_compress {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n)
    (hm : ∀ kk < 16, ∀ h ≤ 1, (M (Blake2s.ML kk h) s).val < 65536) :
    ∀ i < 8, Spec.Blake2s.compress (diagSlot M s) (fun kk => msgWord M kk s) (inT M s) (fBit M s) i = outWord M s i :=
  Blake2s.compress_sound (gadget_sat hsat) hs hsn hm

theorem pre_init {s j q : ℕ} (hs : s % 88 = 0) (hj : j < 4) (hq : q < 88) (hr : s + q < n) :
    (p (P_INIT j)).eval n preCols pub M (s + q) = if q = j then 1 else 0 := by
  rw [p, eval_pre_gadget (by simp [P_INIT]; omega), Blake2s.pre_at hs hq hr (by simp [P_INIT]; omega),
    Blake2s.bPre_INIT hj hq]

omit hsat in
theorem h0_bits (i b : ℕ) : ((h0Bit i b : ℕ) : F) = (((Spec.Blake2s.h0 i).getLsbD b).toNat : F) := by
  unfold h0Bit h0
  rw [BitVec.getLsbD, Nat.testBit]
  split_ifs with h <;> simp_all [Nat.testBit]

theorem bits4 {r : ℕ} (hr : r < n) (w : ℕ) (hw : w < 8) : ∀ i < 32, (M (32 * w + i) r).val ≤ 1 :=
  Blake2s.word_bits (gadget_sat hsat) hr hw

/-- **A first block starts from `h0`.** -/
theorem h_first {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n)
    (hf : M FST s ≠ 0) : ∀ i < 8, diagSlot M s i = Spec.Blake2s.h0 i := by
  have row : ∀ j < 4, rw4 M (s + j) 0 = Spec.Blake2s.h0 j ∧ rw4 M (s + j) 1 = Spec.Blake2s.h0 (bidx j) := by
    intro j hj
    have hr : s + j < n := by omega
    have hfj : M FST (s + j) ≠ 0 := by
      rw [per_const hsat (X := FST) (by simp [perConst]) hs j (by omega) hr]; exact hf
    have key : ∀ (w : ℕ) (hw : w < 8) (idx : ℕ), (∀ b < 32, Expr.mul (k FST) (.mul (p (P_INIT j))
        (.sub (k (Blake2s.WB w b)) (cst (h0Bit idx b)))) ∈ initC) → word M (32 * w) (s + j) = Spec.Blake2s.h0 idx := by
      intro w hw idx hmem
      apply word_of_vals (bits4 hsat hr w hw)
      intro b hb
      have := sat hsat (mem_init (hmem b hb)) hr
      simp only [Expr.eval, ev_k hr, pre_init hsat hs hj (by omega) hr, eq_self_iff_true, if_true, one_mul, eval_cst] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hfj
      rw [sub_eq_zero] at h
      have this := h
      rw [show Blake2s.WB w b = 32 * w + b from rfl] at this
      rw [this, h0_bits]
    have mem : ∀ b < 32, ∀ e ∈ [Expr.mul (k FST) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 0) b)) (cst (h0Bit j b)))),
        Expr.mul (k FST) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 1) b)) (cst (h0Bit (bidx j) b))))],
        e ∈ initC := by
      intro b hb e he
      simp only [initC, List.mem_flatMap, List.mem_range]
      exact ⟨j, hj, b, hb, by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; tauto⟩
    exact ⟨key 4 (by norm_num) j (fun b hb => mem b hb _ (by simp [Blake2s.outW])),
      key 7 (by norm_num) (bidx j) (fun b hb => mem b hb _ (by simp [Blake2s.outW]))⟩
  intro i hi
  obtain ⟨a0, b0⟩ := row 0 (by norm_num); obtain ⟨a1, b1⟩ := row 1 (by norm_num)
  obtain ⟨a2, b2⟩ := row 2 (by norm_num); obtain ⟨a3, b3⟩ := row 3 (by norm_num)
  interval_cases i <;> simp_all [diagSlot, bidx]

/-- **A continuing period chains**: its chaining value is the previous period's output. -/
theorem h_chain {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (h88 : 88 ≤ s) (hc : M CHN s = 1) :
    ∀ i < 8, diagSlot M s i = outWord M (s - 88) i := by
  have row : ∀ j < 4, rw4 M (s + j) 0 = outWord M (s - 88) j ∧ rw4 M (s + j) 1 = outWord M (s - 88) (bidx j) := by
    intro j hj
    have hr : s + j < n := by omega
    have hcj : M CHN (s + j) = 1 := by
      have e := defn hsat (a := CHN) (e := om (.add (k FST) (k NIL))) (by simp [flagC]) hr
      have e0 := defn hsat (a := CHN) (e := om (.add (k FST) (k NIL))) (by simp [flagC]) (show s < n by omega)
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr] at e
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k (show s < n by omega)] at e0
      rw [e, per_const hsat (X := FST) (by simp [perConst]) hs j (by omega) hr,
        per_const hsat (X := NIL) (by simp [perConst]) hs j (by omega) hr, ← e0, hc]
    have hwr : wrap n (s + j) (-4) = s - 88 + 84 + j := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; omega
    have key : ∀ (w : ℕ) (hw : w < 8) (w' : ℕ), w' < 8 → (∀ b < 32, Expr.mul (k CHN) (.mul (p (P_INIT j))
        (.sub (k (Blake2s.WB w b)) (col (Blake2s.WB w' b) (-4)))) ∈ initC) →
        word M (32 * w) (s + j) = word M (32 * w') (s - 88 + 84 + j) := by
      intro w hw w' hw' hmem
      apply word_of_vals (bits4 hsat hr w hw)
      intro b hb
      have := sat hsat (mem_init (hmem b hb)) hr
      simp only [Expr.eval, ev_k hr, pre_init hsat hs hj (by omega) hr, eq_self_iff_true, if_true, one_mul, hcj, eval_col, hwr,
        sub_eq_zero] at this
      rw [show Blake2s.WB w b = 32 * w + b from rfl, show Blake2s.WB w' b = 32 * w' + b from rfl] at this
      rw [this, eq_bit (bits4 hsat (show s - 88 + 84 + j < n by omega) w' hw' b hb), word_getLsbD _ _ hb]
    have mem : ∀ b < 32, ∀ e ∈ [Expr.mul (k CHN) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 0) b)) (col (Blake2s.WB 0 b) (-4)))),
        Expr.mul (k CHN) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 1) b)) (col (Blake2s.WB 1 b) (-4))))],
        e ∈ initC := by
      intro b hb e he
      simp only [initC, List.mem_flatMap, List.mem_range]
      exact ⟨j, hj, b, hb, by simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢; tauto⟩
    refine ⟨?_, ?_⟩
    · rw [rw4, show Blake2s.outW 0 = 4 from rfl, key 4 (by norm_num) 0 (by norm_num) (fun b hb => mem b hb _ (by simp [Blake2s.outW])), outWord, if_pos hj]
    · rw [rw4, show Blake2s.outW 1 = 7 from rfl, key 7 (by norm_num) 1 (by norm_num) (fun b hb => mem b hb _ (by simp [Blake2s.outW])), outWord,
        if_neg (by interval_cases j <;> simp [bidx]), show (bidx j + 3) % 4 = j by interval_cases j <;> rfl]
  intro i hi
  obtain ⟨a0, b0⟩ := row 0 (by norm_num); obtain ⟨a1, b1⟩ := row 1 (by norm_num)
  obtain ⟨a2, b2⟩ := row 2 (by norm_num); obtain ⟨a3, b3⟩ := row 3 (by norm_num)
  interval_cases i <;> simp_all [diagSlot, bidx]

end Period2

theorem ofBits_extend {g : ℕ → Bool} {m K : ℕ} (h : ∀ i, m ≤ i → i < K → g i = false) (hk : m ≤ K) :
    ofBits g K = ofBits g m := by
  induction K with
  | zero => have : m = 0 := by omega
            subst this; rfl
  | succ K ih =>
    rcases Nat.eq_or_lt_of_le hk with e | e
    · rw [e]
    · rw [ofBits, ih (fun i a b => h i a (by omega)) (by omega), h K (by omega) (by omega)]; simp

section Period3

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

/-- **The counter and the flag** of a used period are `T` and `LASTF`. -/
theorem tf {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (hnil : M NIL s = 0) :
    inT M s = (M T s).val ∧ (fBit M s = true ↔ M LASTF s = 1) := by
  have hr : s < n := by omega
  have hg : (Expr.mul (p P_R0) (om (k NIL))).eval n preCols pub M s = 1 := by
    simp [Expr.eval, om, one, eval_cst, ev_r0 hr, hs, ev_k hr, hnil]
  have c := fun (e : Expr) (h : Expr.mul (Expr.mul (p P_R0) (om (k NIL))) e ∈ tfC) => by
    have := sat hsat (mem_tf h) hr
    rw [Expr.eval, hg, one_mul] at this
    exact this
  have b0 := bits4 hsat hr 0 (by norm_num)
  have b2 := bits4 hsat hr 2 (by norm_num)
  set g : ℕ → Bool := fun i => bit M (32 * 0 + i) s with hgdef
  -- `t_lo`'s bits 25–31 and all of `t_hi`'s are zero
  have hhi : ∀ i, 25 ≤ i → i < 32 → g i = false := by
    intro i h1 h2
    have := c (k (Blake2s.WB 0 i)) (by
      simp only [tfC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false]
      left; right; exact ⟨i - 25, by omega, by rw [show 25 + (i - 25) = i by omega]⟩)
    rw [ev_k hr] at this
    have e : M i s = 0 := by simpa [Blake2s.WB] using this
    simp [hgdef, bit, e]
  have hw1 : word M (32 * 1) s = 0 := by
    apply word_of_vals (bits4 hsat hr 1 (by norm_num))
    intro i hi
    have := c (k (Blake2s.WB 1 i)) (by
      simp only [tfC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false]
      right; exact ⟨i, hi, rfl⟩)
    rw [ev_k hr] at this
    have e : M (32 * 1 + i) s = 0 := by simpa [Blake2s.WB] using this
    rw [e]; simp
  have hw0 : (word M (32 * 0) s).toNat = ofBits g 25 := by
    simp only [word]; rw [bv32_toNat, ofBits_extend hhi (by norm_num)]
  -- the low bits sum to `TV`
  have hsum := c (.sub (bitSum 0 25) (k T)) (by simp [tfC])
  simp only [Expr.eval, ev_k hr, sub_eq_zero] at hsum
  rw [bitSum, Sha256.eval_sumPow_bits _ g 25 (fun j hj => by
    rw [ev_k hr]; exact eq_bit (b0 j (by omega)))] at hsum
  refine ⟨?_, ?_⟩
  · unfold inT
    rw [hw0, hw1, ← hsum, ZMod.val_natCast_of_lt (by have := ofBits_lt g 25; unfold P; omega)]; simp
  · have hf := c (.sub (k (Blake2s.WB 2 0)) (k LASTF)) (by simp [tfC])
    simp only [Expr.eval, ev_k hr, sub_eq_zero] at hf
    unfold fBit bit
    rw [show 32 * 2 = Blake2s.WB 2 0 from rfl, hf]
    constructor
    · intro h
      have := b2 0 (by norm_num)
      rw [show 32 * 2 + 0 = Blake2s.WB 2 0 from rfl, hf] at this
      have := decide_eq_true_iff.mp h
      rw [← ZMod.natCast_zmod_val (M LASTF s), this]; simp
    · intro h; rw [h]; simp [ZMod.val_one]

/-- **Message words**: row `s + j`'s `WLO`, `WHI` are message word `j`'s limbs. -/
theorem msg_word {s j : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (hj : j < 16) :
    M WLO (s + j) = M (Blake2s.ML j 0) s ∧ M WHI (s + j) = M (Blake2s.ML j 1) s := by
  have hr : s + j < n := by omega
  have hlt : (p P_LT16).eval n preCols pub M (s + j) = 1 := by
    rw [ev_lt16 hr, if_pos (by omega)]
  have sel : ∀ kk < 16, (pre (54 + kk)).eval n preCols pub M (s + j) = if kk = j then 1 else 0 := by
    intro kk hk
    have := ev_rk (pub := pub) (M := M) hk hr
    simp only [p, P_RK] at this
    rw [this, show (s + j) % 88 = j by omega]
    by_cases h : kk = j
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have w := fun (h : ℕ) (hh : h ≤ 1) (e : Expr) (he : Expr.mul (p P_LT16) (.sub (k (if h = 0 then WLO else WHI))
      (Blake2s.msgLimb 54 h)) ∈ wordC) => by
    have := sat hsat (mem_word he) hr
    simp only [Expr.eval, hlt, one_mul, ev_k hr, sub_eq_zero] at this
    rw [Blake2s.eval_msgLimb hr hj sel h, Blake2s.msg_copy (gadget_sat hsat) hs hsn hj hh j (by simp [Blake2s.PERIOD]; omega)] at this
    exact this
  exact ⟨w 0 (by norm_num) (cst 0) (by simp [wordC, Blake2s.msgLimb, p, k, P_RK]),
    w 1 (by norm_num) (cst 0) (by simp [wordC, Blake2s.msgLimb, p, k, P_RK])⟩

end Period3

end StarkedAir.Block.B2s
