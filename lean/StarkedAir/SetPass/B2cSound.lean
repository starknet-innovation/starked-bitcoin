/-
**A segment's Blake2s compressions, soundness (`set_b2c`).** In a satisfied trace whose message-word
reads are answered by the walker (words of a byte string `X`, blocks below `m`) and whose end token is
yielded (a last row `r ≡ 87` of a period with `LASTU`): period 0 starts from the public `h_in` limbs, each
used period continuing the previous one compresses the next block with counter `64·(nb_in + b + 1)` and
the final flag off, and the last block's period (whole, by the token) outputs the public `h_out`. So
`h_out` is `chainS h_in (64·nb_in) X m` (`b2c_sound`) and `nb_in + m < 2^30`.
-/
import StarkedAir.SetPass.B2c
import StarkedAir.Spec.Blake2sBlocks
import StarkedAir.Block.B2sSound

namespace StarkedAir.SetPass.B2c

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back word bit eq_bit word_getLsbD half16)
open StarkedAir.Blake2s (BlakeSat diagSlot msgWord inT fBit outWord rw4 P_INIT P_FIN)
open StarkedAir.Block.B2s (bidx per88)

/-- The incoming chaining value, from its public limbs (word `w`: limbs `2w`, `2w + 1`). -/
def hIn (pub : ℕ → F) (w : ℕ) : Spec.Blake2s.Word :=
  BitVec.ofNat 32 ((pub (H_LIMB B2_IN (2 * w))).val + 65536 * (pub (H_LIMB B2_IN (2 * w + 1))).val)

theorem ofBits_split (g : ℕ → Bool) (j k : ℕ) :
    ofBits g (j + k) = ofBits g j + 2 ^ j * ofBits (fun i => g (j + i)) k := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih =>
    rw [show j + (k + 1) = (j + k) + 1 by omega]
    show ofBits g (j + k) + 2 ^ (j + k) * (g (j + k)).toNat =
      ofBits g j + 2 ^ j * (ofBits (fun i => g (j + i)) k + 2 ^ k * (g (j + k)).toNat)
    rw [ih, pow_add]; ring

theorem ofBits_zero_below {g : ℕ → Bool} {j : ℕ} (h : ∀ i < j, g i = false) : ofBits g j = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => simp [ofBits, ih (fun i hi => h i (by omega)), h j (by omega)]

/-- A word whose two limbs are `a` and `b` (as field elements) is `a + 2^16·b`. -/
theorem word_of_limbs {W : Spec.Blake2s.Word} {a b : F} (ha : ((half16 W 0 : ℕ) : F) = a)
    (hb : ((half16 W 1 : ℕ) : F) = b) : W = BitVec.ofNat 32 (a.val + 65536 * b.val) := by
  have hP : ∀ x, x < 65536 → x < P := fun x hx => by unfold P; omega
  rw [← ha, ← hb, ZMod.val_natCast_of_lt (hP _ (Sha256.half16_lt W 0)),
    ZMod.val_natCast_of_lt (hP _ (Sha256.half16_lt W 1))]
  simp only [half16]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_add_div, Nat.mod_eq_of_lt W.isLt]

theorem preCols_assoc : preCols = Blake2s.preCols ++
    ([ .rowLt 88, per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
      per88 (fun r => if r < 16 then r else 0) ] ++
    (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))) := by
  simp [preCols, List.append_assoc]

/-- A gadget constraint evaluates the same with this component's preprocessed columns. -/
theorem eval_gadget {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r : ℕ} {c : Expr} (hc : c ∈ Blake2s.constraints) :
    c.eval n preCols pub M r = c.eval n Blake2s.preCols pub M r := by
  rw [preCols_assoc]
  apply Expr.eval_pre_append
  rw [Block.B2s.gadget_len]
  exact List.all_eq_true.mp Block.B2s.gadget_pre c hc

theorem eval_pre_gadget {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r i : ℕ} (hi : i < 50) :
    (pre i).eval n preCols pub M r = (pre i).eval n Blake2s.preCols pub M r := by
  rw [preCols_assoc]
  apply Expr.eval_pre_append
  simp [pre, Expr.preBelow, Block.B2s.gadget_len, hi]

theorem mem_gadget {c : Expr} (h : c ∈ Blake2s.constraints) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_flag {c : Expr} (h : c ∈ flagC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_chain {c : Expr} (h : c ∈ chainC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_init {c : Expr} (h : c ∈ initC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_tf {c : Expr} (h : c ∈ tfC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_word {c : Expr} (h : c ∈ wordC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_out {c : Expr} (h : c ∈ outC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto

section Period

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem gadget_sat : BlakeSat n Blake2s.preCols pub M := fun r hr c hc => by
  rw [← eval_gadget hc]
  exact hsat r hr c (mem_gadget hc)

theorem gadget_sat' : BlakeSat n preCols pub M := fun r hr c hc => hsat r hr c (mem_gadget hc)

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

omit hsat in
theorem ev_kq {c s : ℕ} (h88 : 88 ≤ s) (hs : s < n) : (kq c).eval n preCols pub M s = M c (s - 88) := by
  simp only [kq, eval_col]
  rw [show (-88 : ℤ) = -((88 : ℕ) : ℤ) by simp, wrap_back h88 hs]

omit hsat in
theorem ev_per88 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per88 f) {r : ℕ} (hr : r < n) :
    (pre i).eval n preCols pub M r = ((f (r % 88) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 88 < 88 := Nat.mod_lt _ (by norm_num)
  simp [per88, PreCol.eval, Blake2s.PERIOD, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_p0 {r : ℕ} (hr : r < n) : (p P_P0).eval n preCols pub M r = if r < 88 then 1 else 0 := by
  simp [p, pre, Expr.eval, wrap_zero hr, preCols, P_P0, PreCol.eval, Blake2s.preCols]

omit hsat in
theorem ev_r0 {r : ℕ} (hr : r < n) : (p P_R0).eval n preCols pub M r = if r % 88 = 0 then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r = 0 then 1 else 0) (by simp [preCols, P_R0, Blake2s.preCols]) hr]
  split_ifs <;> simp

omit hsat in
theorem ev_lt16 {r : ℕ} (hr : r < n) : (p P_LT16).eval n preCols pub M r = if r % 88 < 16 then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r < 16 then 1 else 0) (by simp [preCols, P_LT16, Blake2s.preCols]) hr]
  split_ifs <;> simp

omit hsat in
theorem ev_kr {r : ℕ} (hr : r < n) : (p P_KR).eval n preCols pub M r = if r % 88 < 16 then ((r % 88 : ℕ) : F) else 0 := by
  rw [p, ev_per88 (f := fun r => if r < 16 then r else 0) (by simp [preCols, P_KR, Blake2s.preCols]) hr]
  split_ifs <;> simp

omit hsat in
theorem ev_rk {j r : ℕ} (hj : j < 16) (hr : r < n) :
    (p (P_RK j)).eval n preCols pub M r = if r % 88 = j then 1 else 0 := by
  rw [p, ev_per88 (f := fun r => if r = j then 1 else 0) (by
    rw [preCols_assoc, P_RK, List.getD_append_right _ _ _ _ (by rw [Block.B2s.gadget_len]; omega), Block.B2s.gadget_len,
      List.getD_append_right _ _ _ _ (by simp; omega), List.length_cons, List.length_cons, List.length_cons,
      List.length_cons, List.length_nil, show 54 + j - 50 - (0 + 1 + 1 + 1 + 1) = j by omega]
    simp [List.getD_eq_getElem?_getD, hj]) hr]
  split_ifs <;> simp

theorem bool_flag {c : ℕ} (hc : c ∈ [NIL, LASTU]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := hsat r hr _ (mem_flag (c := boolC (k c)) (by
    simp only [flagC, List.mem_append, List.mem_map]; left; left; exact ⟨c, hc, rfl⟩))
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ flagC) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := hsat r hr _ (mem_flag h)
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
    have := hsat _ hr _ (mem_flag (c := .mul (om (p P_R0)) (.sub (k X) (kp X)))
      (by simp only [flagC, List.mem_append, List.mem_map]; right; exact ⟨X, hX, rfl⟩))
    rw [show s + (q + 1) = s + q + 1 by ring] at this hr ⊢
    simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_r0 hr, ev_k hr, ev_kp hr,
      show ¬ ((s + q + 1) % 88 = 0) by omega, if_false, sub_zero, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega) (by omega)]

theorem usew_def {r : ℕ} (hr : r < n) : M USEW r = 1 - M NIL r := by
  rw [defn hsat (a := USEW) (e := om (k NIL)) (by simp [flagC]) hr]
  simp [Expr.eval, om, one, eval_cst, ev_k hr]

theorem usew_const {s : ℕ} (hs : s % 88 = 0) {q : ℕ} (hq : q < 88) (hr : s + q < n) : M USEW (s + q) = M USEW s := by
  rw [usew_def hsat hr, usew_def hsat (by omega), per_const hsat (X := NIL) (by simp [perConst]) hs q hq hr]

theorem bits4 {r : ℕ} (hr : r < n) (w : ℕ) (hw : w < 8) : ∀ i < 32, (M (32 * w + i) r).val ≤ 1 :=
  Blake2s.word_bits (gadget_sat hsat) hr hw

omit hsat in
theorem pre_gadget_at {s j q : ℕ} (hs : s % 88 = 0) (hj : j < 50) (hq : q < 88) (hr : s + q < n) :
    (p j).eval n preCols pub M (s + q) = Blake2s.bPre j q := by
  rw [p, eval_pre_gadget hj, Blake2s.pre_at hs hq hr hj]

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
  have w := fun (h : ℕ) (hh : h ≤ 1) (he : Expr.mul (p P_LT16) (.sub (k (if h = 0 then WLO else WHI))
      (Blake2s.msgLimb 54 h)) ∈ wordC) => by
    have := hsat _ hr _ (mem_word he)
    simp only [Expr.eval, hlt, one_mul, ev_k hr, sub_eq_zero] at this
    rw [Blake2s.eval_msgLimb hr hj sel h, Blake2s.msg_copy (gadget_sat hsat) hs hsn hj hh j (by simp [Blake2s.PERIOD]; omega)] at this
    exact this
  exact ⟨w 0 (by norm_num) (by simp [wordC, Blake2s.msgLimb, p, k, P_RK]),
    w 1 (by norm_num) (by simp [wordC, Blake2s.msgLimb, p, k, P_RK])⟩

/-- **The counter and the flag** of a used period: `t = 64·v` with `v = nb_in + BLKI + 1 < 2^30`, `f` off. -/
theorem tf {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (hu : M USEW s = 1) :
    ∃ v : ℕ, v < 2 ^ 30 ∧ inT M s = 64 * v ∧ (v : F) = pub (H_NB B2_IN) + M BLKI s + 1 ∧ fBit M s = false := by
  have hr : s < n := by omega
  have hg : (Expr.mul (p P_R0) (k USEW)).eval n preCols pub M s = 1 := by
    simp [Expr.eval, ev_r0 hr, hs, ev_k hr, hu]
  have c := fun (e : Expr) (h : Expr.mul (Expr.mul (p P_R0) (k USEW)) e ∈ tfC) => by
    have := hsat s hr _ (mem_tf h)
    rw [Expr.eval, hg, one_mul] at this
    exact this
  have b0 := bits4 hsat hr 0 (by norm_num)
  have b1 := bits4 hsat hr 1 (by norm_num)
  have b2 := bits4 hsat hr 2 (by norm_num)
  set g : ℕ → Bool := fun i => bit M (32 * 0 + i) s with hgdef
  set h : ℕ → Bool := fun i => bit M (32 * 1 + i) s with hhdef
  have glo : ∀ i < 6, g i = false := by
    intro i hi
    have := c (k (Blake2s.WB 0 i)) (by
      simp only [tfC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false]
      left; right; exact ⟨i, hi, rfl⟩)
    rw [ev_k hr] at this
    have e : M (32 * 0 + i) s = 0 := by simpa [Blake2s.WB] using this
    show bit M (32 * 0 + i) s = false
    unfold bit; rw [e]; simp
  have hhi : ∀ i, 4 ≤ i → i < 32 → h i = false := by
    intro i h1 h2
    have := c (k (Blake2s.WB 1 (4 + (i - 4)))) (by
      simp only [tfC, List.mem_append, List.mem_cons, List.mem_map, List.mem_range, List.not_mem_nil, or_false]
      right; exact ⟨i - 4, by omega, rfl⟩)
    rw [ev_k hr, show 4 + (i - 4) = i by omega] at this
    have e : M (32 * 1 + i) s = 0 := by simpa [Blake2s.WB] using this
    show bit M (32 * 1 + i) s = false
    unfold bit; rw [e]; simp
  have hsum := c (.sub (.add (bitSum 0 6 26) (.mul (cst (2 ^ 26)) (bitSum 1 0 4)))
      (.add (.add (.pub (H_NB B2_IN)) (k BLKI)) one)) (by simp [tfC])
  simp only [Expr.eval, ev_k hr, eval_cst, one, Nat.cast_one, sub_eq_zero] at hsum
  rw [bitSum, Sha256.eval_sumPow_bits _ (fun i => g (6 + i)) 26 (fun j hj => by
      rw [ev_k hr]; exact eq_bit (b0 (6 + j) (by omega))),
    bitSum, Sha256.eval_sumPow_bits _ h 4 (fun j hj => by
      rw [ev_k hr, Nat.zero_add]; exact eq_bit (b1 j (by omega)))] at hsum
  obtain ⟨A, hAd⟩ : ∃ A, A = ofBits (fun i => g (6 + i)) 26 := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = ofBits h 4 := ⟨_, rfl⟩
  rw [← hAd, ← hBd] at hsum
  have hA : A < 2 ^ 26 := hAd ▸ ofBits_lt _ 26
  have hB : B < 2 ^ 4 := hBd ▸ ofBits_lt _ 4
  have hw0 : (word M (32 * 0) s).toNat = 64 * A := by
    rw [show word M (32 * 0) s = bv32 g from rfl, bv32_toNat, show (32 : ℕ) = 6 + 26 from rfl, ofBits_split,
      ofBits_zero_below glo, hAd]; ring
  have hw1 : (word M (32 * 1) s).toNat = B := by
    rw [show word M (32 * 1) s = bv32 h from rfl, bv32_toNat, Block.B2s.ofBits_extend hhi (by norm_num), hBd]
  refine ⟨A + 2 ^ 26 * B, by omega, ?_, ?_, ?_⟩
  · unfold inT; rw [hw0, hw1]; ring
  · rw [← hsum]; push_cast; ring
  · have hf := c (k (Blake2s.WB 2 0)) (by simp [tfC])
    rw [ev_k hr] at hf
    unfold fBit bit
    rw [show 32 * 2 = Blake2s.WB 2 0 from rfl, hf]
    simp

/-- **Period 0 starts from the public `h_in`.** -/
theorem h_first (hsn : 88 ≤ n) : ∀ i < 8, diagSlot M 0 i = hIn pub i := by
  have row : ∀ j < 4, rw4 M j 0 = hIn pub j ∧ rw4 M j 1 = hIn pub (bidx j) := by
    intro j hj
    have hr : j < n := by omega
    have hp0 : (p P_P0).eval n preCols pub M j = 1 := by rw [ev_p0 hr, if_pos (by omega)]
    have hin : (p (P_INIT j)).eval n preCols pub M j = 1 := by
      have := pre_gadget_at (n := n) (pub := pub) (M := M) (s := 0) (j := P_INIT j) (q := j) (by norm_num) (by simp [P_INIT]; omega) (by omega)
        (by omega)
      rw [Nat.zero_add] at this
      rw [this, Blake2s.bPre_INIT hj (by simp [Blake2s.PERIOD]; omega), if_pos rfl]
    have lim : ∀ (w hh : ℕ) (hw : w < 8) (hh1 : hh ≤ 1) (idx : ℕ),
        Expr.mul (p P_P0) (.mul (p (P_INIT j)) (.sub (Blake2s.limb w hh) (.pub (H_LIMB B2_IN idx)))) ∈ initC →
        ((half16 (word M (32 * w) j) hh : ℕ) : F) = pub (H_LIMB B2_IN idx) := by
      intro w hh hw hh1 idx hmem
      have := hsat j hr _ (mem_init hmem)
      simp only [Expr.eval, hp0, hin, one_mul, sub_eq_zero] at this
      rw [Blake2s.limb_here (gadget_sat' hsat) hr hw hh1] at this
      exact this
    have mem : ∀ hh < 2, ∀ e ∈ [Expr.mul (p P_P0) (.mul (p (P_INIT j))
          (.sub (Blake2s.limb (Blake2s.outW 0) hh) (.pub (H_LIMB B2_IN (2 * j + hh))))),
        Expr.mul (p P_P0) (.mul (p (P_INIT j))
          (.sub (Blake2s.limb (Blake2s.outW 1) hh) (.pub (H_LIMB B2_IN (2 * bidx j + hh)))))], e ∈ initC := by
      intro hh hhl e he
      simp only [initC, List.mem_flatMap, List.mem_range, List.mem_append]
      exact ⟨j, hj, Or.inl ⟨hh, hhl, he⟩⟩
    constructor
    · exact word_of_limbs (lim 4 0 (by norm_num) (by norm_num) _ (mem 0 (by norm_num) _ (by simp [Blake2s.outW])))
        (lim 4 1 (by norm_num) (by norm_num) _ (mem 1 (by norm_num) _ (by simp [Blake2s.outW])))
    · exact word_of_limbs (lim 7 0 (by norm_num) (by norm_num) _ (mem 0 (by norm_num) _ (by simp [Blake2s.outW])))
        (lim 7 1 (by norm_num) (by norm_num) _ (mem 1 (by norm_num) _ (by simp [Blake2s.outW])))
  intro i hi
  obtain ⟨a0, b0⟩ := row 0 (by norm_num); obtain ⟨a1, b1⟩ := row 1 (by norm_num)
  obtain ⟨a2, b2⟩ := row 2 (by norm_num); obtain ⟨a3, b3⟩ := row 3 (by norm_num)
  interval_cases i <;> simp_all [diagSlot, bidx]

/-- A used period after period 0 continues the previous one. -/
theorem chn_one {s : ℕ} (hs : s % 88 = 0) (h88 : 88 ≤ s) {q : ℕ} (hq : q < 88) (hr : s + q < n)
    (hu : M USEW s = 1) : M CHN (s + q) = 1 := by
  rw [defn hsat (a := CHN) (e := .mul (k USEW) (om (p P_P0))) (by simp [flagC]) hr]
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, ev_p0 hr, if_neg (show ¬ s + q < 88 by omega),
    sub_zero, mul_one, usew_const hsat hs hq hr, hu]

/-- **A continuing period chains**: its chaining value is the previous period's output. -/
theorem h_chain {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (h88 : 88 ≤ s) (hu : M USEW s = 1) :
    ∀ i < 8, diagSlot M s i = outWord M (s - 88) i := by
  have row : ∀ j < 4, rw4 M (s + j) 0 = outWord M (s - 88) j ∧ rw4 M (s + j) 1 = outWord M (s - 88) (bidx j) := by
    intro j hj
    have hr : s + j < n := by omega
    have hcj : M CHN (s + j) = 1 := chn_one hsat hs h88 (by omega) hr hu
    have hin : (p (P_INIT j)).eval n preCols pub M (s + j) = 1 := by
      rw [pre_gadget_at hs (by simp [P_INIT]; omega) (by omega) hr, Blake2s.bPre_INIT hj (by simp [Blake2s.PERIOD]; omega),
        if_pos rfl]
    have hwr : wrap n (s + j) (-4) = s - 88 + 84 + j := by
      rw [show (-4 : ℤ) = -((4 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; omega
    have key : ∀ (w : ℕ) (hw : w < 8) (w' : ℕ), w' < 8 → (∀ b < 32, Expr.mul (k CHN) (.mul (p (P_INIT j))
        (.sub (k (Blake2s.WB w b)) (col (Blake2s.WB w' b) (-4)))) ∈ initC) →
        word M (32 * w) (s + j) = word M (32 * w') (s - 88 + 84 + j) := by
      intro w hw w' hw' hmem
      apply Block.B2s.word_of_vals (bits4 hsat hr w hw)
      intro b hb
      have := hsat _ hr _ (mem_init (hmem b hb))
      simp only [Expr.eval, ev_k hr, hin, one_mul, hcj, eval_col, hwr, sub_eq_zero] at this
      rw [show Blake2s.WB w b = 32 * w + b from rfl, show Blake2s.WB w' b = 32 * w' + b from rfl] at this
      rw [this, eq_bit (bits4 hsat (show s - 88 + 84 + j < n by omega) w' hw' b hb), word_getLsbD _ _ hb]
    have mem : ∀ b < 32, ∀ e ∈ [Expr.mul (k CHN) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 0) b)) (col (Blake2s.WB 0 b) (-4)))),
        Expr.mul (k CHN) (.mul (p (P_INIT j)) (.sub (k (Blake2s.WB (Blake2s.outW 1) b)) (col (Blake2s.WB 1 b) (-4))))],
        e ∈ initC := by
      intro b hb e he
      simp only [initC, List.mem_flatMap, List.mem_range, List.mem_append]
      exact ⟨j, hj, Or.inr ⟨b, hb, he⟩⟩
    refine ⟨?_, ?_⟩
    · rw [rw4, show Blake2s.outW 0 = 4 from rfl, key 4 (by norm_num) 0 (by norm_num) (fun b hb => mem b hb _ (by simp [Blake2s.outW])),
        outWord, if_pos hj]
    · rw [rw4, show Blake2s.outW 1 = 7 from rfl, key 7 (by norm_num) 1 (by norm_num) (fun b hb => mem b hb _ (by simp [Blake2s.outW])),
        outWord, if_neg (by interval_cases j <;> simp [bidx]), show (bidx j + 3) % 4 = j by interval_cases j <;> rfl]
  intro i hi
  obtain ⟨a0, b0⟩ := row 0 (by norm_num); obtain ⟨a1, b1⟩ := row 1 (by norm_num)
  obtain ⟨a2, b2⟩ := row 2 (by norm_num); obtain ⟨a3, b3⟩ := row 3 (by norm_num)
  interval_cases i <;> simp_all [diagSlot, bidx]

/-- **A continuing period's predecessor** is a used period, one block earlier. -/
theorem prev_period {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ n) (h88 : 88 ≤ s) (hu : M USEW s = 1) :
    M USEW (s - 88) = 1 ∧ M BLKI s = M BLKI (s - 88) + 1 := by
  have hsr : s < n := by omega
  have hr0 : (p P_R0).eval n preCols pub M s = 1 := by rw [ev_r0 hsr, if_pos hs]
  have hc := chn_one hsat hs h88 (q := 0) (by norm_num) (by omega) hu
  rw [Nat.add_zero] at hc
  have c2 := hsat s hsr _ (mem_chain (c := .mul (p P_R0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)))
    (by simp [chainC]))
  have c3 := hsat s hsr _ (mem_chain (c := .mul (p P_R0) (.mul (k CHN) (kq NIL))) (by simp [chainC]))
  simp only [Expr.eval, hr0, one_mul, ev_k hsr, hc, ev_kq h88 hsr, one, eval_cst, Nat.cast_one,
    sub_eq_zero] at c2 c3
  refine ⟨?_, by linear_combination c2⟩
  rw [usew_def hsat (by omega), c3, sub_zero]

/-- A used period's row 0 reads a word, so its block index is a block below `m`. -/
theorem mu_row {s q : ℕ} (hs : s % 88 = 0) (hq : q < 16) (hr : s + q < n) (hu : M USEW s = 1) :
    M MU (s + q) = 1 := by
  rw [defn hsat (a := MU) (e := .mul (k USEW) (p P_LT16)) (by simp [flagC]) hr]
  simp only [Expr.eval, ev_k hr, ev_lt16 hr, show (s + q) % 88 < 16 by omega, if_true, mul_one,
    usew_const hsat hs (show q < 88 by omega) hr, hu]

/-- **The b2c chain.** With the walker's words of `X`, a used period with block index `b` starts from
`chainS h_in (64·nb_in) X b`. -/
theorem chain_state (X : List UInt8) {m : ℕ} (hmn : m ≤ 2 ^ 25) (hnb : (pub (H_NB B2_IN)).val < 2 ^ 30)
    (hw : ∀ r < n, M MU r = 1 → ∃ b : ℕ, b < m ∧ M BLKI r = (b : F) ∧
      M WLO r = (((Spec.Blake2s.wordAt X b (r % 88)).toNat % 65536 : ℕ) : F) ∧
      M WHI r = (((Spec.Blake2s.wordAt X b (r % 88)).toNat / 65536 : ℕ) : F)) :
    ∀ b : ℕ, b < m → ∀ s, s % 88 = 0 → s + 88 ≤ n → M USEW s = 1 → M BLKI s = (b : F) →
      (∀ i < 8, diagSlot M s i = Spec.Blake2s.chainS (hIn pub) (64 * (pub (H_NB B2_IN)).val) X b i) ∧
      (∀ kk < 16, msgWord M kk s = Spec.Blake2s.wordAt X b kk ∧ ∀ h ≤ 1, (M (Blake2s.ML kk h) s).val < 65536) ∧
      inT M s = 64 * ((pub (H_NB B2_IN)).val + b + 1) ∧ fBit M s = false ∧ (pub (H_NB B2_IN)).val + b + 1 < 2 ^ 30 := by
  have hPv : ∀ x : ℕ, x ≤ 2 ^ 30 → x < P := fun x hx => by unfold P; omega
  have hPP : ∀ x : ℕ, x < 2 ^ 31 - 1 → x < P := fun x hx => by unfold P; exact hx
  have hP65 : ∀ x : ℕ, x < 65536 → x < P := fun x hx => hPv x (by omega)
  -- the block index of a used whole period
  have bidx_of : ∀ s, s % 88 = 0 → s + 88 ≤ n → M USEW s = 1 → ∃ b : ℕ, b < m ∧ M BLKI s = (b : F) := by
    intro s hs hsn hu
    obtain ⟨b, hb, hbk, -⟩ := hw s (by omega) (by simpa using mu_row hsat hs (q := 0) (by norm_num) (by omega) hu)
    exact ⟨b, hb, hbk⟩
  -- the words, counter and flag of a used whole period hashing block `b`
  have facts : ∀ b : ℕ, b < m → ∀ s, s % 88 = 0 → s + 88 ≤ n → M USEW s = 1 → M BLKI s = (b : F) →
      (∀ kk < 16, msgWord M kk s = Spec.Blake2s.wordAt X b kk ∧ ∀ h ≤ 1, (M (Blake2s.ML kk h) s).val < 65536) ∧
      inT M s = 64 * ((pub (H_NB B2_IN)).val + b + 1) ∧ fBit M s = false ∧ (pub (H_NB B2_IN)).val + b + 1 < 2 ^ 30 := by
    intro b hb s hs hsn hu hblk
    refine ⟨fun kk hkk => ?_, ?_⟩
    · have hr : s + kk < n := by omega
      obtain ⟨b', hb', hbk', hlo, hhi⟩ := hw (s + kk) hr (mu_row hsat hs hkk hr hu)
      rw [per_const hsat (X := BLKI) (by simp [perConst]) hs kk (by omega) hr, hblk] at hbk'
      have e : b = b' := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) hbk'
      subst e
      obtain ⟨wlo, whi⟩ := msg_word hsat hs hsn hkk
      rw [show (s + kk) % 88 = kk by omega] at hlo hhi
      have W := Spec.Blake2s.wordAt X b kk
      have hv0 : (M (Blake2s.ML kk 0) s).val = (Spec.Blake2s.wordAt X b kk).toNat % 65536 := by
        rw [← wlo, hlo, ZMod.val_natCast_of_lt (hP65 _ (Nat.mod_lt _ (by norm_num)))]
      have hv1 : (M (Blake2s.ML kk 1) s).val = (Spec.Blake2s.wordAt X b kk).toNat / 65536 := by
        have := (Spec.Blake2s.wordAt X b kk).isLt
        rw [← whi, hhi, ZMod.val_natCast_of_lt (hP65 _ (by omega))]
      refine ⟨?_, fun h hh => ?_⟩
      · unfold Blake2s.msgWord
        rw [hv0, hv1, Nat.mod_add_div]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
      · have := (Spec.Blake2s.wordAt X b kk).isLt
        interval_cases h
        · rw [hv0]; omega
        · rw [hv1]; omega
    · obtain ⟨v, hv, hinT, hvF, hf⟩ := tf hsat hs hsn hu
      rw [hblk] at hvF
      have hnbF : pub (H_NB B2_IN) = (((pub (H_NB B2_IN)).val : ℕ) : F) := (ZMod.natCast_zmod_val _).symm
      rw [hnbF] at hvF
      have e : v = (pub (H_NB B2_IN)).val + b + 1 :=
        natCast_inj_of_lt (hPv _ (by omega)) (hPP _ (by omega)) (by rw [hvF]; push_cast; ring)
      refine ⟨by rw [hinT, e], hf, by omega⟩
  intro b
  induction b with
  | zero =>
    intro hb s hs hsn hu hblk
    refine ⟨?_, facts 0 hb s hs hsn hu hblk⟩
    by_cases h0 : s = 0
    · subst h0
      intro i hi
      rw [h_first hsat (by omega) i hi]; rfl
    · exfalso
      obtain ⟨hu', hbk⟩ := prev_period hsat hs hsn (by omega) hu
      obtain ⟨b', hb', hbk'⟩ := bidx_of (s - 88) (by omega) (by omega) hu'
      rw [hblk, hbk'] at hbk
      have : ((b' + 1 : ℕ) : F) = ((0 : ℕ) : F) := by push_cast at hbk ⊢; linear_combination -hbk
      have := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) this
      omega
  | succ b ih =>
    intro hb s hs hsn hu hblk
    refine ⟨?_, facts (b + 1) hb s hs hsn hu hblk⟩
    have h88 : 88 ≤ s := by
      by_contra hc
      have h0 : s = 0 := by omega
      subst h0
      have := hsat 0 (by omega) _ (mem_chain (c := .mul (p P_P0) (k BLKI)) (by simp [chainC]))
      simp only [Expr.eval, ev_p0 (show 0 < n by omega), show (0 : ℕ) < 88 by norm_num, if_true, one_mul,
        ev_k (show 0 < n by omega), hblk] at this
      have := natCast_inj_of_lt (a := b + 1) (b := 0) (hPv _ (by omega)) (hPv _ (by omega)) (by simpa using this)
      omega
    obtain ⟨hu', hbk⟩ := prev_period hsat hs hsn h88 hu
    obtain ⟨b', hb', hbk'⟩ := bidx_of (s - 88) (by omega) (by omega) hu'
    have e : b' = b := by
      rw [hblk, hbk'] at hbk
      have : ((b' + 1 : ℕ) : F) = ((b + 1 : ℕ) : F) := by push_cast at hbk ⊢; linear_combination -hbk
      have := natCast_inj_of_lt (hPv _ (by omega)) (hPv _ (by omega)) this
      omega
    subst e
    have hs' : (s - 88) % 88 = 0 := by omega
    have hsn' : s - 88 + 88 ≤ n := by omega
    obtain ⟨ihs, hwords, hinT, hfb, -⟩ := ih (by omega) (s - 88) hs' hsn' hu' hbk'
    have hcomp := Blake2s.compress_sound (gadget_sat hsat) hs' hsn' (fun kk hkk => (hwords kk hkk).2)
    intro i hi
    rw [h_chain hsat hs hsn h88 hu i hi, ← hcomp i hi, hinT, hfb]
    simp only [Spec.Blake2s.chainS, if_pos hi]
    rw [show 64 * ((pub (H_NB B2_IN)).val + b' + 1) = 64 * (pub (H_NB B2_IN)).val + 64 * (b' + 1) by ring]
    exact Spec.Blake2s.compress_congr ihs (fun kk hkk => (hwords kk hkk).1) _ _ i hi

/-- **A segment's Blake2s compressions.** With the walker's words of `X` (blocks below `m`) and the end
token yielded, `nb_in + m < 2^30` and the public `h_out` limbs are those of `chainS h_in (64·nb_in) X m`. -/
theorem b2c_sound (X : List UInt8) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ 2 ^ 25)
    (hm : pub (H_NB B2_OUT) - pub (H_NB B2_IN) = (m : F)) (hnb : (pub (H_NB B2_IN)).val < 2 ^ 30)
    (hw : ∀ r < n, M MU r = 1 → ∃ b : ℕ, b < m ∧ M BLKI r = (b : F) ∧
      M WLO r = (((Spec.Blake2s.wordAt X b (r % 88)).toNat % 65536 : ℕ) : F) ∧
      M WHI r = (((Spec.Blake2s.wordAt X b (r % 88)).toNat / 65536 : ℕ) : F))
    (hend : ∃ r < n, r % 88 = 87 ∧ M LASTU r = 1) :
    (pub (H_NB B2_IN)).val + m < 2 ^ 30 ∧
    ∀ w < 8, ∀ h ≤ 1, pub (H_LIMB B2_OUT (2 * w + h)) =
      ((half16 (Spec.Blake2s.chainS (hIn pub) (64 * (pub (H_NB B2_IN)).val) X m w) h : ℕ) : F) := by
  obtain ⟨r, hr, hr87, hlr⟩ := hend
  set s := r - 87 with hsdef
  have hs : s % 88 = 0 := by omega
  have hsn : s + 88 ≤ n := by omega
  have hsr : s < n := by omega
  have hl : M LASTU s = 1 := by
    rw [← per_const hsat (X := LASTU) (by simp [perConst]) hs 87 (by norm_num) (by omega),
      show s + 87 = r by omega, hlr]
  have hnil : M NIL s = 0 := by
    have := hsat s hsr _ (mem_flag (c := .mul (k LASTU) (k NIL)) (by simp [flagC]))
    simp only [Expr.eval, ev_k hsr, hl, one_mul] at this
    exact this
  have hu : M USEW s = 1 := by rw [usew_def hsat hsr, hnil, sub_zero]
  have hblk : M BLKI s = ((m - 1 : ℕ) : F) := by
    have := hsat s hsr _ (mem_flag (c := .mul (k LASTU) (.sub (k BLKI) mLast)) (by simp [flagC]))
    simp only [Expr.eval, ev_k hsr, hl, one_mul, mLast, one, eval_cst, Nat.cast_one, sub_eq_zero] at this
    rw [this, hm, Nat.cast_sub hm1]; simp
  obtain ⟨hch, hwords, hinT, hfb, hlt⟩ :=
    chain_state hsat X hmn hnb hw (m - 1) (by omega) s hs hsn hu hblk
  rw [show (pub (H_NB B2_IN)).val + (m - 1) + 1 = (pub (H_NB B2_IN)).val + m by omega] at hlt hinT
  refine ⟨hlt, ?_⟩
  have hcomp := Blake2s.compress_sound (gadget_sat hsat) hs hsn (fun kk hkk => (hwords kk hkk).2)
  -- the output words are the chain after `m` blocks
  have hout : ∀ w < 8, outWord M s w = Spec.Blake2s.chainS (hIn pub) (64 * (pub (H_NB B2_IN)).val) X m w := by
    intro w hw8
    rw [← hcomp w hw8, hinT, hfb, show m = m - 1 + 1 by omega]
    simp only [Spec.Blake2s.chainS, if_pos hw8]
    rw [show 64 * ((pub (H_NB B2_IN)).val + (m - 1 + 1)) = 64 * (pub (H_NB B2_IN)).val + 64 * (m - 1 + 1) by ring]
    exact Spec.Blake2s.compress_congr hch (fun kk hkk => (hwords kk hkk).1) _ _ w hw8
  -- the public limbs at the final rows
  have fin : ∀ j < 4, ∀ hh ≤ 1,
      pub (H_LIMB B2_OUT (2 * j + hh)) = ((half16 (word M (32 * 0) (s + 84 + j)) hh : ℕ) : F) ∧
      pub (H_LIMB B2_OUT (2 * bidx j + hh)) = ((half16 (word M (32 * 1) (s + 84 + j)) hh : ℕ) : F) := by
    intro j hj hh hh1
    have hrj : s + 84 + j < n := by omega
    have hlj : M LASTU (s + 84 + j) = 1 := by
      rw [show s + 84 + j = s + (84 + j) by ring, per_const hsat (X := LASTU) (by simp [perConst]) hs _ (by omega)
        (by omega), hl]
    have hfin : (p (P_FIN j)).eval n preCols pub M (s + 84 + j) = 1 := by
      rw [show s + 84 + j = s + (84 + j) by ring, pre_gadget_at hs (by simp [P_FIN]; omega) (by omega) (by omega),
        Blake2s.bPre_FIN hj (by simp [Blake2s.PERIOD]; omega), if_pos rfl]
    have mem : ∀ e ∈ [Expr.mul (Expr.mul (k LASTU) (p (P_FIN j))) (.sub (Blake2s.limb 0 hh) (.pub (H_LIMB B2_OUT (2 * j + hh)))),
        Expr.mul (Expr.mul (k LASTU) (p (P_FIN j))) (.sub (Blake2s.limb 1 hh) (.pub (H_LIMB B2_OUT (2 * bidx j + hh))))],
        e ∈ outC := by
      intro e he
      simp only [outC, List.mem_flatMap, List.mem_range]
      exact ⟨j, hj, hh, by omega, he⟩
    have ev := fun (w : ℕ) (hw : w < 8) (idx : ℕ) (he : Expr.mul (Expr.mul (k LASTU) (p (P_FIN j)))
        (.sub (Blake2s.limb w hh) (.pub (H_LIMB B2_OUT idx))) ∈ outC) => by
      have := hsat _ hrj _ (mem_out he)
      simp only [Expr.eval, ev_k hrj, hlj, hfin, one_mul, sub_eq_zero] at this
      rw [Blake2s.limb_here (gadget_sat' hsat) hrj hw hh1] at this
      exact this.symm
    exact ⟨ev 0 (by norm_num) _ (mem _ (by simp)), ev 1 (by norm_num) _ (mem _ (by simp))⟩
  intro w hw8 hh hh1
  by_cases h4 : w < 4
  · rw [(fin w h4 hh hh1).1, ← hout w hw8, outWord, if_pos h4]
  · set j := (w + 3) % 4 with hj
    have hbj : bidx j = w := by
      have : w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> rfl
    rw [← hbj, (fin j (by omega) hh hh1).2, hbj, ← hout w hw8, outWord, if_neg h4]

end Period

end StarkedAir.SetPass.B2c
