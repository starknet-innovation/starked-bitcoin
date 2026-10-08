/-
**Block fields soundness (M3a.2, AIR layer).** From a satisfied fields trace: row kinds, the
grammar transitions, CompactSize decoding and the tiling, leading to `fields_sound`: the rows'
tokens are accepted by `toksBlock` and their bytes are the block's.
-/
import StarkedAir.Block.Fields
import StarkedAir.Spec.BlockTokens

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow eval_col eval_cst wrap_back)

theorem mem_kindC {c : Expr} (h : c ∈ kindC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_transC {c : Expr} (h : c ∈ transC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_tileC {c : Expr} (h : c ∈ tileC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_compactC {c : Expr} (h : c ∈ compactC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_segC {c : Expr} (h : c ∈ segC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_countC {c : Expr} (h : c ∈ countC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_zeroC {c : Expr} (h : c ∈ zeroC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_bitC {c : Expr} (h : c ∈ bitC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

theorem castv1 {x : F} (h : x.val = 1) : (((x.val : ℕ)) : F) = 1 := by rw [h]; simp

theorem bool_val {x : F} (h : x = 0 ∨ x = 1) : x = ((x.val : ℕ) : F) ∧ x.val ≤ 1 := by
  rcases h with rfl | rfl
  · simp
  · have : (1 : F).val = 1 := ZMod.val_one P
    simp [this]

theorem kinds_range : kinds = List.range 9 := rfl

theorem sum_bits_lt (v : ℕ → ℕ) (hv : ∀ j, v j ≤ 1) : ∀ k, ∑ j ∈ Finset.range k, 2 ^ j * v j < 2 ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := sum_bits_lt v hv k
    have h2 : 2 ^ k * v k ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ (hv k)
    omega

theorem val_lt_of_eq_cast {x : F} {m : ℕ} (h : x = (m : F)) (hm : m < P) : x.val = m := by
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt hm]

/-- `x = a − m` with `m < 2^25`, `a ≤ 2^25` and `x` small: `x ≤ a`. -/
theorem val_of_sub_left {x : F} {a m : ℕ} (h : (m : F) = (a : F) - x) (hm : m < 2 ^ 25) (ha : a ≤ 2 ^ 25)
    (hx : x.val < 2 ^ 26) : x.val + m = a := by
  have e : x = (a : F) - (m : F) := by rw [h]; ring
  by_cases hma : m ≤ a
  · rw [e, ← Nat.cast_sub hma, ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold P; omega)] at hx ⊢; omega
  · exfalso
    have e2 : x = -(((m - a : ℕ)) : F) := by rw [e, Nat.cast_sub (by omega)]; ring
    have hne : (((m - a : ℕ)) : F) ≠ 0 := by
      intro h0
      have := congrArg ZMod.val h0
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold P; omega), ZMod.val_zero] at this; omega
    haveI : NeZero (((m - a : ℕ)) : F) := ⟨hne⟩
    rw [e2, ZMod.val_neg_of_ne_zero, ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold P; omega)] at hx
    unfold P at hx; omega

/-- `x − a = m` with small `a`, `m`: `x = a + m`. -/
theorem val_of_sub_right {x : F} {a m : ℕ} (h : (m : F) = x - (a : F)) (hm : m < 2 ^ 25) (ha : a ≤ 2 ^ 25) :
    x.val = a + m := by
  have e : x = ((a + m : ℕ) : F) := by push_cast; rw [h]; ring
  rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]

theorem u8_eq {a b : ℕ} (h : a % 256 = b % 256) : UInt8.ofNat a = UInt8.ofNat b :=
  UInt8.toNat_inj.mp (by simp; omega)

theorem lt_P {m : ℕ} (h : m ≤ 2 ^ 30) : m < P := lt_of_le_of_lt h (by unfold P; norm_num)

theorem one_add_one_ne : (1 : F) + 1 ≠ 0 := by
  intro e
  have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num)
    (by push_cast; linear_combination e)
  omega

theorem val_pred {x : F} {k : ℕ} (hx : x.val = k + 1) : (x - 1).val = k := by
  have e : x = ((k + 1 : ℕ) : F) := by rw [← hx, ZMod.natCast_zmod_val]
  rw [e, show ((k + 1 : ℕ) : F) - 1 = ((k : ℕ) : F) by push_cast; ring]
  exact val_lt_of_eq_cast rfl (by have := ZMod.val_lt x; omega)

section Rows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

/-! ### Evaluation -/

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, pre, Expr.eval, preCols, PreCol.eval, wrap_zero hr]

omit hsat in
theorem ev_last {r : ℕ} (hr : r < n) : isLast.eval n preCols pub M r = if r + 1 < n then 0 else 1 := by
  simp [isLast, pre, Expr.eval, preCols, PreCol.eval, wrap_zero hr, cst]; split_ifs <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

/-! ### Booleans and kinds -/

theorem bool_of {e : ℕ} (hc : boolC (k e) ∈ constraints) {r : ℕ} (hr : r < n) : M e r = 0 ∨ M e r = 1 := by
  have := sat hsat hc hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem kind_bool {c : ℕ} (hc : c ∈ kinds) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 :=
  bool_of hsat (mem_kindC (by simp only [kindC, List.mem_append, List.mem_map]; left; exact ⟨c, hc, rfl⟩)) hr

theorem kind_sum {r : ℕ} (hr : r < n) :
    M K_BLK r + (M K_TXH r + (M K_IN r + (M K_NOUT r + (M K_OUT r + (M K_WCNT r + (M K_WITEM r +
      (M K_LOCK r + (M K_PAD r + 0)))))))) = 1 := by
  have := sat hsat (mem_kindC (c := .sub (kinds.foldr (fun c acc => .add (k c) acc) (cst 0)) one)
    (by simp [kindC])) hr
  simp only [kinds, List.foldr, Expr.eval, ev_k hr, eval_cst, one, Nat.cast_zero, Nat.cast_one, sub_eq_zero] at this
  exact this

theorem kind_sumN {r : ℕ} (hr : r < n) : ∑ c ∈ Finset.range 9, (M c r).val = 1 := by
  have hs := kind_sum hsat hr
  have bv : ∀ c < 9, M c r = ((M c r).val : F) ∧ (M c r).val ≤ 1 :=
    fun c hc => bool_val (kind_bool hsat (by rw [kinds_range]; exact List.mem_range.mpr hc) hr)
  have hle : ∑ c ∈ Finset.range 9, (M c r).val ≤ 9 := by
    calc _ ≤ ∑ _c ∈ Finset.range 9, 1 := Finset.sum_le_sum (fun c hc => (bv c (Finset.mem_range.mp hc)).2)
      _ = 9 := by simp
  have hcast : ((∑ c ∈ Finset.range 9, (M c r).val : ℕ) : F) = ((1 : ℕ) : F) := by
    push_cast
    rw [Finset.sum_congr rfl (fun c hc => (bv c (Finset.mem_range.mp hc)).1.symm)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD] at hs
    rw [← hs]; ring
  exact natCast_inj_of_lt (lt_of_le_of_lt hle (by unfold P; norm_num)) (by unfold P; norm_num) hcast

/-- **One-hot kinds**: a row of kind `a` has every other kind column 0. -/
theorem kind_unique {r : ℕ} (hr : r < n) {a b : ℕ} (ha : a < 9) (hb : b < 9) (hab : a ≠ b) (h : M a r = 1) :
    M b r = 0 := by
  have hs := kind_sumN hsat hr
  have := Finset.add_le_sum (f := fun c => (M c r).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr ha) (Finset.mem_range.mpr hb) hab
  have hb' := (bool_val (kind_bool hsat (by rw [kinds_range]; exact List.mem_range.mpr hb) hr)).1
  have ha1 : (M a r).val = 1 := by rw [h]; exact ZMod.val_one P
  rw [hb', show (M b r).val = 0 by omega]; simp

/-- Every row has a kind. -/
theorem kind_exists {r : ℕ} (hr : r < n) : ∃ a < 9, M a r = 1 := by
  have hs := kind_sumN hsat hr
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ c ∈ Finset.range 9, (M c r).val ≠ 0)
  refine ⟨a, Finset.mem_range.mp ha, ?_⟩
  have bv := bool_val (kind_bool hsat (by rw [kinds_range]; exact List.mem_range.mpr (Finset.mem_range.mp ha)) hr)
  rcases kind_bool hsat (by rw [kinds_range]; exact List.mem_range.mpr (Finset.mem_range.mp ha)) hr with h | h
  · rw [h] at hne; simp at hne
  · exact h

/-! ### Transitions and decisions -/

omit hsat in
theorem ev_notFirst {r : ℕ} (hr : r + 1 < n) : notFirst.eval n preCols pub M (r + 1) = 1 := by
  simp [notFirst, pre, Expr.eval, preCols, PreCol.eval, wrap_zero (show r + 1 < n from hr), cst]

theorem trans_eq {X : ℕ} {fm : Expr} (h : trans X fm ∈ transC) {r : ℕ} (hr : r + 1 < n) :
    M X (r + 1) = fm.eval n preCols pub M (r + 1) := by
  have := sat hsat (mem_transC h) hr
  simp only [trans, Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ constraints) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat h hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem z_spec {z inv : ℕ} {e : Expr} (h : ∀ c ∈ isZero z inv e, c ∈ constraints) {r : ℕ} (hr : r < n) :
    (M z r = 0 ∨ M z r = 1) ∧ (M z r = 1 ↔ e.eval n preCols pub M r = 0) := by
  have h1 := sat hsat (h (boolC (k z)) (by simp [isZero])) hr
  have h2 := sat hsat (h (.mul (k z) e) (by simp [isZero])) hr
  have h3 := sat hsat (h (.mul (oneMinus (k z)) (.sub (.mul e (k inv)) one)) (by simp [isZero])) hr
  simp only [boolC, oneMinus, one, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at h1 h2 h3
  have hb : M z r = 0 ∨ M z r = 1 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  refine ⟨hb, ⟨fun hz => by rw [hz, one_mul] at h2; exact h2, fun he => ?_⟩⟩
  rcases hb with hz | hz
  · rw [hz, he] at h3; simp at h3
  · exact hz

theorem z1_spec {r : ℕ} (hr : r < n) : (M Z1 r = 0 ∨ M Z1 r = 1) ∧ (M Z1 r = 1 ↔ M E1C r = 0) := by
  have := z_spec hsat (z := Z1) (inv := INV1) (e := k E1C)
    (fun c hc => mem_zeroC (by simp only [zeroC, List.mem_append]; exact Or.inl (Or.inr hc))) hr
  simpa [ev_k hr] using this

theorem z2_spec {r : ℕ} (hr : r < n) : (M Z2 r = 0 ∨ M Z2 r = 1) ∧ (M Z2 r = 1 ↔ M E2C r = 0) := by
  have := z_spec hsat (z := Z2) (inv := INV2) (e := k E2C)
    (fun c hc => mem_zeroC (by simp only [zeroC, List.mem_append]; exact Or.inr hc)) hr
  simpa [ev_k hr] using this

theorem seg_bool {r : ℕ} (hr : r < n) : M SEG r = 0 ∨ M SEG r = 1 :=
  bool_of hsat (mem_segC (by simp [segC])) hr

/-- Kind columns at a row of known kind. -/
theorem kinds_at {r : ℕ} (hr : r < n) {a : ℕ} (ha : a < 9) (h : M a r = 1) :
    ∀ b < 9, M b r = if b = a then 1 else 0 := by
  intro b hb
  split_ifs with e
  · subst e; exact h
  · exact kind_unique hsat hr ha hb (Ne.symm e) h

theorem eoc_eq {r : ℕ} (hr : r < n) : M EOC r = (M K_NOUT r + M K_OUT r) * M Z1 r := by
  rw [defn hsat (e := .mul (.add (k K_NOUT) (k K_OUT)) (k Z1)) (mem_transC (by simp [transC])) hr]
  simp [Expr.eval, ev_k hr]

theorem esc_eq {r : ℕ} (hr : r < n) : M ESC r = (M K_WCNT r + M K_WITEM r) * M Z1 r := by
  rw [defn hsat (e := .mul (.add (k K_WCNT) (k K_WITEM)) (k Z1)) (mem_transC (by simp [transC])) hr]
  simp [Expr.eval, ev_k hr]

/-- The transition equations, at row `r + 1`. -/
theorem trans_all {r : ℕ} (hr : r + 1 < n) :
    M K_TXH (r + 1) = M K_BLK r + M K_LOCK r * (1 - M Z1 r) ∧
    M K_IN (r + 1) = M K_TXH r + M K_IN r * (1 - M Z1 r) ∧
    M K_NOUT (r + 1) = M K_IN r * M Z1 r ∧
    M K_OUT (r + 1) = (M K_NOUT r + M K_OUT r) * (1 - M Z1 r) ∧
    M K_WCNT (r + 1) = M EOC r * M SEG r + M ESC r * (1 - M Z2 r) ∧
    M K_WITEM (r + 1) = (M K_WCNT r + M K_WITEM r) * (1 - M Z1 r) ∧
    M K_LOCK (r + 1) = M EOC r * (1 - M SEG r) + M ESC r * M Z2 r ∧
    M K_PAD (r + 1) = M K_LOCK r * M Z1 r + M K_PAD r := by
  have hn := ev_notFirst (pub := pub) (M := M) hr
  have t := fun (X : ℕ) (fm : Expr) (h : trans X fm ∈ transC) => trans_eq hsat (X := X) (fm := fm) h hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [t K_TXH (.add (kp K_BLK) (.mul (kp K_LOCK) (oneMinus (kp Z1)))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_IN (.add (kp K_TXH) (.mul (kp K_IN) (oneMinus (kp Z1)))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_NOUT (.mul (kp K_IN) (kp Z1)) (by simp [transC])]
    simp [Expr.eval, ev_kp hr]
  · rw [t K_OUT (.mul (.add (kp K_NOUT) (kp K_OUT)) (oneMinus (kp Z1))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_WCNT (.add (.mul (kp EOC) (kp SEG)) (.mul (kp ESC) (oneMinus (kp Z2)))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_WITEM (.mul (.add (kp K_WCNT) (kp K_WITEM)) (oneMinus (kp Z1))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_LOCK (.add (.mul (kp EOC) (oneMinus (kp SEG))) (.mul (kp ESC) (kp Z2))) (by simp [transC])]
    simp [Expr.eval, ev_kp hr, oneMinus, one, eval_cst]
  · rw [t K_PAD (.add (.mul (kp K_LOCK) (kp Z1)) (.mul (kp K_PAD) notFirst)) (by simp [transC])]
    simp only [Expr.eval, ev_kp hr, hn, mul_one]

/-- **Next kinds.** -/
theorem next_kind {r : ℕ} (hr : r + 1 < n) :
    (M K_BLK r = 1 → M K_TXH (r + 1) = 1) ∧
    (M K_TXH r = 1 → M K_IN (r + 1) = 1) ∧
    (M K_IN r = 1 → M Z1 r = 0 → M K_IN (r + 1) = 1) ∧
    (M K_IN r = 1 → M Z1 r = 1 → M K_NOUT (r + 1) = 1) ∧
    (M K_NOUT r = 1 ∨ M K_OUT r = 1 → M Z1 r = 0 → M K_OUT (r + 1) = 1) ∧
    (M K_NOUT r = 1 ∨ M K_OUT r = 1 → M Z1 r = 1 → M SEG r = 1 → M K_WCNT (r + 1) = 1) ∧
    (M K_NOUT r = 1 ∨ M K_OUT r = 1 → M Z1 r = 1 → M SEG r = 0 → M K_LOCK (r + 1) = 1) ∧
    (M K_WCNT r = 1 ∨ M K_WITEM r = 1 → M Z1 r = 0 → M K_WITEM (r + 1) = 1) ∧
    (M K_WCNT r = 1 ∨ M K_WITEM r = 1 → M Z1 r = 1 → M Z2 r = 0 → M K_WCNT (r + 1) = 1) ∧
    (M K_WCNT r = 1 ∨ M K_WITEM r = 1 → M Z1 r = 1 → M Z2 r = 1 → M K_LOCK (r + 1) = 1) ∧
    (M K_LOCK r = 1 → M Z1 r = 0 → M K_TXH (r + 1) = 1) ∧
    (M K_LOCK r = 1 → M Z1 r = 1 → M K_PAD (r + 1) = 1) ∧
    (M K_PAD r = 1 → M K_PAD (r + 1) = 1) := by
  have hr0 : r < n := by omega
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩ := trans_all hsat hr
  have eo := eoc_eq hsat hr0
  have es := esc_eq hsat hr0
  have ka := fun {a : ℕ} (ha : a < 9) (h : M a r = 1) => kinds_at hsat hr0 ha h
  simp only [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD] at *
  refine ⟨fun h => ?_, fun h => ?_, fun h z => ?_, fun h z => ?_, fun h z => ?_, fun h z sg => ?_,
    fun h z sg => ?_, fun h z => ?_, fun h z z2 => ?_, fun h z z2 => ?_, fun h z => ?_, fun h z => ?_, fun h => ?_⟩
  all_goals first
    | (have k' := ka (by norm_num) h; simp [k'] at t1 t2 t3 t4 t5 t6 t7 t8 eo es; simp_all)
    | (rcases h with h | h <;> (have k' := ka (by norm_num) h; simp [k'] at t1 t2 t3 t4 t5 t6 t7 t8 eo es; simp_all))

/-! ### Range checks and CompactSize -/

/-- A 25-bit decomposition evaluates to a natural below `2^25`. -/
theorem bits25 {base : ℕ} (hb : ∀ j < 25, boolC (k (base + j)) ∈ constraints) {r : ℕ} (hr : r < n) :
    ∃ m : ℕ, m < 2 ^ 25 ∧ (sumPow (fun j => k (base + j)) 25).eval n preCols pub M r = (m : F) := by
  have bv : ∀ j < 25, M (base + j) r = ((M (base + j) r).val : F) ∧ (M (base + j) r).val ≤ 1 :=
    fun j hj => bool_val (bool_of hsat (hb j hj) hr)
  refine ⟨∑ j ∈ Finset.range 25, 2 ^ j * (if j < 25 then (M (base + j) r).val else 0),
    sum_bits_lt _ (fun j => by split_ifs with h; exact (bv j h).2; omega) 25, ?_⟩
  rw [Sha256.eval_sumPow]
  push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  rw [if_pos hj', ev_k hr, ← (bv j hj').1]

theorem cp_bool {c : ℕ} (hc : c = CP1 ∨ c = CP3 ∨ c = CP5 ∨ c = C4B0 ∨ c = C4B1) {r : ℕ} (hr : r < n) :
    M c r = 0 ∨ M c r = 1 :=
  bool_of hsat (mem_bitC (by rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [bitC])) hr

/-- The CompactSize form of a row (meaningful when it has one). -/
def prefOf (M : ℕ → ℕ → F) (r : ℕ) : ℕ := if M CP1 r = 1 then 1 else if M CP3 r = 1 then 3 else 5

theorem compact_eqs {r : ℕ} (hr : r < n) :
    M VAL r = M CP1 r * M (CB 0) r + (M CP3 r * (M (CB 1) r + 256 * M (CB 2) r) +
      M CP5 r * (M (CB 1) r + (256 * M (CB 2) r + (65536 * M (CB 3) r + 16777216 * M (CB 4) r)))) ∧
    M (CB 0) r = M CP1 r * M VAL r + (253 * M CP3 r + 254 * M CP5 r) ∧
    M CP1 r + (M CP3 r + M CP5 r) = 1 - (M K_LOCK r + M K_PAD r) ∧
    (∃ m : ℕ, m < 2 ^ 25 ∧ (m : F) = M CP1 r * (252 - M VAL r) + (M CP3 r * (M VAL r - 253) +
      M CP5 r * (M VAL r - 65536))) ∧
    (∃ m : ℕ, m < 2 ^ 25 ∧ (m : F) = M CP5 r * ((MAXS : ℕ) - M VAL r)) ∧
    M CP5 r * (M (CB 4) r - (M C4B0 r + 2 * M C4B1 r)) = 0 := by
  have c := fun (e : Expr) (h : e ∈ compactC) => sat hsat (mem_compactC h) hr
  have hv := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have h0 := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have hc := c _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have ha := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    List.mem_cons_self))))
  have hb := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))))
  have h4 := c _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))))
  obtain ⟨ma, hma, ea⟩ := bits25 hsat (base := 22) (fun j hj => mem_bitC (by
    simp only [bitC, List.mem_append, List.mem_flatMap, List.mem_range]; right; exact ⟨j, hj, by simp [RA]⟩)) hr
  obtain ⟨mb, hmb, eb⟩ := bits25 hsat (base := 47) (fun j hj => mem_bitC (by
    simp only [bitC, List.mem_append, List.mem_flatMap, List.mem_range]; right; exact ⟨j, hj, by simp [RB]⟩)) hr
  simp only [valE, hasC, oneMinus, one, k, Expr.eval, eval_col, eval_cst, wrap_zero hr, sub_eq_zero, MAXS] at hv h0 hc h4
  simp only [Expr.eval, sub_eq_zero] at ha hb
  have eA : (sumPow (fun j => k (RA j)) 25).eval n preCols pub M r = (ma : F) := by
    simpa [RA] using ea
  have eB : (sumPow (fun j => k (RB j)) 25).eval n preCols pub M r = (mb : F) := by
    simpa [RB] using eb
  rw [eA] at ha; rw [eB] at hb
  simp only [k, Expr.eval, eval_col, eval_cst, wrap_zero hr, MAXS] at ha hb
  push_cast at hv h0 hc ha hb h4 ⊢
  refine ⟨hv, h0, by linear_combination hc, ⟨ma, hma, ha⟩, ⟨mb, hmb, hb⟩, ?_⟩
  simpa [sub_eq_zero] using h4

/-- Exactly one CompactSize form on rows that have one. -/
theorem compact_form {r : ℕ} (hr : r < n) (hL : M K_LOCK r = 0) (hP : M K_PAD r = 0) :
    (M CP1 r = 1 ∧ M CP3 r = 0 ∧ M CP5 r = 0) ∨ (M CP1 r = 0 ∧ M CP3 r = 1 ∧ M CP5 r = 0) ∨
    (M CP1 r = 0 ∧ M CP3 r = 0 ∧ M CP5 r = 1) := by
  obtain ⟨-, -, hc, -⟩ := compact_eqs hsat hr
  rw [hL, hP] at hc
  have v1 := bool_val (cp_bool hsat (c := CP1) (by simp) hr)
  have v3 := bool_val (cp_bool hsat (c := CP3) (by simp) hr)
  have v5 := bool_val (cp_bool hsat (c := CP5) (by simp) hr)
  have hs : (M CP1 r).val + (M CP3 r).val + (M CP5 r).val = 1 := by
    refine natCast_inj_of_lt ?_ (by unfold P; norm_num) ?_
    · have := v1.2; have := v3.2; have := v5.2; exact lt_P (by omega)
    · push_cast; rw [← v1.1, ← v3.1, ← v5.1]; linear_combination hc
  have z : ∀ x : F, x.val = 0 → x = 0 := fun x h => (ZMod.val_eq_zero x).mp h
  have o : ∀ x : F, x.val = 1 → x = 1 := fun x h => by rw [← ZMod.natCast_zmod_val x, h]; simp
  rcases (by omega : ((M CP1 r).val = 1 ∧ (M CP3 r).val = 0 ∧ (M CP5 r).val = 0) ∨
      ((M CP1 r).val = 0 ∧ (M CP3 r).val = 1 ∧ (M CP5 r).val = 0) ∨
      ((M CP1 r).val = 0 ∧ (M CP3 r).val = 0 ∧ (M CP5 r).val = 1)) with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩
  · exact Or.inl ⟨o _ a, z _ b, z _ c⟩
  · exact Or.inr (Or.inl ⟨z _ a, o _ b, z _ c⟩)
  · exact Or.inr (Or.inr ⟨z _ a, z _ b, o _ c⟩)

/-- **CompactSize.** A row with a CompactSize (not locktime, not padding) whose read bytes are
bytes holds a value at most `MAX_SIZE`, and those bytes are its canonical serialization. -/
theorem compact_ser {r : ℕ} (hr : r < n) (hL : M K_LOCK r = 0) (hP : M K_PAD r = 0)
    (hb : ∀ j < prefOf M r, (M (CB j) r).val < 256) :
    (M VAL r).val ≤ MAXS ∧
    (List.range (prefOf M r)).map (fun j => UInt8.ofNat (M (CB j) r).val) = Spec.Block.serCompact (M VAL r).val := by
  obtain ⟨hv, h0, -, ⟨ma, hma, ha⟩, ⟨mb, hmb, hbb⟩, h4⟩ := compact_eqs hsat hr
  have cast_lt : ∀ m : ℕ, m < P → ((m : ℕ) : F).val = m := fun m hm => by rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm]
  have e : ∀ x : F, x = ((x.val : ℕ) : F) := fun x => (ZMod.natCast_zmod_val x).symm
  rcases compact_form hsat hr hL hP with ⟨c1, c3, c5⟩ | ⟨c1, c3, c5⟩ | ⟨c1, c3, c5⟩
  · -- 1 byte.
    have pf : prefOf M r = 1 := by simp [prefOf, c1]
    rw [pf] at hb ⊢
    simp only [c1, c3, c5, zero_mul, one_mul, zero_add, add_zero, mul_zero] at hv h0 ha
    have hb0 := hb 0 (by norm_num)
    have hvv : (M VAL r).val = (M (CB 0) r).val := by rw [hv]
    have hle := val_of_sub_left (a := 252) (by rw [ha]; push_cast; ring) hma (by norm_num) (by rw [hvv]; omega)
    refine ⟨by unfold MAXS; omega, ?_⟩
    unfold Spec.Block.serCompact
    rw [if_pos (by omega)]
    simp [hvv]
  · -- 3 bytes.
    have pf : prefOf M r = 3 := by simp [prefOf, c1, c3]
    rw [pf] at hb ⊢
    simp only [c1, c3, c5, zero_mul, one_mul, zero_add, add_zero, mul_zero] at hv h0 ha
    have hb1 := hb 1 (by norm_num); have hb2 := hb 2 (by norm_num)
    have hvv : (M VAL r).val = (M (CB 1) r).val + 256 * (M (CB 2) r).val := by
      refine val_lt_of_eq_cast ?_ (lt_P (by omega))
      rw [hv, e (M (CB 1) r), e (M (CB 2) r)]; push_cast; simp
    have lo := val_of_sub_right (x := M VAL r) (a := 253) (by rw [ha]; push_cast; ring) hma (by norm_num)
    have hcb0 : (M (CB 0) r).val = 253 := by rw [h0]; exact cast_lt 253 (by unfold P; norm_num)
    refine ⟨by unfold MAXS; omega, ?_⟩
    unfold Spec.Block.serCompact Spec.Block.leBytes
    rw [if_neg (by omega), if_pos (by omega)]
    simp only [List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.map_append,
      List.cons_append, hcb0]
    simp only [List.cons.injEq, and_true]
    refine ⟨rfl, u8_eq (by simp; omega), u8_eq (by simp; omega)⟩
  · -- 5 bytes.
    have pf : prefOf M r = 5 := by simp [prefOf, c1, c3]
    rw [pf] at hb ⊢
    simp only [c1, c3, c5, zero_mul, one_mul, zero_add, add_zero, mul_zero] at hv h0 ha hbb h4
    have q0 := bool_val (cp_bool hsat (c := C4B0) (by simp) hr)
    have q1 := bool_val (cp_bool hsat (c := C4B1) (by simp) hr)
    have b4le : (M (CB 4) r).val ≤ 3 := by
      have : M (CB 4) r = (((M C4B0 r).val + 2 * (M C4B1 r).val : ℕ) : F) := by
        rw [sub_eq_zero] at h4; rw [h4]; push_cast; rw [← q0.1, ← q1.1]
      have hv4 : (M (CB 4) r).val = (M C4B0 r).val + 2 * (M C4B1 r).val :=
        val_lt_of_eq_cast this (by have := q0.2; have := q1.2; exact lt_P (by omega))
      have := q0.2; have := q1.2; omega
    have hb1 := hb 1 (by norm_num); have hb2 := hb 2 (by norm_num); have hb3 := hb 3 (by norm_num)
    have hvv : (M VAL r).val = (M (CB 1) r).val + 256 * (M (CB 2) r).val + 65536 * (M (CB 3) r).val +
        16777216 * (M (CB 4) r).val := by
      refine val_lt_of_eq_cast ?_ (lt_P (by omega))
      rw [hv, e (M (CB 1) r), e (M (CB 2) r), e (M (CB 3) r), e (M (CB 4) r)]; push_cast; simp; ring
    have lo := val_of_sub_right (x := M VAL r) (a := 65536) (by rw [ha]; push_cast; ring) hma (by norm_num)
    have hi := val_of_sub_left (a := MAXS) (by rw [hbb]) hmb (by unfold MAXS; norm_num) (by rw [hvv]; omega)
    have hcb0 : (M (CB 0) r).val = 254 := by rw [h0]; exact cast_lt 254 (by unfold P; norm_num)
    refine ⟨by omega, ?_⟩
    unfold Spec.Block.serCompact Spec.Block.leBytes
    rw [if_neg (by omega), if_neg (by omega), if_pos (by unfold MAXS at hi; omega)]
    simp only [List.range_succ, List.range_zero, List.map_nil, List.map_cons, List.nil_append, List.map_append,
      List.cons_append, hcb0]
    simp only [List.cons.injEq, and_true]
    refine ⟨rfl, u8_eq (by simp; omega), u8_eq (by simp; omega), u8_eq (by simp; omega), u8_eq (by simp; omega)⟩

/-! ### Row values and tiling -/

theorem len_eq {r : ℕ} (hr : r < n) : M LEN r =
    M K_BLK r * (80 + (M CP1 r + (3 * M CP3 r + 5 * M CP5 r))) +
    (M K_TXH r * (4 + 2 * M SEG r + (M CP1 r + (3 * M CP3 r + 5 * M CP5 r))) +
    (M K_IN r * (40 + (M CP1 r + (3 * M CP3 r + 5 * M CP5 r)) + M VAL r) +
    (M K_NOUT r * (M CP1 r + (3 * M CP3 r + 5 * M CP5 r)) +
    (M K_OUT r * (8 + (M CP1 r + (3 * M CP3 r + 5 * M CP5 r)) + M VAL r) +
    (M K_WCNT r * (M CP1 r + (3 * M CP3 r + 5 * M CP5 r)) +
    (M K_WITEM r * ((M CP1 r + (3 * M CP3 r + 5 * M CP5 r)) + M VAL r) +
    M K_LOCK r * 4)))))) := by
  rw [defn hsat (a := LEN) (e := lenE) (mem_tileC (by simp [tileC])) hr]
  simp [lenE, pref, Expr.eval, ev_k hr, eval_cst]

theorem off_eq {r : ℕ} (hr : r < n) : M OFF r =
    M K_BLK r * 80 + (M K_TXH r * (4 + 2 * M SEG r) + (M K_IN r * 36 + M K_OUT r * 8)) := by
  rw [defn hsat (a := OFF) (e := offE) (mem_compactC (by simp [compactC])) hr]
  simp [offE, Expr.eval, ev_k hr, eval_cst]

theorem e1_eq {r : ℕ} (hr : r < n) : M E1C r =
    M K_BLK r * M VAL r + (M K_TXH r * M VAL r + (M K_IN r * (M INL r - 1) + (M K_NOUT r * M VAL r +
    (M K_OUT r * (M OUTL r - 1) + (M K_WCNT r * M VAL r + (M K_WITEM r * (M ITEML r - 1) +
    M K_LOCK r * M TXL r)))))) := by
  rw [defn hsat (a := E1C) (e := e1) (mem_zeroC (by simp [zeroC])) hr]
  simp [e1, one, Expr.eval, ev_k hr, eval_cst]

theorem e2_eq {r : ℕ} (hr : r < n) : M E2C r =
    (M K_WCNT r + M K_WITEM r) * (M WINL r - 1) + M K_LOCK r * M HASW r := by
  rw [defn hsat (a := E2C) (e := e2) (mem_zeroC (by simp [zeroC])) hr]
  simp [e2, one, Expr.eval, ev_k hr, eval_cst]

theorem start_lt {r : ℕ} (hr : r < n) : (M START r).val < 2 ^ 25 := by
  obtain ⟨m, hm, e⟩ := bits25 hsat (base := 72) (fun j hj => mem_bitC (by
    simp only [bitC, List.mem_append, List.mem_flatMap, List.mem_range]; right; exact ⟨j, hj, by simp [RS]⟩)) hr
  have := defn hsat (a := START) (e := sumPow (fun j => k (RS j)) 25) (mem_tileC (by simp [tileC])) hr
  rw [show (fun j => k (RS j)) = (fun j => k (72 + j)) from rfl, e] at this
  rw [val_lt_of_eq_cast this (lt_P (by omega))]; exact hm

theorem start_zero (hn : 0 < n) : M START 0 = 0 := by
  have := sat hsat (mem_tileC (c := .mul first (k START)) (by simp [tileC])) hn
  simpa [Expr.eval, ev_first hn, ev_k hn] using this

theorem start_succ {r : ℕ} (hr : r + 1 < n) : M START (r + 1) = M START r + M LEN r := by
  have := sat hsat (mem_tileC (c := .mul notFirst (.sub (k START) (.add (kp START) (kp LEN))))
    (by simp [tileC])) hr
  simp only [Expr.eval, ev_notFirst hr, ev_k hr, ev_kp hr, one_mul, sub_eq_zero] at this
  exact this

theorem pad_start {r : ℕ} (hr : r < n) (h : M K_PAD r = 1) : M START r = pub 0 := by
  have := sat hsat (mem_tileC (c := .mul (k K_PAD) (.sub (k START) LENPUB)) (by simp [tileC])) hr
  simp only [Expr.eval, ev_k hr, LENPUB, h, one_mul, sub_eq_zero] at this
  exact this

theorem last_pad (hn : 0 < n) : M K_PAD (n - 1) = 1 := by
  have hl : n - 1 < n := by omega
  have := sat hsat (mem_kindC (c := .mul isLast (oneMinus (k K_PAD))) (by simp [kindC])) hl
  simp only [Expr.eval, ev_last hl, show ¬ (n - 1 + 1 < n) by omega, if_false, one_mul, oneMinus, one, eval_cst,
    ev_k hl, Nat.cast_one, sub_eq_zero] at this
  exact this.symm

theorem first_blk (hn : 0 < n) : M K_BLK 0 = 1 := by
  have := defn hsat (a := K_BLK) (e := first) (mem_kindC (by simp [kindC])) hn
  rw [this, ev_first hn]; simp

theorem not_blk {r : ℕ} (hr : r + 1 < n) : M K_BLK (r + 1) = 0 := by
  have := defn hsat (a := K_BLK) (e := first) (mem_kindC (by simp [kindC])) hr
  rw [this, ev_first hr]; simp

/-! ### Counters -/

/-- The counter constraints as equations (`c` a member of `countC` or `segC`). -/
theorem cnt {e : Expr} (h : e ∈ countC) {r : ℕ} (hr : r < n) : e.eval n preCols pub M r = 0 :=
  sat hsat (mem_countC h) hr

theorem counters {r : ℕ} (hr : r + 1 < n) :
    -- row r + 1 from row r
    M TXL (r + 1) = M TXL r - M K_LOCK r ∧
    (M K_TXH (r + 1) = 0 → M INL (r + 1) = M INL r - M K_IN r) ∧
    (M K_TXH (r + 1) = 0 → M NIN (r + 1) = M NIN r) ∧
    (M K_NOUT (r + 1) = 0 → M OUTL (r + 1) = M OUTL r - M K_OUT r) ∧
    (M EOC r = 1 → M WINL (r + 1) = M NIN (r + 1)) ∧
    (M EOC r = 0 → M WINL (r + 1) = M WINL r - M ESC r) ∧
    (M K_WCNT (r + 1) = 0 → M ITEML (r + 1) = M ITEML r - M K_WITEM r) ∧
    (M K_TXH (r + 1) = 0 → M SEG (r + 1) = M SEG r) ∧
    (M K_TXH (r + 1) = 0 → M HASW (r + 1) = M HASW r + M K_WCNT r * (1 - M Z1 r)) := by
  have hr0 : r < n := by omega
  have hn := ev_notFirst (pub := pub) (M := M) hr
  have c := fun (e : Expr) (h : e ∈ countC) => cnt hsat h hr
  have sg := fun (e : Expr) (h : e ∈ segC) => sat hsat (mem_segC h) hr
  refine ⟨?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := c (.mul notFirst (.add (.sub (k TXL) (kp TXL)) (kp K_LOCK))) (by simp [countC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, one_mul] at this; linear_combination this
  · have := c (.mul (oneMinus (k K_TXH)) (.mul notFirst (.add (.sub (k INL) (kp INL)) (kp K_IN)))) (by simp [countC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))
  · have := c (.mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k NIN) (kp NIN)))) (by simp [countC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))
  · have := c (.mul (oneMinus (k K_NOUT)) (.mul notFirst (.add (.sub (k OUTL) (kp OUTL)) (kp K_OUT)))) (by simp [countC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))
  · have := c (.mul (kp EOC) (.sub (k WINL) (k NIN))) (by simp [countC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, h, one_mul] at this; linear_combination this
  · have := c (.mul (oneMinus (kp EOC)) (.add (.sub (k WINL) (kp WINL)) (kp ESC))) (by simp [countC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h, sub_zero, one_mul] at this
    linear_combination this
  · have := c (.mul (oneMinus (k K_WCNT)) (.mul notFirst (.add (.sub (k ITEML) (kp ITEML)) (kp K_WITEM)))) (by simp [countC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))
  · have := sg (.mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k SEG) (kp SEG)))) (by simp [segC])
    simp only [Expr.eval, hn, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))
  · have := sg (.mul (oneMinus (k K_TXH)) (.sub (k HASW) (.add (kp HASW) (.mul (kp K_WCNT) (oneMinus (kp Z1))))))
      (by simp [segC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, oneMinus, one, eval_cst, Nat.cast_one, h] at this
    linear_combination (by simpa using this : _ = (0 : F))

/-- Values set on a row by its own kind. -/
theorem row_sets {r : ℕ} (hr : r < n) :
    (M K_BLK r = 1 → M TXL r = M VAL r - 1 ∧ M Z1 r = 0) ∧
    (M K_TXH r = 1 → M INL r = M VAL r ∧ M NIN r = M VAL r ∧ M HASW r = 0 ∧ M Z1 r = 0) ∧
    (M K_NOUT r = 1 → M OUTL r = M VAL r) ∧
    (M K_WCNT r = 1 → M ITEML r = M VAL r) ∧
    (M K_LOCK r = 1 → M SEG r = 1 → M Z2 r = 0) := by
  have c := fun (e : Expr) (h : e ∈ countC) => cnt hsat h hr
  have sg := fun (e : Expr) (h : e ∈ segC) => sat hsat (mem_segC h) hr
  have ev : ∀ x : ℕ, (k x).eval n preCols pub M r = M x r := fun x => ev_k hr
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_, ?_, ?_⟩, fun h => ?_, fun h => ?_, fun h hs => ?_⟩
  · have := c (.mul (k K_BLK) (.add (.sub (k TXL) (k VAL)) one)) (by simp [countC])
    simp only [Expr.eval, ev, h, one_mul, one, eval_cst, Nat.cast_one] at this; linear_combination this
  · have := c (.mul (k K_BLK) (k Z1)) (by simp [countC])
    simpa [Expr.eval, ev, h] using this
  · have := c (.mul (k K_TXH) (.sub (k INL) (k VAL))) (by simp [countC])
    simp only [Expr.eval, ev, h, one_mul] at this; linear_combination this
  · have := c (.mul (k K_TXH) (.sub (k NIN) (k VAL))) (by simp [countC])
    simp only [Expr.eval, ev, h, one_mul] at this; linear_combination this
  · have := sg (.mul (k K_TXH) (k HASW)) (by simp [segC])
    simpa [Expr.eval, ev, h] using this
  · have := c (.mul (k K_TXH) (k Z1)) (by simp [countC])
    simpa [Expr.eval, ev, h] using this
  · have := c (.mul (k K_NOUT) (.sub (k OUTL) (k VAL))) (by simp [countC])
    simp only [Expr.eval, ev, h, one_mul] at this; linear_combination this
  · have := c (.mul (k K_WCNT) (.sub (k ITEML) (k VAL))) (by simp [countC])
    simp only [Expr.eval, ev, h, one_mul] at this; linear_combination this
  · have := sg (.mul (k K_LOCK) (.mul (k SEG) (k Z2))) (by simp [segC])
    simpa [Expr.eval, ev, h, hs] using this

/-- Rows without a CompactSize have every form bit 0. -/
theorem no_compact {r : ℕ} (hr : r < n) (h : M K_LOCK r + M K_PAD r = 1) :
    M CP1 r = 0 ∧ M CP3 r = 0 ∧ M CP5 r = 0 := by
  obtain ⟨-, -, hc, -⟩ := compact_eqs hsat hr
  rw [h, sub_self] at hc
  have v1 := bool_val (cp_bool hsat (c := CP1) (by simp) hr)
  have v3 := bool_val (cp_bool hsat (c := CP3) (by simp) hr)
  have v5 := bool_val (cp_bool hsat (c := CP5) (by simp) hr)
  have hs : (M CP1 r).val + (M CP3 r).val + (M CP5 r).val = 0 := by
    refine natCast_inj_of_lt ?_ (by unfold P; norm_num) ?_
    · have := v1.2; have := v3.2; have := v5.2; exact lt_P (by omega)
    · push_cast; rw [← v1.1, ← v3.1, ← v5.1]; linear_combination hc
  exact ⟨(ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega)⟩

theorem lock_pad {r : ℕ} (hr : r < n) : M K_LOCK r + M K_PAD r = 0 ∨ M K_LOCK r + M K_PAD r = 1 := by
  have hs := kind_sumN hsat hr
  have := Finset.add_le_sum (f := fun c => (M c r).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show K_LOCK < 9 by simp [K_LOCK])) (Finset.mem_range.mpr (show K_PAD < 9 by simp [K_PAD]))
    (by simp [K_LOCK, K_PAD])
  have bl := kind_bool hsat (c := K_LOCK) (by simp [kinds]) hr
  have bp := kind_bool hsat (c := K_PAD) (by simp [kinds]) hr
  have one_val : (1 : F).val = 1 := ZMod.val_one P
  rcases bl with h1 | h1 <;> rcases bp with h2 | h2
  · left; rw [h1, h2]; ring
  · right; rw [h1, h2]; ring
  · right; rw [h1, h2]; ring
  · exfalso; rw [h1, h2, one_val] at this; omega

theorem cp35 {r : ℕ} (hr : r < n) :
    (M K_LOCK r + M K_PAD r = 1 → M CP1 r = 0 ∧ M CP3 r = 0 ∧ M CP5 r = 0) ∧
    (M K_LOCK r + M K_PAD r = 0 → (M CP1 r = 1 ∧ M CP3 r = 0 ∧ M CP5 r = 0) ∨ (M CP1 r = 0 ∧ M CP3 r = 1 ∧ M CP5 r = 0) ∨
      (M CP1 r = 0 ∧ M CP3 r = 0 ∧ M CP5 r = 1)) := by
  refine ⟨no_compact hsat hr, fun h => ?_⟩
  have bl := kind_bool hsat (c := K_LOCK) (by simp [kinds]) hr
  have bp := kind_bool hsat (c := K_PAD) (by simp [kinds]) hr
  have two : (1 : F) + 1 ≠ 0 := by
    intro e; have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num)
      (by push_cast; linear_combination e)
    omega
  have hL : M K_LOCK r = 0 := by
    rcases bl with h1 | h1
    · exact h1
    · exfalso
      rcases bp with h2 | h2 <;> rw [h1, h2] at h
      · simp at h
      · exact two h
  have hP : M K_PAD r = 0 := by rw [hL, zero_add] at h; exact h
  exact compact_form hsat hr hL hP

/-- Every lookup's multiplicity is `−1` or `0`. -/
theorem mult_vals {r : ℕ} (hr : r < n) {kk : ℕ} (hk : kk < 7) :
    ((lookups.getD kk ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 ∨
     (lookups.getD kk ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = 0) := by
  have sb := seg_bool hsat hr
  have tb := kind_bool hsat (c := K_TXH) (by simp [kinds]) hr
  obtain ⟨c1, c2⟩ := cp35 hsat hr
  have txs : M K_TXH r * M SEG r = 0 ∨ M K_TXH r * M SEG r = 1 := by
    rcases tb with h | h <;> rcases sb with g | g <;> simp [h, g]
  rcases lock_pad hsat hr with hc | hc
  · rcases c2 hc with ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ <;>
    interval_cases kk <;>
      simp only [lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, ev_k hr, hasC, oneMinus, one,
        eval_cst, Nat.cast_one, f1, f3, f5, hc] <;>
      rcases txs with ht | ht <;> simp [ht]
  · obtain ⟨f1, f3, f5⟩ := c1 hc
    interval_cases kk <;>
      simp only [lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, ev_k hr, hasC, oneMinus, one,
        eval_cst, Nat.cast_one, f1, f3, f5, hc] <;>
      rcases txs with ht | ht <;> simp [ht]

/-- The CompactSize offset of kind `a` (`seg` for transaction heads). -/
def offN (a seg : ℕ) : ℕ :=
  if a = K_BLK then 80 else if a = K_TXH then 4 + 2 * seg else if a = K_IN then 36 else if a = K_OUT then 8 else 0

/-- The row length of kind `a` with CompactSize length `p` and value `v`. -/
def lenN (a seg p v : ℕ) : ℕ :=
  if a = K_BLK then 80 + p else if a = K_TXH then 4 + 2 * seg + p else if a = K_IN then 40 + p + v
  else if a = K_NOUT then p else if a = K_OUT then 8 + p + v else if a = K_WCNT then p
  else if a = K_WITEM then p + v else if a = K_LOCK then 4 else 0

theorem pref_cast {r : ℕ} (hr : r < n) :
    M CP1 r + (3 * M CP3 r + 5 * M CP5 r) =
      ((if M K_LOCK r + M K_PAD r = 0 then prefOf M r else 0 : ℕ) : F) := by
  rcases lock_pad hsat hr with hc | hc
  · rw [if_pos hc]
    rcases (cp35 hsat hr).2 hc with ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ <;>
      simp [prefOf, f1, f3, f5] <;> norm_num
  · rw [if_neg (by rw [hc]; exact one_ne_zero)]
    obtain ⟨f1, f3, f5⟩ := (cp35 hsat hr).1 hc
    simp [f1, f3, f5]

/-- **Offsets and lengths by kind**, as naturals. -/
theorem kind_vals {r : ℕ} (hr : r < n) {a : ℕ} (ha : a < 9) (h : M a r = 1) :
    M OFF r = ((offN a (M SEG r).val : ℕ) : F) ∧
    M LEN r = ((lenN a (M SEG r).val (if a = K_LOCK ∨ a = K_PAD then 0 else prefOf M r) (M VAL r).val : ℕ) : F) := by
  have ka := kinds_at hsat hr ha h
  have sv := (bool_val (seg_bool hsat hr)).1
  have pc := pref_cast hsat hr
  rw [off_eq hsat hr, len_eq hsat hr, pc]
  have hLP : M K_LOCK r + M K_PAD r = if a = K_LOCK ∨ a = K_PAD then 1 else 0 := by
    rw [ka K_LOCK (by simp [K_LOCK]), ka K_PAD (by simp [K_PAD])]
    by_cases h7 : a = K_LOCK
    · subst h7; simp [K_LOCK, K_PAD]
    · by_cases h8 : a = K_PAD
      · subst h8; simp [K_LOCK, K_PAD]
      · simp [Ne.symm h7, Ne.symm h8, h7, h8]
  rw [hLP]
  rw [ka K_BLK (by simp [K_BLK]), ka K_TXH (by simp [K_TXH]), ka K_IN (by simp [K_IN]), ka K_NOUT (by simp [K_NOUT]),
    ka K_OUT (by simp [K_OUT]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM]),
    ka K_LOCK (by simp [K_LOCK])]
  conv_lhs => skip
  interval_cases a <;>
    simp [offN, lenN, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD] <;>
    rw [sv] <;> push_cast <;> ring_nf <;> simp

theorem z1_iff_val {r : ℕ} (hr : r < n) {x : F} {k : ℕ} (he : M E1C r = x - 1) (hx : x.val = k + 1) :
    (M Z1 r = 1 ↔ k = 0) := by
  rw [(z1_spec hsat hr).2, he]
  constructor
  · intro h; have := val_pred hx; rw [h, ZMod.val_zero] at this; omega
  · intro h; subst h; rw [← ZMod.natCast_zmod_val x, hx]; simp

theorem z1_iff_val0 {r : ℕ} (hr : r < n) {x : F} (he : M E1C r = x) (hx : x.val < P) :
    (M Z1 r = 1 ↔ x.val = 0) := by
  rw [(z1_spec hsat hr).2, he, ZMod.val_eq_zero]

/-- Transaction-level values carry from row `r` to `r + 1` when no transaction starts or ends and
no non-empty witness stack opens. -/
theorem step_inv {r : ℕ} (hr1 : r + 1 < n) (hnT : M K_TXH (r + 1) = 0) (hnL : M K_LOCK r = 0)
    (hW : M K_WCNT r * (1 - M Z1 r) = 0) :
    M SEG (r + 1) = M SEG r ∧ M NIN (r + 1) = M NIN r ∧ M TXL (r + 1) = M TXL r ∧ M HASW (r + 1) = M HASW r := by
  obtain ⟨c1, -, c3, -, -, -, -, c8, c9⟩ := counters hsat hr1
  exact ⟨c8 hnT, c3 hnT, by rw [c1, hnL, sub_zero], by rw [c9 hnT, hW, add_zero]⟩

end Rows

end StarkedAir.Block.Fields

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow eval_col eval_cst wrap_back)

/-! ### Slices -/

/-- Bytes `[a, a + b)` of `R`. -/
def slice (R : Spec.Block.Bytes) (a b : ℕ) : Spec.Block.Bytes := (R.drop a).take b

theorem slice_length {R : Spec.Block.Bytes} {a b : ℕ} (h : a + b ≤ R.length) : (slice R a b).length = b := by
  simp [slice]; omega

theorem slice_append {R : Spec.Block.Bytes} {a b c : ℕ} (h : a + b + c ≤ R.length) :
    slice R a b ++ slice R (a + b) c = slice R a (b + c) := by
  unfold slice
  rw [List.take_add, List.drop_drop]

theorem slice_eq_map {R : Spec.Block.Bytes} {a b : ℕ} (h : a + b ≤ R.length) :
    slice R a b = (List.range b).map (fun j => R.getD (a + j) 0) := by
  apply List.ext_getElem (by rw [slice_length h]; simp)
  intro j h1 h2
  simp only [slice, List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp at h2; omega)]

theorem slice_zero {R : Spec.Block.Bytes} : slice R 0 R.length = R := by simp [slice]

/-- The block's bytes, read from the byte table. -/
def blockBytes (Mb : ℕ → ℕ → F) (len : ℕ) : Spec.Block.Bytes := (List.range len).map fun i => UInt8.ofNat (Mb BYTE i).val

theorem blockBytes_length (Mb : ℕ → ℕ → F) (len : ℕ) : (blockBytes Mb len).length = len := by simp [blockBytes]

theorem blockBytes_get {Mb : ℕ → ℕ → F} {len i : ℕ} (h : i < len) :
    (blockBytes Mb len).getD i 0 = UInt8.ofNat (Mb BYTE i).val := by
  rw [List.getD_eq_getElem _ _ (by simp [blockBytes]; exact h)]; simp [blockBytes]

/-- Row `r`'s token, from its columns and the block bytes `R`. -/
def tokOf (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) : Spec.Block.Tok :=
  let s := (M START r).val
  let v := (M VAL r).val
  let p := prefOf M r
  if M K_BLK r = 1 then .blk (slice R s 80) v
  else if M K_TXH r = 1 then .txh (slice R s 4) (decide (M SEG r = 1)) v
  else if M K_IN r = 1 then .inp (slice R s 32) (slice R (s + 32) 4) (slice R (s + 36 + p) v) (slice R (s + 36 + p + v) 4)
  else if M K_NOUT r = 1 then .nout v
  else if M K_OUT r = 1 then .out (slice R s 8) (slice R (s + 8 + p) v)
  else if M K_WCNT r = 1 then .wcnt v
  else if M K_WITEM r = 1 then .witem (slice R (s + p) v)
  else .lock (slice R s 4)

/-! ### Tokens serialize to their slices -/

section Tokens

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  (hmk : ∀ r < n, M K_TXH r = 1 → M SEG r = 1 →
    (M START r).val + 5 < R.length ∧ R.getD ((M START r).val + 4) 0 = 0 ∧ R.getD ((M START r).val + 5) 0 = 1)
include hsat hcs hmk

/-- **A row's token serializes to its slice of the block.** -/
theorem tok_bytes {r : ℕ} (hr : r < n) (hnp : M K_PAD r = 0)
    (hfit : (M START r).val + (M LEN r).val ≤ R.length) :
    Spec.Block.Tok.bytes (tokOf M R r) = slice R (M START r).val (M LEN r).val := by
  obtain ⟨a, ha, h1⟩ := kind_exists hsat hr
  have ka := kinds_at hsat hr ha h1
  obtain ⟨hoff, hlen⟩ := kind_vals hsat hr ha h1
  have sb := seg_bool hsat hr
  have hlenv : ∀ l : ℕ, M LEN r = (l : F) → l ≤ 2 ^ 27 → (M LEN r).val = l :=
    fun l h hl => val_lt_of_eq_cast h (lt_P (by omega))
  have pb : 1 ≤ prefOf M r ∧ prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
  have kz : ∀ c < 9, c ≠ a → M c r = 0 := fun c hc hne => by rw [ka c hc, if_neg hne]
  interval_cases a <;>
    simp only [offN, lenN, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD] at hoff hlen h1 kz ⊢ <;>
    norm_num at hoff hlen
  · -- BLK
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨b1, -, b3⟩ := hcs r hr hLP 80 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (80 + prefOf M r) (by rw [hlen]; push_cast [ZMod.natCast_zmod_val]; try ring) (by omega)
    simp only [tokOf, K_BLK, h1, if_true, Spec.Block.Tok.bytes, hl]
    rw [b3, slice_append (by omega)]
  · -- TXH
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    have b0 : M 0 r = 0 := kz 0 (by norm_num) (by norm_num)
    rcases sb with sg | sg
    · obtain ⟨b1, -, b3⟩ := hcs r hr hLP 4 (by rw [hoff, sg]; norm_num) (by norm_num)
      have hl := hlenv (4 + prefOf M r) (by rw [hlen, sg]; push_cast; ring) (by omega)
      simp only [tokOf, K_BLK, K_TXH, b0, h1, zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, hl, sg,
        decide_false, Bool.false_eq_true, List.append_nil]
      rw [b3, slice_append (by omega)]
    · obtain ⟨b1, -, b3⟩ := hcs r hr hLP 6 (by rw [hoff, sg]; norm_num) (by norm_num)
      have hl := hlenv (6 + prefOf M r) (by rw [hlen, sg]; push_cast; ring) (by omega)
      obtain ⟨m5, m0, m1⟩ := hmk r hr h1 sg
      have mk : ([0, 1] : Spec.Block.Bytes) = slice R ((M START r).val + 4) 2 := by
        rw [slice_eq_map (by omega)]
        simp [List.range_succ, show (M START r).val + 4 + 1 = (M START r).val + 5 by ring]
        exact ⟨by rw [← List.getD_eq_getElem?_getD, m0], by rw [← List.getD_eq_getElem?_getD, m1]⟩
      simp only [tokOf, K_BLK, K_TXH, b0, h1, zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, hl, sg,
        decide_true]
      rw [mk, b3, slice_append (by omega), show (M START r).val + 4 + 2 = (M START r).val + 6 by ring,
        slice_append (by omega)]
  · -- IN
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨c1, cv, c3⟩ := hcs r hr hLP 36 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (40 + prefOf M r + (M VAL r).val) (by rw [hlen]; push_cast [ZMod.natCast_zmod_val]; try ring) (by unfold MAXS at cv; omega)
    rw [hl] at hfit ⊢
    simp only [tokOf, K_BLK, K_TXH, K_IN, kz 0 (by norm_num) (by norm_num), kz 1 (by norm_num) (by norm_num), h1,
      zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, Spec.Block.serVarBytes,
      slice_length (show (M START r).val + 36 + prefOf M r + (M VAL r).val ≤ R.length by omega)]
    rw [c3]
    set s0 := (M START r).val
    set p0 := prefOf M r
    set v0 := (M VAL r).val
    rw [slice_append (a := s0 + 36) (b := p0) (c := v0) (by omega), slice_append (a := s0) (b := 32) (c := 4) (by omega),
      show s0 + 36 = s0 + (32 + 4) by ring, slice_append (a := s0) (b := 32 + 4) (c := p0 + v0) (by omega),
      show s0 + (32 + 4) + p0 + v0 = s0 + (32 + 4 + (p0 + v0)) by ring,
      slice_append (a := s0) (b := 32 + 4 + (p0 + v0)) (c := 4) (by omega)]
    congr 1; ring
  · -- NOUT
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨-, -, c3⟩ := hcs r hr hLP 0 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (prefOf M r) (by rw [hlen]) (by omega)
    simp only [tokOf, K_BLK, K_TXH, K_IN, K_NOUT, kz 0 (by norm_num) (by norm_num), kz 1 (by norm_num) (by norm_num),
      kz 2 (by norm_num) (by norm_num), h1, zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, hl]
    rw [c3, Nat.add_zero]
  · -- OUT
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨c1, cv, c3⟩ := hcs r hr hLP 8 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (8 + prefOf M r + (M VAL r).val) (by rw [hlen]; push_cast [ZMod.natCast_zmod_val]; try ring) (by unfold MAXS at cv; omega)
    rw [hl] at hfit ⊢
    simp only [tokOf, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, kz 0 (by norm_num) (by norm_num),
      kz 1 (by norm_num) (by norm_num), kz 2 (by norm_num) (by norm_num), kz 3 (by norm_num) (by norm_num), h1,
      zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, Spec.Block.serVarBytes,
      slice_length (show (M START r).val + 8 + prefOf M r + (M VAL r).val ≤ R.length by omega)]
    rw [c3, slice_append (a := (M START r).val + 8) (by omega), slice_append (a := (M START r).val) (b := 8) (by omega)]
    congr 1; ring
  · -- WCNT
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨-, -, c3⟩ := hcs r hr hLP 0 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (prefOf M r) (by rw [hlen]) (by omega)
    simp only [tokOf, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, kz 0 (by norm_num) (by norm_num),
      kz 1 (by norm_num) (by norm_num), kz 2 (by norm_num) (by norm_num), kz 3 (by norm_num) (by norm_num),
      kz 4 (by norm_num) (by norm_num), h1, zero_ne_one, if_false, if_true, Spec.Block.Tok.bytes, hl]
    rw [c3, Nat.add_zero]
  · -- WITEM
    have hLP : M 7 r + M 8 r = 0 := by rw [kz 7 (by norm_num) (by norm_num), kz 8 (by norm_num) (by norm_num)]; simp
    obtain ⟨c1, cv, c3⟩ := hcs r hr hLP 0 (by exact_mod_cast hoff) (by norm_num)
    have hl := hlenv (prefOf M r + (M VAL r).val) (by rw [hlen]; push_cast [ZMod.natCast_zmod_val]; try ring) (by unfold MAXS at cv; omega)
    rw [hl] at hfit ⊢
    simp only [tokOf, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, kz 0 (by norm_num) (by norm_num),
      kz 1 (by norm_num) (by norm_num), kz 2 (by norm_num) (by norm_num), kz 3 (by norm_num) (by norm_num),
      kz 4 (by norm_num) (by norm_num), kz 5 (by norm_num) (by norm_num), h1, zero_ne_one, if_false, if_true,
      Spec.Block.Tok.bytes, Spec.Block.serVarBytes,
      slice_length (show (M START r).val + prefOf M r + (M VAL r).val ≤ R.length by omega)]
    rw [c3, Nat.add_zero, slice_append (by omega)]
  · -- LOCK
    have hl := hlenv (4) (by rw [hlen]; push_cast [ZMod.natCast_zmod_val]; try ring) (by norm_num)
    simp only [tokOf, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, kz 0 (by norm_num) (by norm_num),
      kz 1 (by norm_num) (by norm_num), kz 2 (by norm_num) (by norm_num), kz 3 (by norm_num) (by norm_num),
      kz 4 (by norm_num) (by norm_num), kz 5 (by norm_num) (by norm_num), kz 6 (by norm_num) (by norm_num),
      zero_ne_one, if_false, Spec.Block.Tok.bytes, hl]
  · -- PAD: excluded
    simp only [K_PAD] at hnp; rw [hnp] at h1; exact absurd h1 zero_ne_one

/-- Row lengths are small. -/
theorem len_small {r : ℕ} (hr : r < n) : (M LEN r).val ≤ 2 ^ 26 := by
  obtain ⟨a, ha, h1⟩ := kind_exists hsat hr
  have ka := kinds_at hsat hr ha h1
  obtain ⟨hoff, hlen⟩ := kind_vals hsat hr ha h1
  have pb : prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
  have sv := (bool_val (seg_bool hsat hr)).2
  by_cases hlp : a = K_LOCK ∨ a = K_PAD
  · rw [if_pos hlp] at hlen
    rcases hlp with rfl | rfl <;>
      simp [lenN, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD] at hlen <;> rw [hlen] <;>
      norm_num [ZMod.val_ofNat] <;> exact le_trans (Nat.mod_le _ _) (by norm_num)
  · rw [if_neg hlp] at hlen
    have hLP : M K_LOCK r + M K_PAD r = 0 := by
      rw [ka K_LOCK (by simp [K_LOCK]), ka K_PAD (by simp [K_PAD]), if_neg (by tauto), if_neg (by tauto)]; simp
    have ho : offN a (M SEG r).val ≤ 86 := by unfold offN; split_ifs <;> omega
    have hv := (hcs r hr hLP _ hoff ho).2.1
    unfold MAXS at hv
    rw [val_lt_of_eq_cast hlen (lt_P (by unfold lenN; split_ifs <;> omega))]
    unfold lenN; split_ifs <;> omega

theorem start_val_succ {r : ℕ} (hr : r + 1 < n) :
    (M START (r + 1)).val = (M START r).val + (M LEN r).val := by
  rw [start_succ hsat hr, ZMod.val_add_of_lt]
  have := start_lt hsat (show r < n by omega); have := len_small hsat R hcs hmk (show r < n by omega)
  exact lt_P (by omega)

/-- **Tiling.** With `m` the first padding row, the tokens of rows `0 … m−1` serialize to exactly
the block's bytes. -/
theorem tiling (hn : 0 < n) (hRl : R.length = (pub 0).val) :
    ∃ m, m < n ∧ M K_PAD m = 1 ∧ (∀ r < m, M K_PAD r = 0) ∧ (∀ r < n, m ≤ r → M K_PAD r = 1) ∧
      (∀ r < m, (M START r).val + (M LEN r).val ≤ R.length) ∧
      ((List.range m).flatMap fun r => Spec.Block.Tok.bytes (tokOf M R r)) = R := by
  classical
  have hex : ∃ r, r < n ∧ M K_PAD r = 1 := ⟨n - 1, by omega, last_pad hsat hn⟩
  set m := Nat.find hex with hmdef
  have hm : m < n ∧ M K_PAD m = 1 := Nat.find_spec hex
  have hmin : ∀ r < m, M K_PAD r = 0 := fun r hr => by
    rcases kind_bool hsat (c := K_PAD) (by simp [kinds]) (show r < n by omega) with h | h
    · exact h
    · exact absurd ⟨by omega, h⟩ (Nat.find_min hex hr)
  have hSm : (M START m).val = R.length := by rw [pad_start hsat hm.1 hm.2, hRl]
  -- Starts increase.
  have mono : ∀ k j, k ≤ j → j ≤ m → (M START k).val ≤ (M START j).val := by
    intro k j hkj hjm
    induction j, hkj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hkj ih =>
      rw [start_val_succ hsat R hcs hmk (show j + 1 < n by omega)]
      have := ih (by omega); omega
  have cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (tokOf M R r)) =
      slice R 0 (M START k).val := by
    intro k
    induction k with
    | zero => intro _; rw [start_zero hsat hn]; simp [slice]
    | succ k ih =>
      intro hk
      have hs := start_val_succ hsat R hcs hmk (show k + 1 < n by omega)
      have hfit : (M START k).val + (M LEN k).val ≤ R.length := by
        rw [← hs, ← hSm]; exact mono _ _ hk le_rfl
      have ap := slice_append (R := R) (a := 0) (b := (M START k).val) (c := (M LEN k).val) (by omega)
      rw [Nat.zero_add] at ap
      rw [List.range_succ, List.flatMap_append, ih (by omega), List.flatMap_singleton,
        tok_bytes hsat R hcs hmk (show k < n by omega) (hmin k (by omega)) hfit, ap, hs]
  have suffix : ∀ j, m + j < n → M K_PAD (m + j) = 1 := by
    intro j
    induction j with
    | zero => intro _; exact hm.2
    | succ j ih =>
      intro hj
      exact (next_kind hsat (r := m + j) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 (ih (by omega))
  refine ⟨m, hm.1, hm.2, hmin, fun r hr hmr => ?_, fun r hr => ?_, ?_⟩
  · have := suffix (r - m) (by omega); rwa [Nat.add_sub_cancel' hmr] at this
  · rw [← start_val_succ hsat R hcs hmk (show r + 1 < n by omega), ← hSm]; exact mono _ _ (by omega) le_rfl
  · rw [cat m le_rfl, hSm, slice_zero]

end Tokens

/-! ### The grammar, row by row -/

/-- The tokens of rows `r … m−1`. -/
def toksFrom (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (m r : ℕ) : List Spec.Block.Tok :=
  (List.range (m - r)).map fun i => tokOf M R (r + i)

theorem toksFrom_cons {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r : ℕ} (h : r < m) :
    toksFrom M R m r = tokOf M R r :: toksFrom M R m (r + 1) := by
  unfold toksFrom
  rw [show m - r = (m - (r + 1)) + 1 by omega, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  apply List.map_congr_left; intro i _; simp [Function.comp]; ring_nf

theorem toksFrom_end {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m : ℕ} : toksFrom M R m m = [] := by
  simp [toksFrom]

section Grammar

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

theorem lt_m {r : ℕ} (hr : r < n) (h : M K_PAD r = 0) : r < m := by
  by_contra hc; have := hpad r hr (by omega); rw [h] at this; exact zero_ne_one this

/-- Per-row facts for a row of kind `a` with a CompactSize (before the padding). -/
theorem row_info {r : ℕ} (hr : r < m) {a : ℕ} (ha : a < 9) (h : M a r = 1) (hnl : a ≠ K_LOCK) (hnp : a ≠ K_PAD) :
    (M VAL r).val ≤ MAXS ∧ (M LEN r).val = lenN a (M SEG r).val (prefOf M r) (M VAL r).val ∧
    1 ≤ prefOf M r ∧ prefOf M r ≤ 5 ∧ (M START r).val + (M LEN r).val ≤ R.length := by
  have hrn : r < n := by omega
  have ka := kinds_at hsat hrn ha h
  obtain ⟨hoff, hlen⟩ := kind_vals hsat hrn ha h
  rw [if_neg (by tauto)] at hlen
  have hLP : M K_LOCK r + M K_PAD r = 0 := by
    rw [ka K_LOCK (by simp [K_LOCK]), ka K_PAD (by simp [K_PAD]), if_neg (Ne.symm hnl), if_neg (Ne.symm hnp)]; simp
  have sv := (bool_val (seg_bool hsat hrn)).2
  have ho : offN a (M SEG r).val ≤ 86 := by unfold offN; split_ifs <;> omega
  have hv := (hcs r hrn hLP _ hoff ho).2.1
  have pb : 1 ≤ prefOf M r ∧ prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
  refine ⟨hv, val_lt_of_eq_cast hlen (lt_P (by unfold MAXS at hv; unfold lenN; split_ifs <;> omega)), pb.1, pb.2,
    hfit r hr⟩

theorem kz_of {r : ℕ} (hr : r < n) {a : ℕ} (ha : a < 9) (h : M a r = 1) {c : ℕ} (hc : c < 9) (hne : c ≠ a) :
    M c r = 0 := by
  rw [kinds_at hsat hr ha h c hc, if_neg hne]

theorem tok_blk {r : ℕ} (hr : r < n) (h : M K_BLK r = 1) :
    tokOf M R r = .blk (slice R (M START r).val 80) (M VAL r).val := by
  simp only [tokOf, h, if_true]

theorem tok_txh {r : ℕ} (hr : r < n) (h : M K_TXH r = 1) :
    tokOf M R r = .txh (slice R (M START r).val 4) (decide (M SEG r = 1)) (M VAL r).val := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_TXH) (by simp [K_TXH]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_TXH])]

theorem tok_in {r : ℕ} (hr : r < n) (h : M K_IN r = 1) :
    tokOf M R r = .inp (slice R (M START r).val 32) (slice R ((M START r).val + 32) 4)
      (slice R ((M START r).val + 36 + prefOf M r) (M VAL r).val)
      (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4) := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_IN) (by simp [K_IN]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_IN]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_IN])]

theorem tok_nout {r : ℕ} (hr : r < n) (h : M K_NOUT r = 1) : tokOf M R r = .nout (M VAL r).val := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_NOUT) (by simp [K_NOUT]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_NOUT]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_NOUT]),
    z K_IN (by simp [K_IN]) (by simp [K_IN, K_NOUT])]

theorem tok_out {r : ℕ} (hr : r < n) (h : M K_OUT r = 1) :
    tokOf M R r = .out (slice R (M START r).val 8) (slice R ((M START r).val + 8 + prefOf M r) (M VAL r).val) := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_OUT) (by simp [K_OUT]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_OUT]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_OUT]),
    z K_IN (by simp [K_IN]) (by simp [K_IN, K_OUT]), z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_OUT])]

theorem tok_wcnt {r : ℕ} (hr : r < n) (h : M K_WCNT r = 1) : tokOf M R r = .wcnt (M VAL r).val := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_WCNT) (by simp [K_WCNT]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_WCNT]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_WCNT]),
    z K_IN (by simp [K_IN]) (by simp [K_IN, K_WCNT]), z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_WCNT]),
    z K_OUT (by simp [K_OUT]) (by simp [K_OUT, K_WCNT])]

theorem tok_witem {r : ℕ} (hr : r < n) (h : M K_WITEM r = 1) :
    tokOf M R r = .witem (slice R ((M START r).val + prefOf M r) (M VAL r).val) := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_WITEM) (by simp [K_WITEM]) h (c := c) hc hne
  simp [tokOf, h, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_WITEM]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_WITEM]),
    z K_IN (by simp [K_IN]) (by simp [K_IN, K_WITEM]), z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_WITEM]),
    z K_OUT (by simp [K_OUT]) (by simp [K_OUT, K_WITEM]), z K_WCNT (by simp [K_WCNT]) (by simp [K_WCNT, K_WITEM])]

theorem tok_lock {r : ℕ} (hr : r < n) (h : M K_LOCK r = 1) : tokOf M R r = .lock (slice R (M START r).val 4) := by
  have z := fun c hc hne => kz_of hsat R hcs hmn hpad hfit hr (a := K_LOCK) (by simp [K_LOCK]) h (c := c) hc hne
  simp [tokOf, z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_LOCK]), z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_LOCK]),
    z K_IN (by simp [K_IN]) (by simp [K_IN, K_LOCK]), z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_LOCK]),
    z K_OUT (by simp [K_OUT]) (by simp [K_OUT, K_LOCK]), z K_WCNT (by simp [K_WCNT]) (by simp [K_WCNT, K_LOCK]),
    z K_WITEM (by simp [K_WITEM]) (by simp [K_WITEM, K_LOCK])]

/-- **Inputs.** From an input row with `k + 1` inputs left (this one included), `insT` reads them and
stops at the output count. -/
theorem ins_sim : ∀ k r, r < m → M K_IN r = 1 → (M INL r).val = k + 1 →
    ∃ ins, Spec.Block.insT (k + 1) (toksFrom M R m r) = some (ins, toksFrom M R m (r + k + 1)) ∧
      r + k + 1 < m ∧ M K_NOUT (r + k + 1) = 1 := by
  intro k
  induction k with
  | zero =>
    intro r hr hin hinl
    have hrn : r < n := by omega
    have hr1 : r + 1 < n := by omega
    obtain ⟨hv, hlen, p1, p5, hft⟩ := row_info hsat R hcs hmn hpad hfit hr (a := K_IN) (by simp [K_IN]) hin
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, if_false, if_true, show (2 : ℕ) ≠ 0 by norm_num,
      show (2 : ℕ) ≠ 1 by norm_num] at hlen
    have ka := kinds_at hsat hrn (a := K_IN) (by simp [K_IN]) hin
    have he : M E1C r = M INL r - 1 := by
      rw [e1_eq hsat hrn, ka K_BLK (by simp [K_BLK]), ka K_TXH (by simp [K_TXH]), ka K_NOUT (by simp [K_NOUT]),
        ka K_OUT (by simp [K_OUT]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM]),
        ka K_LOCK (by simp [K_LOCK]), hin]
      simp [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK]
    have hz : M Z1 r = 1 := (z1_iff_val hsat hrn he hinl).2 rfl
    have hnout : M K_NOUT (r + 1) = 1 := (next_kind hsat hr1).2.2.2.1 hin hz
    have hr1m : r + 1 < m := lt_m hsat R hcs hmn hpad hfit hr1
      (kz_of hsat R hcs hmn hpad hfit hr1 (a := K_NOUT) (by simp [K_NOUT]) hnout (c := K_PAD) (by simp [K_PAD])
        (by simp [K_PAD, K_NOUT]))
    refine ⟨[(⟨⟨slice R (M START r).val 32, Spec.Block.le (slice R ((M START r).val + 32) 4)⟩,
      slice R ((M START r).val + 36 + prefOf M r) (M VAL r).val,
      Spec.Block.le (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4), []⟩ : Spec.Block.TxIn)], ?_, by simpa using hr1m, by simpa using hnout⟩
    rw [toksFrom_cons hr, tok_in hsat R hcs hmn hpad hfit hrn hin]
    simp only [Spec.Block.insT]
    rw [if_pos ⟨slice_length (by omega), slice_length (by omega), by rw [slice_length (by omega)]; exact hv,
      slice_length (by omega)⟩]
    simp
  | succ k ih =>
    intro r hr hin hinl
    have hrn : r < n := by omega
    have hr1 : r + 1 < n := by omega
    obtain ⟨hv, hlen, p1, p5, hft⟩ := row_info hsat R hcs hmn hpad hfit hr (a := K_IN) (by simp [K_IN]) hin
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, if_false, if_true, show (2 : ℕ) ≠ 0 by norm_num,
      show (2 : ℕ) ≠ 1 by norm_num] at hlen
    have ka := kinds_at hsat hrn (a := K_IN) (by simp [K_IN]) hin
    have he : M E1C r = M INL r - 1 := by
      rw [e1_eq hsat hrn, ka K_BLK (by simp [K_BLK]), ka K_TXH (by simp [K_TXH]), ka K_NOUT (by simp [K_NOUT]),
        ka K_OUT (by simp [K_OUT]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM]),
        ka K_LOCK (by simp [K_LOCK]), hin]
      simp [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK]
    have hz : M Z1 r = 0 := by
      rcases (z1_spec hsat hrn).1 with h | h
      · exact h
      · exact absurd ((z1_iff_val hsat hrn he hinl).1 h) (by omega)
    have hin1 : M K_IN (r + 1) = 1 := (next_kind hsat hr1).2.2.1 hin hz
    have ht1 : M K_TXH (r + 1) = 0 :=
      kz_of hsat R hcs hmn hpad hfit hr1 (a := K_IN) (by simp [K_IN]) hin1 (c := K_TXH) (by simp [K_TXH]) (by simp [K_TXH, K_IN])
    have hinl1 : (M INL (r + 1)).val = k + 1 := by
      rw [(counters hsat hr1).2.1 ht1, hin]; exact val_pred hinl
    have hr1m : r + 1 < m := lt_m hsat R hcs hmn hpad hfit hr1
      (kz_of hsat R hcs hmn hpad hfit hr1 (a := K_IN) (by simp [K_IN]) hin1 (c := K_PAD) (by simp [K_PAD]) (by simp [K_PAD, K_IN]))
    obtain ⟨ins, hins, hlt, hno⟩ := ih (r + 1) hr1m hin1 hinl1
    refine ⟨(⟨⟨slice R (M START r).val 32, Spec.Block.le (slice R ((M START r).val + 32) 4)⟩,
      slice R ((M START r).val + 36 + prefOf M r) (M VAL r).val,
      Spec.Block.le (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4), []⟩ : Spec.Block.TxIn) :: ins, ?_, by rw [show r + (k + 1) + 1 = r + 1 + k + 1 by ring]; exact hlt,
      by rw [show r + (k + 1) + 1 = r + 1 + k + 1 by ring]; exact hno⟩
    rw [toksFrom_cons hr, tok_in hsat R hcs hmn hpad hfit hrn hin]
    simp only [Spec.Block.insT]
    rw [if_pos ⟨slice_length (by omega), slice_length (by omega), by rw [slice_length (by omega)]; exact hv,
      slice_length (by omega)⟩, hins, show r + 1 + k + 1 = r + (k + 1) + 1 by ring]
    simp

/-- **Outputs.** From an output row with `k + 1` outputs left, `outsT` reads them; the last one
ends the outputs (its `Z1` is 1). -/
theorem outs_sim : ∀ k r, r < m → M K_OUT r = 1 → (M OUTL r).val = k + 1 →
    ∃ outs, Spec.Block.outsT (k + 1) (toksFrom M R m r) = some (outs, toksFrom M R m (r + k + 1)) ∧
      r + k < m ∧ M K_OUT (r + k) = 1 ∧ M Z1 (r + k) = 1 ∧
      M SEG (r + k) = M SEG r ∧ M NIN (r + k) = M NIN r ∧ M TXL (r + k) = M TXL r ∧ M HASW (r + k) = M HASW r := by
  intro k
  induction k with
  | zero =>
    intro r hr hout houtl
    have hrn : r < n := by omega
    obtain ⟨hv, hlen, p1, p5, hft⟩ := row_info hsat R hcs hmn hpad hfit hr (a := K_OUT) (by simp [K_OUT]) hout
      (by simp [K_OUT, K_LOCK]) (by simp [K_OUT, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, if_false, if_true, show (4 : ℕ) ≠ 0 by norm_num,
      show (4 : ℕ) ≠ 1 by norm_num, show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num] at hlen
    have ka := kinds_at hsat hrn (a := K_OUT) (by simp [K_OUT]) hout
    have he : M E1C r = M OUTL r - 1 := by
      rw [e1_eq hsat hrn, ka K_BLK (by simp [K_BLK]), ka K_TXH (by simp [K_TXH]), ka K_IN (by simp [K_IN]),
        ka K_NOUT (by simp [K_NOUT]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM]),
        ka K_LOCK (by simp [K_LOCK]), hout]
      simp [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK]
    have hz : M Z1 r = 1 := (z1_iff_val hsat hrn he houtl).2 rfl
    refine ⟨[⟨Spec.Block.signed64 (Spec.Block.le (slice R (M START r).val 8)),
      slice R ((M START r).val + 8 + prefOf M r) (M VAL r).val⟩], ?_, by simpa using hr, by simpa using hout,
      by simpa using hz, by simp, by simp, by simp, by simp⟩
    rw [toksFrom_cons hr, tok_out hsat R hcs hmn hpad hfit hrn hout]
    simp only [Spec.Block.outsT]
    rw [if_pos ⟨slice_length (by omega), by rw [slice_length (by omega)]; exact hv⟩]
    simp
  | succ k ih =>
    intro r hr hout houtl
    have hrn : r < n := by omega
    have hr1 : r + 1 < n := by omega
    obtain ⟨hv, hlen, p1, p5, hft⟩ := row_info hsat R hcs hmn hpad hfit hr (a := K_OUT) (by simp [K_OUT]) hout
      (by simp [K_OUT, K_LOCK]) (by simp [K_OUT, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, if_false, if_true, show (4 : ℕ) ≠ 0 by norm_num,
      show (4 : ℕ) ≠ 1 by norm_num, show (4 : ℕ) ≠ 2 by norm_num, show (4 : ℕ) ≠ 3 by norm_num] at hlen
    have ka := kinds_at hsat hrn (a := K_OUT) (by simp [K_OUT]) hout
    have he : M E1C r = M OUTL r - 1 := by
      rw [e1_eq hsat hrn, ka K_BLK (by simp [K_BLK]), ka K_TXH (by simp [K_TXH]), ka K_IN (by simp [K_IN]),
        ka K_NOUT (by simp [K_NOUT]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM]),
        ka K_LOCK (by simp [K_LOCK]), hout]
      simp [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK]
    have hz : M Z1 r = 0 := by
      rcases (z1_spec hsat hrn).1 with h | h
      · exact h
      · exact absurd ((z1_iff_val hsat hrn he houtl).1 h) (by omega)
    have hout1 : M K_OUT (r + 1) = 1 := (next_kind hsat hr1).2.2.2.2.1 (Or.inr hout) hz
    have kz1 := fun {c : ℕ} (hc : c < 9) (hne : c ≠ K_OUT) =>
      kz_of hsat R hcs hmn hpad hfit hr1 (a := K_OUT) (by simp [K_OUT]) hout1 hc hne
    have houtl1 : (M OUTL (r + 1)).val = k + 1 := by
      rw [(counters hsat hr1).2.2.2.1 (kz1 (by simp [K_NOUT]) (by simp [K_NOUT, K_OUT])), hout]; exact val_pred houtl
    have inv := step_inv hsat hr1 (kz1 (by simp [K_TXH]) (by simp [K_TXH, K_OUT])) (ka K_LOCK (by simp [K_LOCK]) |>.trans
      (by simp [K_LOCK, K_OUT])) (by rw [ka K_WCNT (by simp [K_WCNT])]; simp [K_WCNT, K_OUT])
    have hr1m : r + 1 < m := lt_m hsat R hcs hmn hpad hfit hr1 (kz1 (by simp [K_PAD]) (by simp [K_PAD, K_OUT]))
    obtain ⟨outs, houts, hlt, ho, hz', i1, i2, i3, i4⟩ := ih (r + 1) hr1m hout1 houtl1
    have e : r + 1 + k = r + (k + 1) := by ring
    rw [e] at hlt ho hz' i1 i2 i3 i4
    refine ⟨⟨Spec.Block.signed64 (Spec.Block.le (slice R (M START r).val 8)),
      slice R ((M START r).val + 8 + prefOf M r) (M VAL r).val⟩ :: outs, ?_, hlt, ho, hz',
      i1.trans inv.1, i2.trans inv.2.1, i3.trans inv.2.2.1, i4.trans inv.2.2.2⟩
    rw [toksFrom_cons hr, tok_out hsat R hcs hmn hpad hfit hrn hout]
    simp only [Spec.Block.outsT]
    rw [if_pos ⟨slice_length (by omega), by rw [slice_length (by omega)]; exact hv⟩, houts,
      show r + 1 + k + 1 = r + (k + 1) + 1 by ring]
    simp

end Grammar

/-! ### The block system: bytes (component 0) and fields (component 1) -/

def blockSys : System := ⟨2, fun i => if i = 0 then bytes else fields⟩

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) (hL : L ≤ 25)
  (hsat : blockSys.SatisfiedExt inst pub [])
include h0L h1L hL hsat

theorem fields_sat : ∀ r < 2 ^ L, ∀ c ∈ constraints, c.eval (2 ^ L) preCols pub (inst 1).main r = 0 := by
  have := hsat.1 1 (by decide); rw [h1L] at this; exact this

theorem bytes_sat : bytes.air.Satisfied L pub (inst 0).main := by
  have := hsat.1 0 (by decide); rw [h0L] at this; exact this

theorem rows_lt_P : 2 ^ L < P := lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hL) (by unfold P; norm_num)

omit hL hsat in
theorem sites_len : (sites blockSys inst).length = 8 * 2 ^ L := by
  simp [sites, blockSys, h0L, h1L, List.length_flatMap, bytes, fields, lookups, List.sum_range_succ]
  ring

/-- **A fields read.** A lookup of fields row `r` with multiplicity `−1` reads the block byte at its
position. -/
theorem sys_read {r : ℕ} (hr : r < 2 ^ L) {kk : ℕ} (hk : kk < 7)
    (hm : (lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) preCols pub (inst 1).main r = -1) :
    ∃ r0, r0 < (pub 0).val ∧
      ((lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) preCols pub (inst 1).main r)) =
        [(r0 : F), (inst 0).main BYTE r0] := by
  classical
  have fs := fields_sat h0L h1L hL hsat
  have hs1 : ((1, r, kk) : Site) ∈ sites blockSys inst := by
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨1, by decide, r, by rw [h1L]; exact hr, kk, by simp [blockSys, fields, lookups]; omega, rfl⟩
  have hrel : siteRel blockSys ((1, r, kk) : Site) = REL_BYTE := by
    simp only [siteRel, siteLookup, blockSys, fields]; interval_cases kk <;> rfl
  have hmult : siteMult blockSys inst pub ((1, r, kk) : Site) = -1 := by
    simpa [siteMult, siteEval, siteLookup, blockSys, fields, h1L] using hm
  -- The tuple has two entries.
  obtain ⟨p, b, hpb⟩ : ∃ p b, siteVals blockSys inst pub ((1, r, kk) : Site) = [p, b] := by
    simp only [siteVals, siteLookup, blockSys, fields]
    interval_cases kk <;> exact ⟨_, _, rfl⟩
  obtain ⟨r0, hr0, hp, hb⟩ := read_byte hsat.2 (by rfl)
    (by have := bytes_sat h0L h1L hL hsat; rw [h0L]; exact this) (by rw [h0L]; exact rows_lt_P h0L h1L hL hsat)
    (fun s hs h0 hrel => by
      obtain ⟨i, r', k'⟩ := s
      have hm := (List.mem_flatMap.mp hs)
      simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map] at hs
      obtain ⟨i', hi', r'', hr'', k'', hk'', e⟩ := hs
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      simp only at h0
      have hi1 : i' = 1 := by simp [blockSys] at hi'; omega
      subst hi1
      have hk7 : k'' < 7 := by simpa [blockSys, fields, lookups] using hk''
      rw [h1L] at hr''
      have := mult_vals fs hr'' hk7
      simpa [siteMult, siteEval, siteLookup, blockSys, fields, h1L] using this)
    (by
      calc _ ≤ (sites blockSys inst).length := List.length_filter_le _ _
        _ = 8 * 2 ^ L := sites_len h0L h1L
        _ < P := by
          have : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL
          unfold P; omega)
    hs1 (by simp) hrel hmult hpb
  refine ⟨r0, hr0, ?_⟩
  have : siteVals blockSys inst pub ((1, r, kk) : Site) =
      (lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) preCols pub (inst 1).main r) := by
    simp [siteVals, siteEval, siteLookup, blockSys, fields, h1L]
  rw [← this, hpb, hp, hb]

/-- **CompactSize bytes are the block's.** On a row with a CompactSize at offset `o`, byte `j`
of the form is the block byte at `START + o + j`. -/
theorem compact_read {r : ℕ} (hr : r < 2 ^ L)
    (hLP : (inst 1).main K_LOCK r + (inst 1).main K_PAD r = 0) {o : ℕ} (ho : (inst 1).main OFF r = (o : F))
    (hoP : o ≤ 86) {j : ℕ} (hj : j < prefOf (inst 1).main r) :
    ((inst 1).main START r).val + o + j < (pub 0).val ∧
      (inst 1).main (CB j) r = (inst 0).main BYTE (((inst 1).main START r).val + o + j) := by
  have fs := fields_sat h0L h1L hL hsat
  have forms := (cp35 fs hr).2 hLP
  have hst := start_lt fs hr
  have hj5 : j < 5 := by unfold prefOf at hj; split_ifs at hj <;> omega
  have hm : (lookups.getD j ⟨0, .const 0, []⟩).mult.eval (2 ^ L) preCols pub (inst 1).main r = -1 := by
    rcases forms with ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ | ⟨f1, f3, f5⟩ <;>
      simp only [prefOf, f1, f3, f5, if_true, if_false, one_ne_zero, zero_ne_one] at hj <;>
      interval_cases j <;>
      simp [lookups, Expr.eval, ev_k hr, hasC, oneMinus, one, eval_cst, f1, f3, f5, hLP]
  obtain ⟨r0, hr0, hv⟩ := sys_read h0L h1L hL hsat hr (by omega) hm
  have e : ((inst 1).main START r + (inst 1).main OFF r + (j : F)) = (r0 : F) ∧
      (inst 1).main (CB j) r = (inst 0).main BYTE r0 := by
    interval_cases j <;> simpa [lookups, Expr.eval, ev_k hr, eval_cst] using hv
  have hpos : ((inst 1).main START r).val + o + j = r0 := by
    refine natCast_inj_of_lt (lt_P (by omega)) (lt_P (by
      have := rows_lt_P h0L h1L hL hsat
      have : (pub 0).val ≤ 2 ^ L := by
        have hb := bytes_rows (n := 2 ^ L) (pub := pub) (main := (inst 0).main)
          (by have := bytes_sat h0L h1L hL hsat; exact this) this (by positivity)
        exact hb.2.1
      have : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL
      omega)) ?_
    push_cast
    rw [← e.1, ho, ZMod.natCast_zmod_val]
  refine ⟨by omega, ?_⟩
  rw [hpos]; exact e.2

/-- **The segwit marker and flag** of a segwit transaction head are the block's `00 01`. -/
theorem marker_read {r : ℕ} (hr : r < 2 ^ L) (hT : (inst 1).main K_TXH r = 1) (hS : (inst 1).main SEG r = 1) :
    ((inst 1).main START r).val + 5 < (pub 0).val ∧
      (inst 0).main BYTE (((inst 1).main START r).val + 4) = 0 ∧
      (inst 0).main BYTE (((inst 1).main START r).val + 5) = 1 := by
  have fs := fields_sat h0L h1L hL hsat
  have hst := start_lt fs hr
  have hLb : (pub 0).val ≤ 2 ^ 25 := by
    have := rows_lt_P h0L h1L hL hsat
    have hb := bytes_rows (n := 2 ^ L) (pub := pub) (main := (inst 0).main)
      (by have := bytes_sat h0L h1L hL hsat; exact this) this (by positivity)
    have : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL
    omega
  have rd : ∀ kk (hk : kk < 7), kk = 5 ∨ kk = 6 → ∃ r0, r0 < (pub 0).val ∧
      ((lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) preCols pub (inst 1).main r)) =
        [(r0 : F), (inst 0).main BYTE r0] := fun kk hk h56 =>
    sys_read h0L h1L hL hsat hr hk (by rcases h56 with rfl | rfl <;> simp [lookups, Expr.eval, ev_k hr, hT, hS])
  obtain ⟨r4, h4, v4⟩ := rd 5 (by norm_num) (Or.inl rfl)
  obtain ⟨r5, h5, v5⟩ := rd 6 (by norm_num) (Or.inr rfl)
  simp [lookups, Expr.eval, ev_k hr, eval_cst] at v4 v5
  have p4 : ((inst 1).main START r).val + 4 = r4 := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    (by push_cast; rw [← v4.1, ZMod.natCast_zmod_val])
  have p5 : ((inst 1).main START r).val + 5 = r5 := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    (by push_cast; rw [← v5.1, ZMod.natCast_zmod_val])
  refine ⟨by omega, by rw [p4]; exact v4.2.symm, by rw [p5]; exact v5.2.symm⟩

theorem len_le : (pub 0).val ≤ 2 ^ 25 := by
  have := rows_lt_P h0L h1L hL hsat
  have hb := bytes_rows (n := 2 ^ L) (pub := pub) (main := (inst 0).main)
    (by have := bytes_sat h0L h1L hL hsat; exact this) this (by positivity)
  have : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL
  omega

/-- **A row's CompactSize is the block's bytes at its offset.** -/
theorem compact_slice {r : ℕ} (hr : r < 2 ^ L)
    (hLP : (inst 1).main K_LOCK r + (inst 1).main K_PAD r = 0) {o : ℕ} (ho : (inst 1).main OFF r = (o : F))
    (hoP : o ≤ 86) :
    ((inst 1).main START r).val + o + prefOf (inst 1).main r ≤ (pub 0).val ∧
      ((inst 1).main VAL r).val ≤ MAXS ∧
      Spec.Block.serCompact ((inst 1).main VAL r).val =
        slice (blockBytes (inst 0).main (pub 0).val) (((inst 1).main START r).val + o) (prefOf (inst 1).main r) := by
  have fs := fields_sat h0L h1L hL hsat
  have rd := fun j (hj : j < prefOf (inst 1).main r) => compact_read h0L h1L hL hsat hr hLP ho hoP hj
  have hp1 : 1 ≤ prefOf (inst 1).main r := by unfold prefOf; split_ifs <;> omega
  have bnd : ((inst 1).main START r).val + o + prefOf (inst 1).main r ≤ (pub 0).val := by
    have := (rd (prefOf (inst 1).main r - 1) (by omega)).1; omega
  have hbytes := bytes_rows (n := 2 ^ L) (pub := pub) (main := (inst 0).main)
    (by have := bytes_sat h0L h1L hL hsat; exact this) (rows_lt_P h0L h1L hL hsat) (by positivity)
  have b256 : ∀ j < prefOf (inst 1).main r, ((inst 1).main (CB j) r).val < 256 := fun j hj => by
    rw [(rd j hj).2]
    exact (hbytes.1 _ (by have := (rd j hj).1; have := hbytes.2.1; omega)).2
  have hLk : (inst 1).main K_LOCK r = 0 := by
    rcases kind_bool fs (c := K_LOCK) (by simp [kinds]) hr with h | h
    · exact h
    · exfalso; rcases kind_bool fs (c := K_PAD) (by simp [kinds]) hr with g | g <;> rw [h, g] at hLP
      · simp at hLP
      · exact absurd hLP one_add_one_ne
  have hPk : (inst 1).main K_PAD r = 0 := by rw [hLk, zero_add] at hLP; exact hLP
  obtain ⟨hv, hser⟩ := compact_ser fs hr hLk hPk b256
  refine ⟨bnd, hv, ?_⟩
  rw [← hser, slice_eq_map (by rw [blockBytes_length]; omega)]
  refine List.map_congr_left (fun j hj => ?_)
  have hj' := List.mem_range.mp hj
  rw [blockBytes_get (by have := (rd j hj').1; omega), ← (rd j hj').2]

theorem u8_get_eq {Mb : ℕ → ℕ → F} {len i : ℕ} (h : i < len) {b : ℕ} (hb : Mb BYTE i = (b : F)) (b256 : b < 256) :
    (blockBytes Mb len).getD i 0 = UInt8.ofNat b := by
  rw [blockBytes_get h, hb, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_P (by omega))]

end System

end StarkedAir.Block.Fields
