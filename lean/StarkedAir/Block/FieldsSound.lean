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

end Rows

end StarkedAir.Block.Fields
