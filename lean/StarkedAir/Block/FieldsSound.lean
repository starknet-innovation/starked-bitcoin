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
  have hn := ev_notFirst hsat hr
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

end Rows

end StarkedAir.Block.Fields
