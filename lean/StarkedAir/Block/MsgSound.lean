/-
**Hash messages soundness (M3a.3, message component).** Row facts first: kinds, transitions,
helpers; then a forward walk over one message.
-/
import StarkedAir.Block.Msg
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Msg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow eval_col eval_cst wrap_back)
open StarkedAir.Block.Fields (bool_val val_lt_of_eq_cast lt_P one_add_one_ne)

theorem mem_kindC {c : Expr} (h : c ∈ kindC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_transC {c : Expr} (h : c ∈ transC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_msgC {c : Expr} (h : c ∈ msgC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto
theorem mem_padC {c : Expr} (h : c ∈ padC) : c ∈ constraints := by simp only [constraints, List.mem_append]; tauto

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
theorem ev_per64 {i : ℕ} {p : ℕ → Bool} (hi : preCols.getD i (.periodic [0]) = per64 p) {r : ℕ} (hr : r < n) :
    (pre i).eval n preCols pub M r = if p (r % 64) then 1 else 0 := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp only [per64, PreCol.eval, List.length_map, List.length_range, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range this, Option.map_some, Option.getD_some]
  split <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

theorem bool_of {e : ℕ} (hc : boolC (k e) ∈ constraints) {r : ℕ} (hr : r < n) : M e r = 0 ∨ M e r = 1 := by
  have := sat hsat hc hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem bool_col {e : ℕ} (he : e ∈ [D, P80, ZR, LN, NIL, FIRSTM, PC0, PC1, PC2, HDR, WTX, SEG, Z]) {r : ℕ} (hr : r < n) :
    M e r = 0 ∨ M e r = 1 := by
  have hm : boolC (k e) ∈ kindC := by
    simp only [kindC, List.mem_append, List.mem_map]
    left; exact ⟨e, Or.inl he, rfl⟩
  exact bool_of hsat (mem_kindC hm) hr

omit hsat in
theorem kinds_range : kinds = List.range 5 := rfl

/-- The kind sum, as naturals. -/
theorem kind_sumN {r : ℕ} (hr : r < n) : ∑ c ∈ Finset.range 5, (M c r).val = 1 := by
  have hs := sat hsat (mem_kindC (c := .sub (kinds.foldr (fun c acc => .add (k c) acc) (cst 0)) one)
    (by simp [kindC])) hr
  simp only [kinds, List.foldr, Expr.eval, ev_k hr, eval_cst, one, Nat.cast_zero, Nat.cast_one, sub_eq_zero] at hs
  have bv : ∀ c < 5, M c r = ((M c r).val : F) ∧ (M c r).val ≤ 1 := fun c hc => bool_val (bool_col hsat (by
    simp only [List.mem_cons]; interval_cases c <;> simp [D, P80, ZR, LN, NIL]) hr)
  have hle : ∑ c ∈ Finset.range 5, (M c r).val ≤ 5 := by
    calc _ ≤ ∑ _c ∈ Finset.range 5, 1 := Finset.sum_le_sum (fun c hc => (bv c (Finset.mem_range.mp hc)).2)
      _ = 5 := by simp
  have hcast : ((∑ c ∈ Finset.range 5, (M c r).val : ℕ) : F) = ((1 : ℕ) : F) := by
    push_cast
    rw [Finset.sum_congr rfl (fun c hc => (bv c (Finset.mem_range.mp hc)).1.symm)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [D, P80, ZR, LN, NIL] at hs
    rw [← hs]; ring
  exact natCast_inj_of_lt (lt_of_le_of_lt hle (by unfold P; norm_num)) (by unfold P; norm_num) hcast

/-- **One-hot kinds.** -/
theorem kind_unique {r : ℕ} (hr : r < n) {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : a ≠ b) (h : M a r = 1) :
    M b r = 0 := by
  have hs := kind_sumN hsat hr
  have := Finset.add_le_sum (f := fun c => (M c r).val) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr ha) (Finset.mem_range.mpr hb) hab
  have hb' := (bool_val (bool_col hsat (e := b) (by
    simp only [List.mem_cons]; interval_cases b <;> simp [D, P80, ZR, LN, NIL]) hr)).1
  have ha1 : (M a r).val = 1 := by rw [h]; exact ZMod.val_one P
  rw [hb', show (M b r).val = 0 by omega]; simp

theorem kind_exists {r : ℕ} (hr : r < n) : ∃ a < 5, M a r = 1 := by
  have hs := kind_sumN hsat hr
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : ∑ c ∈ Finset.range 5, (M c r).val ≠ 0)
  refine ⟨a, Finset.mem_range.mp ha, ?_⟩
  rcases bool_col hsat (e := a) (by
    have := Finset.mem_range.mp ha; simp only [List.mem_cons]; interval_cases a <;> simp [D, P80, ZR, LN, NIL]) hr with h | h
  · rw [h] at hne; simp at hne
  · exact h

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ constraints) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat h hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem helpers {r : ℕ} (hr : r < n) :
    M CONT r = M D r * (1 - M Z r) ∧ M SW r = M Z r * (M MT r * (M PC0 r + M PC1 r)) ∧
    M ENDD r = M D r * M Z r - M SW r := by
  refine ⟨?_, ?_, ?_⟩
  · rw [defn hsat (a := CONT) (e := .mul (k D) (om (k Z))) (mem_transC (by simp [transC])) hr]
    simp [Expr.eval, ev_k hr, om, one, eval_cst]
  · rw [defn hsat (a := SW) (e := .mul (k Z) (.mul (k MT) (.add (k PC0) (k PC1)))) (mem_transC (by simp [transC])) hr]
    simp [Expr.eval, ev_k hr]
  · rw [defn hsat (a := ENDD) (e := .sub (.mul (k D) (k Z)) (k SW)) (mem_transC (by simp [transC])) hr]
    simp [Expr.eval, ev_k hr]

/-- The transitions, at row `r + 1` from row `r`. -/
theorem trans_all {r : ℕ} (hr : r + 1 < n) :
    M D (r + 1) - M FIRSTM (r + 1) = M CONT r + M SW r ∧
    M P80 (r + 1) = M ENDD r ∧
    M ZR (r + 1) = (M P80 r + M ZR r) * (1 - (if (r + 1) % 64 = 56 then 1 else 0)) ∧
    M LN (r + 1) = (M P80 r + M ZR r) * (if (r + 1) % 64 = 56 then 1 else 0) +
      M LN r * (1 - (if (r + 1) % 64 = 0 then 1 else 0)) ∧
    M NIL (r + 1) + M FIRSTM (r + 1) = M LN r * (if (r + 1) % 64 = 0 then 1 else 0) + M NIL r ∧
    M PC0 (r + 1) - M FIRSTM (r + 1) = M CONT r * M PC0 r ∧
    M PC1 (r + 1) = M CONT r * M PC1 r + M SW r * M PC0 r ∧
    M PC2 (r + 1) = M CONT r * M PC2 r + M SW r * M PC1 r := by
  have t := fun (e : Expr) (h : e ∈ transC) => sat hsat (mem_transC h) hr
  have i56 : (pre IS56).eval n preCols pub M (r + 1) = if (r + 1) % 64 = 56 then 1 else 0 := by
    rw [ev_per64 (p := (· = 56)) rfl hr]; simp
  have i0 : (pre IS0).eval n preCols pub M (r + 1) = if (r + 1) % 64 = 0 then 1 else 0 := by
    rw [ev_per64 (p := (· = 0)) rfl hr]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := t (.sub (.sub (k D) (k FIRSTM)) (.add (kp CONT) (kp SW))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr] at this; exact sub_eq_zero.mp this
  · have := t (.sub (k P80) (kp ENDD)) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr] at this; exact sub_eq_zero.mp this
  · have := t (.sub (k ZR) (.mul (.add (kp P80) (kp ZR)) (om (pre IS56)))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, i56] at this; exact sub_eq_zero.mp this
  · have := t (.sub (k LN) (.add (.mul (.add (kp P80) (kp ZR)) (pre IS56)) (.mul (kp LN) (om (pre IS0))))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, i56, i0] at this; exact sub_eq_zero.mp this
  · have := t (.sub (.add (k NIL) (k FIRSTM)) (.add (.mul (kp LN) (pre IS0)) (kp NIL))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr, i0] at this; exact sub_eq_zero.mp this
  · have := t (.sub (.sub (k PC0) (k FIRSTM)) (.mul (kp CONT) (kp PC0))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr] at this; exact sub_eq_zero.mp this
  · have := t (.sub (k PC1) (.add (.mul (kp CONT) (kp PC1)) (.mul (kp SW) (kp PC0)))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr] at this; exact sub_eq_zero.mp this
  · have := t (.sub (k PC2) (.add (.mul (kp CONT) (kp PC2)) (.mul (kp SW) (kp PC1)))) (by simp [transC])
    simp only [Expr.eval, ev_k hr, ev_kp hr] at this; exact sub_eq_zero.mp this

/-- The cyclic predecessor of row `r`. -/
def prv (n r : ℕ) : ℕ := (r + n - 1) % n

omit hsat in
theorem wrap_prv {r : ℕ} (hr : r < n) : wrap n r (-1) = prv n r := by
  unfold wrap prv
  have hn : (0 : ℤ) < n := by omega
  rw [show ((r : ℤ) + -1) = ((r + n - 1 : ℕ) : ℤ) - (n : ℤ) by push_cast [show 1 ≤ r + n by omega]; ring,
    Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [show ((r + n - 1 : ℕ) : ℤ) % (n : ℤ) = (((r + n - 1) % n : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

omit hsat in
theorem ev_kpp {c r : ℕ} (hr : r < n) : (kp c).eval n preCols pub M r = M c (prv n r) := by
  simp only [kp, eval_col, wrap_prv hr]

/-- The last row pads. -/
theorem last_nil (hn : 0 < n) : M NIL (n - 1) = 1 := by
  have hl : n - 1 < n := by omega
  have := sat hsat (mem_kindC (c := .mul (om (pre NOTLAST)) (om (k NIL))) (by simp [kindC])) hl
  have hnl : (pre NOTLAST).eval n preCols pub M (n - 1) = 0 := by
    simp [pre, Expr.eval, wrap_zero hl, preCols, PreCol.eval, NOTLAST]; omega
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, hnl, sub_zero, one_mul, ev_k hl, sub_eq_zero] at this
  exact this.symm

/-- Rows that are not data have no piece. -/
theorem pieces_zero {r : ℕ} (hr : r < n) (hd : M D r = 0) : M PC0 r = 0 ∧ M PC1 r = 0 ∧ M PC2 r = 0 := by
  have := sat hsat (mem_transC (c := .sub (.add (k PC0) (.add (k PC1) (k PC2))) (k D)) (by simp [transC])) hr
  simp only [Expr.eval, ev_k hr, hd, sub_zero] at this
  have b0 := bool_val (bool_col hsat (e := PC0) (by simp) hr)
  have b1 := bool_val (bool_col hsat (e := PC1) (by simp) hr)
  have b2 := bool_val (bool_col hsat (e := PC2) (by simp) hr)
  have hs : (M PC0 r).val + (M PC1 r).val + (M PC2 r).val = 0 := by
    refine natCast_inj_of_lt ?_ (by unfold P; norm_num) ?_
    · have := b0.2; have := b1.2; have := b2.2; exact lt_P (by omega)
    · push_cast; rw [← b0.1, ← b1.1, ← b2.1]; linear_combination this
  exact ⟨(ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega), (ZMod.val_eq_zero _).mp (by omega)⟩

omit hsat in
theorem diff_one {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : a - b = 1) : a = 1 ∧ b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp at h
  · exact absurd (by linear_combination -h) one_add_one_ne
  · exact ⟨rfl, rfl⟩
  · simp at h

omit hsat in
theorem prod_one {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : a * (1 - b) = 1) : a = 1 ∧ b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

omit hsat in
theorem first_off {r : ℕ} (hr : r + 1 < n) : (pre FIRST).eval n preCols pub M (r + 1) = 0 := by
  simp [pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval, FIRST]

theorem firstm_d {r : ℕ} (hr : r < n) (h : M FIRSTM r = 1) : M D r = 1 := by
  have := sat hsat (mem_kindC (c := .mul (k FIRSTM) (om (k D))) (by simp [kindC])) hr
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr, h, one_mul, sub_eq_zero] at this
  exact this.symm

/-- **Inside a message** the index counts rows and the tuple is constant. -/
theorem in_msg {r : ℕ} (hr : r + 1 < n) (hf : M FIRSTM (r + 1) = 0) :
    M IDX (r + 1) = M IDX r + 1 ∧ ∀ c ∈ [HDR, WTX, SEG, TI, TA, TW, TL], M c (r + 1) = M c r := by
  constructor
  · have := sat hsat (mem_msgC (c := .mul (om (k FIRSTM)) (.mul notFirst (.sub (.sub (k IDX) (kp IDX)) one)))
      (by simp [msgC])) hr
    simp only [Expr.eval, om, one, notFirst, eval_cst, Nat.cast_one, ev_k hr, ev_kp hr, hf, first_off hr,
      sub_zero, one_mul] at this
    linear_combination this
  · intro c hc
    have := sat hsat (mem_msgC (c := .mul (om (k FIRSTM)) (.mul notFirst (.sub (k c) (kp c))))
      (by simp only [msgC, List.mem_append, List.mem_map]; right; exact ⟨c, hc, rfl⟩)) hr
    simp only [Expr.eval, om, one, notFirst, eval_cst, Nat.cast_one, ev_k hr, ev_kp hr, hf, first_off hr,
      sub_zero, one_mul] at this
    exact sub_eq_zero.mp this

/-- A continuing data row: the next row is data of the same piece. -/
theorem step_cont {r : ℕ} (hr : r + 1 < n) (h : M CONT r = 1) :
    M Z r = 0 ∧ M D (r + 1) = 1 ∧ M FIRSTM (r + 1) = 0 ∧
    M PC0 (r + 1) = M PC0 r ∧ M PC1 (r + 1) = M PC1 r ∧ M PC2 (r + 1) = M PC2 r := by
  have hr' : r < n := by omega
  obtain ⟨hc, hs, -⟩ := helpers hsat hr'
  obtain ⟨hd, hz⟩ := prod_one (bool_col hsat (e := D) (by simp) hr') (bool_col hsat (e := Z) (by simp) hr') (hc ▸ h)
  have hsw : M SW r = 0 := by rw [hs, hz, zero_mul]
  obtain ⟨t1, -, -, -, -, t6, t7, t8⟩ := trans_all hsat hr
  rw [h, hsw, add_zero] at t1
  obtain ⟨d1, f1⟩ := diff_one (bool_col hsat (e := D) (by simp) hr) (bool_col hsat (e := FIRSTM) (by simp) hr) t1
  refine ⟨hz, d1, f1, ?_, ?_, ?_⟩
  · rw [f1, h, sub_zero, one_mul] at t6; exact t6
  · rw [t7, h, hsw]; ring
  · rw [t8, h, hsw]; ring

/-- A piece switch: the next row is data of the next piece. -/
theorem step_sw {r : ℕ} (hr : r + 1 < n) (h : M SW r = 1) :
    M Z r = 1 ∧ M CONT r = 0 ∧ M D (r + 1) = 1 ∧ M FIRSTM (r + 1) = 0 ∧
    M PC0 (r + 1) = 0 ∧ M PC1 (r + 1) = M PC0 r ∧ M PC2 (r + 1) = M PC1 r := by
  have hr' : r < n := by omega
  obtain ⟨hc, hs, -⟩ := helpers hsat hr'
  have hz : M Z r = 1 := by
    rcases bool_col hsat (e := Z) (by simp) hr' with z | z
    · rw [hs, z, zero_mul] at h; exact absurd h zero_ne_one
    · exact z
  have hco : M CONT r = 0 := by rw [hc, hz, sub_self, mul_zero]
  obtain ⟨t1, -, -, -, -, t6, t7, t8⟩ := trans_all hsat hr
  rw [h, hco, zero_add] at t1
  obtain ⟨d1, f1⟩ := diff_one (bool_col hsat (e := D) (by simp) hr) (bool_col hsat (e := FIRSTM) (by simp) hr) t1
  refine ⟨hz, hco, d1, f1, ?_, ?_, ?_⟩
  · rw [f1, hco, sub_zero, zero_mul] at t6; exact t6
  · rw [t7, h, hco]; ring
  · rw [t8, h, hco]; ring

/-- The end of the data: the next row is the `0x80` byte. -/
theorem step_end {r : ℕ} (hr : r + 1 < n) (h : M ENDD r = 1) :
    M P80 (r + 1) = 1 ∧ M FIRSTM (r + 1) = 0 := by
  obtain ⟨-, t2, -⟩ := trans_all hsat hr
  have p1 : M P80 (r + 1) = 1 := t2.trans h
  refine ⟨p1, ?_⟩
  rcases bool_col hsat (e := FIRSTM) (by simp) hr with f | f
  · exact f
  · have := kind_unique hsat hr (a := P80) (b := D) (by simp [P80]) (by simp [D]) (by simp [P80, D]) p1
    rw [firstm_d hsat hr f] at this; exact absurd this one_ne_zero

theorem kind_off {r : ℕ} (hr : r < n) {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : a ≠ b) (h : M a r = 1)
    (h' : M b r = 1) : False := by
  have := kind_unique hsat hr ha hb hab h; rw [h'] at this; exact one_ne_zero this

/-- A row of kind other than data does not start a message. -/
theorem no_first {r : ℕ} (hr : r < n) {a : ℕ} (ha : a < 5) (had : a ≠ D) (h : M a r = 1) : M FIRSTM r = 0 := by
  rcases bool_col hsat (e := FIRSTM) (by simp) hr with f | f
  · exact f
  · exact (kind_off hsat hr ha (by simp [D]) had h (firstm_d hsat hr f)).elim

/-- After `0x80` or a zero: a zero, or at row 56 of the block the length starts. -/
theorem step_pad {r : ℕ} (hr : r + 1 < n) (h : M P80 r = 1 ∨ M ZR r = 1) :
    M FIRSTM (r + 1) = 0 ∧ ((r + 1) % 64 = 56 → M LN (r + 1) = 1) ∧ ((r + 1) % 64 ≠ 56 → M ZR (r + 1) = 1) := by
  have hr' : r < n := by omega
  have hs : M P80 r + M ZR r = 1 := by
    rcases h with h | h
    · rw [h, kind_unique hsat hr' (a := P80) (b := ZR) (by simp [P80]) (by simp [ZR]) (by simp [P80, ZR]) h, add_zero]
    · rw [h, kind_unique hsat hr' (a := ZR) (b := P80) (by simp [ZR]) (by simp [P80]) (by simp [P80, ZR]) h, zero_add]
  have hl : M LN r = 0 := by
    rcases h with h | h
    · exact kind_unique hsat hr' (a := P80) (b := LN) (by simp [P80]) (by simp [LN]) (by simp [P80, LN]) h
    · exact kind_unique hsat hr' (a := ZR) (b := LN) (by simp [ZR]) (by simp [LN]) (by simp [ZR, LN]) h
  obtain ⟨-, -, t3, t4, -⟩ := trans_all hsat hr
  rw [hs, one_mul] at t3 t4; rw [hl, zero_mul, add_zero] at t4
  by_cases h56 : (r + 1) % 64 = 56
  · simp only [h56, if_true] at t4
    exact ⟨no_first hsat hr (a := LN) (by simp [LN]) (by simp [LN, D]) t4, fun _ => t4, fun h => (h h56).elim⟩
  · simp only [h56, if_false, sub_zero] at t3
    exact ⟨no_first hsat hr (a := ZR) (by simp [ZR]) (by simp [ZR, D]) t3, fun h => (h56 h).elim, fun _ => t3⟩

/-- In the length: the next row continues it, or at a block start ends the message. -/
theorem step_ln {r : ℕ} (hr : r + 1 < n) (h : M LN r = 1) :
    ((r + 1) % 64 ≠ 0 → M LN (r + 1) = 1 ∧ M FIRSTM (r + 1) = 0) ∧
    ((r + 1) % 64 = 0 → M NIL (r + 1) + M FIRSTM (r + 1) = 1) := by
  have hr' : r < n := by omega
  have hp := kind_unique hsat hr' (a := LN) (b := P80) (by simp [LN]) (by simp [P80]) (by simp [P80, LN]) h
  have hz := kind_unique hsat hr' (a := LN) (b := ZR) (by simp [LN]) (by simp [ZR]) (by simp [ZR, LN]) h
  have hn := kind_unique hsat hr' (a := LN) (b := NIL) (by simp [LN]) (by simp [NIL]) (by simp [NIL, LN]) h
  obtain ⟨-, -, -, t4, t5, -⟩ := trans_all hsat hr
  rw [hp, hz, add_zero, zero_mul, zero_add, h, one_mul] at t4
  rw [h, hn, add_zero, one_mul] at t5
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · simp only [h0, if_false, sub_zero] at t4
    exact ⟨t4, no_first hsat hr (a := LN) (by simp [LN]) (by simp [LN, D]) t4⟩
  · simpa [h0] using t5

/-- A row of kind other than `NIL` is not the last. -/
theorem succ_lt {r : ℕ} (hr : r < n) {a : ℕ} (ha : a < 5) (hna : a ≠ NIL) (h : M a r = 1) : r + 1 < n := by
  by_contra hc
  have hl := last_nil hsat (by omega : 0 < n)
  rw [show n - 1 = r by omega] at hl
  exact kind_off hsat hr ha (by simp [NIL]) hna h hl

/-- **Zero run**: after `0x80` (or a zero) at row `p`, zeros until row 56 of a block. -/
theorem zero_run {p : ℕ} (hp : p < n) (h : M P80 p = 1 ∨ M ZR p = 1) (i : ℕ)
    (hj : ∀ j ≤ i, (p + j + 1) % 64 ≠ 56) : p + i + 1 < n ∧ M ZR (p + i + 1) = 1 ∧ M FIRSTM (p + i + 1) = 0 := by
  induction i with
  | zero =>
    have h1 : p + 1 < n := by
      rcases h with h | h
      · exact succ_lt hsat hp (a := P80) (by simp [P80]) (by simp [P80, NIL]) h
      · exact succ_lt hsat hp (a := ZR) (by simp [ZR]) (by simp [ZR, NIL]) h
    obtain ⟨f, -, z⟩ := step_pad hsat h1 h
    exact ⟨h1, z (hj 0 le_rfl), f⟩
  | succ i ih =>
    obtain ⟨hl, hz, -⟩ := ih (fun j hj' => hj j (by omega))
    have h2 := succ_lt hsat hl (a := ZR) (by simp [ZR]) (by simp [ZR, NIL]) hz
    obtain ⟨f, -, z⟩ := step_pad hsat h2 (Or.inr hz)
    have e : p + (i + 1) + 1 = p + i + 1 + 1 := by ring
    rw [e]; exact ⟨h2, z (by rw [← e]; exact hj (i + 1) le_rfl), f⟩

/-- **Length run**: the length rows continue to the end of the block. -/
theorem ln_run {q : ℕ} (hq : q < n) (h : M LN q = 1) (i : ℕ) (hi : q % 64 + i < 64) :
    q + i < n ∧ M LN (q + i) = 1 ∧ (0 < i → M FIRSTM (q + i) = 0) := by
  induction i with
  | zero => exact ⟨hq, h, fun h => absurd h (lt_irrefl 0)⟩
  | succ i ih =>
    obtain ⟨hl, hln, -⟩ := ih (by omega)
    have h2 := succ_lt hsat hl (a := LN) (by simp [LN]) (by simp [LN, NIL]) hln
    have hm : (q + i + 1) % 64 ≠ 0 := by omega
    obtain ⟨l1, f1⟩ := (step_ln hsat h2 hln).1 hm
    exact ⟨h2, l1, fun _ => f1⟩

/-- **Padding.** After `0x80` at row `p`: zeros up to the next row `s ≡ 56`, eight length rows, then a
new block row that is unused or starts a message. -/
theorem pad_ok {p : ℕ} (hp : p < n) (h : M P80 p = 1) :
    let s := p + 1 + (119 - p % 64) % 64
    s % 64 = 56 ∧ s + 8 < n ∧ (∀ j, p < j → j < s → M ZR j = 1 ∧ M FIRSTM j = 0) ∧
    (∀ j, s ≤ j → j < s + 8 → M LN j = 1 ∧ M FIRSTM j = 0) ∧ M NIL (s + 8) + M FIRSTM (s + 8) = 1 := by
  intro s
  have hs : s % 64 = 56 := by omega
  -- the row before `s` is `0x80` or a zero
  have hpre : s - 1 < n ∧ (M P80 (s - 1) = 1 ∨ M ZR (s - 1) = 1) := by
    by_cases h0 : (119 - p % 64) % 64 = 0
    · exact ⟨by omega, Or.inl (by rw [show s - 1 = p by omega]; exact h)⟩
    · obtain ⟨hl, hz, -⟩ := zero_run hsat hp (Or.inl h) ((119 - p % 64) % 64 - 1) (fun j hj => by omega)
      rw [show p + ((119 - p % 64) % 64 - 1) + 1 = s - 1 by omega] at hl hz
      exact ⟨hl, Or.inr hz⟩
  have hsn : s < n := by
    have := hpre.2
    rcases hpre.2 with h' | h'
    · have := succ_lt hsat hpre.1 (a := P80) (by simp [P80]) (by simp [P80, NIL]) h'; omega
    · have := succ_lt hsat hpre.1 (a := ZR) (by simp [ZR]) (by simp [ZR, NIL]) h'; omega
  obtain ⟨-, l56, -⟩ := step_pad hsat (by omega : s - 1 + 1 < n) hpre.2
  rw [show s - 1 + 1 = s by omega] at l56
  have hl := l56 hs
  obtain ⟨h7, l7, -⟩ := ln_run hsat hsn hl 7 (by omega)
  have h8 := succ_lt hsat h7 (a := LN) (by simp [LN]) (by simp [LN, NIL]) l7
  refine ⟨hs, h8, fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, ?_⟩
  · obtain ⟨-, hz, hf⟩ := zero_run hsat hp (Or.inl h) (j - p - 1) (fun j' hj' => by omega)
    rw [show p + (j - p - 1) + 1 = j by omega] at hz hf; exact ⟨hz, hf⟩
  · obtain ⟨-, hz, hf⟩ := ln_run hsat hsn hl (j - s) (by omega)
    rw [show s + (j - s) = j by omega] at hz hf
    refine ⟨hz, ?_⟩
    by_cases hjs : j = s
    · subst hjs; exact no_first hsat hsn (a := LN) (by simp [LN]) (by simp [LN, D]) hl
    · exact hf (by omega)
  · exact (step_ln hsat h8 l7).2 (by omega)

omit hsat in
theorem ev_byte {r j : ℕ} (hj : j ≤ r) (hr : r < n) :
    (byteE (-(j : ℤ))).eval n preCols pub M r = M BYTE (r - j) := by
  simp only [byteE, eval_col]; rw [wrap_back hj hr]

theorem pad_rows {p : ℕ} (hp : p < n) (h : M P80 p = 1) {j : ℕ} (hj1 : p < j)
    (hj2 : j < p + 1 + (119 - p % 64) % 64 + 8) :
    j < n ∧ M P80 j = 0 ∧ M FIRSTM j = 0 ∧ (M ZR j = 1 ∨ M LN j = 1) := by
  obtain ⟨-, h8, hz, hl, -⟩ := pad_ok hsat hp h
  have hjn : j < n := by omega
  by_cases hjs : j < p + 1 + (119 - p % 64) % 64
  · obtain ⟨z, f⟩ := hz j hj1 hjs
    exact ⟨hjn, kind_unique hsat hjn (a := ZR) (b := P80) (by simp [ZR]) (by simp [P80]) (by simp [ZR, P80]) z, f, Or.inl z⟩
  · obtain ⟨l, f⟩ := hl j (by omega) hj2
    exact ⟨hjn, kind_unique hsat hjn (a := LN) (b := P80) (by simp [LN]) (by simp [P80]) (by simp [LN, P80]) l, f, Or.inr l⟩

/-- Through the padding the index counts on and `DLC` holds the data length (the index at `0x80`). -/
theorem pad_idx {p : ℕ} (hp : p < n) (h : M P80 p = 1) (i : ℕ) (hi : i < (119 - p % 64) % 64 + 9) :
    M DLC (p + i) = M IDX p ∧ M IDX (p + i) = M IDX p + i := by
  induction i with
  | zero =>
    have := sat hsat (mem_padC (c := .mul (k P80) (.sub (k DLC) (k IDX))) (by simp [padC])) hp
    simp only [Expr.eval, ev_k hp, h, one_mul, sub_eq_zero] at this
    simpa using this
  | succ i ih =>
    obtain ⟨d, x⟩ := ih (by omega)
    obtain ⟨hjn, p0, f0, -⟩ := pad_rows hsat hp h (j := p + i + 1) (by omega) (by omega)
    have hjn' : p + i + 1 < n := hjn
    rw [show p + (i + 1) = p + i + 1 by ring]
    constructor
    · have := sat hsat (mem_padC (c := .mul (om (k P80)) (.mul notFirst (.sub (k DLC) (kp DLC)))) (by simp [padC])) hjn'
      simp only [Expr.eval, om, one, notFirst, eval_cst, Nat.cast_one, ev_k hjn', ev_kp hjn', p0, first_off hjn',
        sub_zero, one_mul] at this
      rw [sub_eq_zero.mp this, d]
    · rw [(in_msg hsat hjn' f0).1, x]; push_cast; ring

/-- **Padding bytes**: `0x80`, zeros, then the bit length `8 · (data length)` big-endian in the last
four rows. -/
theorem pad_bytes {p : ℕ} (hp : p < n) (h : M P80 p = 1) :
    let s := p + 1 + (119 - p % 64) % 64
    M BYTE p = 128 ∧ (∀ j, p < j → j < s + 4 → M BYTE j = 0) ∧
    16777216 * M BYTE (s + 4) + 65536 * M BYTE (s + 5) + 256 * M BYTE (s + 6) + M BYTE (s + 7) = 8 * M IDX p := by
  intro s
  obtain ⟨hs, h8, -, hl, -⟩ := pad_ok hsat hp h
  refine ⟨?_, fun j hj1 hj2 => ?_, ?_⟩
  · have := sat hsat (mem_padC (c := .mul (k P80) (.sub (k BYTE) (cst 128))) (by simp [padC])) hp
    simp only [Expr.eval, ev_k hp, h, one_mul, eval_cst, sub_eq_zero] at this
    rw [this]; norm_num
  · obtain ⟨hjn, -, -, zl⟩ := pad_rows hsat hp h (j := j) hj1 (by omega)
    by_cases hjs : j < s
    · have z := (pad_ok hsat hp h).2.2.1 j hj1 hjs |>.1
      have := sat hsat (mem_padC (c := .mul (k ZR) (k BYTE)) (by simp [padC])) hjn
      simp only [Expr.eval, ev_k hjn, z, one_mul] at this; exact this
    · have l := (hl j (by omega) (by omega)).1
      have hc := sat hsat (mem_padC (c := .mul (k LN) (.mul (pre LZ) (k BYTE))) (by simp [padC])) hjn
      rw [show Expr.eval n preCols pub M j (.mul (k LN) (.mul (pre LZ) (k BYTE))) =
        M LN j * ((pre LZ).eval n preCols pub M j * M BYTE j) by simp [Expr.eval, ev_k hjn],
        ev_per64 (p := fun q => 56 ≤ q && q < 60) rfl hjn, l, one_mul] at hc
      have hm : 56 ≤ j % 64 ∧ j % 64 < 60 := by omega
      simpa [hm] using hc
  · have hr : s + 7 < n := by omega
    have l := (hl (s + 7) (by omega) (by omega)).1
    have := sat hsat (mem_padC (c := .mul (pre IS63) (.mul (k LN) (.sub (.add (.add (.add (.mul (cst 16777216) (byteE (-3)))
      (.mul (cst 65536) (byteE (-2)))) (.mul (cst 256) (byteE (-1)))) (k BYTE)) (.mul (cst 8) (k DLC))))) (by simp [padC])) hr
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by simp, show (-2 : ℤ) = -((2 : ℕ) : ℤ) by simp,
      show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp] at this
    simp only [Expr.eval, ev_k hr, ev_byte (by omega : 3 ≤ s + 7) hr, ev_byte (by omega : 2 ≤ s + 7) hr,
      ev_byte (by omega : 1 ≤ s + 7) hr, ev_per64 (i := IS63) (p := (· = 63)) rfl hr, l, eval_cst, one_mul] at this
    have h63 : (s + 7) % 64 = 63 := by omega
    simp only [h63, decide_true, if_true, one_mul, sub_eq_zero] at this
    rw [show s + 7 - 3 = s + 4 by omega, show s + 7 - 2 = s + 5 by omega, show s + 7 - 1 = s + 6 by omega] at this
    have hd := (pad_idx hsat hp h (s + 7 - p) (by omega)).1
    rw [show p + (s + 7 - p) = s + 7 by omega] at hd
    rw [hd] at this
    push_cast at this ⊢; linear_combination this

/-- On a data row exactly one piece flag is set; in particular `PC0 + PC1` is a bit. -/
theorem pieces_one {r : ℕ} (hr : r < n) (hd : M D r = 1) : M PC0 r + M PC1 r = 0 ∨ M PC0 r + M PC1 r = 1 := by
  have := sat hsat (mem_transC (c := .sub (.add (k PC0) (.add (k PC1) (k PC2))) (k D)) (by simp [transC])) hr
  simp only [Expr.eval, ev_k hr, hd] at this
  have b0 := bool_val (bool_col hsat (e := PC0) (by simp) hr)
  have b1 := bool_val (bool_col hsat (e := PC1) (by simp) hr)
  have b2 := bool_val (bool_col hsat (e := PC2) (by simp) hr)
  have hs : (M PC0 r).val + (M PC1 r).val + (M PC2 r).val = 1 := by
    refine natCast_inj_of_lt ?_ (by unfold P; norm_num) ?_
    · have := b0.2; have := b1.2; have := b2.2; exact lt_P (by omega)
    · push_cast; rw [← b0.1, ← b1.1, ← b2.1]; linear_combination this
  rw [b0.1, b1.1, ← Nat.cast_add]
  have : (M PC0 r).val + (M PC1 r).val ≤ 1 := by omega
  interval_cases h : (M PC0 r).val + (M PC1 r).val <;> simp

theorem mt_bool {r : ℕ} (hr : r < n) : M MT r = 0 ∨ M MT r = 1 := by
  have hm := defn hsat (a := MT) (e := .mul (.sub (om (k WTX)) (k HDR)) (k SEG)) (mem_msgC (by simp [msgC])) hr
  have hx := sat hsat (mem_msgC (c := .mul (k WTX) (k HDR)) (by simp [msgC])) hr
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hr] at hm hx
  rw [hm]
  rcases bool_col hsat (e := WTX) (by simp) hr with w | w <;> rcases bool_col hsat (e := HDR) (by simp) hr with h | h <;>
    rcases bool_col hsat (e := SEG) (by simp) hr with g | g <;> simp_all

/-- A data row continues, switches piece, or ends the data; when it neither continues nor switches it
ends. -/
theorem data_next {r : ℕ} (hr : r < n) (hd : M D r = 1) (hc : M CONT r ≠ 1) (hs : M SW r ≠ 1) : M ENDD r = 1 := by
  obtain ⟨c, w, e⟩ := helpers hsat hr
  have hz : M Z r = 1 := by
    rcases bool_col hsat (e := Z) (by simp) hr with z | z
    · exact absurd (by rw [c, hd, z]; ring) hc
    · exact z
  have hsw : M SW r = 0 := by
    rw [w, hz, one_mul]
    rcases mt_bool hsat hr with m | m <;> rcases pieces_one hsat hr hd with q | q
    · rw [m, zero_mul]
    · rw [m, zero_mul]
    · rw [m, q, mul_zero]
    · exact absurd (by rw [w, hz, m, q]; ring) hs
  rw [e, hd, hz, hsw]; ring

/-- **Data walk.** From a message's first row `r0`, while no earlier row ended the data, each row is a
data row of the same message, at index `i`. -/
theorem data_walk {r0 : ℕ} (hr0 : r0 < n) (hf : M FIRSTM r0 = 1) (i : ℕ)
    (hi : ∀ j < i, M CONT (r0 + j) = 1 ∨ M SW (r0 + j) = 1) :
    r0 + i < n ∧ M D (r0 + i) = 1 ∧ M IDX (r0 + i) = i ∧ (0 < i → M FIRSTM (r0 + i) = 0) ∧
    ∀ c ∈ [HDR, WTX, SEG, TI, TA, TW, TL], M c (r0 + i) = M c r0 := by
  induction i with
  | zero =>
    have := sat hsat (mem_msgC (c := .mul (k FIRSTM) (k IDX)) (by simp [msgC])) hr0
    simp only [Expr.eval, ev_k hr0, hf, one_mul] at this
    exact ⟨hr0, firstm_d hsat hr0 hf, by simpa using this, fun h => absurd h (lt_irrefl 0), fun _ _ => rfl⟩
  | succ i ih =>
    obtain ⟨hl, hd, hx, -, ht⟩ := ih (fun j hj => hi j (by omega))
    have h2 := succ_lt hsat hl (a := D) (by simp [D]) (by simp [D, NIL]) hd
    have hd2 : M D (r0 + i + 1) = 1 ∧ M FIRSTM (r0 + i + 1) = 0 := by
      rcases hi i (by omega) with c | c
      · obtain ⟨-, d, f, -⟩ := step_cont hsat h2 c; exact ⟨d, f⟩
      · obtain ⟨-, -, d, f, -⟩ := step_sw hsat h2 c; exact ⟨d, f⟩
    obtain ⟨ix, tx⟩ := in_msg hsat h2 hd2.2
    rw [show r0 + (i + 1) = r0 + i + 1 by ring]
    refine ⟨h2, hd2.1, by rw [ix, hx]; push_cast; ring, fun _ => hd2.2, fun c hc => by rw [tx c hc, ht c hc]⟩

/-- **The data ends**: some row `r0 + d` ends it, every earlier one continues or switches. -/
theorem data_exit {r0 : ℕ} (hr0 : r0 < n) (hf : M FIRSTM r0 = 1) :
    ∃ d, (∀ j < d, M CONT (r0 + j) = 1 ∨ M SW (r0 + j) = 1) ∧ M ENDD (r0 + d) = 1 := by
  have ex : ∃ d, ¬ (M CONT (r0 + d) = 1 ∨ M SW (r0 + d) = 1) := by
    by_contra hne
    have := (data_walk hsat hr0 hf n (fun j _ => not_not.mp (not_exists.mp hne j))).1
    omega
  have hmin : ∀ j < Nat.find ex, M CONT (r0 + j) = 1 ∨ M SW (r0 + j) = 1 :=
    fun j hj => not_not.mp (Nat.find_min ex hj)
  refine ⟨Nat.find ex, hmin, ?_⟩
  · have hm := not_or.mp (Nat.find_spec ex)
    obtain ⟨hl, hd, -⟩ := data_walk hsat hr0 hf (Nat.find ex) hmin
    exact data_next hsat hl hd hm.1 hm.2

end Rows

end StarkedAir.Block.Msg
