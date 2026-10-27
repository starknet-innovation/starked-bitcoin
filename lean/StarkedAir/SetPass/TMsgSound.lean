/-
**The `TxOutSer` stream, soundness (`set_tmsg`).** In a satisfied `set_tmsg` trace whose lookups are
answered (pending bytes, file bytes, code bytes, records), the on rows are the stream `x`: the incoming
pending bytes, then per record `ρ < cnt` (in order) its `TxOutSer` bytes (`recSer`); the outgoing block
count and pending length are `|x| / 64` and `|x| % 64`, the outgoing pending bytes are `x`'s tail, and
every word yield is a word of a whole block of `x` (`tmsg_sound`).
-/
import StarkedAir.SetPass.TMsg
import StarkedAir.Gadgets.Sha256Sound

namespace StarkedAir.SetPass.TMsg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

/-- A record's `TxOutSer` bytes: the 36 outpoint bytes at its start, the 4 code bytes, `ser`. -/
def recSer (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) (ρ : ℕ) : List ℕ :=
  (List.range 36).map (fun j => S (st ρ + j)) ++ (List.range 4).map (cb ρ) ++
    (List.range (ln ρ)).map (fun j => S (st ρ + 49 + j))

/-- The stream: `ql` pending bytes, then the records' `TxOutSer` bytes. -/
def stream (pin : ℕ → ℕ) (ql cnt : ℕ) (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) : List ℕ :=
  (List.range ql).map pin ++ (List.range cnt).flatMap (recSer S cb st ln)

theorem recSer_length (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) (ρ : ℕ) :
    (recSer S cb st ln ρ).length = 40 + ln ρ := by
  simp [recSer]; omega

/-- Record `ρ` starts at `ql + Σ_{σ < ρ} (40 + ln σ)`. -/
def bnd (ql : ℕ) (ln : ℕ → ℕ) : ℕ → ℕ
  | 0 => ql
  | ρ + 1 => bnd ql ln ρ + (40 + ln ρ)

theorem bnd_mono (ql : ℕ) (ln : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : bnd ql ln a + 40 * (b - a) ≤ bnd ql ln b := by
  induction b with
  | zero => simp at h; subst h; simp
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · simp
    · have := ih (by omega); simp only [bnd]; rw [show b + 1 - a = b - a + 1 by omega]; omega

theorem flatMap_length (f : ℕ → List ℕ) (ql : ℕ) (ln : ℕ → ℕ) (hf : ∀ ρ, (f ρ).length = 40 + ln ρ) :
    ∀ cnt, ql + ((List.range cnt).flatMap f).length = bnd ql ln cnt
  | 0 => by simp [bnd]
  | c + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, ← Nat.add_assoc, flatMap_length f ql ln hf c]
    simp [bnd, hf]

theorem flatMap_getD (f : ℕ → List ℕ) (ql : ℕ) (ln : ℕ → ℕ) (hf : ∀ ρ, (f ρ).length = 40 + ln ρ) :
    ∀ cnt ρ o, ρ < cnt → o < 40 + ln ρ →
      ((List.range cnt).flatMap f).getD (bnd ql ln ρ + o - ql) 0 = (f ρ).getD o 0
  | 0, ρ, o, h, _ => absurd h (Nat.not_lt_zero _)
  | c + 1, ρ, o, h, ho => by
    have hl := flatMap_length f ql ln hf c
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | rfl
    · have hb : bnd ql ln ρ + o < bnd ql ln c := by
        have := bnd_mono ql ln (show ρ + 1 ≤ c by omega); simp only [bnd] at this; omega
      have hq : ql ≤ bnd ql ln ρ := by have := bnd_mono ql ln (Nat.zero_le ρ); simp [bnd] at this; omega
      rw [List.getD_append _ _ _ _ (by omega), flatMap_getD f ql ln hf c ρ o h' ho]
    · have hq : ql ≤ bnd ql ln ρ := by have := bnd_mono ql ln (Nat.zero_le ρ); simp [bnd] at this; omega
      rw [List.getD_append_right _ _ _ _ (by omega),
        show bnd ql ln ρ + o - ql - ((List.range ρ).flatMap f).length = o by omega]
      simp

theorem stream_length (pin : ℕ → ℕ) (ql cnt : ℕ) (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) :
    (stream pin ql cnt S cb st ln).length = bnd ql ln cnt := by
  rw [stream, List.length_append, List.length_map, List.length_range]
  exact flatMap_length _ ql ln (recSer_length S cb st ln) cnt

theorem stream_pend (pin : ℕ → ℕ) (ql cnt : ℕ) (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) {y : ℕ}
    (hy : y < ql) : (stream pin ql cnt S cb st ln).getD y 0 = pin y := by
  rw [stream, List.getD_append _ _ _ _ (by simpa using hy)]
  simp [hy]

theorem stream_rec (pin : ℕ → ℕ) (ql cnt : ℕ) (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) {ρ o : ℕ}
    (hρ : ρ < cnt) (ho : o < 40 + ln ρ) :
    (stream pin ql cnt S cb st ln).getD (bnd ql ln ρ + o) 0 = (recSer S cb st ln ρ).getD o 0 := by
  have hq : ql ≤ bnd ql ln ρ := by have := bnd_mono ql ln (Nat.zero_le ρ); simp [bnd] at this; omega
  rw [stream, List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range]
  exact flatMap_getD _ ql ln (recSer_length S cb st ln) cnt ρ o hρ ho

theorem recSer_get (S : ℕ → ℕ) (cb : ℕ → ℕ → ℕ) (st ln : ℕ → ℕ) (ρ o : ℕ) (ho : o < 40 + ln ρ) :
    (recSer S cb st ln ρ).getD o 0 =
      if o < 36 then S (st ρ + o) else if o < 40 then cb ρ (o - 36) else S (st ρ + 49 + (o - 40)) := by
  unfold recSer
  split_ifs with h1 h2
  · rw [List.append_assoc, List.getD_append _ _ _ _ (by simpa using h1)]; simp [h1]
  · rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [show o - 36 < 4 by omega]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [show o - 40 < ln ρ by omega]

/-! ### Small facts -/

theorem ltP {m : ℕ} (h : m ≤ 1073741824) : m < P := lt_of_le_of_lt h (by unfold P; norm_num)

theorem ceq {a b : ℕ} (ha : a ≤ 1073741824) (hb : b ≤ 1073741824) (h : (a : F) = (b : F)) : a = b :=
  natCast_inj_of_lt (ltP ha) (ltP hb) h

theorem v_one {x : F} (h : x = 1) : x.val = 1 := by rw [h]; exact ZMod.val_one P

theorem of_v1 {x : F} (h : x.val = 1) : x = 1 := by rw [← ZMod.natCast_zmod_val x, h]; simp

theorem of_v0 {x : F} (h : x.val = 0) : x = 0 := (ZMod.val_eq_zero x).mp h

theorem v_le {x : F} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by rcases h with h | h <;> simp [h, ZMod.val_one]

/-- **A monotone boolean column is a prefix.** -/
theorem prefix_of {n : ℕ} {f : ℕ → F} (hs : ∀ r, r + 1 < n → f (r + 1) = 1 → f r = 1) : ∃ E ≤ n, ∀ r < n, (f r = 1 ↔ r < E) := by
  classical
  by_cases hall : ∀ r < n, f r = 1
  · exact ⟨n, le_rfl, fun r hr => ⟨fun _ => hr, fun _ => hall r hr⟩⟩
  · push Not at hall
    have ex : ∃ r, r < n ∧ f r ≠ 1 := hall
    obtain ⟨hEn, hE1⟩ := Nat.find_spec ex
    have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ f r ≠ 1) := fun r h => Nat.find_min ex h
    generalize Nat.find ex = E at hEn hE1 hmin
    refine ⟨E, hEn.le, fun r hr => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
    · by_contra hc
      push Not at hc
      have : ∀ d, d ≤ r - E → f (r - d) = 1 := by
        intro d
        induction d with
        | zero => intro _; simpa using h1
        | succ d ih =>
          intro hd
          exact hs (r - (d + 1)) (by omega) (by rw [show r - (d + 1) + 1 = r - d by omega]; exact ih (by omega))
      have := this (r - E) le_rfl
      rw [show r - (r - E) = E by omega] at this
      exact hE1 this
    · have := hmin r hlt
      push Not at this
      exact this hr

/-- **No endless run**: a row property that always continues to a next row below `E` never holds. -/
theorem no_run {E : ℕ} (Q : ℕ → Prop) (hQ : ∀ y, Q y → y + 1 < E ∧ Q (y + 1)) (y : ℕ) : ¬ Q y := by
  intro hy
  have : ∀ d, y + d < E ∧ Q (y + d) := by
    intro d
    induction d with
    | zero => exact ⟨by have := (hQ y hy).1; omega, hy⟩
    | succ d ih =>
      have := hQ _ ih.2
      exact ⟨by omega, by rw [← Nat.add_assoc]; exact this.2⟩
  have := (this E).1
  omega

/-- Row `y` is byte `o` of record `ρ`, with its part and end flag. -/
abbrev RowSt (M : ℕ → ℕ → F) (ql : ℕ) (st ln : ℕ → ℕ) (cnt y ρ o : ℕ) : Prop :=
  ρ < cnt ∧ o < 40 + ln ρ ∧ y = bnd ql ln ρ + o ∧ M R y = (ρ : F) ∧ M O y = (o : F) ∧ M RST y = (st ρ : F) ∧
    M RLEN y = (ln ρ : F) ∧ (o < 36 → M P0 y = 1) ∧ (36 ≤ o → o < 40 → M PC y = 1) ∧ (40 ≤ o → M PS y = 1) ∧
    (M ENDR y = 1 ↔ o = 39 + ln ρ)

theorem sum01 {a b : F} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (h : a + b = 1) :
    (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp at h ⊢

theorem cast_ne {a b : ℕ} (ha : a ≤ 1073741824) (hb : b ≤ 1073741824) (h : a ≠ b) : (a : F) ≠ (b : F) :=
  fun e => h (ceq ha hb e)

/-! ### Rows -/

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
theorem ev_back {c r j : ℕ} (hj : j ≤ r) (hr : r < n) :
    (col c (-(j : ℤ))).eval n preCols pub M r = M c (r - j) := by
  rw [eval_col, wrap_back hj hr]

omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, p, pre, Expr.eval, wrap_zero hr, preCols, P_FIRST, PreCol.eval]

omit hsat in
theorem ev_f0 (hn : 0 < n) : first.eval n preCols pub M 0 = 1 := by simp [ev_first hn]

omit hsat in
theorem ev_fs {r : ℕ} (hr : r + 1 < n) : first.eval n preCols pub M (r + 1) = 0 := by simp [ev_first hr]

omit hsat in
theorem ev_nf0 (hn : 0 < n) : notFirst.eval n preCols pub M 0 = 0 := by
  simp [notFirst, om, one, Expr.eval, eval_cst, ev_f0 hn]

omit hsat in
theorem ev_nfs {r : ℕ} (hr : r + 1 < n) : notFirst.eval n preCols pub M (r + 1) = 1 := by
  simp [notFirst, om, one, Expr.eval, eval_cst, ev_fs hr]

omit hsat in
theorem ev_last {r : ℕ} (hr : r < n) : isLast.eval n preCols pub M r = if r + 1 < n then 0 else 1 := by
  simp only [isLast, om, one, Expr.eval, eval_cst, p, pre, wrap_zero hr, preCols, P_NOTLAST]
  simp [PreCol.eval]; split_ifs <;> simp

omit hsat in
theorem ev_per4 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per4 f) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub M r = ((f (r % 4) : ℕ) : F) := by
  simp only [p, pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
  simp [per4, PreCol.eval, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_per64 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = per64 f) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub M r = ((f (r % 64) : ℕ) : F) := by
  simp only [p, pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 64 < 64 := Nat.mod_lt _ (by norm_num)
  simp [per64, PreCol.eval, List.getD_eq_getElem?_getD, this]

omit hsat in
theorem ev_IS3 {r : ℕ} (hr : r < n) : (p P_IS3).eval n preCols pub M r = if r % 4 = 3 then 1 else 0 := by
  rw [ev_per4 (f := fun r => if r = 3 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_B0 {r : ℕ} (hr : r < n) : (p P_B0).eval n preCols pub M r = if r % 64 = 0 then 1 else 0 := by
  rw [ev_per64 (f := fun r => if r = 0 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_B63 {r : ℕ} (hr : r < n) : (p P_B63).eval n preCols pub M r = if r % 64 = 63 then 1 else 0 := by
  rw [ev_per64 (f := fun r => if r = 63 then 1 else 0) rfl hr]; split_ifs <;> simp

omit hsat in
theorem ev_K64 {r : ℕ} (hr : r < n) : (p P_K64).eval n preCols pub M r = ((r % 64 : ℕ) : F) :=
  ev_per64 (f := id) rfl hr

theorem bool {c : ℕ} (hc : c ∈ [ON, PND, P0, PC, PS, NEW, ENDR, TAIL]) {r : ℕ} (hr : r < n) :
    M c r = 0 ∨ M c r = 1 := by
  have h := hsat r hr (boolC (k c)) (by
    simp only [constraints, List.mem_append, List.mem_map]; left; exact ⟨c, hc, rfl⟩)
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at h
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem bv {c : ℕ} (hc : c ∈ [ON, PND, P0, PC, PS, NEW, ENDR, TAIL]) {r : ℕ} (hr : r < n) : (M c r).val ≤ 1 :=
  v_le (bool hsat hc hr)

/-! #### The constraints, evaluated -/

theorem c_on {r : ℕ} (hr : r < n) : M ON r = M PND r + (M P0 r + M PC r + M PS r) := by
  have h := hsat r hr (.sub (k ON) (.add (k PND) rec)) (by simp [constraints])
  simp only [Expr.eval, ev_k hr, rec] at h
  exact sub_eq_zero.mp h

theorem c_on0 (hn : 0 < n) : M ON 0 = 1 := by
  have h := hsat 0 hn (.mul first (om (k ON))) (by simp [constraints])
  simp only [Expr.eval, ev_f0 hn, om, one, eval_cst, ev_k hn, Nat.cast_one, one_mul] at h
  exact (sub_eq_zero.mp h).symm

theorem c_onl (hn : 0 < n) : M ON (n - 1) = 0 := by
  have hr : n - 1 < n := by omega
  have h := hsat (n - 1) hr (.mul isLast (k ON)) (by simp [constraints])
  simp only [Expr.eval, ev_last hr, ev_k hr, if_neg (show ¬ (n - 1 + 1 < n) by omega), one_mul] at h
  exact h

theorem c_onp {r : ℕ} (hr : r + 1 < n) : M ON (r + 1) * (1 - M ON r) = 0 := by
  have h := hsat (r + 1) hr (.mul notFirst (.mul (k ON) (om (kp ON)))) (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one] at h
  exact h

theorem c_y0 (hn : 0 < n) : M Y 0 = 0 := by
  have h := hsat 0 hn (.mul first (k Y)) (by simp [constraints])
  simpa only [Expr.eval, ev_f0 hn, ev_k hn, one_mul] using h

theorem c_ys {r : ℕ} (hr : r + 1 < n) : M Y (r + 1) = M Y r + 1 := by
  have h := hsat (r + 1) hr (.mul notFirst (.sub (.sub (k Y) (kp Y)) one)) (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr, one, eval_cst, Nat.cast_one] at h
  linear_combination h

theorem c_pndp {r : ℕ} (hr : r + 1 < n) : M PND (r + 1) * (1 - M PND r) = 0 := by
  have h := hsat (r + 1) hr (.mul notFirst (.mul (k PND) (om (kp PND)))) (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one] at h
  exact h

theorem c_pnd0 (hn : 0 < n) : (1 - M PND 0) * pub (H_PLEN SHA_IN) = 0 := by
  have h := hsat 0 hn (.mul first (.mul (om (k PND)) qlenIn)) (by simp [constraints])
  simp only [Expr.eval, ev_f0 hn, one_mul, ev_k hn, om, one, eval_cst, Nat.cast_one, qlenIn] at h
  exact h

theorem c_pndq {r : ℕ} (hr : r + 1 < n) : (M PND r - M PND (r + 1)) * (M Y (r + 1) - pub (H_PLEN SHA_IN)) = 0 := by
  have h := hsat (r + 1) hr (.mul notFirst (.mul (.sub (kp PND) (k PND)) (.sub (k Y) qlenIn)))
    (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr, qlenIn] at h
  exact h

theorem c_fr0 (hn : 0 < n) : M FR 0 = 1 - M PND 0 := by
  have h := hsat 0 hn (.sub (k FR) (.add (.mul first (om (k PND))) (.mul notFirst (.mul (kp PND) (om (k PND))))))
    (by simp [constraints])
  simp only [Expr.eval, ev_f0 hn, ev_nf0 hn, one_mul, zero_mul, add_zero, ev_k hn, om, one, eval_cst,
    Nat.cast_one] at h
  exact sub_eq_zero.mp h

theorem c_frs {r : ℕ} (hr : r + 1 < n) : M FR (r + 1) = M PND r * (1 - M PND (r + 1)) := by
  have h := hsat (r + 1) hr (.sub (k FR) (.add (.mul first (om (k PND))) (.mul notFirst (.mul (kp PND) (om (k PND))))))
    (by simp [constraints])
  simp only [Expr.eval, ev_fs hr, ev_nfs hr, one_mul, zero_mul, zero_add, ev_k hr, ev_kp hr, om, one, eval_cst,
    Nat.cast_one] at h
  exact sub_eq_zero.mp h

theorem c_new0 (hn : 0 < n) : M NEW 0 = M FR 0 := by
  have h := hsat 0 hn (.sub (k NEW) (.add (k FR) (.mul notFirst (.mul (kp ENDR) (k ON))))) (by simp [constraints])
  simp only [Expr.eval, ev_nf0 hn, zero_mul, add_zero, ev_k hn] at h
  exact sub_eq_zero.mp h

theorem c_news {r : ℕ} (hr : r + 1 < n) : M NEW (r + 1) = M FR (r + 1) + M ENDR r * M ON (r + 1) := by
  have h := hsat (r + 1) hr (.sub (k NEW) (.add (k FR) (.mul notFirst (.mul (kp ENDR) (k ON)))))
    (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr] at h
  exact sub_eq_zero.mp h

theorem c_newp0 {r : ℕ} (hr : r < n) : M NEW r * (1 - M P0 r) = 0 := by
  have h := hsat r hr (.mul (k NEW) (om (k P0))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_newo {r : ℕ} (hr : r < n) : M NEW r * M O r = 0 := by
  have h := hsat r hr (.mul (k NEW) (k O)) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr] using h

theorem c_frr {r : ℕ} (hr : r < n) : M FR r * M R r = 0 := by
  have h := hsat r hr (.mul (k FR) (k R)) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr] using h

theorem c_rs {r : ℕ} (hr : r + 1 < n) : (M NEW (r + 1) - M FR (r + 1)) * (M R (r + 1) - M R r - 1) = 0 := by
  have h := hsat (r + 1) hr (.mul (.sub (k NEW) (k FR)) (.sub (.sub (k R) (kp R)) one)) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, ev_kp hr, one, eval_cst, Nat.cast_one] using h

theorem c_cont {r : ℕ} (hr : r + 1 < n) (hct : M P0 (r + 1) + M PC (r + 1) + M PS (r + 1) - M NEW (r + 1) = 1) :
    M R (r + 1) = M R r ∧ M RST (r + 1) = M RST r ∧ M RLEN (r + 1) = M RLEN r ∧ M O (r + 1) = M O r + 1 := by
  have h1 := hsat (r + 1) hr (.mul cont (.sub (k R) (kp R))) (by simp [constraints])
  have h2 := hsat (r + 1) hr (.mul cont (.sub (k RST) (kp RST))) (by simp [constraints])
  have h3 := hsat (r + 1) hr (.mul cont (.sub (k RLEN) (kp RLEN))) (by simp [constraints])
  have h4 := hsat (r + 1) hr (.mul cont (.sub (.sub (k O) (kp O)) one)) (by simp [constraints])
  simp only [Expr.eval, cont, rec, ev_k hr, ev_kp hr, one, eval_cst, Nat.cast_one, hct, one_mul] at h1 h2 h3 h4
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3, by linear_combination h4⟩

theorem c_p0n {r : ℕ} (hr : r + 1 < n) : M P0 r * (1 - (M P0 (r + 1) + M PC (r + 1))) = 0 := by
  have h := hsat r (by omega) (.mul (k P0) (om (.add (kn P0) (kn PC)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_p0pc {r : ℕ} (hr : r + 1 < n) : M P0 r * (M PC (r + 1) * (M O r - 35)) = 0 := by
  have h := hsat r (by omega) (.mul (k P0) (.mul (kn PC) (.sub (k O) (cst 35)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, eval_cst, Nat.cast_ofNat] using h

theorem c_pcn {r : ℕ} (hr : r + 1 < n) : M PC r * (1 - (M PC (r + 1) + M PS (r + 1))) = 0 := by
  have h := hsat r (by omega) (.mul (k PC) (om (.add (kn PC) (kn PS)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_pcps {r : ℕ} (hr : r + 1 < n) : M PC r * (M PS (r + 1) * (M O r - 39)) = 0 := by
  have h := hsat r (by omega) (.mul (k PC) (.mul (kn PS) (.sub (k O) (cst 39)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, eval_cst, Nat.cast_ofNat] using h

theorem c_psn {r : ℕ} (hr : r + 1 < n) : M PS r * ((1 - M ENDR r) * (1 - M PS (r + 1))) = 0 := by
  have h := hsat r (by omega) (.mul (k PS) (.mul (om (k ENDR)) (om (kn PS)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_endr {r : ℕ} (hr : r < n) : M ENDR r * (1 - M PS r) = 0 := by
  have h := hsat r hr (.mul (k ENDR) (om (k PS))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_endro {r : ℕ} (hr : r < n) : M ENDR r * (M O r - (39 + M RLEN r)) = 0 := by
  have h := hsat r hr (.mul (k ENDR) (.sub (k O) (.add (cst 39) (k RLEN)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, eval_cst, Nat.cast_ofNat] using h

theorem c_ends {r : ℕ} (hr : r + 1 < n) : M ENDS r = M ON r * (1 - M ON (r + 1)) := by
  have h := hsat r (by omega) (.sub (k ENDS) (.mul (k ON) (om (kn ON)))) (by simp [constraints])
  simp only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, om, one, eval_cst, Nat.cast_one] at h
  exact sub_eq_zero.mp h

theorem c_endsr {r : ℕ} (hr : r < n) : M ENDS r * (1 - M ENDR r) = 0 := by
  have h := hsat r hr (.mul (k ENDS) (om (k ENDR))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_tailon {r : ℕ} (hr : r < n) : M TAIL r * (1 - M ON r) = 0 := by
  have h := hsat r hr (.mul (k TAIL) (om (k ON))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_tail0 (hn : 0 < n) : M TAIL 0 = 0 := by
  have h := hsat 0 hn (.mul first (k TAIL)) (by simp [constraints])
  simpa only [Expr.eval, ev_f0 hn, ev_k hn, one_mul] using h

theorem c_tails {r : ℕ} (hr : r + 1 < n) : M ON (r + 1) * (M TAIL r * (1 - M TAIL (r + 1))) = 0 := by
  have h := hsat (r + 1) hr (.mul (k ON) (.mul (kp TAIL) (om (k TAIL)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one] using h

theorem c_tailst {r : ℕ} (hr : r + 1 < n) :
    M TAIL (r + 1) * ((1 - M TAIL r) * (1 - if (r + 1) % 64 = 0 then 1 else 0)) = 0 := by
  have h := hsat (r + 1) hr (.mul (k TAIL) (.mul (om (kp TAIL)) (om (p P_B0)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, ev_B0 hr] using h

theorem c_tail63 {r : ℕ} (hr : r < n) : M TAIL r * (if r % 64 = 63 then 1 else 0) = 0 := by
  have h := hsat r hr (.mul (k TAIL) (p P_B63)) (by simp [constraints])
  simpa only [Expr.eval, ev_k hr, ev_B63 hr] using h

theorem c_nt {r : ℕ} (hr : r < n) : M NT r = M ON r * (1 - M TAIL r) := by
  have h := hsat r hr (.sub (k NT) (.mul (k ON) (om (k TAIL)))) (by simp [constraints])
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h
  exact sub_eq_zero.mp h

theorem c_ntend {r : ℕ} (hr : r + 1 < n) :
    M NT r * ((1 - if r % 64 = 63 then 1 else 0) * (1 - M ON (r + 1))) = 0 := by
  have h := hsat r (by omega) (.mul (k NT) (.mul (om (p P_B63)) (om (kn ON)))) (by simp [constraints])
  simpa only [Expr.eval, ev_k (show r < n by omega), ev_kn hr, om, one, eval_cst, Nat.cast_one,
    ev_B63 (show r < n by omega)] using h

theorem c_sb0 (hn : 0 < n) : M SB 0 = 0 := by
  have h := hsat 0 hn (.mul first (k SB)) (by simp [constraints])
  simpa only [Expr.eval, ev_f0 hn, ev_k hn, one_mul] using h

theorem c_sbs {r : ℕ} (hr : r + 1 < n) : M SB (r + 1) = M SB r + if (r + 1) % 64 = 0 then 1 else 0 := by
  have h := hsat (r + 1) hr (.mul notFirst (.sub (.sub (k SB) (kp SB)) (p P_B0))) (by simp [constraints])
  simp only [Expr.eval, ev_nfs hr, one_mul, ev_k hr, ev_kp hr, ev_B0 hr] at h
  linear_combination h

theorem c_out {r : ℕ} (hr : r < n) :
    M ENDS r * (pub (H_PLEN SHA_OUT) - M TAIL r * (((r % 64 : ℕ) : F) + 1)) = 0 ∧
    M ENDS r * ((pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)) - (M SB r + 1 - M TAIL r)) = 0 ∧
    M ENDS r * ((M R r + 1) - (pub PUB_I_OUT - pub PUB_I_IN)) = 0 := by
  have h1 := hsat r hr (.mul (k ENDS) (.sub (.pub (H_PLEN SHA_OUT)) (.mul (k TAIL) (.add (p P_K64) one))))
    (by simp [constraints])
  have h2 := hsat r hr (.mul (k ENDS) (.sub (.sub (.pub (H_NB SHA_OUT)) (.pub (H_NB SHA_IN)))
    (.sub (.add (k SB) one) (k TAIL)))) (by simp [constraints])
  have h3 := hsat r hr (.mul (k ENDS) (.sub (.add (k R) one) (.sub (.pub PUB_I_OUT) (.pub PUB_I_IN))))
    (by simp [constraints])
  simp only [Expr.eval, ev_k hr, ev_K64 hr, one, eval_cst, Nat.cast_one] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-! #### Structure -/

theorem kinds {r : ℕ} (hr : r < n) :
    (M ON r).val = (M PND r).val + (M P0 r).val + (M PC r).val + (M PS r).val := by
  have b1 := bv hsat (c := ON) (by simp) hr
  have b2 := bv hsat (c := PND) (by simp) hr
  have b3 := bv hsat (c := P0) (by simp) hr
  have b4 := bv hsat (c := PC) (by simp) hr
  have b5 := bv hsat (c := PS) (by simp) hr
  have e : (((M ON r).val : ℕ) : F) = (((M PND r).val + (M P0 r).val + (M PC r).val + (M PS r).val : ℕ) : F) := by
    push_cast; simp only [ZMod.natCast_zmod_val]; rw [c_on hsat hr]; ring
  exact ceq (by omega) (by omega) e

/-- A row of one kind is on and of no other kind. -/
theorem excl {r : ℕ} (hr : r < n) :
    (M P0 r = 1 → M PND r = 0 ∧ M PC r = 0 ∧ M PS r = 0 ∧ M ON r = 1) ∧
    (M PC r = 1 → M PND r = 0 ∧ M P0 r = 0 ∧ M PS r = 0 ∧ M ON r = 1) ∧
    (M PS r = 1 → M PND r = 0 ∧ M P0 r = 0 ∧ M PC r = 0 ∧ M ON r = 1) ∧
    (M PND r = 1 → M P0 r = 0 ∧ M PC r = 0 ∧ M PS r = 0 ∧ M ON r = 1) := by
  have hk := kinds hsat hr
  have b1 := bv hsat (c := ON) (by simp) hr
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> have := v_one h <;>
    exact ⟨of_v0 (by omega), of_v0 (by omega), of_v0 (by omega), of_v1 (by omega)⟩

theorem endr_ps {r : ℕ} (hr : r < n) (h : M ENDR r = 1) : M PS r = 1 := by
  have := c_endr hsat hr; rw [h, one_mul] at this; exact (sub_eq_zero.mp this).symm

theorem endr_zero {r : ℕ} (hr : r < n) (h : M PS r = 0) : M ENDR r = 0 := by
  have := c_endr hsat hr; rw [h, sub_zero, mul_one] at this; exact this

theorem on_prefix (hn : 0 < n) : ∃ E, 0 < E ∧ E < n ∧ ∀ r < n, (M ON r = 1 ↔ r < E) := by
  obtain ⟨E, -, hE⟩ := prefix_of (n := n) (f := fun r => M ON r) (fun r hr h1 => by
    have := c_onp hsat hr; rw [h1, one_mul] at this; exact (sub_eq_zero.mp this).symm)
  have h0 := (hE 0 hn).mp (c_on0 hsat hn)
  have hl : ¬ (n - 1 < E) := fun h => by
    have := (hE (n - 1) (by omega)).mpr h; rw [c_onl hsat hn] at this; exact zero_ne_one this
  exact ⟨E, h0, by omega, hE⟩

theorem y_row (hn : 0 < n) : ∀ r < n, M Y r = (r : F) := by
  intro r
  induction r with
  | zero => intro _; rw [c_y0 hsat hn]; simp
  | succ r ih => intro hr; rw [c_ys hsat hr, ih (by omega)]; push_cast; ring

theorem sb_row (hn : 0 < n) : ∀ r < n, M SB r = ((r / 64 : ℕ) : F) := by
  intro r
  induction r with
  | zero => intro _; rw [c_sb0 hsat hn]; simp
  | succ r ih =>
    intro hr; rw [c_sbs hsat hr, ih (by omega)]
    split_ifs with h
    · rw [show (r + 1) / 64 = r / 64 + 1 by omega]; push_cast; ring
    · rw [show (r + 1) / 64 = r / 64 by omega]; ring

/-- **A continuing row**: after a row that is neither pending nor a record's end, the next on row continues
the record. -/
theorem cont_next {y : ℕ} (hy : y + 1 < n) (hon : M ON (y + 1) = 1) (hp : M PND y = 0) (he : M ENDR y = 0) :
    M NEW (y + 1) = 0 ∧ M PND (y + 1) = 0 ∧ M R (y + 1) = M R y ∧ M RST (y + 1) = M RST y ∧
      M RLEN (y + 1) = M RLEN y ∧ M O (y + 1) = M O y + 1 := by
  have hp1 : M PND (y + 1) = 0 := by
    rcases bool hsat (c := PND) (by simp) hy with h | h
    · exact h
    · have := c_pndp hsat hy; rw [h, hp] at this; simp at this
  have hfr : M FR (y + 1) = 0 := by rw [c_frs hsat hy, hp, zero_mul]
  have hnew : M NEW (y + 1) = 0 := by rw [c_news hsat hy, hfr, he, zero_mul, add_zero]
  have hct : M P0 (y + 1) + M PC (y + 1) + M PS (y + 1) - M NEW (y + 1) = 1 := by
    have := c_on hsat hy; rw [hon, hp1, zero_add] at this; rw [hnew, sub_zero, ← this]
  exact ⟨hnew, hp1, c_cont hsat hy hct⟩

/-- **An outpoint part never runs past 36 bytes.** -/
theorem p0_run {E : ℕ} (hEn : E < n) (hE : ∀ r < n, M ON r = 1 ↔ r < E) (hn25 : n ≤ 33554432) (z : ℕ) :
    ¬ (z < n ∧ M P0 z = 1 ∧ ∃ o : ℕ, 36 ≤ o ∧ o ≤ z ∧ M O z = (o : F)) := by
  refine no_run (E := E) (fun z => z < n ∧ M P0 z = 1 ∧ ∃ o : ℕ, 36 ≤ o ∧ o ≤ z ∧ M O z = (o : F)) ?_ z
  rintro z ⟨hz, hp, o, ho36, hoz, hO⟩
  obtain ⟨hpnd, -, hps, hon⟩ := (excl hsat hz).1 hp
  have hzE := (hE z hz).mp hon
  have hz1 : z + 1 < n := by omega
  have he := endr_zero hsat hz hps
  have h1 := c_p0n hsat hz1
  have h2 := c_p0pc hsat hz1
  rw [hp, one_mul] at h1 h2
  have h35 : M O z - 35 ≠ 0 := by
    rw [hO, sub_ne_zero]; intro e
    have := ceq (a := o) (b := 35) (by omega) (by norm_num) (by rw [e]; norm_num); omega
  have hpc : M PC (z + 1) = 0 := (mul_eq_zero.mp h2).resolve_right h35
  have hp1 : M P0 (z + 1) = 1 := by rw [hpc, add_zero] at h1; exact (sub_eq_zero.mp h1).symm
  have hon1 := ((excl hsat hz1).1 hp1).2.2.2
  obtain ⟨-, -, -, -, -, hO1⟩ := cont_next hsat hz1 hon1 hpnd he
  exact ⟨(hE (z + 1) hz1).mp hon1, hz1, hp1, o + 1, by omega, by omega, by rw [hO1, hO]; push_cast; ring⟩

/-- **A `ser` part ends at its length**: past `39 + len` it would never end. -/
theorem ps_run {E : ℕ} (hEn : E < n) (hE : ∀ r < n, M ON r = 1 ↔ r < E) (hn25 : n ≤ 33554432) (z : ℕ) :
    ¬ (z < n ∧ M PS z = 1 ∧ M ENDR z = 0 ∧
      ∃ o l : ℕ, 39 + l ≤ o ∧ o ≤ z ∧ M O z = (o : F) ∧ M RLEN z = (l : F)) := by
  refine no_run (E := E) (fun z => z < n ∧ M PS z = 1 ∧ M ENDR z = 0 ∧
    ∃ o l : ℕ, 39 + l ≤ o ∧ o ≤ z ∧ M O z = (o : F) ∧ M RLEN z = (l : F)) ?_ z
  rintro z ⟨hz, hp, he, o, l, hol, hoz, hO, hL⟩
  obtain ⟨hpnd, -, -, hon⟩ := (excl hsat hz).2.2.1 hp
  have hzE := (hE z hz).mp hon
  have hz1 : z + 1 < n := by omega
  have h1 := c_psn hsat hz1
  rw [hp, he, one_mul, sub_zero, one_mul] at h1
  have hp1 : M PS (z + 1) = 1 := (sub_eq_zero.mp h1).symm
  have hon1 := ((excl hsat hz1).2.2.1 hp1).2.2.2
  obtain ⟨-, -, -, -, hL1, hO1⟩ := cont_next hsat hz1 hon1 hpnd he
  have he1 : M ENDR (z + 1) = 0 := by
    have h := c_endro hsat hz1
    rw [hO1, hL1, hO, hL] at h
    refine (mul_eq_zero.mp h).resolve_right (fun e0 => ?_)
    have e := sub_eq_zero.mp e0
    have := ceq (a := o + 1) (b := 39 + l) (by omega) (by omega) (by push_cast; rw [e]); omega
  exact ⟨(hE (z + 1) hz1).mp hon1, hz1, hp1, he1, o + 1, l, by omega, by omega, by rw [hO1, hO]; push_cast; ring,
    by rw [hL1, hL]⟩

variable {LEN : ℕ} {st ln : ℕ → ℕ}

/-- **The first record row**: right after the pending rows. -/
theorem base (hn : 0 < n) {E y0 : ℕ} (hEn : E < n) (hE : ∀ r < n, M ON r = 1 ↔ r < E)
    (hy0 : ∀ r < n, M PND r = 1 ↔ r < y0) (hy0E : y0 ≤ E)
    (hnew : ∀ r < n, M NEW r = 1 → ∃ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val,
      M R r = (ρ : F) ∧ M RST r = (st ρ : F) ∧ M RLEN r = (ln ρ : F)) :
    y0 < E ∧ RowSt M y0 st ln (pub PUB_I_OUT - pub PUB_I_IN).val y0 0 0 := by
  have hy0n : y0 < n := by omega
  have hp0 : M PND y0 = 0 := by
    rcases bool hsat (c := PND) (by simp) hy0n with h | h
    · exact h
    · exact absurd ((hy0 y0 hy0n).mp h) (lt_irrefl _)
  have hnw : M NEW y0 = 1 := by
    rcases Nat.eq_zero_or_pos y0 with h0 | hpos
    · subst h0; rw [c_new0 hsat hn, c_fr0 hsat hn, hp0, sub_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, y0 = j + 1 := ⟨y0 - 1, by omega⟩
      have hj : M PND j = 1 := (hy0 j (by omega)).mpr (by omega)
      have hej : M ENDR j = 0 := endr_zero hsat (by omega) ((excl hsat (by omega)).2.2.2 hj).2.2.1
      rw [c_news hsat hy0n, c_frs hsat hy0n, hj, hp0, hej]; ring
  have hP0 : M P0 y0 = 1 := by
    have := c_newp0 hsat hy0n; rw [hnw, one_mul] at this; exact (sub_eq_zero.mp this).symm
  obtain ⟨-, -, hps, hon⟩ := (excl hsat hy0n).1 hP0
  have hO : M O y0 = 0 := by have := c_newo hsat hy0n; rwa [hnw, one_mul] at this
  have hfr : M FR y0 = 1 := by
    rcases Nat.eq_zero_or_pos y0 with h0 | hpos
    · subst h0; rw [c_fr0 hsat hn, hp0, sub_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, y0 = j + 1 := ⟨y0 - 1, by omega⟩
      rw [c_frs hsat hy0n, (hy0 j (by omega)).mpr (by omega), hp0]; ring
  have hR : M R y0 = 0 := by have := c_frr hsat hy0n; rwa [hfr, one_mul] at this
  obtain ⟨ρ, hρ, hRρ, hst, hln⟩ := hnew y0 hy0n hnw
  have hρ0 : ρ = 0 := by
    have hlt := ZMod.val_lt (pub PUB_I_OUT - pub PUB_I_IN)
    exact natCast_inj_of_lt (by omega) (by unfold P; norm_num) (by rw [← hRρ, hR]; simp)
  subst hρ0
  refine ⟨(hE y0 hy0n).mp hon, hρ, by omega, by simp [bnd], by rw [hR]; simp, by rw [hO]; simp, hst, hln,
    fun _ => hP0, fun h => absurd h (by omega), fun h => absurd h (by omega), ⟨fun h => ?_, fun h => by omega⟩⟩
  rw [endr_ps hsat hy0n h] at hps; exact absurd hps one_ne_zero

/-- **One row on**: the next row is the next byte of the record, or the next record's first. -/
theorem step (hn25 : n ≤ 33554432) {E y0 : ℕ} (hEn : E < n) (hE : ∀ r < n, M ON r = 1 ↔ r < E)
    (hy0 : ∀ r < n, M PND r = 1 ↔ r < y0) (hLEN : LEN ≤ 67108864)
    (hrec : ∀ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val, 1 ≤ ln ρ ∧ st ρ + 49 + ln ρ ≤ LEN)
    (hpc : ∀ r < n, M PC r = 1 → ∃ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val, ∃ i : ℕ, i < 4 ∧
      M R r = (ρ : F) ∧ M O r - 36 = (i : F))
    (hnew : ∀ r < n, M NEW r = 1 → ∃ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val,
      M R r = (ρ : F) ∧ M RST r = (st ρ : F) ∧ M RLEN r = (ln ρ : F))
    {y ρ o : ℕ} (hy0y : y0 ≤ y) (hyE : y + 1 < E)
    (hs : RowSt M y0 st ln (pub PUB_I_OUT - pub PUB_I_IN).val y ρ o) :
    ∃ ρ' o', RowSt M y0 st ln (pub PUB_I_OUT - pub PUB_I_IN).val (y + 1) ρ' o' := by
  set cnt := (pub PUB_I_OUT - pub PUB_I_IN).val with hcnt
  have hcP : cnt < P := ZMod.val_lt _
  obtain ⟨hρ, ho, hyb, hR, hO, hRS, hRL, hq0, hqc, hqs, hend⟩ := hs
  have hy : y < n := by omega
  have hy1 : y + 1 < n := by omega
  have hon1 : M ON (y + 1) = 1 := (hE (y + 1) hy1).mpr hyE
  have hp : M PND y = 0 := by
    rcases bool hsat (c := PND) (by simp) hy with h | h
    · exact h
    · exact absurd ((hy0 y hy).mp h) (by omega)
  obtain ⟨hl1, hlL⟩ := hrec ρ hρ
  have hbo : bnd y0 ln ρ + o < n := by omega
  by_cases hfin : o = 39 + ln ρ
  · -- the record ends: the next row starts record `ρ + 1`
    have he : M ENDR y = 1 := hend.mpr hfin
    have hp1 : M PND (y + 1) = 0 := by
      rcases bool hsat (c := PND) (by simp) hy1 with h | h
      · exact h
      · have := c_pndp hsat hy1; rw [h, hp] at this; simp at this
    have hfr : M FR (y + 1) = 0 := by rw [c_frs hsat hy1, hp, zero_mul]
    have hnw : M NEW (y + 1) = 1 := by rw [c_news hsat hy1, hfr, he, hon1]; ring
    have hP0 : M P0 (y + 1) = 1 := by
      have := c_newp0 hsat hy1; rw [hnw, one_mul] at this; exact (sub_eq_zero.mp this).symm
    obtain ⟨-, -, hps, -⟩ := (excl hsat hy1).1 hP0
    have hO1 : M O (y + 1) = 0 := by have := c_newo hsat hy1; rwa [hnw, one_mul] at this
    have hR1 : M R (y + 1) = ((ρ + 1 : ℕ) : F) := by
      have := c_rs hsat hy1; rw [hnw, hfr, sub_zero, one_mul, hR] at this; push_cast; linear_combination this
    obtain ⟨ρ', hρ', hRρ', hst', hln'⟩ := hnew (y + 1) hy1 hnw
    have e : ρ' = ρ + 1 := natCast_inj_of_lt (by omega) (by omega) (by rw [← hRρ', hR1])
    subst e
    refine ⟨ρ + 1, 0, hρ', by omega, by simp only [bnd]; omega, hR1, by rw [hO1]; simp, hst', hln',
      fun _ => hP0, fun h => absurd h (by omega), fun h => absurd h (by omega), ⟨fun h => ?_, fun h => by omega⟩⟩
    rw [endr_ps hsat hy1 h] at hps; exact absurd hps one_ne_zero
  · -- the record continues
    have he : M ENDR y = 0 := by
      rcases bool hsat (c := ENDR) (by simp) hy with h | h
      · exact h
      · exact absurd (hend.mp h) hfin
    obtain ⟨-, -, hR1, hRS1, hRL1, hO1⟩ := cont_next hsat hy1 hon1 hp he
    have hO1' : M O (y + 1) = ((o + 1 : ℕ) : F) := by rw [hO1, hO]; push_cast; ring
    -- the part of the next row
    have parts : (o + 1 < 36 → M P0 (y + 1) = 1) ∧ (36 ≤ o + 1 → o + 1 < 40 → M PC (y + 1) = 1) ∧
        (40 ≤ o + 1 → M PS (y + 1) = 1) := by
      by_cases h35 : o < 36
      · have hP0 := hq0 h35
        have h1 := c_p0n hsat hy1
        have h2 := c_p0pc hsat hy1
        rw [hP0, one_mul] at h1 h2
        have hsum : M P0 (y + 1) + M PC (y + 1) = 1 := (sub_eq_zero.mp h1).symm
        rcases sum01 (bool hsat (c := P0) (by simp) hy1) (bool hsat (c := PC) (by simp) hy1) hsum with
          ⟨ha, hb⟩ | ⟨ha, hb⟩
        · refine ⟨fun _ => ha, fun h1 h2 => ?_, fun h => absurd h (by omega)⟩
          exact absurd (p0_run hsat hEn hE hn25 (y + 1) ⟨hy1, ha, o + 1, by omega, by omega, hO1'⟩) (by simp)
        · have h35' : o = 35 := by
            rw [hb, one_mul, hO, sub_eq_zero] at h2
            exact ceq (by omega) (by norm_num) (by rw [h2]; norm_num)
          exact ⟨fun h => absurd h (by omega), fun _ _ => hb, fun h => absurd h (by omega)⟩
      · by_cases h39 : o < 40
        · have hPC := hqc (by omega) h39
          have h1 := c_pcn hsat hy1
          have h2 := c_pcps hsat hy1
          rw [hPC, one_mul] at h1 h2
          have hsum : M PC (y + 1) + M PS (y + 1) = 1 := (sub_eq_zero.mp h1).symm
          rcases sum01 (bool hsat (c := PC) (by simp) hy1) (bool hsat (c := PS) (by simp) hy1) hsum with
            ⟨ha, hb⟩ | ⟨ha, hb⟩
          · refine ⟨fun h => absurd h (by omega), fun _ _ => ha, fun h => ?_⟩
            exfalso
            obtain ⟨ρ', -, i, hi, -, hOi⟩ := hpc (y + 1) hy1 ha
            rw [hO1', show o + 1 = 40 by omega] at hOi
            have := ceq (a := 4) (b := i) (by norm_num) (by omega) (by rw [← hOi]; norm_num)
            omega
          · have h39' : o = 39 := by
              rw [hb, one_mul, hO, sub_eq_zero] at h2
              exact ceq (by omega) (by norm_num) (by rw [h2]; norm_num)
            exact ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ => hb⟩
        · have hPS := hqs (by omega)
          have h1 := c_psn hsat hy1
          rw [hPS, he, one_mul, sub_zero, one_mul] at h1
          exact ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ => (sub_eq_zero.mp h1).symm⟩
    obtain ⟨pp0, ppc, pps⟩ := parts
    refine ⟨ρ, o + 1, hρ, by omega, by omega, by rw [hR1, hR], hO1', by rw [hRS1, hRS], by rw [hRL1, hRL],
      pp0, ppc, pps, ⟨fun h => ?_, fun h => ?_⟩⟩
    · -- an end row is a `ser` row at `39 + len`
      have hps := endr_ps hsat hy1 h
      by_cases h40 : 40 ≤ o + 1
      · have hc := c_endro hsat hy1
        rw [h, one_mul, hO1', hRL1, hRL, sub_eq_zero] at hc
        exact ceq (by omega) (by omega) (by rw [hc]; push_cast; ring)
      · exfalso
        by_cases h36 : o + 1 < 36
        · exact absurd hps (by rw [((excl hsat hy1).1 (pp0 h36)).2.2.1]; exact zero_ne_one)
        · exact absurd hps (by rw [((excl hsat hy1).2.1 (ppc (by omega) (by omega))).2.2.1]; exact zero_ne_one)
    · -- at `39 + len` the record ends
      by_contra hne
      have he1 : M ENDR (y + 1) = 0 := (bool hsat (c := ENDR) (by simp) hy1).resolve_right hne
      exact ps_run hsat hEn hE hn25 (y + 1) ⟨hy1, pps (by omega), he1, o + 1, ln ρ, by omega, by omega, hO1',
        by rw [hRL1, hRL]⟩

/-- **The tail**: the rows from the last multiple of 64 to the stream's end. -/
theorem tail_set (hn : 0 < n) {E : ℕ} (hEn : E < n) (hE : ∀ r < n, M ON r = 1 ↔ r < E) :
    ∀ r < n, (M TAIL r = 1 ↔ 64 * (E / 64) ≤ r ∧ r < E) := by
  classical
  have tON : ∀ r < n, M TAIL r = 1 → r < E := fun r hr h => by
    have := c_tailon hsat hr; rw [h, one_mul] at this; exact (hE r hr).mp (sub_eq_zero.mp this).symm
  by_cases hex : ∃ r, r < E ∧ M TAIL r = 1
  · obtain ⟨ht0E, ht01⟩ := Nat.find_spec hex
    have hmin : ∀ r < Nat.find hex, ¬ (r < E ∧ M TAIL r = 1) := fun r h => Nat.find_min hex h
    generalize Nat.find hex = t0 at ht0E ht01 hmin
    have ht0 : t0 ≠ 0 := by rintro rfl; rw [c_tail0 hsat hn] at ht01; exact zero_ne_one ht01
    obtain ⟨j, rfl⟩ : ∃ j, t0 = j + 1 := ⟨t0 - 1, by omega⟩
    have hj : M TAIL j = 0 := (bool hsat (c := TAIL) (by simp) (by omega)).resolve_right
      (fun h => hmin j (by omega) ⟨by omega, h⟩)
    have hm : (j + 1) % 64 = 0 := by
      have := c_tailst hsat (r := j) (by omega)
      rw [ht01, hj, one_mul, sub_zero, one_mul] at this
      by_contra hc; rw [if_neg hc, sub_zero] at this; exact one_ne_zero this
    have fwd : ∀ d, j + 1 + d < E → M TAIL (j + 1 + d) = 1 := by
      intro d
      induction d with
      | zero => intro _; simpa using ht01
      | succ d ih =>
        intro hd
        have h := c_tails hsat (r := j + 1 + d) (by omega)
        rw [(hE (j + 1 + d + 1) (by omega)).mpr (by omega), ih (by omega), one_mul, one_mul] at h
        rw [← Nat.add_assoc]; exact (sub_eq_zero.mp h).symm
    have hE63 : E ≤ j + 1 + 63 := by
      by_contra hc
      have h1 := fwd 63 (by omega)
      have := c_tail63 hsat (r := j + 1 + 63) (by omega)
      rw [h1, if_pos (by omega), one_mul] at this; exact one_ne_zero this
    intro r hr
    constructor
    · intro h
      have := tON r hr h
      refine ⟨?_, this⟩
      by_contra hc; exact hmin r (by omega) ⟨this, h⟩
    · rintro ⟨h1, h2⟩
      have := fwd (r - (j + 1)) (by omega); rwa [show j + 1 + (r - (j + 1)) = r by omega] at this
  · push Not at hex
    have hE0 : 0 < E := by
      by_contra h0
      have := (hE 0 hn).mpr; have := c_on0 hsat hn
      have := (hE 0 hn).mp this; omega
    have hl : M TAIL (E - 1) = 0 :=
      (bool hsat (c := TAIL) (by simp) (by omega)).resolve_right (hex _ (by omega))
    have hnt : M NT (E - 1) = 1 := by rw [c_nt hsat (by omega), (hE _ (by omega)).mpr (by omega), hl]; ring
    have hE64 : E % 64 = 0 := by
      have := c_ntend hsat (r := E - 1) (by omega)
      rw [hnt, one_mul, show E - 1 + 1 = E by omega] at this
      have hoff : M ON E = 0 := (bool hsat (c := ON) (by simp) hEn).resolve_right
        (fun h => absurd ((hE E hEn).mp h) (lt_irrefl _))
      rw [hoff, sub_zero, mul_one] at this
      by_contra hc
      rw [if_neg (by omega), sub_zero] at this; exact one_ne_zero this
    intro r hr
    constructor
    · intro h; exact absurd h (hex r (tON r hr h))
    · rintro ⟨h1, h2⟩; omega

/-- **`set_tmsg` is sound.** With every lookup answered (pending bytes, file bytes `S`, code bytes `cb`,
records `(st, ln)`), the on rows are the stream `x` (`stream`): its length is below `n`, the outgoing block
count and pending length are `|x| / 64` and `|x| % 64`, the outgoing pending bytes are `x`'s tail, and a
word yield at row `y` is `x`'s big-endian word at `y − 3`, in a whole block. -/
theorem tmsg_sound (hn : 0 < n) (hn25 : n ≤ 33554432) {S : ℕ → ℕ} {cb : ℕ → ℕ → ℕ} (hLEN : LEN ≤ 67108864)
    (hrec : ∀ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val, 1 ≤ ln ρ ∧ st ρ + 49 + ln ρ ≤ LEN)
    (hpnd : ∀ r < n, M PND r = 1 → ∃ q : ℕ, q < 64 ∧ M Y r = (q : F) ∧ M B r = pub (H_PEND SHA_IN q))
    (hp0 : ∀ r < n, M P0 r = 1 → ∃ q < LEN, M RST r + M O r = (q : F) ∧ (M B r).val = S q)
    (hps : ∀ r < n, M PS r = 1 → ∃ q < LEN, M RST r + M O r + 9 = (q : F) ∧ (M B r).val = S q)
    (hpc : ∀ r < n, M PC r = 1 → ∃ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val, ∃ i : ℕ, i < 4 ∧
      M R r = (ρ : F) ∧ M O r - 36 = (i : F) ∧ (M B r).val = cb ρ i)
    (hnew : ∀ r < n, M NEW r = 1 → ∃ ρ < (pub PUB_I_OUT - pub PUB_I_IN).val,
      M R r = (ρ : F) ∧ M RST r = (st ρ : F) ∧ M RLEN r = (ln ρ : F))
    (htail : ∀ r < n, M TAIL r = 1 → ∃ q : ℕ, q < 64 ∧ ((r % 64 : ℕ) : F) = (q : F) ∧
      M B r = pub (H_PEND SHA_OUT q)) :
    let x := stream (fun q => (pub (H_PEND SHA_IN q)).val) (pub (H_PLEN SHA_IN)).val
      (pub PUB_I_OUT - pub PUB_I_IN).val S cb st ln
    (pub (H_PLEN SHA_IN)).val ≤ 64 ∧ x.length < n ∧
    pub (H_NB SHA_OUT) - pub (H_NB SHA_IN) = ((x.length / 64 : ℕ) : F) ∧
    pub (H_PLEN SHA_OUT) = ((x.length % 64 : ℕ) : F) ∧
    (∀ q < x.length % 64, (pub (H_PEND SHA_OUT q)).val = x.getD (64 * (x.length / 64) + q) 0) ∧
    (∀ y < n, (Expr.mul (k NT) (p P_IS3)).eval n preCols pub M y ≠ 0 →
      y % 4 = 3 ∧ y < 64 * (x.length / 64) ∧
      (Expr.sub (k Y) (cst 3)).eval n preCols pub M y = ((y - 3 : ℕ) : F) ∧
      loW.eval n preCols pub M y = ((256 * x.getD (y - 1) 0 + x.getD y 0 : ℕ) : F) ∧
      hiW.eval n preCols pub M y = ((256 * x.getD (y - 3) 0 + x.getD (y - 2) 0 : ℕ) : F)) := by
  intro x
  have hxdef : x = stream (fun q => (pub (H_PEND SHA_IN q)).val) (pub (H_PLEN SHA_IN)).val
      (pub PUB_I_OUT - pub PUB_I_IN).val S cb st ln := rfl
  set cnt := (pub PUB_I_OUT - pub PUB_I_IN).val with hcnt
  have hcP : cnt < P := ZMod.val_lt _
  obtain ⟨E, hE0, hEn, hE⟩ := on_prefix hsat hn
  have hY := y_row hsat hn
  obtain ⟨y0, -, hy0⟩ := prefix_of (n := n) (f := fun r => M PND r) (fun r hr h1 => by
    have := c_pndp hsat hr; rw [h1, one_mul] at this; exact (sub_eq_zero.mp this).symm)
  have hy0E : y0 ≤ E := by
    by_contra hc
    have := (excl hsat hEn).2.2.2 ((hy0 E hEn).mpr (by omega))
    exact absurd ((hE E hEn).mp this.2.2.2) (lt_irrefl _)
  -- the pending length
  have hql : (pub (H_PLEN SHA_IN)).val = y0 ∧ y0 ≤ 64 := by
    rcases Nat.eq_zero_or_pos y0 with h0 | hpos
    · subst h0
      have hp : M PND 0 = 0 := (bool hsat (c := PND) (by simp) hn).resolve_right
        (fun h => absurd ((hy0 0 hn).mp h) (lt_irrefl _))
      have := c_pnd0 hsat hn; rw [hp, sub_zero, one_mul] at this
      rw [this]; simp
    · obtain ⟨j, rfl⟩ : ∃ j, y0 = j + 1 := ⟨y0 - 1, by omega⟩
      have hj : M PND j = 1 := (hy0 j (by omega)).mpr (by omega)
      have hj1 : M PND (j + 1) = 0 := (bool hsat (c := PND) (by simp) (by omega)).resolve_right
        (fun h => absurd ((hy0 _ (by omega)).mp h) (lt_irrefl _))
      have h := c_pndq hsat (r := j) (by omega)
      rw [hj, hj1, sub_zero, one_mul, hY (j + 1) (by omega), sub_eq_zero] at h
      obtain ⟨q, hq, hYq, -⟩ := hpnd j (by omega) hj
      rw [hY j (by omega)] at hYq
      have := ceq (by omega) (by omega) hYq
      refine ⟨?_, by omega⟩
      rw [← h, ZMod.val_natCast, Nat.mod_eq_of_lt (ltP (by omega))]
  obtain ⟨hqlv, hy064⟩ := hql
  obtain ⟨hy0lt, hb⟩ := base hsat hn hEn hE hy0 hy0E hnew
  have walk : ∀ d, y0 + d < E → ∃ ρ o, RowSt M y0 st ln cnt (y0 + d) ρ o := by
    intro d
    induction d with
    | zero => intro _; exact ⟨0, 0, hb⟩
    | succ d ih =>
      intro hd
      obtain ⟨ρ, o, hs⟩ := ih (by omega)
      rw [← Nat.add_assoc]
      exact step hsat hn25 hEn hE hy0 hLEN hrec
        (fun r hr h => by obtain ⟨ρ, hρ, i, hi, hR, hO, -⟩ := hpc r hr h; exact ⟨ρ, hρ, i, hi, hR, hO⟩)
        hnew (by omega) (by omega) hs
  -- the last row ends the last record
  have hoff : M ON E = 0 := (bool hsat (c := ON) (by simp) hEn).resolve_right
    (fun h => absurd ((hE E hEn).mp h) (lt_irrefl _))
  have hends : M ENDS (E - 1) = 1 := by
    rw [c_ends hsat (r := E - 1) (by omega), show E - 1 + 1 = E by omega, (hE _ (by omega)).mpr (by omega), hoff]
    ring
  have hlast : E = bnd y0 ln cnt := by
    obtain ⟨ρ, o, hρ, ho, hyb, hR, -, -, -, -, -, -, hend⟩ := walk (E - 1 - y0) (by omega)
    rw [show y0 + (E - 1 - y0) = E - 1 by omega] at hyb hR hend
    have he : M ENDR (E - 1) = 1 := by
      have := c_endsr hsat (r := E - 1) (by omega); rw [hends, one_mul] at this; exact (sub_eq_zero.mp this).symm
    have hfin := hend.mp he
    have hR1 := (c_out hsat (r := E - 1) (by omega)).2.2
    rw [hends, one_mul, hR, sub_eq_zero] at hR1
    have hc : ρ + 1 = cnt := by
      apply natCast_inj_of_lt (by omega) hcP
      rw [hcnt, ZMod.natCast_zmod_val]; push_cast; exact hR1
    rw [← hc]; simp only [bnd]; omega
  have hlen : x.length = E := by rw [hxdef, stream_length, hqlv, ← hlast]
  have bytes : ∀ y < E, (M B y).val = x.getD y 0 := by
    intro y hy
    by_cases hy0y : y < y0
    · obtain ⟨q, hq, hYq, hBq⟩ := hpnd y (by omega) ((hy0 y (by omega)).mpr hy0y)
      rw [hY y (by omega)] at hYq
      have := ceq (by omega) (by omega) hYq
      subst this
      rw [hBq, hxdef, stream_pend _ _ _ _ _ _ _ (by rw [hqlv]; exact hy0y)]
    · obtain ⟨ρ, o, hρ, ho, hyb, hR, hO, hRS, hRL, hq0, hqc, hqs, -⟩ := walk (y - y0) (by omega)
      rw [show y0 + (y - y0) = y by omega] at hyb hR hO hRS hRL hq0 hqc hqs
      obtain ⟨hl1, hlL⟩ := hrec ρ hρ
      have hx : x.getD y 0 = (recSer S cb st ln ρ).getD o 0 := by
        rw [hyb, hxdef, hqlv]; exact stream_rec _ _ _ _ _ _ _ hρ ho
      rw [hx, recSer_get _ _ _ _ _ _ ho]
      split_ifs with h1 h2
      · obtain ⟨q, hq, hpos, hB⟩ := hp0 y (by omega) (hq0 h1)
        rw [hRS, hO] at hpos
        have := ceq (a := st ρ + o) (b := q) (by omega) (by omega) (by push_cast; exact hpos)
        rw [hB, ← this]
      · obtain ⟨ρ', hρ', i, hi, hR', hOi, hB⟩ := hpc y (by omega) (hqc (by omega) h2)
        have e1 : ρ' = ρ := natCast_inj_of_lt (by omega) (by omega) (by rw [← hR', hR])
        rw [hO] at hOi
        have e2 : o - 36 = i := ceq (by omega) (by omega) (by rw [Nat.cast_sub (by omega), ← hOi]; norm_num)
        rw [hB, e1, e2]
      · obtain ⟨q, hq, hpos, hB⟩ := hps y (by omega) (hqs (by omega))
        rw [hRS, hO] at hpos
        have := ceq (a := st ρ + o + 9) (b := q) (by omega) (by omega) (by push_cast; exact hpos)
        rw [hB, ← this, show st ρ + o + 9 = st ρ + 49 + (o - 40) by omega]
  -- the tail and the outgoing state
  have hts := tail_set hsat hn hEn hE
  have hSB := sb_row hsat hn
  obtain ⟨o1, o2, -⟩ := c_out hsat (r := E - 1) (by omega)
  rw [hends, one_mul] at o1 o2
  have htl : M TAIL (E - 1) = if E % 64 = 0 then 0 else 1 := by
    split_ifs with h
    · exact (bool hsat (c := TAIL) (by simp) (by omega)).resolve_right
        (fun h1 => by have := (hts _ (by omega)).mp h1; omega)
    · exact (hts _ (by omega)).mpr ⟨by omega, by omega⟩
  rw [hSB (E - 1) (by omega), htl] at o2
  rw [htl] at o1
  refine ⟨by rw [hqlv]; exact hy064, by rw [hlen]; exact hEn, ?_, ?_, ?_, ?_⟩
  · rw [hlen, sub_eq_zero.mp o2]
    split_ifs with h
    · rw [show E / 64 = (E - 1) / 64 + 1 by omega]; push_cast; ring
    · rw [show (E - 1) / 64 = E / 64 by omega]; ring
  · rw [hlen, sub_eq_zero.mp o1]
    split_ifs with h
    · rw [h]; simp
    · rw [show E % 64 = (E - 1) % 64 + 1 by omega]; push_cast; ring
  · intro q hq
    rw [hlen] at hq ⊢
    have hr : 64 * (E / 64) + q < E := by omega
    obtain ⟨q', hq', hrq, hB⟩ := htail _ (by omega) ((hts _ (by omega)).mpr ⟨by omega, hr⟩)
    have : q = q' := ceq (by omega) (by omega) (by rw [← hrq, show (64 * (E / 64) + q) % 64 = q by omega])
    subst this
    rw [← hB, bytes _ hr]
  · intro y hy hm
    simp only [Expr.eval, ev_k hy, ev_IS3 hy] at hm
    have h3 : y % 4 = 3 := by
      by_contra h; rw [if_neg h, mul_zero] at hm; exact hm rfl
    rw [if_pos h3, mul_one, c_nt hsat hy] at hm
    have hon : M ON y = 1 := by
      rcases bool hsat (c := ON) (by simp) hy with h | h
      · rw [h, zero_mul] at hm; exact absurd rfl hm
      · exact h
    have hyE := (hE y hy).mp hon
    have htl0 : M TAIL y ≠ 1 := fun h => by rw [h, sub_self, mul_zero] at hm; exact hm rfl
    have hyt : y < 64 * (E / 64) := by
      by_contra hc; exact htl0 ((hts y hy).mpr ⟨by omega, hyE⟩)
    have hB : ∀ j ≤ 3, M B (y - j) = ((x.getD (y - j) 0 : ℕ) : F) := fun j hj => by
      rw [← bytes (y - j) (by omega), ZMod.natCast_zmod_val]
    have hB0 : M B y = ((x.getD y 0 : ℕ) : F) := by rw [← bytes y hyE, ZMod.natCast_zmod_val]
    have w1 : wrap n y (-1) = y - 1 := by
      have := wrap_back (n' := n) (k := 1) (by omega) hy; simpa using this
    have w2 : wrap n y (-2) = y - 2 := by
      have := wrap_back (n' := n) (k := 2) (by omega) hy; simpa using this
    have w3 : wrap n y (-3) = y - 3 := by
      have := wrap_back (n' := n) (k := 3) (by omega) hy; simpa using this
    refine ⟨h3, by rw [hlen]; exact hyt, ?_, ?_, ?_⟩
    · simp only [Expr.eval, ev_k hy, eval_cst, hY y hy]
      rw [Nat.cast_sub (by omega)]
    · simp only [loW, Expr.eval, eval_cst, ev_k hy, eval_col, w1, hB 1 (by norm_num), hB0]
      push_cast; ring
    · simp only [hiW, Expr.eval, eval_cst, eval_col, w2, w3, hB 2 (by norm_num), hB 3 (by norm_num)]
      push_cast; ring

end Rows

end StarkedAir.SetPass.TMsg

