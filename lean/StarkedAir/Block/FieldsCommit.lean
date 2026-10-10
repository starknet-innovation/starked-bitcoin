/-
**The commitment output's selection (M3a.5e), fields side.** `ISC` marks at most one output, a coinbase
output with segwit active; `AFT` counts the marked rows above; `HASC` says whether one is marked. Every
other coinbase output that must not match (all of them without a mark, those after the mark with one)
shows a mismatch: its script is at most 37 bytes, or one of its first six bytes differs from the
pattern `6a24aa21a9ed`.
-/
import StarkedAir.Block.FieldsScripts

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)

section Commit

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem isc_bool {r : ℕ} (hr : r < n) : M ISC r = 0 ∨ M ISC r = 1 := chk_bool hsat (e := ISC) (by simp [chkC, commitC]) hr

theorem g0_eq {r : ℕ} (hr : r < n) : M G0 r = M K_OUT r * (M ZT r * pub 6) := by
  rw [chk_defn hsat (a := G0) (e := .mul (k K_OUT) (.mul (k ZT) (.pub 6))) (by simp [chkC, commitC]) hr]
  simp [Expr.eval, ev_k hr]

/-- **A marked row** is an output of the coinbase, with segwit active. -/
theorem isc_out {r : ℕ} (hr : r < n) (h : M ISC r = 1) : M K_OUT r = 1 ∧ M ZT r = 1 ∧ pub 6 = 1 := by
  have := sat hsat (mem_chk (c := .mul (k ISC) (oneMinus (k G0))) (by simp [chkC, commitC])) hr
  simp only [Expr.eval, ev_k hr, h, one_mul, oneMinus, one, eval_cst, Nat.cast_one, sub_eq_zero] at this
  rw [g0_eq hsat hr] at this
  have ko := kind_bool hsat (c := K_OUT) (by simp [kinds, K_OUT]) hr
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  rcases ko with a | a <;> rcases zt with b | b <;> rw [a, b] at this <;> simp at this
  exact ⟨a, b, by simpa using this.symm⟩

/-- `AFT` counts the marked rows above. -/
theorem aft_sum (hn : 0 < n) : ∀ r < n, M AFT r = ∑ j ∈ Finset.range r, M ISC j := by
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_chk (c := .mul first (k AFT)) (by simp [chkC, commitC])) hr
    simpa [Expr.eval, ev_first hr, ev_k hr] using this
  | succ r ih =>
    have := sat hsat (mem_chk (c := .mul notFirst (.sub (.sub (k AFT) (kp AFT)) (kp ISC))) (by simp [chkC, commitC])) hr
    simp only [Expr.eval, ev_notFirst (pub := pub) (M := M) hr, one_mul, ev_k hr, ev_kp hr, sub_eq_zero] at this
    rw [Finset.sum_range_succ, ← ih (by omega)]; linear_combination this

/-- The number of marked rows below `r`, as a natural. -/
def iscN (M : ℕ → ℕ → F) (r : ℕ) : ℕ := ∑ j ∈ Finset.range r, (M ISC j).val

theorem aft_nat (hn : 0 < n) (hnP : n ≤ 2 ^ 25) {r : ℕ} (hr : r < n) :
    M AFT r = (iscN M r : F) ∧ iscN M r ≤ r := by
  have hb : ∀ j < n, M ISC j = (((M ISC j).val : ℕ) : F) ∧ (M ISC j).val ≤ 1 := fun j hj => bool_val (isc_bool hsat hj)
  refine ⟨?_, ?_⟩
  · rw [aft_sum hsat hn r hr, iscN, Nat.cast_sum]
    exact Finset.sum_congr rfl (fun j hj => (hb j (by simp at hj; omega)).1)
  · calc iscN M r ≤ ∑ j ∈ Finset.range r, 1 := Finset.sum_le_sum (fun j hj => (hb j (by simp at hj; omega)).2)
      _ = r := by simp

/-- **At most one marked row.** -/
theorem isc_unique (hn : 0 < n) (hnP : n ≤ 2 ^ 25) {r r' : ℕ} (hr : r < n) (hr' : r' < n)
    (h : M ISC r = 1) (h' : M ISC r' = 1) : r = r' := by
  wlog hlt : r < r' generalizing r r'
  · rcases Nat.lt_or_ge r' r with g | g
    · exact (this hr' hr h' h g).symm
    · omega
  exfalso
  have hz := sat hsat (mem_chk (c := .mul (k ISC) (k AFT)) (by simp [chkC, commitC])) hr'
  simp only [Expr.eval, ev_k hr', h', one_mul] at hz
  obtain ⟨ha, hle⟩ := aft_nat hsat hn hnP hr'
  rw [ha] at hz
  have h0 := natCast_inj_of_lt (a := iscN M r') (b := 0) (lt_P (by omega)) (lt_P (by norm_num)) (by simpa using hz)
  have : (M ISC r).val ≤ iscN M r' := Finset.single_le_sum (f := fun j => (M ISC j).val) (by simp)
    (Finset.mem_range.mpr hlt)
  rw [h, ZMod.val_one] at this; omega

/-- **`HASC` says whether a row is marked.** -/
theorem hasc_iff (hn : 0 < n) (hnP : n ≤ 2 ^ 25) :
    (M HASC 0 = 0 ∨ M HASC 0 = 1) ∧ (∀ r < n, M HASC r = M HASC 0) ∧
      (M HASC 0 = 1 ↔ ∃ r < n, M ISC r = 1) := by
  have hb := chk_bool hsat (e := HASC) (by simp [chkC, commitC]) hn
  have hc : ∀ r < n, M HASC r = M HASC 0 := by
    intro r hr
    induction r with
    | zero => rfl
    | succ r ih =>
      have := sat hsat (mem_chk (c := same HASC) (by simp [chkC, commitC])) hr
      simp only [same, Expr.eval, ev_notFirst (pub := pub) (M := M) hr, one_mul, ev_k hr, ev_kp hr, sub_eq_zero] at this
      rw [this, ih (by omega)]
  refine ⟨hb, hc, ?_⟩
  have hl : n - 1 < n := by omega
  have hlast := sat hsat (mem_chk (c := .mul isLast (.sub (k HASC) (k AFT))) (by simp [chkC, commitC])) hl
  simp only [Expr.eval, ev_last hl, show ¬ (n - 1 + 1 < n) by omega, if_false, one_mul, ev_k hl, sub_eq_zero] at hlast
  rw [hc _ hl] at hlast
  obtain ⟨ha, hle⟩ := aft_nat hsat hn hnP hl
  rw [ha] at hlast
  -- the last row is padding, so not marked
  have hisc_last : M ISC (n - 1) = 0 := by
    rcases isc_bool hsat hl with g | g
    · exact g
    · exfalso
      have := (isc_out hsat hl g).1
      rw [kind_unique hsat hl (a := K_PAD) (b := K_OUT) (by simp [K_PAD]) (by simp [K_OUT]) (by simp [K_PAD, K_OUT])
        (last_pad hsat hn)] at this
      exact zero_ne_one this
  constructor
  · intro h1
    rw [h1] at hlast
    have hpos : iscN M (n - 1) ≠ 0 := by
      intro h0; rw [h0] at hlast; simp at hlast
    obtain ⟨j, hj, hjv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos
    refine ⟨j, by simp at hj; omega, ?_⟩
    rcases isc_bool hsat (r := j) (by simp at hj; omega) with g | g
    · rw [g] at hjv; simp at hjv
    · exact g
  · rintro ⟨r, hr, hi⟩
    rcases hb with h0 | h1
    · exfalso
      rw [h0] at hlast
      have h00 := natCast_inj_of_lt (a := iscN M (n - 1)) (b := 0) (lt_P (by omega)) (lt_P (by norm_num))
        (by simpa using hlast.symm)
      rcases Nat.lt_or_ge r (n - 1) with g | g
      · have : (M ISC r).val ≤ iscN M (n - 1) := Finset.single_le_sum (f := fun j => (M ISC j).val) (by simp)
          (Finset.mem_range.mpr g)
        rw [hi, ZMod.val_one] at this; omega
      · rw [show r = n - 1 by omega, hisc_last] at hi; exact zero_ne_one hi
    · exact h1

end Commit

section CommitTok

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hbq : ∀ r < n, M GIN r + M MMB r = 1 → (M AQ r).val < R.length ∧ (M BQ r).val = (R.getD (M AQ r).val 0).toNat)
  (hrg : ∀ r < n, ∀ j < 13, (M (RG j) r).val < 256)
  (hn : n ≤ 2 ^ 25)
include hsat hcs hmn hpad hfit hbq hrg hn

theorem oh_eval {r : ℕ} (hr : r < n) (f : ℕ → ℕ) :
    (ohSum f).eval n preCols pub M r = ∑ j ∈ Finset.range 6, (f j : F) * M (OH j) r := by
  simp [ohSum, List.range_succ, Finset.sum_range_succ, Expr.eval, c, eval_cst, ev_k hr]
  ring

/-- **A coinbase output that must not match doesn't**: its script has at most 37 bytes, or one of its
first six bytes differs from the pattern. -/
theorem req_mismatch {r : ℕ} (hr : r < n) (hout : M K_OUT r = 1) (hzt : M ZT r = 1) (h6 : pub 6 = 1)
    (hisc : M ISC r = 0) (hreq : (M HASC r = 0 ∧ M AFT r = 0) ∨ (M HASC r = 1 ∧ M AFT r = 1)) :
    (M VAL r).val ≤ 37 ∨ ∃ j < 6, (M SSC r).val + j < R.length ∧ (R.getD ((M SSC r).val + j) 0).toNat ≠ pat.getD j 0 := by
  have hrm : r < m := lt_m hsat R hcs hmn hpad hfit hr (kind_unique hsat hr (a := K_OUT) (b := K_PAD) (by simp [K_OUT])
    (by simp [K_PAD]) (by simp [K_OUT, K_PAD]) hout)
  have hg0 : M G0 r = 1 := by rw [g0_eq hsat hr, hout, hzt, h6]; ring
  have hreqc : M REQC r = 1 := by
    rw [chk_defn hsat (a := REQC) (e := .mul (k G0) (oneMinus (k ISC))) (by simp [chkC, commitC]) hr]
    simp [Expr.eval, ev_k hr, oneMinus, one, eval_cst, hg0, hisc]
  have hreq1 : M REQ r = 1 := by
    rw [chk_defn hsat (a := REQ) (e := .mul (k REQC) (.add (oneMinus (k HASC)) (k AFT))) (by simp [chkC, commitC]) hr]
    simp only [Expr.eval, ev_k hr, oneMinus, one, eval_cst, Nat.cast_one, hreqc, one_mul]
    rcases hreq with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b] <;> ring
  have hsum := sat hsat (mem_chk (c := .sub (.add (k MML) (k MMB)) (k REQ)) (by simp [chkC, commitC])) hr
  simp only [Expr.eval, ev_k hr, hreq1, sub_eq_zero] at hsum
  have mml := chk_bool hsat (e := MML) (by simp [chkC, commitC]) hr
  have mmb := chk_bool hsat (e := MMB) (by simp [chkC, commitC]) hr
  have hval := (row_info hsat R hcs hmn hpad hfit hrm (a := K_OUT) (by simp [K_OUT]) hout (by simp [K_OUT, K_LOCK])
    (by simp [K_OUT, K_PAD])).1
  rcases mml with a | a
  · -- a pattern byte differs
    have hb : M MMB r = 1 := by rw [a, zero_add] at hsum; exact hsum
    right
    have hgin : M GIN r = 0 := by
      rw [chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr]
      simp [Expr.eval, ev_k hr, oneMinus, one, eval_cst, hzt]
    obtain ⟨hAQ, hBQ⟩ := hbq r hr (by rw [hgin, hb]; ring)
    -- the one-hot position
    have ohb : ∀ j < 6, M (OH j) r = 0 ∨ M (OH j) r = 1 := fun j hj => chk_bool hsat (e := OH j) (by
      have : boolC (k (OH j)) ∈ (List.range 6).map (fun j => boolC (k (OH j))) :=
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
      simp only [chkC, prevoutC, List.mem_append]; tauto) hr
    have hone := sat hsat (mem_chk (c := .mul (k MMB) (.sub (ohSum (fun _ => 1)) one)) (by simp [chkC, prevoutC])) hr
    simp only [Expr.eval, ev_k hr, hb, one_mul, oh_eval hsat R hcs hmn hpad hfit hbq hrg hn hr, one, eval_cst,
      Nat.cast_one, sub_eq_zero] at hone
    have vb : ∀ j < 6, M (OH j) r = (((M (OH j) r).val : ℕ) : F) ∧ (M (OH j) r).val ≤ 1 := fun j hj => bool_val (ohb j hj)
    have hsumN : ∑ j ∈ Finset.range 6, (M (OH j) r).val = 1 := by
      have e : ∑ j ∈ Finset.range 6, M (OH j) r = ((∑ j ∈ Finset.range 6, (M (OH j) r).val : ℕ) : F) := by
        rw [Nat.cast_sum]; exact Finset.sum_congr rfl (fun j hj => (vb j (by simpa using hj)).1)
      rw [e] at hone
      have : ∑ j ∈ Finset.range 6, (M (OH j) r).val ≤ 6 := by
        calc _ ≤ ∑ j ∈ Finset.range 6, 1 := Finset.sum_le_sum (fun j hj => (vb j (by simpa using hj)).2)
          _ = 6 := by simp
      exact natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) (by simpa using hone)
    obtain ⟨j0, hj0, hv0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsumN]; norm_num : ∑ j ∈ Finset.range 6, (M (OH j) r).val ≠ 0)
    have hj06 : j0 < 6 := by simpa using hj0
    have hoh : ∀ j < 6, M (OH j) r = if j = j0 then 1 else 0 := by
      intro j hj
      have v0 : (M (OH j0) r).val = 1 := by have := (vb j0 hj06).2; omega
      split_ifs with hjj
      · subst hjj; rw [(vb j hj).1, v0]; simp
      · have : (M (OH j) r).val + (M (OH j0) r).val ≤ ∑ j ∈ Finset.range 6, (M (OH j) r).val := by
          rw [← Finset.sum_pair (f := fun j => (M (OH j) r).val) hjj]
          exact Finset.sum_le_sum_of_subset (by intro x hx; simp at hx ⊢; omega)
        rw [hsumN, v0] at this
        rw [(vb j hj).1, show (M (OH j) r).val = 0 by omega]; simp
    have ohs : ∀ f : ℕ → ℕ, ∑ j ∈ Finset.range 6, (f j : F) * M (OH j) r = (f j0 : F) := by
      intro f
      rw [Finset.sum_congr rfl (fun j hj => by rw [hoh j (by simpa using hj)])]
      simp [Finset.sum_ite_eq', hj0]
    have haq := chk_defn hsat (a := AQ) (e := .add (.mul (k GIN) (.add (k START) qE)) (.mul (k MMB) (.add (k SSC) (ohSum id))))
      (by simp [chkC, prevoutC]) hr
    have hexp := chk_defn hsat (a := EXPQ) (e := .add (.mul (k GIN) (.mul (c 255) (k QH)))
      (.mul (k MMB) (ohSum (fun j => pat.getD j 0)))) (by simp [chkC, prevoutC]) hr
    have hne := sat hsat (mem_chk (c := .mul (.add (k GIN) (k MMB)) (.sub (.mul (.sub (k BQ) (k EXPQ)) (k INVQ)) one))
      (by simp [chkC, prevoutC])) hr
    simp only [Expr.eval, ev_k hr, hgin, hb, zero_mul, zero_add, one_mul, oh_eval hsat R hcs hmn hpad hfit hbq hrg hn hr,
      ohs, one, eval_cst, Nat.cast_one] at haq hexp hne
    have hssc := ssc_val hsat R hcs hmn hpad hfit hrm (a := K_OUT) (Or.inr rfl) hout
    have hpre : prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
    have hst := start_lt hsat hr
    have haqv : (M AQ r).val = (M SSC r).val + j0 := by
      rw [haq, show M SSC r + ((id j0 : ℕ) : F) = (((M SSC r).val + j0 : ℕ) : F) by push_cast; rw [ZMod.natCast_zmod_val]; rfl]
      exact ZMod.val_natCast_of_lt (lt_P (by rw [hssc]; simp [K_OUT, K_IN] at *; omega))
    refine ⟨j0, hj06, by rw [← haqv]; exact hAQ, fun heq => ?_⟩
    rw [← haqv, ← hBQ] at heq
    have hbq' : M BQ r = M EXPQ r := by
      rw [hexp, ← ZMod.natCast_zmod_val (M BQ r), heq]
    rw [hbq', sub_self, zero_mul, zero_sub, neg_eq_zero] at hne
    exact one_ne_zero hne
  · -- the script is short
    left
    have hrg12 := sat hsat (mem_chk (c := .mul (k MML) (.sub (rg 12) (.sub (c 37) (k VAL)))) (by simp [chkC, commitC])) hr
    simp only [Expr.eval, ev_k hr, a, one_mul, rg, c, eval_cst, sub_eq_zero] at hrg12
    have h12 := hrg r hr 12 (by norm_num)
    have e : (((M (RG 12) r).val + (M VAL r).val : ℕ) : F) = ((37 : ℕ) : F) := by
      push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, hrg12]; ring
    have := natCast_inj_of_lt (lt_P (by unfold MAXS at hval; omega)) (lt_P (by norm_num)) e
    omega

end CommitTok

end StarkedAir.Block.Fields
