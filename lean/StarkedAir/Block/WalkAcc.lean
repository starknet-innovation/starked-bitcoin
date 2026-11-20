/-
**Sigop walker, the accurate count and the last push (CONNECT-RULES step 3), soundness.** The walker's
rows run the automaton `wstep` (`WalkSound.lean`). `seg_gen` carries any decoration of that automaton
(`Spec/SigWalk.lean`: `runG`) along a span's rows, given one row's step. Three decorations:

* the value a multisig counts (`PV`): a span's `Σ OP · (SG − 20·MS + M1)` is `sigOpsAccurate` of its
  bytes (`seg_acc`), so `SUMA` is the sum over the spans of `(AC + 3·W4) · sigOpsAccurate` (`total_acc`);
* the opcodes above `OP_16` (`HCN`) and the state after the last byte: `PO` is `pushOnly` (`span_po`);
* the length of the last operation's data: `(RS, RL)` is the last push of a push-only script
  (`span_last`).
-/
import StarkedAir.Block.WalkSound
import StarkedAir.Spec.SigWalk

namespace StarkedAir.Block.Walk

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)
open StarkedAir.Spec.Block (WS wstep)
open StarkedAir.Spec.ConnectRules (runG fGH fA fH fL gA gH gL dvW accW)

/-- Row `r` represents state `s`, or is a run-to-the-end row inside data longer than the span. -/
def Rep' (M : ℕ → ℕ → F) (r : ℕ) (s : WS) : Prop :=
  Rep M r s ∨ (M INF r = 1 ∧ ∃ d, s = .data d ∧ (M REM r).val < d)

section Gen

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
  (hopc : ∀ r < n, M OP r = 1 → M PN r = (Tables.pushN (M B r).val : F) ∧ M K1 r = (Tables.isK 0x4c (M B r).val : F) ∧
    M K2 r = (Tables.isK 0x4d (M B r).val : F) ∧ M K4 r = (Tables.isK 0x4e (M B r).val : F) ∧
    M SG r = (Tables.sigN (M B r).val : F) ∧ M NZP r = (Tables.nzp (M B r).val : F))
  (hr8 : ∀ r < n, M TOPF r = 1 → (M B r - 2).val < 256)
  (R : Spec.Block.Bytes)
  (hread : ∀ r < n, M ACT r = 1 → (M POS r).val < R.length ∧ (M B r).val = (R.getD (M POS r).val 0).toNat)
  (hR : R.length ≤ 2 ^ 25)
include hsat hopc hr8 hread hR

omit hopc hr8 hread hR in
/-- A continuing row has one byte less left. -/
theorem rem_step {r : ℕ} (hr : r + 1 < n) (hg : M GC (r + 1) = 1) (h1 : 1 ≤ (M REM r).val)
    (h2 : (M REM r).val ≤ 2 ^ 25) : (M REM (r + 1)).val = (M REM r).val - 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, sREM, -⟩ := step hsat hr hg
  have e : M REM (r + 1) = (((M REM r).val - 1 : ℕ) : F) := by
    rw [sREM, Nat.cast_sub h1, ZMod.natCast_zmod_val]; simp
  rw [e]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))

omit hopc hr8 in
theorem pos_step {r : ℕ} (hr : r + 1 < n) (hg : M GC (r + 1) = 1) (ha : M ACT r = 1) :
    (M POS (r + 1)).val = (M POS r).val + 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, sPOS, -, -⟩ := step hsat hr hg
  obtain ⟨hpos, -⟩ := hread r (by omega) ha
  have e : M POS (r + 1) = (((M POS r).val + 1 : ℕ) : F) := by
    rw [sPOS]; push_cast; rw [ZMod.natCast_zmod_val]
  rw [e]
  exact ZMod.val_natCast_of_lt (Fields.lt_P (m := (M POS r).val + 1) (by omega))

omit hread hR in
/-- **A row's state steps to the next row's.** -/
theorem trans' {r : ℕ} (hr : r + 1 < n) {s : WS} (hs : Rep' M r s) (x : UInt8) (hx : (M B r).val = x.toNat)
    (h1 : 1 ≤ (M REM r).val) (h2 : (M REM r).val ≤ 2 ^ 25) (hg : M GC (r + 1) = 1) : Rep' M (r + 1) (wstep s x).1 := by
  have hrem := rem_step hsat hr hg h1 h2
  rcases hs with hrep | ⟨hinf, d, rfl, hd⟩
  · match s, hrep with
    | .op, h => exact Or.inl ((trans_op hsat hopc hr8 hr h x hx).2 hg)
    | .len k i acc, h =>
      rcases (trans_len hsat hopc hr8 hr h x hx).2 hg with a | ⟨hi, d, hd, he⟩
      · exact Or.inl a
      · exact Or.inr ⟨hi, d, he, by rw [hrem]; omega⟩
    | .data d, h => exact Or.inl ((trans_data hsat hopc hr8 hr h x).2 hg)
  · refine Or.inr ⟨(trans_inf hsat hopc hr8 hr hinf).2 hg, d - 1, ?_, by rw [hrem]; omega⟩
    simp only [wstep]; rw [if_neg (by omega)]

/-- **A span carries a decoration of the automaton.** `hstep` is one row: the row's quantity `q` is the
decoration's count, and the decoration's invariant `St` passes to a continuing row. Then over a span of
`L` rows from `r`, the quantities sum to the decorated run's sum over the span's bytes, and the run's
final state and decoration are one step from the last row's. -/
theorem seg_gen {σ : Type} (f : WS → σ → UInt8 → σ × ℕ) (q : ℕ → F) (St : ℕ → WS → σ → Prop)
    (hstep : ∀ j, j + 1 < n → M ACT j = 1 → 1 ≤ (M REM j).val → (M REM j).val ≤ 2 ^ 25 →
      ∀ (s : WS) (st : σ) (x : UInt8), (M B j).val = x.toNat → Rep' M j s → St j s st →
        q j = (((f s st x).2 : ℕ) : F) ∧
        (M GC (j + 1) = 1 → Rep' M (j + 1) (wstep s x).1 → St (j + 1) (wstep s x).1 (f s st x).1)) :
    ∀ L r, r < n → M ACT r = 1 → (M REM r).val = L → 1 ≤ L → L ≤ 2 ^ 25 → ∀ (s : WS) (st : σ), Rep' M r s → St r s st →
      ∃ (s' : WS) (st' : σ), Rep' M (r + L - 1) s' ∧ St (r + L - 1) s' st' ∧
        ∑ j ∈ Finset.range L, q (r + j) = (((runG f s st (Fields.slice R (M POS r).val L)).1 : ℕ) : F) ∧
        (runG f s st (Fields.slice R (M POS r).val L)).2 =
          ((wstep s' (R.getD (M POS (r + L - 1)).val 0)).1, (f s' st' (R.getD (M POS (r + L - 1)).val 0)).1) := by
  intro L
  induction L with
  | zero => intro r _ _ _ h; omega
  | succ L ih =>
    intro r hr ha hrem _ hL s st hs hst
    have hr1 := act_lt hsat hr ha
    obtain ⟨hpos, hx⟩ := hread r hr ha
    have hsl := slice_cons (L := L) hpos
    obtain ⟨hq, hnext⟩ := hstep r hr1 ha (by omega) (by omega) s st _ hx hs hst
    rcases Nat.eq_zero_or_pos L with h0 | hpos'
    · subst h0
      refine ⟨s, st, by simpa using hs, by simpa using hst, ?_, ?_⟩
      · rw [Finset.sum_range_one, Nat.add_zero, hq, hsl]; simp [runG, Fields.slice]
      · rw [hsl]; simp [runG, Fields.slice]
    · have zr := zspec hsat (z := ZR) (inv := INVR) (e := .sub (k REM) one)
        (fun c hc => by simp only [localC, List.mem_append]; tauto) hr
      simp only [Expr.eval, ev_k hr, one, eval_cst, Nat.cast_one] at zr
      have hz : M ZR r = 0 := by
        rcases zr.1 with h | h
        · exact h
        · exfalso; have := zr.2.1 h
          rw [← ZMod.natCast_zmod_val (M REM r), hrem, sub_eq_zero] at this
          have := natCast_inj_of_lt (a := L + 1) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
            (by simpa using this)
          omega
      have hg := cont hsat hr1 ha hz
      have ha1 : M ACT (r + 1) = 1 := by
        have := (defs hsat hr1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        rw [hg] at this
        rcases bool hsat (c := ACT) (by simp [bools]) hr1 with h | h
        · rw [h, zero_mul] at this; exact absurd this one_ne_zero
        · exact h
      have hrem1 : (M REM (r + 1)).val = L := by
        rw [rem_step hsat hr1 hg (by omega) (by omega), hrem]; rfl
      have hpos1 := pos_step hsat R hread hR hr1 hg ha
      have hs1 := trans' hsat hopc hr8 hr1 hs _ hx (by omega) (by omega) hg
      have hst1 := hnext hg hs1
      obtain ⟨s', st', a, b, c, d⟩ := ih (r + 1) hr1 ha1 hrem1 hpos' (by omega) _ _ hs1 hst1
      have split : ∑ j ∈ Finset.range (L + 1), q (r + j) = q r + ∑ j ∈ Finset.range L, q (r + 1 + j) := by
        rw [Finset.sum_range_succ', add_comm]; simp only [Nat.add_zero]; congr 1
        apply Finset.sum_congr rfl; intro j _; rw [show r + (j + 1) = r + 1 + j by ring]
      rw [show r + (L + 1) - 1 = r + 1 + L - 1 by omega]
      refine ⟨s', st', a, b, ?_, ?_⟩
      · rw [split, hq, hsl, runG, c, hpos1]; push_cast; rfl
      · rw [hsl, runG]; simp only; rw [← hpos1]; exact d

end Gen

/-! ### The accurate count -/

section Acc

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
  (hopc : ∀ r < n, M OP r = 1 → M PN r = (Tables.pushN (M B r).val : F) ∧ M K1 r = (Tables.isK 0x4c (M B r).val : F) ∧
    M K2 r = (Tables.isK 0x4d (M B r).val : F) ∧ M K4 r = (Tables.isK 0x4e (M B r).val : F) ∧
    M SG r = (Tables.sigN (M B r).val : F) ∧ M NZP r = (Tables.nzp (M B r).val : F))
  (hopc2 : ∀ r < n, M OP r = 1 → M HI r = (Tables.hiN (M B r).val : F) ∧ M MS r = (Tables.msN (M B r).val : F) ∧
    M DV r = (Tables.dvN (M B r).val : F))
  (hr8 : ∀ r < n, M TOPF r = 1 → (M B r - 2).val < 256)
  (R : Spec.Block.Bytes)
  (hread : ∀ r < n, M ACT r = 1 → (M POS r).val < R.length ∧ (M B r).val = (R.getD (M POS r).val 0).toNat)
  (hR : R.length ≤ 2 ^ 25)
include hsat hopc hopc2 hr8 hread hR

omit hopc hopc2 hr8 hread hR in
/-- A row that is not at an opcode has `OP = 0`. -/
theorem op_zero {j : ℕ} (hj : j < n) {s : WS} (hs : Rep' M j s) (hne : s ≠ .op) : M OP j = 0 := by
  rcases hs with hrep | ⟨hinf, d, rfl, -⟩
  · match s, hrep, hne with
    | .len k i acc, h, _ => exact (only hsat hj (c := LN) (by simp) h.1).2 OP (by simp) (by simp [LN, OP])
    | .data d, h, _ => exact (only hsat hj (c := DT) (by simp) h.1).2 OP (by simp) (by simp [DT, OP])
  · exact (only hsat hj (c := INF) (by simp) hinf).2 OP (by simp) (by simp [INF, OP])

omit hsat hopc hopc2 hr8 hread hR in
theorem op_one {j : ℕ} {s : WS} (hs : Rep' M j s) (he : s = .op) : M OP j = 1 := by
  subst he
  rcases hs with hrep | ⟨-, d, hd, -⟩
  · exact hrep
  · cases hd

omit hopc hopc2 hr8 hread hR in
/-- The previous opcode's value passes to a continuing row. -/
theorem pv_step {j : ℕ} (hj : j + 1 < n) (hg : M GC (j + 1) = 1) :
    M PV (j + 1) = M OP j * M DV j + (1 - M OP j) * M PV j := by
  have hj' : j < n := by omega
  have c2 := sat hsat (mem_acc (c := .mul (k GC) (.sub (k PV) (kp NPV))) (by simp [accC])) hj
  have c3 := sat hsat (mem_acc (c := .sub (k NPV) (.add (.mul (k OP) (k DV)) (.mul (om (k OP)) (k PV))))
    (by simp [accC])) hj'
  simp only [Expr.eval, ev_k hj, ev_kp hj, hg, one_mul] at c2
  simp only [Expr.eval, ev_k hj', om, one, eval_cst, Nat.cast_one] at c3
  linear_combination c2 + c3

omit hr8 hread hR in
/-- One row of the accurate count: the decoration is `PV`, at most 20. -/
theorem acc_row : ∀ j, j + 1 < n → M ACT j = 1 → 1 ≤ (M REM j).val → (M REM j).val ≤ 2 ^ 25 →
    ∀ (s : WS) (pv : ℕ) (x : UInt8), (M B j).val = x.toNat → Rep' M j s → (M PV j = (pv : F) ∧ pv ≤ 20) →
      M OP j * (M SG j - 20 * M MS j + M M1 j) = (((fA s pv x).2 : ℕ) : F) ∧
      (M GC (j + 1) = 1 → Rep' M (j + 1) (wstep s x).1 →
        (M PV (j + 1) = (((fA s pv x).1 : ℕ) : F) ∧ (fA s pv x).1 ≤ 20)) := by
  intro j hj _ _ _ s pv x hx hs ⟨hpv, hpv20⟩
  have hj' : j < n := by omega
  by_cases hop : s = .op
  · have o1 := op_one hs hop
    subst hop
    obtain ⟨-, hms, hdv⟩ := hopc2 j hj' o1
    have m1 := sat hsat (mem_acc (c := .sub (k M1) (.mul (k MS) (k PV))) (by simp [accC])) hj'
    simp only [Expr.eval, ev_k hj', sub_eq_zero] at m1
    have hf1 : (fA .op pv x).1 = dvW x := by simp [fA, fGH, gA]
    have hf2 : (fA .op pv x).2 = accW pv x := by simp [fA, fGH, gA]
    rw [hf1, hf2]
    refine ⟨?_, fun hg _ => ⟨?_, ?_⟩⟩
    · -- the row's count
      have hsg : M SG j = (Tables.sigN (M B j).val : F) := (hopc j hj' o1).2.2.2.2.1
      rw [o1, one_mul, m1, hsg, hms, hpv, hx]
      unfold Tables.sigN Tables.msN accW
      by_cases h1 : x.toNat = 0xac ∨ x.toNat = 0xad
      · rw [if_pos h1, if_pos h1, if_neg (by omega)]; push_cast; ring
      · by_cases h2 : x.toNat = 0xae ∨ x.toNat = 0xaf
        · rw [if_neg h1, if_pos h2, if_pos h2, if_neg h1, if_pos h2]; push_cast; ring
        · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1, if_neg h2]; push_cast; ring
    · rw [pv_step hsat hj hg, o1, hdv, hx]; unfold Tables.dvN dvW; ring
    · unfold dvW; split_ifs <;> omega
  · have o0 := op_zero hsat hj' hs hop
    have hf : fA s pv x = (pv, 0) := by
      match s, hop with
      | .len k i acc, _ => simp [fA, fGH]
      | .data d, _ => simp [fA, fGH]
    rw [hf]
    exact ⟨by rw [o0]; simp, fun hg _ => ⟨by rw [pv_step hsat hj hg, o0, hpv]; ring, hpv20⟩⟩

omit hopc hopc2 hr8 in
/-- The rows of a span: active, with their bytes left and positions, continuing after the first. -/
theorem span_rows {f L : ℕ} (hf : f < n) (ha : M ACT f = 1) (hrem : (M REM f).val = L) (h1 : 1 ≤ L)
    (hL : L ≤ 2 ^ 25) : ∀ j < L, f + j < n ∧ M ACT (f + j) = 1 ∧ (M REM (f + j)).val = L - j ∧
      (M POS (f + j)).val = (M POS f).val + j ∧ (1 ≤ j → M GC (f + j) = 1) := by
  obtain ⟨hgc, -, -, hfl⟩ := seg_rows hsat L f hf ha hrem h1 hL
  intro j
  induction j with
  | zero => intro _; exact ⟨hf, ha, by simpa using hrem, rfl, fun h => by omega⟩
  | succ j ih =>
    intro hj
    obtain ⟨a1, a2, a3, a4, -⟩ := ih (by omega)
    have hr1 : f + j + 1 < n := by omega
    have hg := hgc (j + 1) (by omega) hj
    rw [show f + (j + 1) = f + j + 1 by omega] at hg ⊢
    have hact : M ACT (f + j + 1) = 1 := by
      have := (defs hsat hr1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      rw [hg] at this
      rcases bool hsat (c := ACT) (by simp [bools]) hr1 with h | h
      · rw [h, zero_mul] at this; exact absurd this one_ne_zero
      · exact h
    refine ⟨hr1, hact, ?_, ?_, fun _ => hg⟩
    · rw [rem_step hsat hr1 hg (by omega) (by omega), a3]; omega
    · rw [pos_step hsat R hread hR hr1 hg a2, a4]; omega

omit hopc hopc2 hr8 hread hR in
/-- A span's mode, weight and outputs are the same on a continuing row. -/
theorem const_step {c : ℕ} (hc : c ∈ [AC, W4, PO, RS, RL]) {r : ℕ} (hr : r + 1 < n) (hg : M GC (r + 1) = 1) :
    M c (r + 1) = M c r := by
  have hm : Expr.mul (k GC) (.sub (k c) (kp c)) ∈ accC := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [accC]
  have := sat hsat (mem_acc hm) hr
  simp only [Expr.eval, ev_k hr, ev_kp hr, hg, one_mul] at this
  linear_combination this

omit hopc hopc2 hr8 in
theorem span_const {c : ℕ} (hc : c ∈ [AC, W4, PO, RS, RL]) {f L : ℕ} (hf : f < n) (ha : M ACT f = 1)
    (hrem : (M REM f).val = L) (h1 : 1 ≤ L) (hL : L ≤ 2 ^ 25) : ∀ j < L, M c (f + j) = M c f := by
  have hrows := span_rows hsat R hread hR hf ha hrem h1 hL
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    obtain ⟨a1, -, -, -, a5⟩ := hrows (j + 1) hj
    rw [show f + (j + 1) = f + j + 1 by omega] at a1 a5 ⊢
    rw [const_step hsat hc a1 (a5 (by omega)), ih (by omega)]

/-- **A span's accurate count** is `GetSigOpCount(true)` of its bytes. -/
theorem seg_acc {f : ℕ} (hf : f < n) (hfs : M FS f = 1) {L : ℕ} (hrem : (M REM f).val = L) (h1 : 1 ≤ L)
    (hL : L ≤ 2 ^ 25) :
    ∑ j ∈ Finset.range L, M OP (f + j) * (M SG (f + j) - 20 * M MS (f + j) + M M1 (f + j)) =
      ((Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val L) : ℕ) : F) := by
  obtain ⟨-, hfa, hfo⟩ := kinds hsat hf
  have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
  have hop : M OP f = 1 := by rw [hfs] at hfo; linear_combination -hfo
  have c2 := sat hsat (mem_acc (c := .mul (k FS) (.sub (k PV) (cst 20))) (by simp [accC])) hf
  simp only [Expr.eval, ev_k hf, eval_cst, hfs, one_mul] at c2
  obtain ⟨s', st', -, -, hsum, -⟩ := seg_gen hsat hopc hr8 R hread hR fA
    (fun j => M OP j * (M SG j - 20 * M MS j + M M1 j)) (fun j _ pv => M PV j = (pv : F) ∧ pv ≤ 20)
    (acc_row hsat hopc hopc2) L f hf ha hrem h1 hL .op 20 (Or.inl hop) ⟨by push_cast; linear_combination c2, le_rfl⟩
  rw [hsum, Spec.ConnectRules.acc_run]

omit hopc hopc2 hr8 hread hR in
/-- An inactive row is no opcode. -/
theorem op_inactive {j : ℕ} (hj : j < n) (h0 : M ACT j = 0) : M OP j = 0 := by
  obtain ⟨hk, -, -⟩ := kinds hsat hj
  have bv := fun d (hd : d ∈ bools) => Fields.bool_val (bool hsat hd hj)
  obtain ⟨vo, lo⟩ := bv OP (by simp [bools]); obtain ⟨vl, ll⟩ := bv LN (by simp [bools])
  obtain ⟨vd, ld⟩ := bv DT (by simp [bools]); obtain ⟨vi, li⟩ := bv INF (by simp [bools])
  have e : (((M OP j).val + (M LN j).val + (M DT j).val + (M INF j).val : ℕ) : F) = ((0 : ℕ) : F) := by
    push_cast; rw [← vo, ← vl, ← vd, ← vi, hk, h0]
  have := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) e
  rw [vo, show (M OP j).val = 0 by omega]; simp

omit hopc hopc2 hr8 hread hR in
/-- **A running sum over the spans.** A column that adds `g` row by row, with `g` zero on inactive rows
and summing to `h f` over the span from each first row `f`, ends as the sum of `h` over the first rows. -/
theorem total_gen (g h : ℕ → F) (X : ℕ) (hfirst : 0 < n → M X 0 = g 0)
    (hadd : ∀ r, r + 1 < n → M X (r + 1) = M X r + g (r + 1))
    (hin : ∀ j < n, M ACT j = 0 → g j = 0)
    (hseg : ∀ f < n, M FS f = 1 → ∑ j ∈ Finset.range (M REM f).val, g (f + j) = h f)
    (hrem : ∀ r < n, M FS r = 1 → 1 ≤ (M REM r).val ∧ (M REM r).val ≤ 2 ^ 25) (hn : 0 < n) :
    M X (n - 1) = ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), h f := by
  have sums : ∀ r < n, M X r = ∑ j ∈ Finset.range (r + 1), g j := by
    intro r
    induction r with
    | zero => intro h0; simp [hfirst h0]
    | succ r ih => intro hr; rw [Finset.sum_range_succ, ← ih (by omega), hadd r hr]
  rw [sums (n - 1) (by omega), show n - 1 + 1 = n by omega]
  have claim : ∀ d f, n - f = d → f ≤ n → (M ACT f = 0 ∨ M FS f = 1) →
      ∑ j ∈ Finset.Ico f n, g j = ∑ j ∈ Finset.Ico f n, (if M FS j = 1 then h j else 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hd hfn hc
      rcases Nat.eq_or_lt_of_le hfn with rfl | hfn'
      · simp
      rcases hc with h0 | hfs
      · have z := inactive hsat hfn' h0
        rw [Finset.sum_eq_zero (fun j hj => hin j (Finset.mem_Ico.mp hj).2
            (z j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).1),
          Finset.sum_eq_zero (fun j hj => by
            rw [if_neg (by rw [(z j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).2.2]; exact zero_ne_one)])]
      · obtain ⟨-, hfa, -⟩ := kinds hsat hfn'
        have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
        obtain ⟨hL1, hL⟩ := hrem f hfn' hfs
        have seg := hseg f hfn' hfs
        set L := (M REM f).val
        obtain ⟨cont', zrl, -, hfl⟩ := seg_rows hsat L f hfn' ha rfl hL1 hL
        have nxt : M ACT (f + L) = 0 ∨ M FS (f + L) = 1 := by
          have hi : f + L - 1 + 1 < n := by omega
          have c := sat hsat (mem_step (c := .mul (k GC) (kp ZR)) (by simp [stepC])) hi
          simp only [Expr.eval, ev_k hi, ev_kp hi, zrl, mul_one] at c
          rw [show f + L - 1 + 1 = f + L by omega] at c
          have gc := (defs hsat (show f + L < n by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          rw [c] at gc
          rcases bool hsat (c := ACT) (by simp [bools]) (show f + L < n by omega) with a0 | a1
          · exact Or.inl a0
          · rw [a1, one_mul] at gc
            exact Or.inr (by linear_combination gc)
        have ih' := ih (n - (f + L)) (by omega) (f + L) rfl (by omega) nxt
        rw [← Finset.sum_Ico_consecutive _ (show f ≤ f + L by omega) (show f + L ≤ n by omega),
          ← Finset.sum_Ico_consecutive (fun j => if M FS j = 1 then h j else 0) (show f ≤ f + L by omega)
            (show f + L ≤ n by omega), ih']
        congr 1
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show f + L - f = L by omega, seg]
        rw [Finset.sum_eq_single 0]
        · simp [hfs]
        · intro j hj hj0
          have hjL := Finset.mem_range.mp hj
          have gcj := cont' j (by omega) hjL
          have := (defs hsat (show f + j < n by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          rw [gcj] at this
          rw [if_neg]
          intro hfs'
          rw [hfs', sub_self, mul_zero] at this; exact one_ne_zero this
        · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hc := claim n 0 (by simp) (by omega) (by
    have c := sat hsat (mem_script (c := .mul first (.mul (k ACT) (om (k FS)))) (by simp [scriptC])) hn
    simp only [Expr.eval, ev_first hn, if_true, one_mul, ev_k hn, om, one, eval_cst, Nat.cast_one] at c
    rcases mul_eq_zero.mp c with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination -h))
  rw [Finset.range_eq_Ico, hc, Finset.sum_filter]

/-- **The walker's accurate total.** `SUMA` at the last row is the sum, over the spans, of the weight
(`AC + 3·W4`: 0 for a script, 1 for a witness script, 4 for a redeem script) times the accurate sigop
count of the span's bytes. -/
theorem total_acc (hrem : ∀ r < n, M FS r = 1 → 1 ≤ (M REM r).val ∧ (M REM r).val ≤ 2 ^ 25) (hn : 0 < n) :
    M SUMA (n - 1) = ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), (M AC f + 3 * M W4 f) *
      ((Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val (M REM f).val) : ℕ) : F) := by
  have an : ∀ r < n, M AN r = (M AC r + 3 * M W4 r) * (M SG r - 20 * M MS r + M M1 r) := by
    intro r hr
    have c := sat hsat (mem_acc (c := .sub (k AN) (.mul (.add (k AC) (.mul (cst 3) (k W4)))
      (.add (.sub (k SG) (.mul (cst 20) (k MS))) (k M1)))) (by simp [accC])) hr
    simp only [Expr.eval, ev_k hr, eval_cst, Nat.cast_ofNat] at c
    linear_combination c
  refine total_gen hsat (fun j => M OP j * M AN j) _ SUMA (fun h0 => ?_) (fun r hr => ?_) (fun j hj h0 => ?_)
    (fun f hf hfs => ?_) hrem hn
  · have c := sat hsat (mem_acc (c := .mul first (.sub (k SUMA) (.mul (k OP) (k AN)))) (by simp [accC])) h0
    simp only [Expr.eval, ev_first h0, if_true, one_mul, ev_k h0, sub_eq_zero] at c
    exact c
  · have c := sat hsat (mem_acc (c := .mul notFirst (.sub (.sub (k SUMA) (kp SUMA)) (.mul (k OP) (k AN))))
      (by simp [accC])) hr
    simp only [Expr.eval, ev_notFirst hr, one_mul, ev_k hr, ev_kp hr] at c
    linear_combination c
  · show M OP j * M AN j = 0
    rw [op_inactive hsat hj h0, zero_mul]
  · obtain ⟨-, hfa, -⟩ := kinds hsat hf
    have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
    obtain ⟨hL1, hL⟩ := hrem f hf hfs
    have hrows := span_rows hsat R hread hR hf ha rfl hL1 hL
    rw [← seg_acc hsat hopc hopc2 hr8 R hread hR hf hfs rfl hL1 hL, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjL := Finset.mem_range.mp hj
    rw [an _ (hrows j hjL).1, span_const hsat R hread hR (c := AC) (by simp) hf ha rfl hL1 hL j hjL,
      span_const hsat R hread hR (c := W4) (by simp) hf ha rfl hL1 hL j hjL]
    ring

end Acc

end StarkedAir.Block.Walk
