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
open StarkedAir.Spec.ConnectRules (runG fGH fA fH fL gA gH gL dvW accW pushOnly lastPush opsD)

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

/-! ### `IsPushOnly` and the last push -/

omit hopc hopc2 hr8 hread hR in
theorem zspecA {z inv : ℕ} {e : Expr} (h : ∀ c ∈ isZero z inv e, c ∈ accC) {r : ℕ} (hr : r < n) :
    (M z r = 0 ∨ M z r = 1) ∧ (M z r = 1 ↔ e.eval n preCols pub M r = 0) := by
  have h1 := sat hsat (mem_acc (h (boolC (k z)) (by simp [isZero]))) hr
  have h2 := sat hsat (mem_acc (h (.mul (k z) e) (by simp [isZero]))) hr
  have h3 := sat hsat (mem_acc (h (.mul (om (k z)) (.sub (.mul e (k inv)) one)) (by simp [isZero]))) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, om, one, Nat.cast_one] at h1 h2 h3
  have hb : M z r = 0 ∨ M z r = 1 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  refine ⟨hb, ⟨fun h1' => by rw [h1', one_mul] at h2; exact h2, fun h0 => ?_⟩⟩
  rcases hb with hz | hz
  · rw [hz, h0] at h3; simp at h3
  · exact hz

omit hopc hopc2 hread hR in
/-- A length-byte row, without looking at the next row: whether it is the last length byte, the length
so far, and its size. -/
theorem len_facts {r k i acc : ℕ} (hr : r < n) (hrep : Rep M r (.len k i acc)) (x : UInt8)
    (hx : (M B r).val = x.toNat) :
    M LE r = (if i + 1 = k then 1 else 0) ∧ M ACC2 r = ((acc + x.toNat * 256 ^ i : ℕ) : F) ∧
    (i + 1 = k → M TOPF r = 0 → acc + x.toNat * 256 ^ i < 2 ^ 25) ∧
    (M TOPF r = 1 → i + 1 = k ∧ acc + x.toNat * 256 ^ i ≠ 0) := by
  obtain ⟨hln, hlk, hik, hli, hlacc, hacc⟩ := hrep
  obtain ⟨hACC2, hENDC, hLE, hLEF, hL4, -⟩ := defs hsat hr
  have xb : x.toNat < 256 := x.toNat_lt
  have hk : k = 1 ∨ k = 2 ∨ k = 4 := by rcases hlk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hi4 : i < 4 := by omega
  have w : M (LI 0) r + 256 * M (LI 1) r + 65536 * M (LI 2) r + 16777216 * M (LI 3) r = ((256 ^ i : ℕ) : F) := by
    rw [hli 0 (by norm_num), hli 1 (by norm_num), hli 2 (by norm_num), hli 3 (by norm_num)]
    interval_cases i <;> norm_num
  have acc2 : M ACC2 r = ((acc + x.toNat * 256 ^ i : ℕ) : F) := by
    rw [hACC2, hlacc, w, ← ZMod.natCast_zmod_val (M B r), hx]; push_cast; ring
  have endc : M ENDC r = if i + 1 = k then 1 else 0 := by
    rw [hENDC, hli 0 (by norm_num), hli 1 (by norm_num), hli 3 (by norm_num)]
    rcases hlk with ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩ <;> rw [a, b, c] <;> interval_cases i <;> norm_num
  have hle : M LE r = if i + 1 = k then 1 else 0 := by rw [hLE, hln, one_mul, endc]
  refine ⟨hle, acc2, fun hend t0 => ?_, fun t1 => ?_⟩
  · rw [if_pos hend] at hle
    have hlef : M LEF r = 1 := by rw [hLEF, hle, t0]; ring
    rcases hk with rfl | rfl | rfl
    · have : i = 0 := by omega
      subst this; simp at hacc ⊢; omega
    · have : i = 1 := by omega
      subst this; simp at hacc ⊢; omega
    · have : i = 3 := by omega
      subst this
      have lk4 : M LK4 r = 1 := by
        rcases hlk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h⟩ <;> first | omega | exact h
      have l4 : M L4 r = 1 := by rw [hL4, hlef, lk4]; ring
      have c := sat hsat (mem_local (c := .mul (Walk.k L4) (.mul (Walk.k B) (.sub (Walk.k B) one))) (by simp [localC])) hr
      simp only [Expr.eval, ev_k hr, l4, one_mul, one, eval_cst, Nat.cast_one] at c
      have hx1 : x.toNat ≤ 1 := by
        rcases mul_eq_zero.mp c with h | h
        · rw [h] at hx; simp at hx; omega
        · rw [sub_eq_zero.mp h, ZMod.val_one] at hx; omega
      simp at hacc ⊢; omega
  · have c := sat hsat (mem_local (c := .mul (Walk.k TOPF) (om (Walk.k LE))) (by simp [localC])) hr
    simp only [Expr.eval, ev_k hr, t1, one_mul, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at c
    have hend : i + 1 = k := by
      by_contra hc; rw [if_neg hc] at hle; rw [hle] at c; exact one_ne_zero c
    have x2 : 2 ≤ x.toNat := by
      have := hr8 r hr t1
      rw [← ZMod.natCast_zmod_val (M B r), hx] at this
      by_contra hc
      have e : ((x.toNat : ℕ) : F) - 2 = ((P - (2 - x.toNat) : ℕ) : F) := by
        rw [Nat.cast_sub (by unfold P; omega)]; simp; push_cast [Nat.cast_sub (show x.toNat ≤ 2 by omega)]; ring
      rw [e, ZMod.val_natCast_of_lt (by unfold P; omega)] at this
      unfold P at this; omega
    refine ⟨hend, ?_⟩
    have : 0 < x.toNat * 256 ^ i := by positivity
    omega

omit hopc2 hread hR in
/-- **The next state is an opcode** exactly when `NOP = 1`. -/
theorem nop_spec {j : ℕ} (hj : j < n) {s : WS} (hs : Rep' M j s) (x : UInt8) (hx : (M B j).val = x.toNat)
    (h1 : 1 ≤ (M REM j).val) :
    (M NOP j = 1 ∧ (wstep s x).1 = .op) ∨ (M NOP j = 0 ∧ (wstep s x).1 ≠ .op) := by
  obtain ⟨-, -, hLE, hLEF, -, hNOP, -⟩ := defs hsat hj
  rcases hs with hrep | ⟨hinf, d, rfl, hd⟩
  · match s, hrep with
    | .op, hop =>
      obtain ⟨-, hz⟩ := only hsat hj (c := OP) (by simp) hop
      have hl : M LN j = 0 := hz LN (by simp) (by simp [LN, OP])
      have hdt : M DT j = 0 := hz DT (by simp) (by simp [DT, OP])
      obtain ⟨-, hk1, hk2, hk4, -, hnzp⟩ := hopc j hj hop
      rw [hx] at hk1 hk2 hk4 hnzp
      have hlef0 : M LEF j = 0 := by rw [hLEF, hLE, hl]; ring
      have e : M NOP j = 1 - ((Tables.nzp x.toNat : F) + Tables.isK 0x4c x.toNat + Tables.isK 0x4d x.toNat +
          Tables.isK 0x4e x.toNat) := by rw [hNOP, hop, hlef0, hdt, hnzp, hk1, hk2, hk4]; ring
      rw [e, Spec.ConnectRules.wstep_opN]
      unfold Tables.nzp Tables.isK
      by_cases h1 : x.toNat < 0x4c
      · by_cases h0 : x.toNat = 0
        · left; rw [if_pos h1, if_pos h0, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact ⟨by norm_num, rfl⟩
        · right; rw [if_pos h1, if_neg h0, if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
          exact ⟨by norm_num, by simp⟩
      · by_cases h2 : x.toNat = 0x4c
        · right; rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos h2, if_neg (by omega), if_neg (by omega)]
          exact ⟨by norm_num, by simp⟩
        by_cases h3 : x.toNat = 0x4d
        · right; rw [if_neg h1, if_neg h2, if_pos h3, if_neg (by omega), if_neg h2, if_pos h3, if_neg (by omega)]
          exact ⟨by norm_num, by simp⟩
        by_cases h4 : x.toNat = 0x4e
        · right
          rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4, if_neg (by omega), if_neg h2, if_neg h3, if_pos h4]
          exact ⟨by norm_num, by simp⟩
        · left
          rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg (by omega), if_neg h2, if_neg h3, if_neg h4]
          exact ⟨by norm_num, rfl⟩
    | .len k i acc, hrep =>
      obtain ⟨hle, acc2, hsmall, htop⟩ := len_facts hsat hr8 hj hrep x hx
      obtain ⟨-, hz⟩ := only hsat hj (c := LN) (by simp) hrep.1
      have ho : M OP j = 0 := hz OP (by simp) (by simp [LN, OP])
      have hdt : M DT j = 0 := hz DT (by simp) (by simp [LN, DT])
      have e : M NOP j = M LEF j * M ZA j := by rw [hNOP, ho, hdt]; ring
      have za := zspec hsat (z := ZA) (inv := INVA) (e := Walk.k ACC2)
        (fun c hc => by simp only [localC, List.mem_append]; tauto) hj
      simp only [ev_k hj] at za
      simp only [wstep]
      by_cases hend : i + 1 = k
      · rw [if_pos hend] at hle ⊢
        rcases bool hsat (c := TOPF) (by simp [bools]) hj with t0 | t1
        · have hlef : M LEF j = 1 := by rw [hLEF, hle, t0]; ring
          have small := hsmall hend t0
          by_cases h0 : acc + x.toNat * 256 ^ i = 0
          · left; rw [if_pos h0]
            exact ⟨by rw [e, hlef, za.2.2 (by rw [acc2, h0]; simp)]; ring, rfl⟩
          · right; rw [if_neg h0]
            have hz0 : M ZA j = 0 := by
              rcases za.1 with h | h
              · exact h
              · exfalso; have := za.2.1 h; rw [acc2] at this
                exact h0 (natCast_inj_of_lt (b := 0) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
                  (by simpa using this))
            exact ⟨by rw [e, hz0]; ring, by simp⟩
        · right
          have hlef : M LEF j = 0 := by rw [hLEF, t1]; ring
          rw [if_neg (htop t1).2]
          exact ⟨by rw [e, hlef]; ring, by simp⟩
      · right
        rw [if_neg hend] at hle ⊢
        have hlef : M LEF j = 0 := by rw [hLEF, hle]; ring
        exact ⟨by rw [e, hlef]; ring, by simp⟩
    | .data d, hrep =>
      obtain ⟨hdt, hdr, hd1, hd25⟩ := hrep
      obtain ⟨-, hz⟩ := only hsat hj (c := DT) (by simp) hdt
      have ho : M OP j = 0 := hz OP (by simp) (by simp [DT, OP])
      have hl : M LN j = 0 := hz LN (by simp) (by simp [LN, DT])
      have hlef0 : M LEF j = 0 := by rw [hLEF, hLE, hl]; ring
      have e : M NOP j = M ZD j := by rw [hNOP, ho, hlef0, hdt]; ring
      have zd := zspec hsat (z := ZD) (inv := INVD) (e := .sub (Walk.k DR) one)
        (fun c hc => by simp only [localC, List.mem_append]; tauto) hj
      simp only [Expr.eval, ev_k hj, one, eval_cst, Nat.cast_one] at zd
      simp only [wstep]
      by_cases hd : d = 1
      · left; rw [if_pos hd]; exact ⟨by rw [e, zd.2.2 (by rw [hdr, hd]; simp)], rfl⟩
      · right; rw [if_neg hd]
        have hz0 : M ZD j = 0 := by
          rcases zd.1 with h | h
          · exact h
          · exfalso
            have := zd.2.1 h
            rw [hdr, sub_eq_zero] at this
            exact hd (natCast_inj_of_lt (a := d) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
              (by simpa using this))
        exact ⟨by rw [e, hz0], by simp⟩
  · right
    obtain ⟨-, hz⟩ := only hsat hj (c := INF) (by simp) hinf
    have ho : M OP j = 0 := hz OP (by simp) (by simp [INF, OP])
    have hl : M LN j = 0 := hz LN (by simp) (by simp [INF, LN])
    have hdt : M DT j = 0 := hz DT (by simp) (by simp [INF, DT])
    have hlef0 : M LEF j = 0 := by rw [hLEF, hLE, hl]; ring
    refine ⟨by rw [hNOP, ho, hlef0, hdt]; ring, ?_⟩
    simp only [wstep]; rw [if_neg (by omega)]; simp

omit hopc hr8 hread hR in
/-- One row of the count of opcodes above `OP_16`. -/
theorem hi_row : ∀ j, j + 1 < n → M ACT j = 1 → 1 ≤ (M REM j).val → (M REM j).val ≤ 2 ^ 25 →
    ∀ (s : WS) (st : Unit) (x : UInt8), (M B j).val = x.toNat → Rep' M j s → True →
      M OP j * M HI j = (((fH s st x).2 : ℕ) : F) ∧ (M GC (j + 1) = 1 → Rep' M (j + 1) (wstep s x).1 → True) := by
  intro j hj _ _ _ s st x hx hs _
  have hj' : j < n := by omega
  refine ⟨?_, fun _ _ => trivial⟩
  by_cases hop : s = .op
  · have o1 := op_one hs hop
    subst hop
    rw [o1, one_mul, (hopc2 j hj' o1).1, hx]
    simp [fH, fGH, gH, Tables.hiN]
  · rw [op_zero hsat hj' hs hop, zero_mul]
    match s, hop with
    | .len k i acc, _ => simp [fH, fGH]
    | .data d, _ => simp [fH, fGH]

omit hopc hopc2 hr8 in
/-- `HCN` counts the span's opcodes above `OP_16` so far. -/
theorem hcn_sum {f L : ℕ} (hf : f < n) (hfs : M FS f = 1) (hrem : (M REM f).val = L) (h1 : 1 ≤ L)
    (hL : L ≤ 2 ^ 25) : ∀ j < L, M HCN (f + j) = ∑ i ∈ Finset.range (j + 1), M OP (f + i) * M HI (f + i) := by
  obtain ⟨-, hfa, -⟩ := kinds hsat hf
  have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
  have hrows := span_rows hsat R hread hR hf ha hrem h1 hL
  intro j
  induction j with
  | zero =>
    intro _
    have c := sat hsat (mem_acc (c := .sub (k HCN) (.add (.mul (k GC) (kp HCN)) (.mul (k OP) (k HI))))
      (by simp [accC])) hf
    have gc := (defs hsat hf).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    rw [hfs, sub_self, mul_zero] at gc
    simp only [Expr.eval, ev_k hf, gc, zero_mul, zero_add, sub_eq_zero] at c
    simpa using c
  | succ j ih =>
    intro hj
    obtain ⟨a1, -, -, -, a5⟩ := hrows (j + 1) hj
    rw [show f + (j + 1) = f + j + 1 by omega] at a1 a5
    have c := sat hsat (mem_acc (c := .sub (k HCN) (.add (.mul (k GC) (kp HCN)) (.mul (k OP) (k HI))))
      (by simp [accC])) a1
    simp only [Expr.eval, ev_k a1, ev_kp a1, a5 (by omega), one_mul] at c
    rw [Finset.sum_range_succ, ← ih (by omega), show f + (j + 1) = f + j + 1 by omega]
    linear_combination c

/-- The last push's invariant: on a data row whose data ends with the span, `RL` is the data's length
and `RS` its start. -/
def LSt (M : ℕ → ℕ → F) (j : ℕ) (s : WS) (l : ℕ) : Prop :=
  ∀ d, s = .data d → (M REM j).val = d → M RL j = (l : F) ∧ M RS j + (l : F) = M POS j + (d : F)

omit hopc hopc2 hr8 hread hR in
/-- One row of the last push. -/
theorem last_row : ∀ j, j + 1 < n → M ACT j = 1 → 1 ≤ (M REM j).val → (M REM j).val ≤ 2 ^ 25 →
    ∀ (s : WS) (l : ℕ) (x : UInt8), (M B j).val = x.toNat → Rep' M j s → LSt M j s l →
      (0 : F) = (((fL s l x).2 : ℕ) : F) ∧
      (M GC (j + 1) = 1 → Rep' M (j + 1) (wstep s x).1 → LSt M (j + 1) (wstep s x).1 (fL s l x).1) := by
  intro j hj _ hr1 hr25 s l x hx hs hst
  have hj' : j < n := by omega
  refine ⟨by cases s <;> simp [fL, fGH, gL], fun hg hs1 d hd hremd => ?_⟩
  obtain ⟨-, -, sDT, -, sDR, -, -, -, -, -, sPOS, -, -⟩ := step hsat hj hg
  have hrem := rem_step hsat hj hg hr1 hr25
  have cRL := const_step hsat (c := RL) (by simp) hj hg
  have cRS := const_step hsat (c := RS) (by simp) hj hg
  rw [hd] at hs1
  -- the next row is a data row with `d` bytes left
  obtain ⟨hdt1, hdr1, hd1, hd25⟩ : Rep M (j + 1) (.data d) := by
    rcases hs1 with h | ⟨-, d', he, hlt⟩
    · exact h
    · exfalso; cases he; omega
  rw [cRL, cRS, sPOS]
  by_cases hdata : ∃ d0, s = .data d0
  · -- inside the data
    obtain ⟨d0, rfl⟩ := hdata
    simp only [wstep] at hd
    have hd0 : d0 ≠ 1 := by intro h; rw [if_pos h] at hd; cases hd
    rw [if_neg hd0] at hd
    have hdd : d = d0 - 1 := by cases hd; rfl
    have hfl : (fL (.data d0) l x).1 = l := by simp [fL, fGH]
    obtain ⟨e1, e2⟩ := hst d0 rfl (by omega)
    rw [hfl]
    have hd0' : 1 ≤ d0 := by omega
    refine ⟨e1, ?_⟩
    rw [hdd, Nat.cast_sub hd0']; push_cast; linear_combination e2
  · -- the data starts after this row
    have hdt0 : M DT j = 0 := by
      rcases hs with hrep | ⟨-, d', he, -⟩
      · match s, hrep with
        | .op, h => exact (only hsat hj' (c := OP) (by simp) h).2 DT (by simp) (by simp [DT, OP])
        | .len k i acc, h => exact (only hsat hj' (c := LN) (by simp) h.1).2 DT (by simp) (by simp [LN, DT])
        | .data d0, _ => exact absurd ⟨d0, rfl⟩ hdata
      · exact absurd ⟨d', he⟩ hdata
    obtain ⟨-, -, -, -, -, -, hNDT, -⟩ := defs hsat hj'
    have hent : entE.eval n preCols pub M j = 1 := by
      have e : entE.eval n preCols pub M j = M NDT j := by
        simp only [entE, Expr.eval, ev_k hj', om, one, eval_cst, Nat.cast_one]
        rw [hNDT, hdt0]; ring
      rw [e, ← sDT, hdt1]
    have hndr : M NDR j = (d : F) := by rw [← sDR, hdr1]
    have hremj : M REM j = ((d + 1 : ℕ) : F) := by
      rw [← ZMod.natCast_zmod_val (M REM j), show (M REM j).val = d + 1 by omega]
    have ze := zspecA hsat (z := ZE) (inv := INVE) (e := .add (.sub (Walk.k NDR) (Walk.k REM)) one)
      (fun c hc => by simp only [accC, List.mem_append]; tauto) hj'
    simp only [Expr.eval, ev_k hj', one, eval_cst, Nat.cast_one] at ze
    have hze : M ZE j = 1 := ze.2.2 (by rw [hndr, hremj]; push_cast; ring)
    have c1 := sat hsat (mem_acc (c := .sub (Walk.k EZ) (.mul entE (Walk.k ZE))) (by simp [accC])) hj'
    have c2 := sat hsat (mem_acc (c := .mul (Walk.k EZ) (.sub (Walk.k RL) (Walk.k NDR))) (by simp [accC])) hj'
    have c3 := sat hsat (mem_acc (c := .mul (Walk.k EZ) (.sub (.sub (Walk.k RS) (Walk.k POS)) one)) (by simp [accC])) hj'
    simp only [Expr.eval, ev_k hj', hent, hze, one_mul, sub_eq_zero] at c1
    simp only [Expr.eval, ev_k hj', c1, one_mul, one, eval_cst, Nat.cast_one] at c2 c3
    -- the decoration is the data's length
    have hfl : (fL s l x).1 = d := by
      match s, hdata with
      | .op, _ =>
        rw [Spec.ConnectRules.wstep_opN] at hd
        by_cases h1 : x.toNat < 0x4c
        · rw [if_pos h1] at hd
          by_cases h0 : x.toNat = 0
          · rw [if_pos h0] at hd; cases hd
          · rw [if_neg h0] at hd; cases hd
            simp [fL, fGH, gL, h1, show ¬ (0x4c ≤ x.toNat) by omega]
        · rw [if_neg h1] at hd; split_ifs at hd
      | .len k i acc, _ =>
        simp only [wstep] at hd
        by_cases hend : i + 1 = k
        · rw [if_pos hend] at hd
          by_cases h0 : acc + x.toNat * 256 ^ i = 0
          · rw [if_pos h0] at hd; cases hd
          · rw [if_neg h0] at hd; cases hd
            simp [fL, fGH, hend]
        · rw [if_neg hend] at hd; cases hd
      | .data d0, h => exact absurd ⟨d0, rfl⟩ h
    rw [hfl]
    exact ⟨by rw [← hndr]; linear_combination c2, by linear_combination c3⟩

/-- **A script span's outputs.** For the span of `L` bytes `sc` from first row `f`: `PO` is
`pushOnly sc`; and for a push-only script, `RL` is the length of its last operation's data, which ends
with the span (`RS + RL` is the span's end) when it is not empty. -/
theorem span_out {f L : ℕ} (hf : f < n) (hfs : M FS f = 1) (hrem : (M REM f).val = L) (h1 : 1 ≤ L)
    (hL : L ≤ 2 ^ 25) :
    ((M PO f = 1 ∧ pushOnly (Fields.slice R (M POS f).val L) = true) ∨
     (M PO f = 0 ∧ pushOnly (Fields.slice R (M POS f).val L) = false)) ∧
    (pushOnly (Fields.slice R (M POS f).val L) = true →
      M RL f = (((lastPush (Fields.slice R (M POS f).val L)).length : ℕ) : F) ∧
      ((lastPush (Fields.slice R (M POS f).val L)).length ≠ 0 →
        M RS f + (((lastPush (Fields.slice R (M POS f).val L)).length : ℕ) : F) = M POS f + (L : F))) := by
  obtain ⟨-, hfa, hfo⟩ := kinds hsat hf
  have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
  have hop : M OP f = 1 := by rw [hfs] at hfo; linear_combination -hfo
  have hrows := span_rows hsat R hread hR hf ha hrem h1 hL
  obtain ⟨he, hae, hreme, hpose, -⟩ := hrows (L - 1) (by omega)
  have hee : f + (L - 1) = f + L - 1 := by omega
  rw [hee] at he hae hreme hpose
  obtain ⟨-, zrl, -, -⟩ := seg_rows hsat L f hf ha hrem h1 hL
  have cst : ∀ c ∈ [AC, W4, PO, RS, RL], M c (f + L - 1) = M c f := fun c hc => by
    have := span_const hsat R hread hR hc hf ha hrem h1 hL (L - 1) (by omega); rwa [hee] at this
  obtain ⟨-, hxe⟩ := hread _ he hae
  have hlen : (Fields.slice R (M POS f).val L).length ≤ L := List.length_take_le _ _
  -- the opcodes above `OP_16` and the state after the last byte
  obtain ⟨s', st', hs', -, hsum, hfin⟩ := seg_gen hsat hopc hr8 R hread hR fH (fun j => M OP j * M HI j)
    (fun _ _ _ => True) (hi_row hsat hopc2) L f hf ha hrem h1 hL .op () (Or.inl hop) trivial
  have hcn := hcn_sum hsat R hread hR hf hfs hrem h1 hL (L - 1) (by omega)
  rw [hee, show L - 1 + 1 = L by omega, hsum] at hcn
  have zh := zspecA hsat (z := ZH) (inv := INVH) (e := Walk.k HCN)
    (fun c hc => by simp only [accC, List.mem_append]; tauto) he
  simp only [ev_k he] at zh
  have cpo := sat hsat (mem_acc (c := .mul (k ZR) (.sub (k PO) (.mul (k ZH) (k NOP)))) (by simp [accC])) he
  simp only [Expr.eval, ev_k he, zrl, one_mul, sub_eq_zero] at cpo
  have hpo : M PO f = M ZH (f + L - 1) * M NOP (f + L - 1) := by rw [← cst PO (by simp)]; exact cpo
  have hnop := nop_spec hsat hopc hr8 he hs' _ hxe (by omega)
  have hfin1 : (runG fH .op () (Fields.slice R (M POS f).val L)).2.1 =
      (wstep s' (R.getD (M POS (f + L - 1)).val 0)).1 := by rw [hfin]
  have hle := Spec.ConnectRules.hi_run_le (Fields.slice R (M POS f).val L) .op ()
  have hpor := Spec.ConnectRules.po_run (Fields.slice R (M POS f).val L)
  have first : (M PO f = 1 ∧ pushOnly (Fields.slice R (M POS f).val L) = true) ∨
      (M PO f = 0 ∧ pushOnly (Fields.slice R (M POS f).val L) = false) := by
    rcases hnop with ⟨n1, w1⟩ | ⟨n0, w0⟩
    · rcases zh.1 with z0 | z1
      · right
        refine ⟨by rw [hpo, z0]; ring, ?_⟩
        rw [Bool.eq_false_iff]; intro hp
        have h0 := (hpor.mp hp).2
        have : M ZH (f + L - 1) = 1 := zh.2.2 (by rw [hcn, h0]; simp)
        rw [z0] at this; exact zero_ne_one this
      · left
        refine ⟨by rw [hpo, z1, n1]; ring, hpor.mpr ⟨by rw [hfin1, w1], ?_⟩⟩
        have := zh.2.1 z1
        rw [hcn] at this
        exact natCast_inj_of_lt (b := 0) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) (by simpa using this)
    · right
      refine ⟨by rw [hpo, n0]; ring, ?_⟩
      rw [Bool.eq_false_iff]; intro hp
      exact w0 (by rw [← hfin1]; exact (hpor.mp hp).1)
  refine ⟨first, fun hp => ?_⟩
  -- the last push
  have hparse : (opsD (Fields.slice R (M POS f).val L)).2 = true := by
    unfold pushOnly at hp; rw [Bool.and_eq_true] at hp; exact hp.1
  obtain ⟨s2, l2, hs2, hst2, -, hfin2⟩ := seg_gen hsat hopc hr8 R hread hR fL (fun _ => 0) (LSt M)
    (last_row hsat) L f hf ha hrem h1 hL .op 0 (Or.inl hop) (fun d hd _ => by cases hd)
  have hw : (wstep s2 (R.getD (M POS (f + L - 1)).val 0)).1 = .op := by
    have := (Spec.ConnectRules.last_ws _).mp hparse; rw [hfin2] at this; exact this
  have hlast : (fL s2 l2 (R.getD (M POS (f + L - 1)).val 0)).1 = (lastPush (Fields.slice R (M POS f).val L)).length := by
    have := Spec.ConnectRules.last_run _ hparse; rw [hfin2] at this; exact this
  have crl := sat hsat (mem_acc (c := .mul (k ZR) (.mul (om (k DT)) (k RL))) (by simp [accC])) he
  simp only [Expr.eval, ev_k he, zrl, one_mul, om, one, eval_cst, Nat.cast_one] at crl
  rw [← cst RL (by simp), ← cst RS (by simp), ← hlast]
  generalize R.getD (M POS (f + L - 1)).val 0 = xe at hw hlast hxe ⊢
  by_cases hdata : ∃ d0, s2 = .data d0
  · obtain ⟨d0, rfl⟩ := hdata
    simp only [wstep] at hw
    have hd0 : d0 = 1 := by by_contra h; rw [if_neg h] at hw; cases hw
    have hfl : (fL (.data d0) l2 xe).1 = l2 := by simp [fL, fGH]
    obtain ⟨e1, e2⟩ := hst2 d0 rfl (by omega)
    rw [hfl]
    refine ⟨e1, fun _ => ?_⟩
    have hposF : M POS (f + L - 1) = M POS f + ((L - 1 : ℕ) : F) := by
      rw [← ZMod.natCast_zmod_val (M POS (f + L - 1)), hpose]; push_cast; rw [ZMod.natCast_zmod_val]
    rw [e2, hposF, hd0, Nat.cast_sub h1]; push_cast; ring
  · have hdt0 : M DT (f + L - 1) = 0 := by
      rcases hs2 with hrep | ⟨-, d', hd', -⟩
      · match s2, hrep with
        | .op, h => exact (only hsat he (c := OP) (by simp) h).2 DT (by simp) (by simp [DT, OP])
        | .len k i acc, h => exact (only hsat he (c := LN) (by simp) h.1).2 DT (by simp) (by simp [LN, DT])
        | .data d0, _ => exact absurd ⟨d0, rfl⟩ hdata
      · exact absurd ⟨d', hd'⟩ hdata
    have hl0 : (fL s2 l2 xe).1 = 0 := by
      match s2, hdata with
      | .op, _ =>
        rw [Spec.ConnectRules.wstep_opN] at hw
        by_cases h1 : xe.toNat < 0x4c
        · rw [if_pos h1] at hw
          by_cases h0 : xe.toNat = 0
          · simp [fL, fGH, gL, h0]
          · rw [if_neg h0] at hw; cases hw
        · rw [if_neg h1] at hw
          by_cases h2 : xe.toNat = 0x4c
          · rw [if_pos h2] at hw; cases hw
          by_cases h3 : xe.toNat = 0x4d
          · rw [if_neg h2, if_pos h3] at hw; cases hw
          by_cases h4 : xe.toNat = 0x4e
          · rw [if_neg h2, if_neg h3, if_pos h4] at hw; cases hw
          simp [fL, fGH, gL, h1, show ¬ xe.toNat ≤ 0x4e by omega]
      | .len k i acc, _ =>
        simp only [wstep] at hw
        by_cases hend : i + 1 = k
        · rw [if_pos hend] at hw
          by_cases h0 : acc + xe.toNat * 256 ^ i = 0
          · simp [fL, fGH, hend, h0]
          · rw [if_neg h0] at hw; cases hw
        · rw [if_neg hend] at hw; cases hw
      | .data d0, h => exact absurd ⟨d0, rfl⟩ h
    rw [hl0]
    refine ⟨?_, fun h => absurd rfl h⟩
    rw [hdt0] at crl; simpa using crl

omit hopc hopc2 hr8 hread hR in
/-- **A sum over the rows is a sum over the spans** (any commutative monoid): `g` zero on inactive rows
and summing to `h f` over the span from each first row `f`. -/
theorem span_sum {β : Type} [AddCommMonoid β] (g h : ℕ → β)
    (hin : ∀ j < n, M ACT j = 0 → g j = 0)
    (hseg : ∀ f < n, M FS f = 1 → ∑ j ∈ Finset.range (M REM f).val, g (f + j) = h f)
    (hrem : ∀ r < n, M FS r = 1 → 1 ≤ (M REM r).val ∧ (M REM r).val ≤ 2 ^ 25) (hn : 0 < n) :
    ∑ j ∈ Finset.range n, g j = ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), h f := by
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

/-- **The walker's accurate total as a natural**: at most 80 per row, and the sum over the spans of
the weight (0, 1 or 4) times the accurate count. -/
theorem total_acc_nat (hrem : ∀ r < n, M FS r = 1 → 1 ≤ (M REM r).val ∧ (M REM r).val ≤ 2 ^ 25) (hn : 0 < n) :
    M SUMA (n - 1) = ((∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), (M AC f + 3 * M W4 f).val *
      Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val (M REM f).val) : ℕ) : F) ∧
    ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), (M AC f + 3 * M W4 f).val *
      Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val (M REM f).val) ≤ 80 * n := by
  refine ⟨?_, ?_⟩
  · rw [total_acc hsat hopc hopc2 hr8 R hread hR hrem hn]
    push_cast
    exact Finset.sum_congr rfl (fun f _ => by rw [ZMod.natCast_zmod_val])
  · -- at most 80 per byte of each span, and the spans are disjoint rows
    have hw : ∀ f < n, (M AC f + 3 * M W4 f).val ≤ 4 := by
      intro f hf
      rcases acc_bool hsat (c := AC) (by simp [accC]) hf with a | a <;>
        rcases acc_bool hsat (c := W4) (by simp [accC]) hf with b | b <;> rw [a, b]
      · simp
      · rw [show (0 : F) + 3 * 1 = ((3 : ℕ) : F) by norm_num, ZMod.val_natCast_of_lt (by unfold P; norm_num)]
        norm_num
      · simp [ZMod.val_one]
      · rw [show (1 : F) + 3 * 1 = ((4 : ℕ) : F) by norm_num, ZMod.val_natCast_of_lt (by unfold P; norm_num)]
    have hspan := span_sum hsat (fun j => if M ACT j = 1 then 80 else 0) (fun f => 80 * (M REM f).val)
      (fun j _ h0 => by simp [h0]) (fun f hf hfs => by
        obtain ⟨-, hfa, -⟩ := kinds hsat hf
        have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
        obtain ⟨hL1, hL⟩ := hrem f hf hfs
        have hrows := span_rows hsat R hread hR hf ha rfl hL1 hL
        rw [Finset.sum_congr rfl (fun j hj => by rw [if_pos (hrows j (Finset.mem_range.mp hj)).2.1])]
        simp [mul_comm]) hrem hn
    calc ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), (M AC f + 3 * M W4 f).val *
          Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val (M REM f).val)
        ≤ ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1), 80 * (M REM f).val := by
          apply Finset.sum_le_sum
          intro f hf
          have hfn := Finset.mem_range.mp (Finset.mem_filter.mp hf).1
          have h1 := hw f hfn
          have h2 := Spec.ConnectRules.acc_le (Fields.slice R (M POS f).val (M REM f).val)
          have h3 : (Fields.slice R (M POS f).val (M REM f).val).length ≤ (M REM f).val := List.length_take_le _ _
          calc (M AC f + 3 * M W4 f).val * Spec.ConnectRules.sigOpsAccurate (Fields.slice R (M POS f).val (M REM f).val)
              ≤ 4 * (20 * (M REM f).val) := Nat.mul_le_mul h1 (le_trans h2 (Nat.mul_le_mul_left _ h3))
            _ = 80 * (M REM f).val := by ring
      _ = ∑ j ∈ Finset.range n, (if M ACT j = 1 then 80 else 0) := hspan.symm
      _ ≤ ∑ j ∈ Finset.range n, 80 := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
      _ = 80 * n := by simp [mul_comm]

end Acc

end StarkedAir.Block.Walk
