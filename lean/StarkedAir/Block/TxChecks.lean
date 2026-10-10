/-
**Per-transaction checks (M3a.5b).** In the fields component, given that byte slots and the auxiliary
read read the block and range slots hold bytes: every transaction has an output; transactions after
the coinbase spend no null prevout; and every transaction is final for the height and cutoff.
-/
import StarkedAir.Block.ValueSound

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC sumPow)

section Checks

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hn : n ≤ 2 ^ 25)
include hsat hcs hmn hpad hfit hn

omit hn in
/-- **Outputs are not empty.** -/
theorem tx_vout_ne {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) : tx.vout ≠ [] := by
  obtain ⟨rh, hrh, -, -, -, -, -, hno, hnv, -, -, -, -, hle⟩ := tx_rows hsat R hcs hmn hpad hfit hat hρm
  intro h0
  have hr : rh + 1 + tx.vin.length < n := by omega
  have := sat hsat (mem_chk (c := .mul (k K_NOUT) (.sub (.mul (k VAL) (k INVN)) one)) (by simp [chkC, valueC])) hr
  simp only [Expr.eval, ev_k hr, hno, one_mul, one, eval_cst, Nat.cast_one, sub_eq_zero] at this
  rw [h0, List.length_nil] at hnv
  have hv : M VAL (rh + 1 + tx.vin.length) = 0 := by rw [← ZMod.natCast_zmod_val (M VAL _), hnv]; simp
  rw [hv, zero_mul] at this; exact zero_ne_one this

omit hcs hmn hpad hfit hn in
/-- The rows of a transaction before its lock time are not lock-time rows (from its row layout). -/
theorem rows_nolock {rh ρ nI k : ℕ} (hρn : ρ < n) (ht : M K_TXH rh = 1)
    (hin : ∀ i < nI, M K_IN (rh + 1 + i) = 1) (hno : M K_NOUT (rh + 1 + nI) = 1)
    (hout : ∀ o < k, M K_OUT (rh + 2 + nI + o) = 1)
    (hwit : ∀ j, rh + 2 + nI + k ≤ j → j < ρ → M K_WCNT j = 1 ∨ M K_WITEM j = 1) :
    ∀ j, rh ≤ j → j < ρ → M K_LOCK j ≠ 1 := by
  intro j h1 h2 hj
  have hjn : j < n := by omega
  have z : ∀ a < 9, a ≠ K_LOCK → M a j = 1 → False := fun a ha hne h => by
    rw [kind_unique hsat hjn ha (by simp [K_LOCK]) hne h] at hj; exact zero_ne_one hj
  rcases Nat.lt_or_ge j (rh + 1) with a | a
  · exact z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_LOCK]) (by rw [show j = rh by omega]; exact ht)
  rcases Nat.lt_or_ge j (rh + 1 + nI) with b | b
  · exact z K_IN (by simp [K_IN]) (by simp [K_IN, K_LOCK])
      (by rw [show j = rh + 1 + (j - (rh + 1)) by omega]; exact hin _ (by omega))
  rcases Nat.lt_or_ge j (rh + 2 + nI) with c | c
  · exact z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_LOCK]) (by rw [show j = rh + 1 + nI by omega]; exact hno)
  rcases Nat.lt_or_ge j (rh + 2 + nI + k) with d | d
  · exact z K_OUT (by simp [K_OUT]) (by simp [K_OUT, K_LOCK])
      (by rw [show j = rh + 2 + nI + (j - (rh + 2 + nI)) by omega]; exact hout _ (by omega))
  rcases hwit j d h2 with h | h
  · exact z K_WCNT (by simp [K_WCNT]) (by simp [K_WCNT, K_LOCK]) h
  · exact z K_WITEM (by simp [K_WITEM]) (by simp [K_WITEM, K_LOCK]) h

/-- **A transaction's rows, with lock counts.** `tx_rows`, plus: the rows from the head to the lock time
all have the lock time's count of earlier lock-time rows. -/
theorem tx_rows' {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) :
    ∃ rh, rh < ρ ∧ M K_TXH rh = 1 ∧ (∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) ∧
      tx.vin.length = (M VAL rh).val ∧ 1 ≤ tx.vin.length ∧
      (∀ i < tx.vin.length, ∃ inp, tx.vin[i]? = some inp ∧ InRow M R (rh + 1 + i) inp) ∧
      M K_NOUT (rh + 1 + tx.vin.length) = 1 ∧ (M VAL (rh + 1 + tx.vin.length)).val = tx.vout.length ∧
      (∀ o < tx.vout.length, ∃ out, tx.vout[o]? = some out ∧ OutRow M R (rh + 2 + tx.vin.length + o) out) ∧
      (∀ j, rh + 2 + tx.vin.length + tx.vout.length ≤ j → j < ρ → M K_WCNT j = 1 ∨ M K_WITEM j = 1) ∧
      tx.lockTime = Spec.Block.le (slice R (M START ρ).val 4) ∧
      (M SEG rh = 1 ↔ tx.hasWitness = true) ∧ rh + 2 + tx.vin.length + tx.vout.length ≤ ρ ∧
      (∀ j, rh ≤ j → j ≤ ρ → locks M j = locks M ρ) := by
  obtain ⟨rh, hrh, ht, hnt, hvl, h1, hins, hno, hnv, houts, hwit, hlt, hseg, hle⟩ :=
    tx_rows hsat R hcs hmn hpad hfit hat hρm
  have hnl := rows_nolock hsat (k := tx.vout.length) (nI := tx.vin.length) (show ρ < n by omega) ht
    (fun i hi => by obtain ⟨_, _, hr⟩ := hins i hi; exact hr.kind) hno
    (fun o ho => by obtain ⟨_, _, hr⟩ := houts o ho; exact hr.kind) hwit
  exact ⟨rh, hrh, ht, hnt, hvl, h1, hins, hno, hnv, houts, hwit, hlt, hseg, hle,
    fun j h1 h2 => (locks_const (a := j) (b := ρ) (fun i a b => hnl i (by omega) b) h2).symm⟩

end Checks

theorem le4_ff {a b c d : ℕ} (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (h : a + 256 * b + 65536 * c + 16777216 * d = 4294967295) : a = 255 ∧ b = 255 ∧ c = 255 ∧ d = 255 := by
  omega

theorem le_slice4 {R : Spec.Block.Bytes} {s : ℕ} (h : s + 4 ≤ R.length) :
    Spec.Block.le (slice R s 4) = (R.getD s 0).toNat + 256 * (R.getD (s + 1) 0).toNat +
      65536 * (R.getD (s + 2) 0).toNat + 16777216 * (R.getD (s + 3) 0).toNat := by
  rw [slice_eq_map h, le_range_map]
  simp [Finset.sum_range_succ]; ring

section Prevouts

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hbq : ∀ r < n, M GIN r + M MMB r = 1 → (M AQ r).val < R.length ∧ (M BQ r).val = (R.getD (M AQ r).val 0).toNat)
  (hn : n ≤ 2 ^ 25)
include hsat hcs hmn hpad hfit hbq hn

/-- **Inputs after the coinbase spend real outputs.** In a transaction with index `≥ 1`, no input's prevout
is null. -/
theorem tx_prevouts {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) (hj : locks M ρ ≠ 0) :
    ∀ i ∈ tx.vin, i.prevout.isNull = false := by
  obtain ⟨rh, hrh, -, -, hvl, -, hins, -, -, -, -, -, -, hle, hlk⟩ := tx_rows' hsat R hcs hmn hpad hfit hn hat hρm
  intro i hi
  obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hi
  obtain ⟨inp, hget, hrow⟩ := hins x hx
  rw [List.getElem?_eq_getElem hx, Option.some.injEq] at hget
  rw [hget]
  set r := rh + 1 + x with hr
  have hrn : r < n := by omega
  -- the row's transaction index is not 0, so `ZT = 0` and `GIN = 1`
  have hP : n < P := lt_of_le_of_lt hn (by unfold P; norm_num)
  have htxi : M TXI r ≠ 0 := by
    rw [txi_count hsat r hrn, hlk r (by omega) (by omega)]
    intro h0
    have := natCast_inj_of_lt (a := locks M ρ) (b := 0) (lt_of_le_of_lt (locks_le ρ) (by omega)) (by unfold P; norm_num)
      (by simpa using h0)
    exact hj this
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hrn
  have hzt : M ZT r = 0 := by
    have := sat hsat (mem_chk (c := .mul (k ZT) (k TXI)) (by simp [chkC, prevoutC])) hrn
    simp only [Expr.eval, ev_k hrn] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h htxi
  have hgin : M GIN r = 1 := by
    rw [chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hrn]
    simp [Expr.eval, ev_k hrn, oneMinus, one, eval_cst, hzt, hrow.kind]
  have hmmb : M MMB r = 0 := by
    rcases chk_bool hsat (e := MMB) (by simp [chkC, commitC]) hrn with h | h
    · exact h
    · exfalso
      rcases gin_mmb hsat hrn with g | g <;> rw [hgin, h] at g
      · exact one_add_one_ne g
      · exact one_ne_zero (by linear_combination g)
  obtain ⟨hAQ, hBQ⟩ := hbq r hrn (by rw [hgin, hmmb]; ring)
  -- the position and the byte
  have bits := fun (c' : ℕ) (h : boolC (k c') ∈ chkC) => chk_bool hsat (e := c') h hrn
  have qh := bits QH (by simp [chkC, prevoutC])
  have qb : ∀ j < 5, M (QB j) r = 0 ∨ M (QB j) r = 1 := fun j hj => bits (QB j) (by
    have : boolC (k (QB j)) ∈ (List.range 5).map (fun j => boolC (k (QB j))) :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    simp only [chkC, prevoutC, List.mem_append]; tauto)
  have hq36 := sat hsat (mem_chk (c := .mul (k QH) (.add (k (QB 2)) (.add (k (QB 3)) (k (QB 4))))) (by simp [chkC, prevoutC])) hrn
  have haq := chk_defn hsat (a := AQ) (e := .add (.mul (k GIN) (.add (k START) qE)) (.mul (k MMB) (.add (k SSC) (ohSum id))))
    (by simp [chkC, prevoutC]) hrn
  have hexp := chk_defn hsat (a := EXPQ) (e := .add (.mul (k GIN) (.mul (c 255) (k QH)))
    (.mul (k MMB) (ohSum (fun j => pat.getD j 0)))) (by simp [chkC, prevoutC]) hrn
  have hne := sat hsat (mem_chk (c := .mul (.add (k GIN) (k MMB)) (.sub (.mul (.sub (k BQ) (k EXPQ)) (k INVQ)) one))
    (by simp [chkC, prevoutC])) hrn
  simp only [Expr.eval, ev_k hrn, hgin, hmmb, qE, sumPow, c, eval_cst, one, oneMinus, zero_mul, add_zero, one_mul,
    mul_zero, Nat.cast_one, Nat.cast_ofNat, zero_add] at hq36 haq hexp hne
  -- the position `q` as a natural
  obtain ⟨vqh, bqh⟩ := bool_val qh
  have bq := fun j (hj : j < 5) => bool_val (qb j hj)
  obtain ⟨v0, l0⟩ := bq 0 (by norm_num); obtain ⟨v1, l1⟩ := bq 1 (by norm_num); obtain ⟨v2, l2⟩ := bq 2 (by norm_num)
  obtain ⟨v3, l3⟩ := bq 3 (by norm_num); obtain ⟨v4, l4⟩ := bq 4 (by norm_num)
  set q := 32 * (M QH r).val + (M (QB 0) r).val + 2 * (M (QB 1) r).val + 4 * (M (QB 2) r).val +
    8 * (M (QB 3) r).val + 16 * (M (QB 4) r).val with hq
  have hlen : (M LEN r).val = 40 + prefOf M r + (M VAL r).val := by
    have := (row_info hsat R hcs hmn hpad hfit (r := r) (by omega) (a := K_IN) (by simp [K_IN]) hrow.kind
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])).2.1
    rw [this]; simp [lenN, K_BLK, K_TXH, K_IN]
  have hfr := hfit r (by omega)
  have hst := start_lt hsat hrn
  have haqv : (M AQ r).val = (M START r).val + q := by
    apply val_eq _ (lt_P (by omega))
    rw [haq, vqh, v0, v1, v2, v3, v4, ← ZMod.natCast_zmod_val (M START r)]
    simp [hq]; push_cast; ring
  have hbne : M BQ r ≠ M EXPQ r := by
    intro h; rw [h, sub_self, zero_mul, zero_sub] at hne; exact one_ne_zero (neg_eq_zero.mp hne)
  have hbyte := hBQ
  rw [haqv] at hbyte
  have hb256 : (M BQ r).val < 256 := by rw [hbyte]; exact UInt8.toNat_lt _
  simp only [Spec.Block.OutPoint.isNull, hrow.hash, hrow.n, Bool.and_eq_false_iff]
  rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp bqh) with h0 | h1
  · -- `q < 32`: a hash byte is not zero
    left
    rw [vqh, h0, Nat.cast_zero, mul_zero] at hexp
    have hqb : q < 32 := by omega
    rw [slice_eq_map (by omega), List.all_eq_false]
    refine ⟨R.getD ((M START r).val + q) 0, List.mem_map.mpr ⟨q, List.mem_range.mpr hqb, rfl⟩, ?_⟩
    intro he
    have h0' : R.getD ((M START r).val + q) 0 = 0 := by simpa using he
    have : (R.getD ((M START r).val + q) 0).toNat = 0 := by rw [h0']; rfl
    rw [← hbyte] at this
    apply hbne; rw [hexp, ← ZMod.natCast_zmod_val (M BQ r), this]; simp
  · -- `32 ≤ q < 36`: an index byte is not `ff`
    right
    rw [vqh, h1, Nat.cast_one, mul_one] at hexp
    have hz : (M (QB 2) r).val = 0 ∧ (M (QB 3) r).val = 0 ∧ (M (QB 4) r).val = 0 := by
      rw [vqh, h1, Nat.cast_one, one_mul, v2, v3, v4] at hq36
      have e : (((M (QB 2) r).val + (M (QB 3) r).val + (M (QB 4) r).val : ℕ) : F) = ((0 : ℕ) : F) := by
        push_cast; rw [← hq36]; ring
      have := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) e
      omega
    have hq32 : 32 ≤ q ∧ q < 36 := by omega
    rw [le_slice4 (by omega), Bool.eq_false_iff]
    intro he
    rw [beq_iff_eq] at he
    have b0 := UInt8.toNat_lt (R.getD ((M START r).val + 32) 0)
    have b1 := UInt8.toNat_lt (R.getD ((M START r).val + 32 + 1) 0)
    have b2 := UInt8.toNat_lt (R.getD ((M START r).val + 32 + 2) 0)
    have b3 := UInt8.toNat_lt (R.getD ((M START r).val + 32 + 3) 0)
    obtain ⟨e0, e1, e2, e3⟩ := le4_ff b0 b1 b2 b3 he
    have hb : (M BQ r).val = 255 := by
      rw [hbyte]
      rcases (by omega : q = 32 ∨ q = 33 ∨ q = 34 ∨ q = 35) with hq' | hq' | hq' | hq'
      · rw [hq']; exact e0
      · rw [show (M START r).val + q = (M START r).val + 32 + 1 by omega]; exact e1
      · rw [show (M START r).val + q = (M START r).val + 32 + 2 by omega]; exact e2
      · rw [show (M START r).val + q = (M START r).val + 32 + 3 by omega]; exact e3
    apply hbne; rw [hexp, ← ZMod.natCast_zmod_val (M BQ r), hb]; simp

end Prevouts


end StarkedAir.Block.Fields
