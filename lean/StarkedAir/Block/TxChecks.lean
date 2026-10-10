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


theorem arith_ty1 {elo ehi lo hi b2 : ℕ} (h1 : elo + 25856 = lo + 65536 * b2) (h2 : ehi + 7629 + b2 = hi) :
    500000000 ≤ lo + 65536 * hi := by omega

theorem arith_cut {dlo dhi lo hi clo chi brw : ℕ} (h1 : dlo + lo + 1 = clo + 65536 * brw) (h2 : dhi + hi + brw = chi) :
    lo + 65536 * hi < clo + 65536 * chi := by omega

section Final

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hby : ∀ r < n, ∀ j < 8, (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 →
    (M BASEC r).val + j < R.length ∧ (M (BY j) r).val = (R.getD ((M BASEC r).val + j) 0).toNat)
  (hrg : ∀ r < n, ∀ j < 13, (M (RG j) r).val < 256)
  (hn : n ≤ 2 ^ 25)
include hsat hcs hmn hpad hfit hby hrg hn

omit hcs hmn hpad hfit hby hrg hn in
/-- A transaction's mode columns are constant from its head through its lock time. -/
theorem mode_const {rh ρ : ℕ} (hρn : ρ < n) (hnt : ∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) {X : ℕ}
    (hX : X ∈ [FZ, FL, FS, TY]) : ∀ j, rh ≤ j → j ≤ ρ → M X j = M X rh := by
  intro j h1 h2
  induction j, h1 using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hjn : j + 1 < n := by omega
    have := sat hsat (mem_chk (c := .mul (oneMinus (k K_TXH)) (same X)) (by
      simp only [chkC, modeC, List.mem_append, List.mem_map]
      left; left; left; left; left; right; exact ⟨X, hX, rfl⟩)) hjn
    simp only [Expr.eval, same, oneMinus, one, eval_cst, Nat.cast_one, ev_k hjn, ev_kp hjn, ev_notFirst hjn,
      hnt (j + 1) (by omega) h2, sub_zero, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega)]

/-- A lock-time row's byte slots are its 4 lock-time bytes. -/
theorem lock_bytes {r : ℕ} (hr : r < n) (hl : M K_LOCK r = 1) {j : ℕ} (hj : j < 4) :
    (M START r).val + j < R.length ∧ (M (BY j) r).val = (R.getD ((M START r).val + j) 0).toNat := by
  have hin : M K_IN r = 0 := kind_zero_of hsat hr (a := K_LOCK) (b := K_IN) (by simp [K_LOCK]) (by simp [K_IN])
    (by simp [K_LOCK, K_IN]) (by rw [hl]; exact one_ne_zero)
  have hout : M K_OUT r = 0 := kind_zero_of hsat hr (a := K_LOCK) (b := K_OUT) (by simp [K_LOCK]) (by simp [K_OUT])
    (by simp [K_LOCK, K_OUT]) (by rw [hl]; exact one_ne_zero)
  have hb : M BASEC r = M START r := by
    have := chk_defn hsat (a := BASEC) (e := .add (k START) (.mul (k K_IN) (.sub (k LEN) (c 4)))) (by simp [chkC, valueC]) hr
    simpa [Expr.eval, ev_k hr, hin] using this
  rw [← hb]
  exact hby r hr j (by omega) (by rw [chk_mult_byte hj]; simp [Expr.eval, ev_k hr, hl, hin, hout])

/-- An input row's byte slots are its 4 sequence bytes. -/
theorem seq_bytes {r : ℕ} (hr : r < m) (hi : M K_IN r = 1) {j : ℕ} (hj : j < 4) :
    (M START r).val + 36 + prefOf M r + (M VAL r).val + j < R.length ∧
    (M (BY j) r).val = (R.getD ((M START r).val + 36 + prefOf M r + (M VAL r).val + j) 0).toNat := by
  have hrn : r < n := by omega
  have hl : M K_LOCK r = 0 := kind_zero_of hsat hrn (a := K_IN) (b := K_LOCK) (by simp [K_IN]) (by simp [K_LOCK])
    (by simp [K_LOCK, K_IN]) (by rw [hi]; exact one_ne_zero)
  have hout : M K_OUT r = 0 := kind_zero_of hsat hrn (a := K_IN) (b := K_OUT) (by simp [K_IN]) (by simp [K_OUT])
    (by simp [K_IN, K_OUT]) (by rw [hi]; exact one_ne_zero)
  have hlen : (M LEN r).val = 40 + prefOf M r + (M VAL r).val := by
    have := (row_info hsat R hcs hmn hpad hfit hr (a := K_IN) (by simp [K_IN]) hi
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])).2.1
    rw [this]; simp [lenN, K_BLK, K_TXH, K_IN]
  have hst := start_lt hsat hrn
  have hfr := hfit r hr
  have hb : (M BASEC r).val = (M START r).val + 36 + prefOf M r + (M VAL r).val := by
    have := chk_defn hsat (a := BASEC) (e := .add (k START) (.mul (k K_IN) (.sub (k LEN) (c 4)))) (by simp [chkC, valueC]) hrn
    simp only [Expr.eval, ev_k hrn, hi, one_mul, c, eval_cst] at this
    obtain ⟨hv, -, -, hp5, -⟩ := row_info hsat R hcs hmn hpad hfit hr (a := K_IN) (by simp [K_IN]) hi
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])
    have e : M BASEC r = (((M START r).val + 36 + prefOf M r + (M VAL r).val : ℕ) : F) := by
      rw [this]
      have hS := ZMod.natCast_zmod_val (M START r)
      have hL' := ZMod.natCast_zmod_val (M LEN r)
      conv_lhs => rw [← hS, ← hL', hlen]
      push_cast; ring
    rw [e]
    exact ZMod.val_natCast_of_lt (lt_P (by unfold MAXS at hv; omega))
  rw [← hb]
  exact hby r hrn j (by omega) (by rw [chk_mult_byte hj]; simp [Expr.eval, ev_k hrn, hl, hi, hout])

set_option maxHeartbeats 4000000 in
/-- **Every transaction is final** (`IsFinalTx`) for the height `pub 2` and the cutoff whose 16-bit limbs
are `CLO`, `CHI`. -/
theorem tx_final {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) (hl : M K_LOCK ρ = 1)
    {height cutoff : ℕ} (hh : pub 2 = (height : F)) (hh23 : height < 2 ^ 23)
    (hco : M CLO ρ = ((cutoff % 65536 : ℕ) : F) ∧ M CHI ρ = ((cutoff / 65536 : ℕ) : F)) (hco32 : cutoff < 2 ^ 32) :
    Spec.Block.isFinal tx height cutoff = true := by
  obtain ⟨rh, hrh, ht, hnt, hvl, h1, hins, hno, hnv, houts, hwit, hlt, hseg, hle, hlk⟩ :=
    tx_rows' hsat R hcs hmn hpad hfit hn hat hρm
  have hρn : ρ < n := by omega
  have mc := fun X (hX : X ∈ [FZ, FL, FS, TY]) => mode_const hsat hρn hnt hX
  -- the lock time's bytes
  have lb := fun j (hj : j < 4) => lock_bytes hsat R hcs hmn hpad hfit hby hrg hn hρn hl hj
  set S := (M START ρ).val
  have hfr : S + 4 ≤ R.length := by have := (lb 3 (by norm_num)).1; omega
  have bv : ∀ j < 4, (M (BY j) ρ).val = (R.getD (S + j) 0).toNat := fun j hj => (lb j hj).2
  have b256 : ∀ j < 4, (M (BY j) ρ).val < 256 := fun j hj => by rw [bv j hj]; exact UInt8.toNat_lt _
  have hlock : tx.lockTime = (M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val + 65536 * (M (BY 2) ρ).val +
      16777216 * (M (BY 3) ρ).val := by
    have b0' : (M (BY 0) ρ).val = (R.getD S 0).toNat := by simpa using bv 0 (by norm_num)
    rw [hlt, le_slice4 hfr, ← b0', ← bv 1 (by norm_num), ← bv 2 (by norm_num), ← bv 3 (by norm_num)]
  have bc : ∀ j, M (BY j) ρ = (((M (BY j) ρ).val : ℕ) : F) := fun j => (ZMod.natCast_zmod_val _).symm
  have x0 := b256 0 (by norm_num); have x1 := b256 1 (by norm_num)
  have x2 := b256 2 (by norm_num); have x3 := b256 3 (by norm_num)
  -- the mode, one-hot
  have mb := fun X (h : boolC (k X) ∈ chkC) => chk_bool hsat (e := X) h hρn
  have fz := mb FZ (by simp [chkC, modeC]); have fl := mb FL (by simp [chkC, modeC])
  have fs := mb FS (by simp [chkC, modeC]); have ty := mb TY (by simp [chkC, modeC])
  have hsum := sat hsat (mem_chk (c := .sub (.add (k FZ) (.add (k FL) (k FS))) one) (by simp [chkC, modeC])) hρn
  simp only [Expr.eval, ev_k hρn, one, eval_cst, Nat.cast_one, sub_eq_zero] at hsum
  have q := fun (cc : Expr) (h : cc ∈ finalC) => sat hsat (mem_chk (c := cc) (by simp [chkC]; tauto)) hρn
  have gdef := fun (a : ℕ) (e : Expr) (h : Expr.sub (k a) e ∈ finalC) =>
    chk_defn hsat (a := a) (e := e) (by simp [chkC]; tauto) hρn
  unfold Spec.Block.isFinal
  rcases fz with z0 | z1
  · rcases fl with l0 | l1
    · -- sequences: every input's sequence is `ffffffff`
      have fs1 : M FS ρ = 1 := by rw [z0, l0] at hsum; simpa using hsum
      simp only [Bool.or_eq_true]; right
      rw [List.all_eq_true]
      intro i hi
      obtain ⟨x, hx, rfl⟩ := List.getElem_of_mem hi
      obtain ⟨inp, hget, hrow⟩ := hins x hx
      rw [List.getElem?_eq_getElem hx, Option.some.injEq] at hget
      rw [hget, hrow.seq]
      set r := rh + 1 + x
      have hrm : r < m := by omega
      have hrn : r < n := by omega
      have fsr : M FS r = 1 := by rw [mc FS (by simp) r (by omega) (by omega), ← mc FS (by simp) ρ (by omega) le_rfl, fs1]
      have gs := gdef GS (.mul (k K_IN) (k FS)) (by simp [finalC])
      have gsr : M GS r = 1 := by
        have := chk_defn hsat (a := GS) (e := .mul (k K_IN) (k FS)) (by simp [chkC, finalC]) hrn
        simp [Expr.eval, ev_k hrn, hrow.kind, fsr] at this; exact this
      have sb := fun j (hj : j < 4) => seq_bytes hsat R hcs hmn hpad hfit hby hrg hn hrm hrow.kind hj
      have ff : ∀ j < 4, (M (BY j) r).val = 255 := by
        intro j hj
        have hc : Expr.mul (k GS) (.sub (by4 j) (c 255)) ∈ finalC := by
          have : Expr.mul (k GS) (.sub (by4 j) (c 255)) ∈ (List.range 4).map (fun j => Expr.mul (k GS) (.sub (by4 j) (c 255))) :=
            List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
          simp only [finalC, List.mem_append]; tauto
        have := sat hsat (mem_chk (c := Expr.mul (k GS) (.sub (by4 j) (c 255))) (by simp [chkC]; tauto)) hrn
        simp only [Expr.eval, ev_k hrn, gsr, one_mul, by4, c, eval_cst, sub_eq_zero] at this
        rw [this]; exact ZMod.val_natCast_of_lt (by unfold P; norm_num)
      have hfr' := (sb 3 (by norm_num)).1
      rw [le_slice4 (by omega)]
      have e0 := (sb 0 (by norm_num)).2; have e1 := (sb 1 (by norm_num)).2
      have e2 := (sb 2 (by norm_num)).2; have e3 := (sb 3 (by norm_num)).2
      rw [ff 0 (by norm_num)] at e0; rw [ff 1 (by norm_num)] at e1
      rw [ff 2 (by norm_num)] at e2; rw [ff 3 (by norm_num)] at e3
      simp only [Nat.add_zero] at e0
      rw [← e0, ← e1, ← e2, ← e3]; rfl
    · -- below the threshold
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      left; right
      rcases ty with t0 | t1
      · -- height-based
        have g0 : M GL0 ρ = 1 := by
          have := gdef GL0 (.mul (k K_LOCK) (.mul (k FL) (oneMinus (k TY)))) (by simp [finalC])
          simpa [Expr.eval, ev_k hρn, oneMinus, one, eval_cst, hl, l1, t0] using this
        have c3 := q (.mul (k GL0) (by4 3)) (by simp [finalC])
        have c4 := q (.mul (k GL0) (.sub (rg 0) (.sub (c 127) (by4 2)))) (by simp [finalC])
        have c5 := q (.mul (k GL0) (.sub (le3 (rg 1) (rg 2) (rg 3)) (.sub (.sub (.pub 2) one) (le3 (by4 0) (by4 1) (by4 2)))))
          (by simp [finalC])
        simp only [Expr.eval, ev_k hρn, g0, one_mul, by4, rg, c, le3, le2, one, eval_cst, sub_eq_zero, Nat.cast_one,
          Nat.cast_ofNat, hh] at c3 c4 c5
        have b3 : (M (BY 3) ρ).val = 0 := by rw [c3]; simp
        have r0 := hrg ρ hρn 0 (by norm_num)
        have b2 : (M (BY 2) ρ).val ≤ 127 := by
          have e : (((M (RG 0) ρ).val + (M (BY 2) ρ).val : ℕ) : F) = ((127 : ℕ) : F) := by
            push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c4
          have := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) e; omega
        have g1 := hrg ρ hρn 1 (by norm_num); have g2 := hrg ρ hρn 2 (by norm_num); have g3 := hrg ρ hρn 3 (by norm_num)
        have e : (((M (RG 1) ρ).val + 256 * (M (RG 2) ρ).val + 65536 * (M (RG 3) ρ).val +
            ((M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val + 65536 * (M (BY 2) ρ).val) + 1 : ℕ) : F) = ((height : ℕ) : F) := by
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c5
        have he := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega)) e
        rw [hlock, b3]
        have hlt5 : (M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val + 65536 * (M (BY 2) ρ).val + 16777216 * 0 < 500000000 := by
          omega
        rw [if_pos hlt5]; omega
      · -- time-based
        have g1 : M GL1 ρ = 1 := by
          have := gdef GL1 (.mul (k K_LOCK) (.mul (k FL) (k TY))) (by simp [finalC])
          simpa [Expr.eval, ev_k hρn, hl, l1, t1] using this
        have c6 := q (.mul (k GL1) (.sub (le2 (rg 4) (rg 5)) (.add (.sub lo16 (c 0x6500)) (.mul (c 65536) (k B2)))))
          (by simp [finalC])
        have c7 := q (.mul (k GL1) (.sub (le2 (rg 6) (rg 7)) (.sub (.sub hi16 (c 0x1DCD)) (k B2)))) (by simp [finalC])
        have c8 := q (.mul (k GL1) (.sub (le2 (rg 8) (rg 9)) (.add (.sub (.sub (k CLO) lo16) one) (.mul (c 65536) (k BRW)))))
          (by simp [finalC])
        have c9 := q (.mul (k GL1) (.sub (le2 (rg 10) (rg 11)) (.sub (.sub (k CHI) hi16) (k BRW)))) (by simp [finalC])
        simp only [Expr.eval, ev_k hρn, g1, one_mul, by4, rg, c, le2, lo16, hi16, one, eval_cst, sub_eq_zero,
          Nat.cast_one, Nat.cast_ofNat] at c6 c7 c8 c9
        obtain ⟨vb2, lb2⟩ := bool_val (chk_bool hsat (e := B2) (by simp [chkC, finalC]) hρn)
        obtain ⟨vbr, lbr⟩ := bool_val (chk_bool hsat (e := BRW) (by simp [chkC, finalC]) hρn)
        have rg' := fun j (hj : j < 13) => hrg ρ hρn j hj
        have y4 := rg' 4 (by norm_num); have y5 := rg' 5 (by norm_num); have y6 := rg' 6 (by norm_num)
        have y7 := rg' 7 (by norm_num); have y8 := rg' 8 (by norm_num); have y9 := rg' 9 (by norm_num)
        have y10 := rg' 10 (by norm_num); have y11 := rg' 11 (by norm_num)
        have co1 : cutoff % 65536 < 65536 := Nat.mod_lt _ (by norm_num)
        have co2 : cutoff / 65536 < 65536 := by omega
        rw [hco.1] at c8; rw [hco.2] at c9
        have n6 : (M (RG 4) ρ).val + 256 * (M (RG 5) ρ).val + 25856 =
            ((M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val) + 65536 * (M B2 ρ).val := by
          apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c6
        have n7 : (M (RG 6) ρ).val + 256 * (M (RG 7) ρ).val + 7629 + (M B2 ρ).val =
            (M (BY 2) ρ).val + 256 * (M (BY 3) ρ).val := by
          apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c7
        have n8 : (M (RG 8) ρ).val + 256 * (M (RG 9) ρ).val + ((M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val) + 1 =
            cutoff % 65536 + 65536 * (M BRW ρ).val := by
          apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c8
        have n9 : (M (RG 10) ρ).val + 256 * (M (RG 11) ρ).val + ((M (BY 2) ρ).val + 256 * (M (BY 3) ρ).val) +
            (M BRW ρ).val = cutoff / 65536 := by
          apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c9
        have ge := arith_ty1 n6 n7
        have lt := arith_cut n8 n9
        rw [hlock]
        have hnlt : ¬ ((M (BY 0) ρ).val + 256 * (M (BY 1) ρ).val + 65536 * (M (BY 2) ρ).val +
            16777216 * (M (BY 3) ρ).val < 500000000) := by omega
        rw [if_neg hnlt]
        have := Nat.div_add_mod cutoff 65536
        omega
  · -- zero lock time
    simp only [Bool.or_eq_true, beq_iff_eq]; left; left
    have gz : M GZ ρ = 1 := by
      have := gdef GZ (.mul (k K_LOCK) (k FZ)) (by simp [finalC])
      simpa [Expr.eval, ev_k hρn, hl, z1] using this
    have cz := q (.mul (k GZ) (.add (by4 0) (.add (by4 1) (.add (by4 2) (by4 3))))) (by simp [finalC])
    simp only [Expr.eval, ev_k hρn, gz, one_mul, by4] at cz
    have e : (((M (BY 0) ρ).val + ((M (BY 1) ρ).val + ((M (BY 2) ρ).val + (M (BY 3) ρ).val)) : ℕ) : F) = ((0 : ℕ) : F) := by
      push_cast; simp only [ZMod.natCast_zmod_val]; exact cz
    have := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) e
    rw [hlock]; omega

end Final

end StarkedAir.Block.Fields
