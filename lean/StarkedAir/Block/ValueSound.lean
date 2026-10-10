/-
**Output values (M3a.5b).** In the fields component, given that byte slots read the block and range
slots hold bytes: every output's value is non-negative, and each transaction's outputs sum to at most
`MAX_MONEY` (`TxOK`'s value conditions, `values_ok_iff`).
-/
import StarkedAir.Block.TxRows
import StarkedAir.Block.FieldsChk
import StarkedAir.Spec.BlockFlat

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)

theorem le_range_map : ∀ (k : ℕ) (f : ℕ → UInt8),
    Spec.Block.le ((List.range k).map f) = ∑ j ∈ Finset.range k, (f j).toNat * 256 ^ j
  | 0, f => by simp [Spec.Block.le]
  | k + 1, f => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Spec.Block.le_cons, le_range_map k,
      Finset.sum_range_succ']
    simp only [Function.comp, pow_zero, mul_one, pow_succ, Finset.mul_sum]
    rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro j _; ring

theorem signed64_of_lt {x : ℕ} (h : x < 2 ^ 63) : Spec.Block.signed64 x = (x : ℤ) := by
  unfold Spec.Block.signed64; rw [if_pos h]

/-- The natural value of a field element known to be a small natural. -/
theorem val_eq {x : F} {m : ℕ} (h : x = (m : F)) (hm : m < P) : x.val = m := by
  rw [h, ZMod.val_natCast_of_lt hm]

theorem arith_total {T1 T0 S A B th tl car : ℕ} (h1 : T1 = th + B + car) (h2 : T0 + 16777216 * car = tl + A)
    (h3 : th * 2 ^ 24 + tl = S) : T1 * 2 ^ 24 + T0 = S + (A + 2 ^ 24 * B) := by
  subst h1 h3; norm_num; omega

theorem arith_bound {d4 d5 d6 d7 d8 d9 d10 T0 T1 bor : ℕ}
    (h1 : d4 + 256 * d5 + 65536 * d6 + T0 = MAXLO + 16777216 * bor)
    (h2 : d7 + 256 * d8 + 65536 * d9 + 16777216 * d10 + T1 + bor = MAXHI) :
    T1 * 2 ^ 24 + T0 ≤ MAXHI * 2 ^ 24 + MAXLO := by
  unfold MAXHI MAXLO at *; norm_num; omega

section Values

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hby : ∀ r < n, ∀ j < 8, (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 →
    (M BASEC r).val + j < R.length ∧ (M (BY j) r).val = (R.getD ((M BASEC r).val + j) 0).toNat)
  (hrg : ∀ r < n, ∀ j < 13, (M (RG j) r).val < 256)
  (hn : n ≤ 2 ^ 25)
include hsat hby hrg hn

omit hby hrg hn in
theorem base_out {r : ℕ} (hr : r < n) (hk : M K_OUT r = 1) : M BASEC r = M START r := by
  have := chk_defn hsat (a := BASEC) (e := .add (k START) (.mul (k K_IN) (.sub (k LEN) (c 4)))) (by simp [chkC, valueC]) hr
  have hin : M K_IN r = 0 := kind_zero_of hsat hr (a := K_OUT) (b := K_IN) (by simp [K_OUT]) (by simp [K_IN])
    (by simp [K_OUT, K_IN]) (by rw [hk]; exact one_ne_zero)
  simpa [Expr.eval, ev_k hr, hin] using this

omit hrg hn in
/-- An output row's byte slots are its 8 value bytes. -/
theorem out_bytes {r : ℕ} (hr : r < n) (hk : M K_OUT r = 1) {j : ℕ} (hj : j < 8) :
    (M START r).val + j < R.length ∧ (M (BY j) r).val = (R.getD ((M START r).val + j) 0).toNat := by
  have hm : (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 := by
    have hl : M K_LOCK r = 0 := kind_zero_of hsat hr (a := K_OUT) (b := K_LOCK) (by simp [K_OUT]) (by simp [K_LOCK])
      (by simp [K_OUT, K_LOCK]) (by rw [hk]; exact one_ne_zero)
    have hi : M K_IN r = 0 := kind_zero_of hsat hr (a := K_OUT) (b := K_IN) (by simp [K_OUT]) (by simp [K_IN])
      (by simp [K_OUT, K_IN]) (by rw [hk]; exact one_ne_zero)
    by_cases h4 : j < 4
    · rw [chk_mult_byte h4]; simp [Expr.eval, ev_k hr, hk, hl, hi]
    · rw [chk_mult_byte2 (by omega) hj]; simp [Expr.eval, ev_k hr, hk]
  rw [← base_out hsat hr hk]; exact hby r hr j hj hm

/-- **An output row's value.** Its 8 bytes read as a natural below `2^51`; the AIR's limbs `vlo` (bytes 0–2)
and `vhi` (bytes 3–6) are those of the value. -/
theorem out_value {r : ℕ} (hr : r < n) (hk : M K_OUT r = 1) :
    let v := Spec.Block.le (slice R (M START r).val 8)
    v < 2 ^ 51 ∧ (vlo.eval n preCols pub M r).val < 2 ^ 24 ∧ (vhi.eval n preCols pub M r).val < 2 ^ 27 ∧
      v = (vlo.eval n preCols pub M r).val + 2 ^ 24 * (vhi.eval n preCols pub M r).val := by
  intro v
  have ob := fun j (hj : j < 8) => out_bytes hsat R hby hr hk hj
  set s := (M START r).val
  have hfit : s + 8 ≤ R.length := by have := (ob 7 (by norm_num)).1; omega
  have hv : v = ∑ j ∈ Finset.range 8, (R.getD (s + j) 0).toNat * 256 ^ j := by
    show Spec.Block.le (slice R s 8) = _
    rw [slice_eq_map hfit, le_range_map]
  -- byte 7 is 0, byte 6 at most 7
  have c7 := sat hsat (mem_chk (c := .mul (k K_OUT) (by4 7)) (by simp [chkC, valueC])) hr
  simp only [Expr.eval, ev_k hr, hk, one_mul, by4] at c7
  have c6 := sat hsat (mem_chk (c := .mul (k K_OUT) (.sub (rg 0) (.sub (c 7) (by4 6)))) (by simp [chkC, valueC])) hr
  simp only [Expr.eval, ev_k hr, hk, one_mul, by4, rg, c, eval_cst, sub_eq_zero] at c6
  have b : ∀ j < 8, (M (BY j) r).val = (R.getD (s + j) 0).toNat := fun j hj => (ob j hj).2
  have bl : ∀ j < 8, (M (BY j) r).val < 256 := fun j hj => by rw [b j hj]; exact UInt8.toNat_lt _
  have bc : ∀ j < 8, M (BY j) r = (((M (BY j) r).val : ℕ) : F) := fun j _ => (ZMod.natCast_zmod_val _).symm
  have h7 : (M (BY 7) r).val = 0 := by rw [c7]; simp
  have r0 := hrg r hr 0 (by norm_num)
  have h6 : (M (BY 6) r).val ≤ 7 := by
    have e : M (RG 0) r + M (BY 6) r = 7 := by rw [c6]; ring
    rw [bc 6 (by norm_num), ZMod.natCast_zmod_val] at e
    have := natCast_inj_of_lt (a := (M (RG 0) r).val + (M (BY 6) r).val) (b := 7)
      (lt_P (by have := bl 6 (by norm_num); omega)) (lt_P (by norm_num))
      (by push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; exact e)
    omega
  have elo : vlo.eval n preCols pub M r =
      (((M (BY 0) r).val + 256 * (M (BY 1) r).val + 65536 * (M (BY 2) r).val : ℕ) : F) := by
    simp only [vlo, le3, le2, by4, c, Expr.eval, ev_k hr, eval_cst]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have ehi : vhi.eval n preCols pub M r = (((M (BY 3) r).val + 256 * (M (BY 4) r).val + 65536 * (M (BY 5) r).val +
      16777216 * (M (BY 6) r).val : ℕ) : F) := by
    simp only [vhi, le4, le3, le2, by4, c, Expr.eval, ev_k hr, eval_cst]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have l0 := bl 0 (by norm_num); have l1 := bl 1 (by norm_num); have l2 := bl 2 (by norm_num)
  have l3 := bl 3 (by norm_num); have l4 := bl 4 (by norm_num); have l5 := bl 5 (by norm_num)
  have hv' : v = ∑ j ∈ Finset.range 8, (M (BY j) r).val * 256 ^ j := by
    rw [hv]; apply Finset.sum_congr rfl; intro j hj; rw [b j (Finset.mem_range.mp hj)]
  rw [val_eq elo (lt_P (by omega)), val_eq ehi (lt_P (by omega)), hv']
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, h7]
  refine ⟨by omega, by omega, by omega, by ring⟩

/-- An output row's value (0 on other rows). -/
def outVal (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) : ℕ :=
  if M K_OUT r = 1 then Spec.Block.le (slice R (M START r).val 8) else 0

/-- The values of the output rows among `a, …, a + d − 1`. -/
def outSum (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (a d : ℕ) : ℕ := ∑ x ∈ Finset.range d, outVal M R (a + x)

omit hsat hby hrg hn in
theorem nat_eqF {a b : ℕ} (h : (a : F) = (b : F)) (ha : a < P) (hb : b < P) : a = b := natCast_inj_of_lt ha hb h

omit hby hrg hn in
theorem running {x : ℕ} (hx : x + 1 < n) :
    M TLO (x + 1) = (1 - M K_TXH (x + 1)) * M TLO x + M K_OUT (x + 1) * vlo.eval n preCols pub M (x + 1) -
        16777216 * M CAR (x + 1) ∧
      M THI (x + 1) = (1 - M K_TXH (x + 1)) * M THI x + M K_OUT (x + 1) * vhi.eval n preCols pub M (x + 1) +
        M CAR (x + 1) := by
  have c1 := sat hsat (mem_chk (c := .mul notFirst (.add (.sub (.sub (k TLO) (.mul (oneMinus (k K_TXH)) (kp TLO)))
    (.mul (k K_OUT) vlo)) (.mul (c 16777216) (k CAR)))) (by simp [chkC, valueC])) hx
  have c2 := sat hsat (mem_chk (c := .mul notFirst (.sub (.sub (.sub (k THI) (.mul (oneMinus (k K_TXH)) (kp THI)))
    (.mul (k K_OUT) vhi)) (k CAR))) (by simp [chkC, valueC])) hx
  simp only [Expr.eval, ev_notFirst hx, ev_k hx, ev_kp hx, oneMinus, one, c, eval_cst, one_mul, Nat.cast_one,
    Nat.cast_ofNat] at c1 c2
  constructor
  · linear_combination c1
  · linear_combination c2

omit hby hrg hn in
theorem car_zero {x : ℕ} (hx : x < n) (h : M K_OUT x = 0) : M CAR x = 0 := by
  have := sat hsat (mem_chk (c := .mul (oneMinus (k K_OUT)) (k CAR)) (by simp [chkC, valueC])) hx
  simpa [Expr.eval, ev_k hx, oneMinus, one, eval_cst, h] using this

set_option maxHeartbeats 2000000 in
/-- **The running total.** From a transaction head `rh` (not row 0) through the rows of that transaction,
`THI · 2^24 + TLO` is the sum of the output values so far, at most `MAX_MONEY`. -/
theorem total_inv {rh : ℕ} (hrh : rh < n) (ht : M K_TXH rh = 1) (h0 : rh ≠ 0) :
    ∀ d, rh + d < n → (∀ j, rh < j → j ≤ rh + d → M K_TXH j = 0) →
      (M TLO (rh + d)).val < 2 ^ 24 ∧ (M THI (rh + d)).val ≤ MAXHI ∧
      (M THI (rh + d)).val * 2 ^ 24 + (M TLO (rh + d)).val = outSum M R (rh + 1) d ∧
      outSum M R (rh + 1) d ≤ MAXHI * 2 ^ 24 + MAXLO := by
  intro d
  induction d with
  | zero =>
    intro hd _
    obtain ⟨rp, rfl⟩ : ∃ rp, rh = rp + 1 := ⟨rh - 1, by omega⟩
    have hout : M K_OUT (rp + 1) = 0 := kind_zero_of hsat hrh (a := K_TXH) (b := K_OUT) (by simp [K_TXH])
      (by simp [K_OUT]) (by simp [K_TXH, K_OUT]) (by rw [ht]; exact one_ne_zero)
    obtain ⟨e1, e2⟩ := running hsat (x := rp) (by omega)
    rw [ht, hout, car_zero hsat hrh hout] at e1 e2
    simp only [sub_self, zero_mul, zero_add, sub_zero, mul_zero, add_zero] at e1 e2
    simp [Nat.add_zero, e1, e2, outSum, MAXHI, MAXLO]
  | succ d ih =>
    intro hd htx
    obtain ⟨tl, th, tot, tm⟩ := ih (by omega) (fun j a b => htx j a (by omega))
    set x := rh + d with hx
    have hxn : x + 1 < n := by omega
    have hnt : M K_TXH (x + 1) = 0 := htx (x + 1) (by omega) (by omega)
    obtain ⟨e1, e2⟩ := running hsat hxn
    simp only [hnt, sub_zero, one_mul] at e1 e2
    have hsum : outSum M R (rh + 1) (d + 1) = outSum M R (rh + 1) d + outVal M R (x + 1) := by
      simp only [outSum, Finset.sum_range_succ]; congr 2; omega
    rw [show rh + (d + 1) = x + 1 by omega, hsum]
    rcases kind_bool hsat (c := K_OUT) (by simp [kinds, K_OUT]) (show x + 1 < n by omega) with ho | ho
    · -- not an output: nothing changes
      rw [ho, car_zero hsat hxn ho] at e1 e2
      simp only [zero_mul, add_zero, sub_zero, mul_zero] at e1 e2
      rw [e1, e2, outVal, if_neg (by rw [ho]; exact zero_ne_one), Nat.add_zero]
      exact ⟨tl, th, tot, tm⟩
    · -- an output: the limbs and the `MAX_MONEY` check
      obtain ⟨vlt, vlo_lt, vhi_lt, veq⟩ := out_value hsat R hby hrg hn hxn ho
      rw [ho, one_mul] at e1 e2
      have rgv := fun j (hj : j < 13) => hrg (x + 1) hxn j hj
      have rgc : ∀ j, M (RG j) (x + 1) = (((M (RG j) (x + 1)).val : ℕ) : F) := fun j => (ZMod.natCast_zmod_val _).symm
      have cr := chk_bool hsat (e := CAR) (by simp [chkC, valueC]) hxn
      have br := chk_bool hsat (e := BOR) (by simp [chkC, valueC]) hxn
      have q := fun (cc : Expr) (h : cc ∈ valueC) => sat hsat (mem_chk (c := cc) (by simp [chkC]; tauto)) hxn
      have r1 := q (.mul (k K_OUT) (.sub (k TLO) (le3 (rg 1) (rg 2) (rg 3)))) (by simp [valueC])
      have r2 := q (.mul (k K_OUT) (.sub (le3 (rg 4) (rg 5) (rg 6)) (.add (.sub (c MAXLO) (k TLO))
        (.mul (c 16777216) (k BOR))))) (by simp [valueC])
      have r3 := q (.mul (k K_OUT) (.sub (le4 (rg 7) (rg 8) (rg 9) (rg 10)) (.sub (.sub (c MAXHI) (k THI)) (k BOR))))
        (by simp [valueC])
      have r4 := q (.mul (k K_OUT) (.sub (rg 11) (.sub (c 7) (rg 10)))) (by simp [valueC])
      simp only [Expr.eval, ev_k hxn, ho, one_mul, le3, le4, le2, rg, c, eval_cst, sub_eq_zero, Nat.cast_ofNat] at r1 r2 r3 r4
      set g := fun j => (M (RG j) (x + 1)).val
      have g0 := rgv 1 (by norm_num); have g1 := rgv 2 (by norm_num); have g2 := rgv 3 (by norm_num)
      have g3 := rgv 4 (by norm_num); have g4 := rgv 5 (by norm_num); have g5 := rgv 6 (by norm_num)
      have g6 := rgv 7 (by norm_num); have g7 := rgv 8 (by norm_num); have g8 := rgv 9 (by norm_num)
      have g9 := rgv 10 (by norm_num); have g10 := rgv 11 (by norm_num)
      -- byte 10 of the high difference is at most 7
      have h10 : (M (RG 10) (x + 1)).val ≤ 7 := by
        have e : (((M (RG 11) (x + 1)).val + (M (RG 10) (x + 1)).val : ℕ) : F) = ((7 : ℕ) : F) := by
          push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination r4
        have := nat_eqF e (lt_P (by omega)) (lt_P (by norm_num)); omega
      -- the new low limb
      have tlo' : (M TLO (x + 1)).val = (M (RG 1) (x + 1)).val + 256 * (M (RG 2) (x + 1)).val +
          65536 * (M (RG 3) (x + 1)).val := by
        apply val_eq _ (lt_P (by omega))
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination r1
      have cv := bool_val cr
      have bv := bool_val br
      -- low: TLO' + 2^24·CAR = TLO + vlo
      have elo : (M TLO (x + 1)).val + 16777216 * (M CAR (x + 1)).val =
          (M TLO x).val + (vlo.eval n preCols pub M (x + 1)).val := by
        apply nat_eqF _ (lt_P (by omega)) (lt_P (by omega))
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination e1
      -- high: THI' = THI + vhi + CAR
      have ehi : (M THI (x + 1)).val = (M THI x).val + (vhi.eval n preCols pub M (x + 1)).val + (M CAR (x + 1)).val := by
        apply val_eq _ (lt_P (by unfold MAXHI at th; omega))
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination e2
      -- the check: D_lo + TLO' = MAXLO + 2^24·BOR, D_hi + THI' + BOR = MAXHI
      have dlo : (M (RG 4) (x + 1)).val + 256 * (M (RG 5) (x + 1)).val + 65536 * (M (RG 6) (x + 1)).val +
          (M TLO (x + 1)).val = MAXLO + 16777216 * (M BOR (x + 1)).val := by
        apply nat_eqF _ (lt_P (by omega)) (lt_P (by unfold MAXLO; omega))
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination r2
      have dhi : (M (RG 7) (x + 1)).val + 256 * (M (RG 8) (x + 1)).val + 65536 * (M (RG 9) (x + 1)).val +
          16777216 * (M (RG 10) (x + 1)).val + (M THI (x + 1)).val + (M BOR (x + 1)).val = MAXHI := by
        apply nat_eqF _ (lt_P (by unfold MAXHI at th; omega)) (lt_P (by unfold MAXHI; omega))
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination r3
      rw [outVal, if_pos ho, veq]
      have g3 := arith_total ehi elo tot
      refine ⟨by omega, by omega, g3, ?_⟩
      rw [← g3]
      exact arith_bound dlo dhi

end Values

theorem list_sum_getD {α β : Type} [AddCommMonoid β] (d : α) (f : α → β) :
    ∀ l : List α, (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i d)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, list_sum_getD d f l, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

section TxValues

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

/-- **`TxOK`'s value conditions.** Every output of a transaction is non-negative and their sum is at most
`MAX_MONEY`. -/
theorem tx_values {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) (hl : M K_LOCK ρ = 1) :
    (∀ o ∈ tx.vout, 0 ≤ o.value) ∧ (tx.vout.map (·.value)).sum ≤ Spec.Block.MAX_MONEY := by
  obtain ⟨rh, hrh, ht, hnt, hvl, h1, hins, hno, hnv, houts, hwit, -, -, hle⟩ := tx_rows hsat R hcs hmn hpad hfit hat hρm
  have hn0 : 0 < n := by omega
  have h0 : rh ≠ 0 := by
    intro e; subst e
    have := first_blk hsat hn0
    rw [kind_unique hsat hn0 (a := K_BLK) (b := K_TXH) (by simp [K_BLK]) (by simp [K_TXH]) (by simp [K_BLK, K_TXH]) this]
      at ht
    exact zero_ne_one ht
  obtain ⟨-, -, tot, tm⟩ := total_inv hsat R hby hrg hn (rh := rh) (by omega) ht h0 (ρ - rh) (by omega)
    (fun j a b => hnt j a (by omega))
  set nI := tx.vin.length
  set k := tx.vout.length
  -- the output values as naturals
  have ov : ∀ o < k, ∃ out, tx.vout[o]? = some out ∧ out.value = (outVal M R (rh + 2 + nI + o) : ℤ) ∧
      outVal M R (rh + 2 + nI + o) < 2 ^ 51 := by
    intro o ho
    obtain ⟨out, hget, hrow⟩ := houts o ho
    have hr : rh + 2 + nI + o < n := by omega
    obtain ⟨vlt, -, -, -⟩ := out_value hsat R hby hrg hn hr hrow.kind
    refine ⟨out, hget, ?_, ?_⟩
    · rw [hrow.value, outVal, if_pos hrow.kind, signed64_of_lt (by omega)]
    · rw [outVal, if_pos hrow.kind]; exact vlt
  have notout : ∀ x < n, M K_OUT x ≠ 1 → outVal M R x = 0 := fun x _ h => by rw [outVal, if_neg h]
  have kz : ∀ x < n, ∀ a < 9, a ≠ K_OUT → M a x = 1 → outVal M R x = 0 := fun x hx a ha hne h => by
    apply notout x hx
    rw [kind_unique hsat hx ha (by simp [K_OUT]) hne h]; exact zero_ne_one
  -- the rows' output values are exactly the outputs'
  have split : outSum M R (rh + 1) (ρ - rh) = ∑ o ∈ Finset.range k, outVal M R (rh + 2 + nI + o) := by
    have e : ρ - rh = (nI + 1) + k + (ρ - rh - (nI + 1 + k)) := by omega
    rw [outSum, e, Finset.sum_range_add, Finset.sum_range_add]
    have z1 : ∑ x ∈ Finset.range (nI + 1), outVal M R (rh + 1 + x) = 0 := by
      apply Finset.sum_eq_zero; intro x hx; rw [Finset.mem_range] at hx
      rcases Nat.lt_or_ge x nI with hlt | hge
      · obtain ⟨_, _, hrow⟩ := hins x hlt
        exact kz _ (by omega) K_IN (by simp [K_IN]) (by simp [K_IN, K_OUT]) hrow.kind
      · have : x = nI := by omega
        subst this
        exact kz _ (by omega) K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_OUT]) hno
    have z3 : ∑ x ∈ Finset.range (ρ - rh - (nI + 1 + k)), outVal M R (rh + 1 + (nI + 1 + k + x)) = 0 := by
      apply Finset.sum_eq_zero; intro x hx; rw [Finset.mem_range] at hx
      by_cases hx' : rh + 1 + (nI + 1 + k + x) < ρ
      · rcases hwit _ (by omega) hx' with h | h
        · exact kz _ (by omega) K_WCNT (by simp [K_WCNT]) (by simp [K_WCNT, K_OUT]) h
        · exact kz _ (by omega) K_WITEM (by simp [K_WITEM]) (by simp [K_WITEM, K_OUT]) h
      · rw [show rh + 1 + (nI + 1 + k + x) = ρ by omega]
        exact kz _ (by omega) K_LOCK (by simp [K_LOCK]) (by simp [K_LOCK, K_OUT]) hl
    rw [z1, z3, zero_add, add_zero]
    apply Finset.sum_congr rfl; intro o _; congr 1; omega
  have hsumz : (tx.vout.map (·.value)).sum = ∑ o ∈ Finset.range k, (outVal M R (rh + 2 + nI + o) : ℤ) := by
    rw [list_sum_getD ⟨0, []⟩]
    apply Finset.sum_congr rfl; intro o ho
    obtain ⟨out, hget, hv, -⟩ := ov o (Finset.mem_range.mp ho)
    rw [List.getD_eq_getElem?_getD, hget, Option.getD_some, hv]
  refine ⟨fun o ho => ?_, ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
    obtain ⟨out, hget, hv, -⟩ := ov i hi
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hget
    rw [hget, hv]; positivity
  · rw [hsumz, ← Nat.cast_sum, ← split]
    have : (outSum M R (rh + 1) (ρ - rh) : ℤ) ≤ ((MAXHI * 2 ^ 24 + MAXLO : ℕ) : ℤ) := by exact_mod_cast tm
    rw [show ((MAXHI * 2 ^ 24 + MAXLO : ℕ) : ℤ) = Spec.Block.MAX_MONEY by
      unfold MAXHI MAXLO Spec.Block.MAX_MONEY; norm_num] at this
    exact this

end TxValues


end StarkedAir.Block.Fields
