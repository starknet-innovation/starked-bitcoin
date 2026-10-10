/-
**The coinbase from its bytes (M3a.5c).** The context component reads the coinbase's bytes at
`cbase = TXA + 2·SEG` (after its version, marker and flag): one input, a null prevout, a one-byte
scriptSig length. With the transaction's rows, these make its inputs `[inp]` with a null prevout and
the scriptSig the bytes after that length.
-/
import StarkedAir.Block.TxWits

namespace StarkedAir.Block.Fields

open StarkedAir

theorem slice_getD {R : Spec.Block.Bytes} {a b i : ℕ} (hi : i < b) (h : a + b ≤ R.length) :
    (slice R a b).getD i 0 = R.getD (a + i) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem serCompact_ne (x : ℕ) : Spec.Block.serCompact x ≠ [] := by
  unfold Spec.Block.serCompact; split_ifs <;> simp

section Coinbase

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hnp : ∀ r < m, M K_PAD r = 0)
  (hmk : ∀ r < n, M K_TXH r = 1 → M SEG r = 1 →
    (M START r).val + 5 < R.length ∧ R.getD ((M START r).val + 4) 0 = 0 ∧ R.getD ((M START r).val + 5) 0 = 1)
include hsat hcs hmn hpad hfit hnp hmk

/-- **The head's columns on the lock-time row**: `TXA` is the head's start and `SEG` its flag. -/
theorem head_cols {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) {rh : ℕ} (hrh : rh < ρ)
    (ht : M K_TXH rh = 1) (hnt : ∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) :
    M TXA ρ = M START rh ∧ M SEG ρ = M SEG rh := by
  obtain ⟨rh', hrh', ht', hnt', htx'⟩ := hat
  obtain rfl : rh' = rh := by
    rcases lt_trichotomy rh' rh with h | h | h
    · have := hnt' rh h (by omega); rw [ht] at this; exact absurd this one_ne_zero
    · exact h
    · have := hnt rh' h (by omega); rw [ht'] at this; exact absurd this one_ne_zero
  obtain ⟨tx', r', -, -, -, -, htx, -, -, hr'm, -, -, -, -, -, hta, -, hsg, -⟩ :=
    tx_cols hsat R hcs hmn hpad hfit (show rh' < m by
      by_contra hc; have := hpad rh' (by omega) (by omega)
      rw [kind_unique hsat (show rh' < n by omega) (a := K_TXH) (b := K_PAD) (by simp [K_TXH]) (by simp [K_PAD])
        (by simp [K_TXH, K_PAD]) ht] at this; exact zero_ne_one this) ht
  rw [htx'] at htx
  simp only [Option.some.injEq, Prod.mk.injEq] at htx
  obtain rfl : ρ = r' := by
    have := congrArg List.length htx.2; simp only [toksFrom_length] at this
    omega
  exact ⟨hta, hsg⟩

/-- **The coinbase's input**, from the bytes at `cbase`: one input, a null prevout, and the scriptSig of
the given one-byte length. -/
theorem cb_tx {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) {cb : ℕ}
    (hcb : cb = (M TXA ρ).val + 2 * (M SEG ρ).val)
    (hbytes : ∀ r ≤ 36, cb + 4 + r < R.length ∧
      (R.getD (cb + 4 + r) 0).toNat = (if r = 0 then 1 else if r ≤ 32 then 0 else 0xff))
    (hs : cb + 41 < R.length ∧ (R.getD (cb + 41) 0).toNat ≤ 100) :
    ∃ inp, tx.vin = [inp] ∧ inp.prevout.isNull = true ∧
      inp.scriptSig = slice R (cb + 42) (R.getD (cb + 41) 0).toNat ∧ cb + 42 + (R.getD (cb + 41) 0).toNat ≤ R.length := by
  obtain ⟨rh, hrh, ht, hnt, hvl, h1, hins, -⟩ := tx_rows hsat R hcs hmn hpad hfit hat hρm
  obtain ⟨hta, hsg⟩ := head_cols hsat R hcs hmn hpad hfit hnp hmk hat hρm hrh ht hnt
  have hrn : rh < n := by omega
  have hrm : rh < m := by omega
  rw [hta, hsg] at hcb
  have sb := (bool_val (seg_bool hsat hrn)).2
  -- the head's bytes: version, marker and flag, input count
  have tb := tok_bytes hsat R hcs hmk hrn (hnp rh hrm) (hfit rh hrm)
  rw [tok_txh hsat R hcs hmn hpad hfit hrn ht] at tb
  simp only [Spec.Block.Tok.bytes] at tb
  have hv4 : (slice R (M START rh).val 4).length = 4 := slice_length (by have := hfit rh hrm; have := hbytes 0 (by norm_num); omega)
  have hmk2 : (if decide (M SEG rh = 1) = true then [(0 : UInt8), 1] else []).length = 2 * (M SEG rh).val := by
    rcases seg_bool hsat hrn with s | s
    · rw [s]; simp
    · rw [s, ZMod.val_one]; simp
  have hlen := congrArg List.length tb
  rw [slice_length (hfit rh hrm)] at hlen
  simp only [List.length_append] at hlen
  rw [hv4, hmk2] at hlen
  -- the input count's first byte is `1`
  have hfirst := congrArg (fun l : Spec.Block.Bytes => l.getD (4 + 2 * (M SEG rh).val) 0) tb
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by rw [hv4]; omega), hv4,
    List.getD_append_right _ _ _ _ (by rw [hmk2]; omega), hmk2,
    show 4 + 2 * (M SEG rh).val - 4 - 2 * (M SEG rh).val = 0 by omega,
    slice_getD (by have := List.length_pos_of_ne_nil (serCompact_ne (M VAL rh).val); omega) (hfit rh hrm)] at hfirst
  have hb0 := hbytes 0 (by norm_num)
  simp only [if_true, Nat.add_zero] at hb0
  rw [show (M START rh).val + (4 + 2 * (M SEG rh).val) = cb + 4 by omega] at hfirst
  obtain ⟨x, rest, hxr⟩ : ∃ x rest, Spec.Block.serCompact (M VAL rh).val = x :: rest :=
    List.exists_cons_of_ne_nil (serCompact_ne _)
  rw [hxr] at hfirst hlen
  simp only [List.getD_cons_zero] at hfirst
  have hx1 : x.toNat = 1 := by rw [hfirst]; exact hb0.2
  obtain ⟨hn1, rfl⟩ := serCompact_head hxr (by omega)
  rw [hx1] at hn1
  simp only [List.length_cons, List.length_nil] at hlen
  -- the input row
  have hvin1 : tx.vin.length = 1 := by rw [hvl, hn1]
  obtain ⟨inp, hget, hrow⟩ := hins 0 (by omega)
  have hs1' : (M START (rh + 1)).val = cb + 5 := by
    rw [start_val_succ hsat R hcs hmk (show rh + 1 < n by omega)]; omega
  refine ⟨inp, ?_, ?_, ?_, ?_⟩
  · match h : tx.vin, hvin1 with
    | [a], _ => rw [h] at hget; simp at hget; rw [hget]
  · have hs1 : (M START (rh + 1)).val = cb + 5 := by
      rw [start_val_succ hsat R hcs hmk (show rh + 1 < n by omega)]; omega
    rw [Spec.Block.OutPoint.isNull, hrow.hash, hrow.n, Nat.add_zero] at *
    rw [hs1]
    have hall : (slice R (cb + 5) 32).all (· == 0) = true := by
      rw [List.all_eq_true]
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have hl : (slice R (cb + 5) 32).length = 32 := slice_length (by have := hbytes 32 (by norm_num); omega)
      have := slice_getD (R := R) (a := cb + 5) (b := 32) (i := i) (by omega) (by have := hbytes 32 (by norm_num); omega)
      rw [List.getD_eq_getElem _ _ (by omega)] at this
      rw [this]
      have hb := (hbytes (1 + i) (by omega)).2
      rw [if_neg (by omega), if_pos (by omega), show cb + 4 + (1 + i) = cb + 5 + i by omega] at hb
      simp only [beq_iff_eq]
      exact UInt8.toNat_inj.mp (by simpa using hb)
    have hff : Spec.Block.le (slice R (cb + 5 + 32) 4) = 0xffffffff := by
      have e : slice R (cb + 5 + 32) 4 = [0xff, 0xff, 0xff, 0xff] := by
        apply List.ext_getElem
        · rw [slice_length (by have := hbytes 36 (by norm_num); omega)]; rfl
        · intro i h1 h2
          have hl4 : i < 4 := by simpa using h2
          have := slice_getD (R := R) (a := cb + 5 + 32) (b := 4) (i := i) hl4 (by have := hbytes 36 (by norm_num); omega)
          rw [List.getD_eq_getElem _ _ h1] at this
          rw [this]
          have hb := (hbytes (33 + i) (by omega)).2
          rw [if_neg (by omega), if_neg (by omega), show cb + 4 + (33 + i) = cb + 5 + 32 + i by omega] at hb
          interval_cases i <;> exact UInt8.toNat_inj.mp (by simpa using hb)
      rw [e]; rfl
    simp [hall, hff]
  · -- the scriptSig: one length byte, then the script
    have hs1 : (M START (rh + 1)).val = cb + 5 := by
      rw [start_val_succ hsat R hcs hmk (show rh + 1 < n by omega)]; omega
    have hr1 : rh + 1 < n := by omega
    have hin := hrow.kind
    have hlp : M K_LOCK (rh + 1) + M K_PAD (rh + 1) = 0 := by
      rw [kind_unique hsat hr1 (a := K_IN) (b := K_LOCK) (by simp [K_IN]) (by simp [K_LOCK]) (by simp [K_IN, K_LOCK]) hin,
        kind_unique hsat hr1 (a := K_IN) (b := K_PAD) (by simp [K_IN]) (by simp [K_PAD]) (by simp [K_IN, K_PAD]) hin]
      ring
    have hoff := (kind_vals hsat hr1 (a := K_IN) (by simp [K_IN]) hin).1
    have hoff' : M OFF (rh + 1) = ((36 : ℕ) : F) := by rw [hoff]; simp [offN, K_IN, K_BLK, K_TXH]
    obtain ⟨hfit1, -, hser⟩ := hcs (rh + 1) hr1 hlp 36 hoff' (by norm_num)
    rw [hs1] at hser hfit1
    have hpre : 1 ≤ prefOf M (rh + 1) ∧ prefOf M (rh + 1) ≤ 5 := by unfold prefOf; split_ifs <;> omega
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, Spec.Block.serCompact (M VAL (rh + 1)).val = y :: rest :=
      List.exists_cons_of_ne_nil (serCompact_ne _)
    have hy : y = R.getD (cb + 41) 0 := by
      have := congrArg (fun l : Spec.Block.Bytes => l.getD 0 0) hser
      simp only [hyr, List.getD_cons_zero] at this
      rw [this, slice_getD (by omega) (by omega)]
    obtain ⟨hv, rfl⟩ := serCompact_head hyr (by rw [hy]; omega)
    have hp1 : prefOf M (rh + 1) = 1 := by
      have := congrArg List.length hser
      rw [hyr, slice_length (by omega)] at this; simpa using this.symm
    rw [hrow.script, hs1, hp1, hv, hy]
  · -- the scriptSig lies in the block
    have hr1 : rh + 1 < m := by omega
    obtain ⟨-, hlen1, -, -, hf1⟩ := row_info hsat R hcs hmn hpad hfit hr1 (a := K_IN) (by simp [K_IN]) hrow.kind
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, if_true] at hlen1
    simp at hlen1
    have hoff' : M OFF (rh + 1) = ((36 : ℕ) : F) := by
      rw [(kind_vals hsat (show rh + 1 < n by omega) (a := K_IN) (by simp [K_IN]) hrow.kind).1]
      simp [offN, K_IN, K_BLK, K_TXH]
    have hlp : M K_LOCK (rh + 1) + M K_PAD (rh + 1) = 0 := by
      rw [kind_unique hsat (show rh + 1 < n by omega) (a := K_IN) (b := K_LOCK) (by simp [K_IN]) (by simp [K_LOCK])
        (by simp [K_IN, K_LOCK]) hrow.kind, kind_unique hsat (show rh + 1 < n by omega) (a := K_IN) (b := K_PAD)
        (by simp [K_IN]) (by simp [K_PAD]) (by simp [K_IN, K_PAD]) hrow.kind]
      ring
    obtain ⟨hfit1, -, hser⟩ := hcs (rh + 1) (by omega) hlp 36 hoff' (by norm_num)
    rw [hs1'] at hser hfit1
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, Spec.Block.serCompact (M VAL (rh + 1)).val = y :: rest :=
      List.exists_cons_of_ne_nil (serCompact_ne _)
    have hy : y = R.getD (cb + 41) 0 := by
      have := congrArg (fun l : Spec.Block.Bytes => l.getD 0 0) hser
      have hpre : 1 ≤ prefOf M (rh + 1) := by unfold prefOf; split_ifs <;> omega
      simp only [hyr, List.getD_cons_zero] at this
      rw [this, slice_getD (by omega) (by omega)]
    obtain ⟨hv, rfl⟩ := serCompact_head hyr (by rw [hy]; omega)
    have hp1 : prefOf M (rh + 1) = 1 := by
      have := congrArg List.length hser
      rw [hyr, slice_length (by omega)] at this; simpa using this.symm
    rw [hs1'] at hf1
    rw [hlen1, hp1, hv] at hf1
    rw [← hy]; omega

end Coinbase

end StarkedAir.Block.Fields

namespace StarkedAir.Block.Fields

open StarkedAir

section Basec

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- **The byte slots' base is small** on output, lock-time and input rows. -/
theorem basec_lt (hR : R.length ≤ 2 ^ 25) {r : ℕ} (hr : r < n)
    (hk : M K_OUT r = 1 ∨ M K_LOCK r = 1 ∨ M K_IN r = 1) : (M BASEC r).val < 2 ^ 26 := by
  have e := chk_defn hsat (a := BASEC) (e := .add (k START) (.mul (k K_IN) (.sub (k LEN) (c 4)))) (by simp [chkC, valueC]) hr
  simp only [Expr.eval, ev_k hr, c, StarkedAir.Sha256.eval_cst] at e
  have hst := start_lt hsat hr
  have hnp : M K_PAD r = 0 := by
    rcases hk with g | g | g
    · exact kind_unique hsat hr (a := K_OUT) (b := K_PAD) (by simp [K_OUT]) (by simp [K_PAD]) (by simp [K_OUT, K_PAD]) g
    · exact kind_unique hsat hr (a := K_LOCK) (b := K_PAD) (by simp [K_LOCK]) (by simp [K_PAD]) (by simp [K_LOCK, K_PAD]) g
    · exact kind_unique hsat hr (a := K_IN) (b := K_PAD) (by simp [K_IN]) (by simp [K_PAD]) (by simp [K_IN, K_PAD]) g
  have hrm := lt_m hsat R hcs hmn hpad hfit hr hnp
  rcases kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr with h0 | h1
  · rw [e, h0, zero_mul, add_zero]; omega
  · obtain ⟨-, hlen, -, hp5, hf⟩ := row_info hsat R hcs hmn hpad hfit hrm (a := K_IN) (by simp [K_IN]) h1
      (by simp [K_IN, K_LOCK]) (by simp [K_IN, K_PAD])
    simp only [lenN, K_BLK, K_TXH, K_IN, if_true] at hlen
    simp at hlen
    rw [e, h1, one_mul]
    have : M START r + (M LEN r - ((4 : ℕ) : F)) = (((M START r).val + (M LEN r).val - 4 : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    rw [this, ZMod.val_natCast_of_lt (lt_P (by omega))]; omega

end Basec

end StarkedAir.Block.Fields
