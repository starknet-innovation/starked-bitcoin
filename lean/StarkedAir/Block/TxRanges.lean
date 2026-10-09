/-
**Transaction byte ranges (M3a.3).** On a transaction's lock-time row the fields hold its byte ranges:
`TXA` (start), `WST` (witness section start), `START` (lock time). The wtxid message `[TXA, START + 4)`
serializes to `serWit`, and the txid message (split around marker/flag and witnesses for segwit) to
`serNoWit`.
-/
import StarkedAir.Block.FieldsSound
import StarkedAir.Spec.TxSplit

namespace StarkedAir.Block.Fields

open StarkedAir

/-! ### Token kinds give row kinds -/

theorem tokk_wit {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} (h : (tokOf M R r).isWit = true) :
    M K_WCNT r = 1 ∨ M K_WITEM r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> simp [Spec.Block.Tok.isWit] at h
  · exact Or.inl h6
  · exact Or.inr h7

theorem tokk_out {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} (h : (tokOf M R r).isOut = true) :
    M K_OUT r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp [Spec.Block.Tok.isOut] at h
  exact h5

theorem tokk_nout {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r k : ℕ} (h : tokOf M R r = .nout k) :
    M K_NOUT r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 <;> simp at h
  exact h4

theorem tokk_lock {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} {l : Spec.Block.Bytes} (h : tokOf M R r = .lock l) :
    M K_BLK r ≠ 1 ∧ M K_TXH r ≠ 1 ∧ M K_IN r ≠ 1 ∧ M K_NOUT r ≠ 1 ∧ M K_OUT r ≠ 1 ∧ M K_WCNT r ≠ 1 ∧
      M K_WITEM r ≠ 1 ∧ l = slice R (M START r).val 4 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> simp at h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h.symm⟩

/-! ### Tokens by row -/

theorem toksFrom_length {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r : ℕ} : (toksFrom M R m r).length = m - r := by
  simp [toksFrom]

theorem toksFrom_get {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r i : ℕ} (hi : i < m - r) :
    (toksFrom M R m r)[i]? = some (tokOf M R (r + i)) := by
  simp [toksFrom, hi]

theorem toksFrom_take {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r j : ℕ} (h : r + j ≤ m) :
    (toksFrom M R m r).take j = toksFrom M R (r + j) r := by
  unfold toksFrom
  rw [← List.map_take, List.take_range, show min j (m - r) = r + j - r by omega]

theorem get_app {α : Type} {A B : List α} {L : List α} (h : L = A ++ B) (j : ℕ) : L[A.length + j]? = B[j]? := by
  rw [h, List.getElem?_append_right (by omega)]; simp

section Layout

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- **A transaction's rows.** From its header row `rh`: input/output rows up to `rw`, witness rows
`rw … r' − 1` (none without the segwit flag), the lock-time row `r'`. `serNoWit` is the header's
version and input count, the rows `rh + 1 … rw − 1`, and the lock time. -/
theorem tx_layout {rh : ℕ} (hr : rh < m) (ht : M K_TXH rh = 1) :
    ∃ tx r' rw v nIn l, Spec.Block.txT (toksFrom M R m rh) = some (tx, toksFrom M R m (r' + 1)) ∧
      rh + 1 < rw ∧ rw ≤ r' ∧ r' < m ∧ M K_LOCK r' = 1 ∧
      tokOf M R rh = .txh v (decide (M SEG rh = 1)) nIn ∧ tokOf M R r' = .lock l ∧
      (∀ j, rw ≤ j → j < r' → M K_WCNT j = 1 ∨ M K_WITEM j = 1) ∧
      (M K_NOUT (rw - 1) = 1 ∨ M K_OUT (rw - 1) = 1) ∧
      (M SEG rh ≠ 1 → rw = r') ∧
      Spec.Block.serNoWit tx = v ++ Spec.Block.serCompact nIn ++ Spec.Block.toksBytes (toksFrom M R rw (rh + 1)) ++ l := by
  obtain ⟨tx, r', htx, hrr', hr'm, hl, -⟩ := tx_sim hsat R hcs hmn hpad hfit hr ht
  have hrn : rh < n := by omega
  have hblk : M K_BLK rh ≠ 1 := by
    rw [kind_unique hsat hrn (a := K_TXH) (b := K_BLK) (by simp [K_TXH]) (by simp [K_BLK]) (by simp [K_TXH, K_BLK]) ht]
    exact zero_ne_one
  have htok : tokOf M R rh = .txh (slice R (M START rh).val 4) (decide (M SEG rh = 1)) (M VAL rh).val := by
    simp [tokOf, hblk, ht]
  rw [toksFrom_cons hr, htok] at htx
  obtain ⟨pin, k, pout, pw, l, hsplit, hout, hwit, hnil, -, -, hnw⟩ := Spec.Block.txT_split htx
  have hlen := congrArg List.length hsplit
  simp only [toksFrom_length, List.length_append, List.length_cons] at hlen
  set rw := rh + 2 + pin.length + pout.length with hrw
  have hr' : r' = rw + pw.length := by omega
  have tk : ∀ i, i < m - (rh + 1) → (toksFrom M R m (rh + 1))[i]? = some (tokOf M R (rh + 1 + i)) :=
    fun i hi => toksFrom_get hi
  -- the output-count row
  have hnout : tokOf M R (rh + 1 + pin.length) = .nout k := by
    have := get_app hsplit 0
    rw [tk _ (by omega)] at this; simpa using this
  -- the lock-time row
  have hlock : tokOf M R r' = .lock l := by
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
        (pin ++ .nout k :: pout ++ pw) ++ (.lock l :: toksFrom M R m (r' + 1)) := by simp
    have := get_app (hsplit.trans e) 0
    rw [tk _ (by simp; omega)] at this
    simp only [List.length_append, List.length_cons] at this
    rw [show rh + 1 + (pin.length + (pout.length + 1) + pw.length + 0) = r' by omega] at this
    simpa using this
  refine ⟨tx, r', rw, _, _, l, ?_, by omega, by omega, hr'm, hl, htok, hlock, fun j h1 h2 => ?_, ?_, fun hs => ?_, ?_⟩
  · rw [toksFrom_cons hr, htok]; exact htx
  · -- witness rows
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
        (pin ++ .nout k :: pout) ++ (pw ++ .lock l :: toksFrom M R m (r' + 1)) := by simp
    have := get_app (hsplit.trans e) (j - rw)
    rw [tk _ (by simp; omega)] at this
    simp only [List.length_append, List.length_cons] at this
    rw [List.getElem?_append_left (by omega)] at this
    rw [show rh + 1 + (pin.length + (pout.length + 1) + (j - rw)) = j by omega] at this
    have hm : tokOf M R j ∈ pw := List.mem_of_getElem? this.symm
    exact tokk_wit (hwit _ hm)
  · -- the row before the witnesses: the output count or the last output
    rcases List.eq_nil_or_concat pout with h0 | ⟨pl, last, hpl⟩
    · left
      rw [h0] at hrw
      rw [show rw - 1 = rh + 1 + pin.length by simp at hrw; omega]
      exact tokk_nout hnout
    · right
      have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
          (pin ++ .nout k :: pl) ++ (last :: (pw ++ .lock l :: toksFrom M R m (r' + 1))) := by rw [hpl]; simp
      have := get_app (hsplit.trans e) 0
      rw [tk _ (by simp; rw [hpl] at hrw; simp at hrw; omega)] at this
      simp only [List.length_append, List.length_cons] at this
      rw [show rh + 1 + (pin.length + (pl.length + 1) + 0) = rw - 1 by rw [hpl] at hrw; simp at hrw; omega] at this
      simp at this
      exact tokk_out (by rw [this]; exact hout last (by rw [hpl]; simp))
  · have : pw = [] := hnil (by simpa using hs)
    rw [hr', this]; simp
  · rw [hnw]
    have e : (toksFrom M R m (rh + 1)).take (pin.length + 1 + pout.length) = pin ++ .nout k :: pout := by
      rw [hsplit, List.take_append, List.take_of_length_le (by omega),
        show pin.length + 1 + pout.length - pin.length = pout.length + 1 by omega, List.take_succ_cons,
        List.take_left' rfl]
    rw [toksFrom_take (by omega), show rh + 1 + (pin.length + 1 + pout.length) = rw by omega] at e
    rw [e]
    simp [Spec.Block.toksBytes, Spec.Block.Tok.bytes, List.append_assoc]

end Layout

end StarkedAir.Block.Fields
