/-
**A transaction's fields by row (M3a.5).** For the transaction `tx` ending at lock-time row `ρ` with head
row `rh`: input `i` is row `rh + 1 + i`, the output count is row `rh + 1 + nIn`, output `o` is row
`rh + 2 + nIn + o`, and each of these rows' slices of the block are the parsed fields. The M3a.5 checks
read those rows' bytes.
-/
import StarkedAir.Block.TxRanges
import StarkedAir.Spec.TxFields

namespace StarkedAir.Block.Fields

open StarkedAir

/-! ### Kinds from tokens -/

theorem tokOf_inp {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} {a b c d : Spec.Block.Bytes}
    (h : tokOf M R r = .inp a b c d) : M K_IN r = 1 ∧ a = slice R (M START r).val 32 ∧
      b = slice R ((M START r).val + 32) 4 ∧ c = slice R ((M START r).val + 36 + prefOf M r) (M VAL r).val ∧
      d = slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 <;> simp at h
  exact ⟨h3, h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem tokOf_nout {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r k : ℕ} (h : tokOf M R r = .nout k) :
    M K_NOUT r = 1 ∧ k = (M VAL r).val := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 <;> simp at h
  exact ⟨h4, h.symm⟩

theorem tokOf_out {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} {a b : Spec.Block.Bytes}
    (h : tokOf M R r = .out a b) : M K_OUT r = 1 ∧ a = slice R (M START r).val 8 ∧
      b = slice R ((M START r).val + 8 + prefOf M r) (M VAL r).val := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp at h
  exact ⟨h5, h.1.symm, h.2.symm⟩

theorem tokOf_lock {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} {l : Spec.Block.Bytes}
    (h : tokOf M R r = .lock l) : l = slice R (M START r).val 4 := by
  unfold tokOf at h
  split_ifs at h <;> simp at h
  exact h.symm

/-- The fields of one input row, as the parse reads them. -/
structure InRow (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) (i : Spec.Block.TxIn) : Prop where
  kind : M K_IN r = 1
  hash : i.prevout.hash = slice R (M START r).val 32
  n : i.prevout.n = Spec.Block.le (slice R ((M START r).val + 32) 4)
  script : i.scriptSig = slice R ((M START r).val + 36 + prefOf M r) (M VAL r).val
  seq : i.sequence = Spec.Block.le (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4)

/-- The fields of one output row. -/
structure OutRow (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) (o : Spec.Block.TxOut) : Prop where
  kind : M K_OUT r = 1
  value : o.value = Spec.Block.signed64 (Spec.Block.le (slice R (M START r).val 8))
  script : o.scriptPubKey = slice R ((M START r).val + 8 + prefOf M r) (M VAL r).val

section Layout

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- **A transaction's rows.** The transaction ending at lock-time row `ρ` has its head at `rh`, its inputs
at `rh + 1 + i`, its output count at `rh + 1 + nIn` and its outputs at `rh + 2 + nIn + o`, each carrying the
parsed fields; the rows up to `ρ` after the outputs are witness rows; its lock time is row `ρ`'s. -/
theorem tx_rows {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) :
    ∃ rh, rh < ρ ∧ M K_TXH rh = 1 ∧ (∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) ∧
      tx.vin.length = (M VAL rh).val ∧ 1 ≤ tx.vin.length ∧
      (∀ i < tx.vin.length, ∃ inp, tx.vin[i]? = some inp ∧ InRow M R (rh + 1 + i) inp) ∧
      M K_NOUT (rh + 1 + tx.vin.length) = 1 ∧ (M VAL (rh + 1 + tx.vin.length)).val = tx.vout.length ∧
      (∀ o < tx.vout.length, ∃ out, tx.vout[o]? = some out ∧ OutRow M R (rh + 2 + tx.vin.length + o) out) ∧
      (∀ j, rh + 2 + tx.vin.length + tx.vout.length ≤ j → j < ρ → M K_WCNT j = 1 ∨ M K_WITEM j = 1) ∧
      tx.lockTime = Spec.Block.le (slice R (M START ρ).val 4) ∧
      (M SEG rh = 1 ↔ tx.hasWitness = true) ∧ rh + 2 + tx.vin.length + tx.vout.length ≤ ρ := by
  obtain ⟨rh, hrh, ht, hnt, htx⟩ := hat
  have hrm : rh < m := by omega
  rw [toksFrom_cons hrm, tok_txh hsat R hcs hmn hpad hfit (by omega) ht] at htx
  obtain ⟨pin, k, pout, pw, l, hsplit, hpl, hpo, hvl, hol, h1, hlt, hl4, hwit, hins, houts, hnseg, hseg⟩ :=
    Spec.Block.txT_vals htx
  have hlen := congrArg List.length hsplit
  simp only [toksFrom_length, List.length_append, List.length_cons] at hlen
  have hρ : ρ = rh + 1 + pin.length + 1 + pout.length + pw.length := by omega
  have tk : ∀ i, i < m - (rh + 1) → (toksFrom M R m (rh + 1))[i]? = some (tokOf M R (rh + 1 + i)) :=
    fun i hi => toksFrom_get hi
  have ev : tx.vin.length = pin.length := by rw [hvl, hpl]
  have eo : tx.vout.length = pout.length := by rw [hol, hpo]
  refine ⟨rh, hrh, ht, hnt, hvl, by omega, fun i hi => ?_, ?_, ?_, fun o ho => ?_, fun j hj1 hj2 => ?_, ?_, ?_,
    by rw [ev, eo]; omega⟩
  · -- input `i`
    obtain ⟨hh, nn, s, q, e1, ⟨w, e2⟩, -, -, -⟩ := hins i (by omega)
    have g : (toksFrom M R m (rh + 1))[i]? = _ := congrArg (fun L => L[i]?) hsplit
    rw [tk i (by omega), List.getElem?_append_left (by omega), e1] at g
    obtain ⟨hk, a1, a2, a3, a4⟩ := tokOf_inp (Option.some.inj g)
    exact ⟨_, e2, ⟨hk, a1, by rw [a2], a3, by rw [a4]⟩⟩
  · have g := get_app hsplit 0
    rw [tk _ (by omega)] at g
    simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at g
    rw [ev]; exact (tokOf_nout g).1
  · have g := get_app hsplit 0
    rw [tk _ (by omega)] at g
    simp only [List.getElem?_cons_zero, Option.some.injEq, Nat.add_zero] at g
    rw [ev, ← (tokOf_nout g).2, hol]
  · -- output `o`
    obtain ⟨val, s, e1, e2, -⟩ := houts o (by omega)
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (ρ + 1))) =
        (pin ++ [.nout k]) ++ (pout ++ (pw ++ .lock l :: toksFrom M R m (ρ + 1))) := by simp
    have g := get_app (hsplit.trans e) o
    rw [tk _ (by simp; omega), List.getElem?_append_left (by omega), e1] at g
    simp only [List.length_append, List.length_singleton] at g
    rw [show rh + 1 + (pin.length + 1 + o) = rh + 2 + tx.vin.length + o by rw [ev]; omega] at g
    obtain ⟨hk, a1, a2⟩ := tokOf_out (Option.some.inj g)
    exact ⟨_, e2, ⟨hk, by rw [a1], a2⟩⟩
  · -- witness rows
    rw [ev, eo] at hj1
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (ρ + 1))) =
        (pin ++ .nout k :: pout) ++ (pw ++ .lock l :: toksFrom M R m (ρ + 1)) := by simp
    have g := get_app (hsplit.trans e) (j - (rh + 2 + pin.length + pout.length))
    simp only [List.length_append, List.length_cons] at g
    rw [tk _ (by omega), List.getElem?_append_left (by omega)] at g
    rw [show rh + 1 + (pin.length + (pout.length + 1) + (j - (rh + 2 + pin.length + pout.length))) = j by omega] at g
    have hm : tokOf M R j ∈ pw := List.mem_of_getElem? g.symm
    exact tokk_wit (hwit _ hm)
  · have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (ρ + 1))) =
        (pin ++ .nout k :: pout ++ pw) ++ (.lock l :: toksFrom M R m (ρ + 1)) := by simp
    have g := get_app (hsplit.trans e) 0
    rw [tk _ (by simp; omega)] at g
    simp only [List.length_append, List.length_cons, List.getElem?_cons_zero, Option.some.injEq] at g
    rw [show rh + 1 + (pin.length + (pout.length + 1) + pw.length + 0) = ρ by omega] at g
    rw [hlt, tokOf_lock g]
  · constructor
    · intro hs; exact (hseg (by simp [hs])).1
    · intro hw
      by_contra hs
      have hs' : decide (M SEG rh = 1) = false := by simp [hs]
      rw [(hnseg hs').2] at hw; exact absurd hw (by simp)

end Layout

end StarkedAir.Block.Fields
