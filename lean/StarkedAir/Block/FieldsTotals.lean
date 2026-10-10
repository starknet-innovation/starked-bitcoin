/-
**Block totals (M3a.5c).** In a satisfied fields trace, the witness-byte total `WB` at the last row is the
tokens' witness bytes (`sumW`), and the segwit count `NS` is the number of segwit heads; when it is zero,
no head is segwit.
-/
import StarkedAir.Block.TxChecks
import StarkedAir.Spec.TokSums

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)

theorem list_sum_range (f : ℕ → ℕ) : ∀ k, ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i
  | 0 => by simp
  | k + 1 => by rw [List.range_succ, List.map_append, List.sum_append, Finset.sum_range_succ, list_sum_range f k]; simp

theorem sumW_toksFrom (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (m : ℕ) :
    Spec.Block.sumW (toksFrom M R m 0) = ∑ i ∈ Finset.range m, Spec.Block.tokW (tokOf M R i) := by
  rw [Spec.Block.sumW, toksFrom, List.map_map, Nat.sub_zero, list_sum_range]; simp [Function.comp]

section Totals

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem dw_eq {r : ℕ} (hr : r < n) :
    M DW r = 2 * (M K_TXH r * M SEG r) + (M K_WCNT r + M K_WITEM r) * M LEN r := by
  rw [chk_defn hsat (a := DW) (e := .add (.mul (c 2) (.mul (k K_TXH) (k SEG))) (.mul (.add (k K_WCNT) (k K_WITEM)) (k LEN)))
    (by simp [chkC, totalsC]) hr]
  simp [Expr.eval, ev_k hr, c, eval_cst]

/-- `WB` is the running sum of `DW`. -/
theorem wb_sum (hn : 0 < n) : ∀ r < n, M WB r = ∑ j ∈ Finset.range (r + 1), M DW j := by
  have hdw0 : M DW 0 = 0 := by
    rw [dw_eq hsat hn]
    have ka := kinds_at hsat hn (a := K_BLK) (by simp [K_BLK]) (first_blk hsat hn)
    rw [ka K_TXH (by simp [K_TXH]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM])]
    simp [K_BLK, K_TXH, K_WCNT, K_WITEM]
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_chk (c := .mul first (k WB)) (by simp [chkC, totalsC])) hr
    simp only [Expr.eval, ev_first hr, if_true, one_mul, ev_k hr] at this
    rw [this]; simp [hdw0]
  | succ r ih =>
    have := sat hsat (mem_chk (c := .mul notFirst (.sub (.sub (k WB) (kp WB)) (k DW))) (by simp [chkC, totalsC])) hr
    simp only [Expr.eval, ev_notFirst (pub := pub) (M := M) hr, one_mul, ev_k hr, ev_kp hr, sub_eq_zero] at this
    rw [Finset.sum_range_succ, ← ih (by omega)]; linear_combination this

/-- `NS` is the running sum of `K_TXH · SEG`. -/
theorem ns_sum (hn : 0 < n) : ∀ r < n, M NS r = ∑ j ∈ Finset.range (r + 1), M K_TXH j * M SEG j := by
  have h0 : M K_TXH 0 = 0 := by
    rw [kinds_at hsat hn (a := K_BLK) (by simp [K_BLK]) (first_blk hsat hn) K_TXH (by simp [K_TXH])]
    simp [K_BLK, K_TXH]
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_chk (c := .mul first (k NS)) (by simp [chkC, totalsC])) hr
    simp only [Expr.eval, ev_first hr, if_true, one_mul, ev_k hr] at this
    rw [this]; simp [h0]
  | succ r ih =>
    have := sat hsat (mem_chk (c := .mul notFirst (.sub (.sub (k NS) (kp NS)) (.mul (k K_TXH) (k SEG))))
      (by simp [chkC, totalsC])) hr
    simp only [Expr.eval, ev_notFirst (pub := pub) (M := M) hr, one_mul, ev_k hr, ev_kp hr, sub_eq_zero] at this
    rw [Finset.sum_range_succ, ← ih (by omega)]; linear_combination this

/-- **No segwit head when `NS` is zero at the last row.** -/
theorem ns_zero (hn : 0 < n) (hnP : n ≤ 2 ^ 25) (h : M NS (n - 1) = 0) :
    ∀ r < n, M K_TXH r = 1 → M SEG r = 0 := by
  have hb : ∀ j < n, M K_TXH j * M SEG j = (((M K_TXH j * M SEG j).val : ℕ) : F) ∧
      (M K_TXH j * M SEG j).val ≤ 1 := fun j hj =>
    bool_val (by
      rcases kind_bool hsat (c := K_TXH) (by simp [kinds, K_TXH]) hj with a | a <;>
        rcases seg_bool hsat hj with b | b <;> rw [a, b] <;> simp)
  rw [ns_sum hsat hn (n - 1) (by omega), show n - 1 + 1 = n by omega,
    Finset.sum_congr rfl (fun j hj => (hb j (Finset.mem_range.mp hj)).1), ← Nat.cast_sum] at h
  have hle : ∑ j ∈ Finset.range n, (M K_TXH j * M SEG j).val ≤ n := by
    calc _ ≤ ∑ j ∈ Finset.range n, 1 := Finset.sum_le_sum (fun j hj => (hb j (Finset.mem_range.mp hj)).2)
      _ = n := by simp
  have h0 := natCast_inj_of_lt (a := ∑ j ∈ Finset.range n, (M K_TXH j * M SEG j).val) (b := 0) (lt_P (by omega))
    (lt_P (by norm_num)) (by simpa using h)
  intro r hr ht
  have := Finset.sum_eq_zero_iff.mp h0 r (Finset.mem_range.mpr hr)
  have e := (hb r hr).1
  rw [this, ht, one_mul] at e; simpa using e

end Totals

section TotalsTok

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

/-- **A row's witness bytes** are its token's. -/
theorem dw_tok {r : ℕ} (hr : r < m) : M DW r = ((Spec.Block.tokW (tokOf M R r) : ℕ) : F) := by
  have hrn : r < n := by omega
  obtain ⟨a, ha, h1⟩ := kind_exists hsat hrn
  have ka := kinds_at hsat hrn ha h1
  rw [dw_eq hsat hrn, ka K_TXH (by simp [K_TXH]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM])]
  have tb := tok_bytes hsat R hcs hmk hrn (hnp r hr) (hfit r hr)
  have hlen : ((Spec.Block.Tok.bytes (tokOf M R r)).length : F) = M LEN r := by
    rw [tb, slice_length (hfit r hr), ZMod.natCast_zmod_val]
  have z := fun c (hc : c < 9) (hne : c ≠ a) => kz_of hsat R hcs hmn hpad hfit hrn ha h1 hc hne
  interval_cases a
  · rw [tok_blk hsat R hcs hmn hpad hfit hrn h1]; simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, K_BLK]
  · rw [tok_txh hsat R hcs hmn hpad hfit hrn h1] at hlen ⊢
    rcases seg_bool hsat hrn with s | s <;> simp [Spec.Block.tokW, s, K_TXH, K_WCNT, K_WITEM]
  · rw [tok_in hsat R hcs hmn hpad hfit hrn h1]; simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, K_IN]
  · rw [tok_nout hsat R hcs hmn hpad hfit hrn h1]; simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, K_NOUT]
  · rw [tok_out hsat R hcs hmn hpad hfit hrn h1]; simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, K_OUT]
  · rw [tok_wcnt hsat R hcs hmn hpad hfit hrn h1] at hlen ⊢
    simp only [Spec.Block.Tok.bytes] at hlen
    simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, ← hlen]
  · rw [tok_witem hsat R hcs hmn hpad hfit hrn h1] at hlen ⊢
    simp only [Spec.Block.Tok.bytes] at hlen
    simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, ← hlen]
  · rw [tok_lock hsat R hcs hmn hpad hfit hrn h1]; simp [Spec.Block.tokW, K_TXH, K_WCNT, K_WITEM, K_LOCK]
  · have := hnp r hr; simp only [K_PAD] at this; rw [this] at h1; exact absurd h1 zero_ne_one

/-- **The witness-byte total** at the last row is the tokens' `sumW`. -/
theorem wb_last : M WB (n - 1) = ((Spec.Block.sumW (toksFrom M R m 0) : ℕ) : F) := by
  have hn : 0 < n := by omega
  rw [wb_sum hsat hn (n - 1) (by omega), show n - 1 + 1 = n by omega, sumW_toksFrom, Nat.cast_sum]
  rw [← Finset.sum_range_add_sum_Ico _ (show m ≤ n by omega)]
  have hz : ∑ j ∈ Finset.Ico m n, M DW j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hj
    have hp := hpad j h2 h1
    have ka := kinds_at hsat h2 (a := K_PAD) (by simp [K_PAD]) hp
    rw [dw_eq hsat h2, ka K_TXH (by simp [K_TXH]), ka K_WCNT (by simp [K_WCNT]), ka K_WITEM (by simp [K_WITEM])]
    simp [K_PAD, K_TXH, K_WCNT, K_WITEM]
  rw [hz, add_zero]
  exact Finset.sum_congr rfl (fun j hj => dw_tok hsat R hcs hmn hpad hfit hnp hmk (Finset.mem_range.mp hj))

end TotalsTok

end StarkedAir.Block.Fields
