/-
**Transaction indices (M3a.3).** In the fields component, `TXI` counts the lock-time rows above:
`TXI r = #{r' < r | K_LOCK r'}`. Hence each index has at most one lock-time row, and the transaction
tuples yielded on lock-time rows are a function of the index.
-/
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst)

theorem mem_txC {c : Expr} (h : c ∈ txC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

section TxIndex

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

/-- Lock-time rows strictly above row `r`. -/
def locks (M : ℕ → ℕ → F) (r : ℕ) : ℕ := ((List.range r).filter fun r' => M K_LOCK r' = 1).length

theorem txi_count : ∀ r < n, M TXI r = ((locks M r : ℕ) : F) := by
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_txC (c := .mul (k K_BLK) (k TXI)) (by simp [txC])) hr
    simp only [Expr.eval, ev_k hr, first_blk hsat hr, one_mul] at this
    simp [locks, this]
  | succ r ih =>
    have := sat hsat (mem_txC (c := .mul notFirst (.sub (k TXI) (.add (kp TXI) (kp K_LOCK)))) (by simp [txC])) hr
    simp only [Expr.eval, ev_notFirst hr, ev_k hr, ev_kp hr, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega)]
    simp only [locks, List.range_succ, List.filter_append, List.length_append]
    rcases kind_bool hsat (c := K_LOCK) (by simp [kinds]) (by omega : r < n) with h | h
    · simp [h]
    · simp [h]

omit hsat in
theorem locks_le (r : ℕ) : locks M r ≤ r := by
  unfold locks; exact (List.length_filter_le _ _).trans (by simp)

omit hsat in
theorem locks_succ (r : ℕ) : locks M (r + 1) = locks M r + (if M K_LOCK r = 1 then 1 else 0) := by
  unfold locks; rw [List.range_succ, List.filter_append, List.length_append]; split_ifs with h <;> simp [h]

omit hsat in
theorem locks_le_add (r k : ℕ) : locks M r ≤ locks M (r + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, locks_succ]; omega

omit hsat in
theorem locks_mono {r r' : ℕ} (h : r < r') (hl : M K_LOCK r = 1) : locks M r + 1 ≤ locks M r' := by
  have := locks_le_add (M := M) (r + 1) (r' - r - 1)
  rw [locks_succ, if_pos hl, show r + 1 + (r' - r - 1) = r' by omega] at this
  exact this

/-- **One lock-time row per index** (rows below `P`). -/
theorem lock_unique (hP : n < P) {r r' : ℕ} (hr : r < n) (hr' : r' < n) (hl : M K_LOCK r = 1)
    (hl' : M K_LOCK r' = 1) (he : M TXI r = M TXI r') : r = r' := by
  rw [txi_count hsat r hr, txi_count hsat r' hr'] at he
  have := natCast_inj_of_lt (lt_of_le_of_lt (locks_le r) (by omega)) (lt_of_le_of_lt (locks_le r') (by omega)) he
  rcases lt_trichotomy r r' with h | h | h
  · have := locks_mono (M := M) h hl; omega
  · exact h
  · have := locks_mono (M := M) h hl'; omega

/-- The index is small: `TXI r = locks r ≤ r` as a natural number. -/
theorem txi_val (hP : n < P) {r : ℕ} (hr : r < n) : (M TXI r).val = locks M r ∧ locks M r ≤ r :=
  ⟨val_lt_of_eq_cast (txi_count hsat r hr) (lt_of_le_of_lt (locks_le r) (by omega)), locks_le r⟩

end TxIndex

end StarkedAir.Block.Fields
