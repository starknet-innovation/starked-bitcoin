/-
The median-time-past rule in counting form (decision D-018): with `k ≤ 11` previous
timestamps, `time > median` iff at least `k/2 + 1` of them are strictly below `time`.
The header-chain AIR enforces the counting form.
-/
import StarkedAir.Spec.Bitcoin

namespace StarkedAir.Spec.Bitcoin

theorem sorted_lt_iff {t : ℕ} : ∀ {s : List ℕ}, s.Pairwise (· ≤ ·) →
    ∀ i < s.length, (s.getD i 0 < t ↔ i < (s.filter (· < t)).length)
  | [], _, i, hi => by simp at hi
  | a :: s, h, i, hi => by
    rw [List.pairwise_cons] at h
    by_cases ha : a < t
    · rw [List.filter_cons_of_pos (by simpa using ha), List.length_cons]
      rcases i with _ | i
      · simpa using ha
      · simp only [List.getD_cons_succ, List.length_cons] at hi ⊢
        rw [sorted_lt_iff h.2 i (by omega)]; omega
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      have h0 : (s.filter (· < t)).length = 0 := by
        rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro x hx; have := h.1 x hx; simp; omega
      rw [h0]
      rcases i with _ | i
      · simpa using ha
      · simp only [List.getD_cons_succ, List.length_cons] at hi ⊢
        have hx : a ≤ s.getD i 0 := by
          rw [List.getD_eq_getElem _ _ (by omega)]; exact h.1 _ (List.getElem_mem _)
        constructor
        · intro h'; omega
        · intro h'; omega

/-- Counting form of the MTP rule: with `k = min 11 (length prev)` timestamps, the header is
valid iff `prev` is empty or at least `k/2 + 1` of them are strictly below `time`. -/
theorem mtpOk_iff_count (time : ℕ) (prev : List ℕ) :
    mtpOk time prev = true ↔
      prev = [] ∨ (prev.take 11).length / 2 + 1 ≤ ((prev.take 11).filter (· < time)).length := by
  unfold mtpOk medianTimePast
  set l := prev.take 11
  set s := l.mergeSort (fun a b => decide (a ≤ b))
  have hperm : s.Perm l := List.mergeSort_perm l _
  have hsort : s.Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
    simpa using this
  have hlen : s.length = l.length := hperm.length_eq
  have hcnt : (s.filter (· < time)).length = (l.filter (· < time)).length :=
    (hperm.filter _).length_eq
  by_cases he : prev = []
  · simp [he]
  · have hl : 0 < l.length := by
      simp only [l, List.length_take]; have := List.length_pos_iff.mpr he; omega
    have key := sorted_lt_iff (t := time) hsort (l.length / 2) (by omega)
    rw [hcnt] at key
    rw [show prev.isEmpty = false by cases prev <;> simp_all, Bool.false_or, decide_eq_true_eq]
    simp only [he, false_or]
    exact key

end StarkedAir.Spec.Bitcoin
