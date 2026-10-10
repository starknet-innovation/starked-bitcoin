/-
**LogUp, the deterministic part (roadmap IR-LOGUP).** Stwo's LogUp encoding, as stwo-zig's
`logup_columns.build` and the in-circuit `finalizeLogupInPairs` implement it, over any field `K`
(for us QM31):

* each row has terms `nⱼ/dⱼ` (numerator: multiplicity; denominator: `combine(α, entry) − z`, as stwo and our circuit compute it; the sign does not affect the argument),
  grouped in batches of at most two (`N/D = n₀/d₀ + n₁/d₁`, i.e. `N = n₀d₁ + n₁d₀`, `D = d₀d₁`);
* secure columns `S₀ … S_{B−1}`: for `b < B−1`, `(S_b − S_{b−1})·D_b = N_b` (with `S_{−1} = 0`);
  for the last, `(S_last(r) − S_last(r−1) − S_{B−2}(r) + c/n)·D_last = N_last`, rows cyclic;
* `c` is the component's claimed sum.

`logup_sum` proves: if every denominator is nonzero, the terms over all rows sum to `c`. The
verifier then checks that the claimed sums (and public contributions) add to zero. Going from
"the fractions sum to zero for random `z, α`" to `Balanced` (Lookup.lean) is the probabilistic
LogUp/Schwartz–Zippel step, trusted together with Stwo (reference/verification.md).
-/
import Mathlib

namespace StarkedAir.LogUp

open Finset

variable {K : Type} [Field K]

/-- Previous row, cyclically. -/
def prev (n r : ℕ) : ℕ := (r + n - 1) % n

theorem sum_prev (n : ℕ) (hn : 0 < n) (f : ℕ → K) :
    ∑ r ∈ range n, f (prev n r) = ∑ r ∈ range n, f r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ]
  have h0 : prev (m + 1) 0 = m := by
    unfold prev; rw [show 0 + (m + 1) - 1 = m by omega, Nat.mod_eq_of_lt (by omega)]
  have hs : ∀ r ∈ range m, f (prev (m + 1) (r + 1)) = f r := by
    intro r hr
    rw [mem_range] at hr
    unfold prev
    rw [show r + 1 + (m + 1) - 1 = r + (m + 1) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [sum_congr rfl hs, h0]

/-- **Telescoping.** If the last column steps by `T r − c/n` at every row (cyclically), the
row totals sum to `c`. -/
theorem telescope (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (S T : ℕ → K) (c : K)
    (h : ∀ r < n, S r - S (prev n r) = T r - c / n) : ∑ r ∈ range n, T r = c := by
  have hs : ∑ r ∈ range n, (S r - S (prev n r)) = ∑ r ∈ range n, (T r - c / n) :=
    sum_congr rfl fun r hr => h r (mem_range.mp hr)
  rw [sum_sub_distrib, sum_prev n hn, sub_self, sum_sub_distrib, sum_const, card_range,
    nsmul_eq_mul, mul_div_cancel₀ c hnK] at hs
  exact (sub_eq_zero.mp hs.symm)

/-- A batch's fraction: `N/D` with nonzero `D`. -/
theorem batch_frac {S Sp N D : K} (hD : D ≠ 0) (h : (S - Sp) * D = N) : S - Sp = N / D := by
  rw [eq_div_iff hD, h]

/-- A pair: `n₀/d₀ + n₁/d₁ = (n₀d₁ + n₁d₀)/(d₀d₁)`. -/
theorem pair_frac {n₀ d₀ n₁ d₁ : K} (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) :
    n₀ / d₀ + n₁ / d₁ = (n₀ * d₁ + n₁ * d₀) / (d₀ * d₁) := by
  field_simp

/-- **LogUp sum.** Batches `0 … B−1` with numerators `N b r` and nonzero denominators `D b r`;
secure columns `S b`. Given the batch constraints (all but the last: `(S_b − S_{b−1})·D_b = N_b`,
with `S_{−1} = 0`; the last: `(S_last − S_last∘prev − S_{B−2} + c/n)·D_last = N_last`), the sum
over all rows and batches of `N/D` is the claimed sum `c`. -/
theorem logup_sum (n B : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) (hB : 0 < B)
    (S N D : ℕ → ℕ → K) (c : K) (hD : ∀ b < B, ∀ r < n, D b r ≠ 0)
    (hmid : ∀ b, b + 1 < B → ∀ r < n, (S b r - (if b = 0 then 0 else S (b - 1) r)) * D b r = N b r)
    (hlast : ∀ r < n, (S (B - 1) r - S (B - 1) (prev n r) - (if B = 1 then 0 else S (B - 2) r) + c / n) *
      D (B - 1) r = N (B - 1) r) :
    ∑ r ∈ range n, ∑ b ∈ range B, N b r / D b r = c := by
  -- The running column `S_{B−2}` is the sum of the first `B−1` batches.
  have hrun : ∀ r < n, ∀ k, k + 1 < B → S k r = ∑ b ∈ range (k + 1), N b r / D b r := by
    intro r hr k
    induction k with
    | zero =>
      intro hk
      have := batch_frac (hD 0 (by omega) r hr) (hmid 0 hk r hr)
      simp only [if_true, sub_zero] at this
      simp [this]
    | succ k ih =>
      intro hk
      have := batch_frac (hD (k + 1) (by omega) r hr) (hmid (k + 1) hk r hr)
      simp only [show k + 1 ≠ 0 from by omega, if_false, Nat.add_sub_cancel] at this
      rw [sum_range_succ, ← ih (by omega), ← this]; ring
  apply telescope n hn hnK (S (B - 1)) _ c
  intro r hr
  have hl := batch_frac (S := S (B - 1) r) (N := N (B - 1) r)
    (Sp := S (B - 1) (prev n r) + (if B = 1 then 0 else S (B - 2) r) - c / n)
    (hD (B - 1) (by omega) r hr) (by rw [← hlast r hr]; ring)
  have hsplit : ∑ b ∈ range B, N b r / D b r =
      (if B = 1 then 0 else S (B - 2) r) + N (B - 1) r / D (B - 1) r := by
    obtain ⟨B', rfl⟩ : ∃ B', B = B' + 1 := ⟨B - 1, by omega⟩
    rw [sum_range_succ, Nat.add_sub_cancel]
    rcases Nat.eq_zero_or_pos B' with rfl | hB'
    · simp
    · rw [if_neg (by omega), hrun r hr (B' + 1 - 2) (by omega), show B' + 1 - 2 + 1 = B' by omega]
  rw [hsplit, ← hl]; ring

end StarkedAir.LogUp
