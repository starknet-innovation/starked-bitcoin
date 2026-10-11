/-
**From a zero epoch sum to a multiset balance (M3b), without ordering.** `epoch_sound_on` needs the
claims' creation indices to be earlier as a hypothesis. For the coin component, a claim's index is
only known to be earlier once the claim is known to be a real created coin, which is what the balance
gives. So the balance is stated on its own:

- `balance_of_sum`: outside the LogUp bad set, with the encoding injective on the epoch's events and
  fewer than `P` events, a zero sum of `init` and created (`+1`) and spent and final (`−1`) gives
  `init + created = spent + final` as multisets of events.

`epoch_from_sound` is then this, plus ordering, plus `run_from_balance`.
-/
import StarkedAir.Spec.UtxoEpochFrom

namespace StarkedAir.Spec.Utxo

open Polynomial StarkedAir.LogUpSZ

variable {E : Type} [DecidableEq E]
variable {𝕂 : Type} [Field 𝕂] [DecidableEq 𝕂] [Algebra F 𝕂]

/-- Entries: `pos` with `+1`, `neg` with `−1`. -/
noncomputable def pnEntries (enc : E → List F) (pos neg : List E) : List (Entry 𝕂) :=
  pos.map (fun t => ((1 : 𝕂), tuplePoly (enc t))) ++ neg.map (fun t => ((-1 : 𝕂), tuplePoly (enc t)))

theorem mult_map_on' {enc : E → List F} (c : 𝕂) :
    ∀ (l : List E) (t0 : E), (∀ t ∈ l, tuplePoly (K := 𝕂) (enc t) = tuplePoly (enc t0) → t = t0) →
      mult (l.map fun t => (c, tuplePoly (enc t))) (tuplePoly (enc t0)) = c * (List.count t0 l : 𝕂)
  | [], _, _ => by simp [mult]
  | t :: l, t0, hi => by
    rw [List.map_cons, mult_cons, mult_map_on' c l t0 (fun u hu => hi u (List.mem_cons_of_mem _ hu)), List.count_cons]
    by_cases h : t = t0
    · subst h; simp; ring
    · have : tuplePoly (K := 𝕂) (enc t) ≠ tuplePoly (enc t0) := fun e => h (hi t List.mem_cons_self e)
      have hb : (t == t0) = false := by simpa using h
      simp [this, hb]

/-- **A zero sum balances.** -/
theorem balance_of_sum [Fintype 𝕂] (enc : E → List F) (w : ℕ) (hw : ∀ t, (enc t).length = w) (pos neg : List E) :
    ∃ Bad : Finset (𝕂 × 𝕂), Bad.card ≤ ((polys (pnEntries (𝕂 := 𝕂) enc pos neg)).card ^ 2 * (w + 1) +
        2 * (polys (pnEntries (𝕂 := 𝕂) enc pos neg)).card) * Fintype.card 𝕂 ∧
      ∀ az ∉ Bad, (∀ t ∈ pos ++ neg, ∀ u ∈ pos ++ neg, enc t = enc u → t = u) → pos.length + neg.length < P →
        fracSum (pnEntries enc pos neg) az.1 az.2 = 0 → (pos : Multiset E) = (neg : Multiset E) := by
  obtain ⟨Bad, hcard, hbad⟩ := logup_sz (pnEntries (𝕂 := 𝕂) enc pos neg) (w + 1) (by
    intro e he'
    simp only [pnEntries, List.mem_append, List.mem_map] at he'
    rcases he' with ⟨t, _, rfl⟩ | ⟨t, _, rfl⟩ <;>
      · have := tuplePoly_natDegree (𝕂 := 𝕂) (enc t); rw [hw] at this; exact this)
  refine ⟨Bad, hcard, fun az haz he hbound hsum => ?_⟩
  have hbal := (hbad az haz).2 hsum
  have hinj : ∀ t ∈ pos ++ neg, ∀ u ∈ pos ++ neg, tuplePoly (K := 𝕂) (enc t) = tuplePoly (enc u) → t = u :=
    fun t ht u hu h => he t ht u hu (tuplePoly_inj (by rw [hw, hw]) h)
  apply Multiset.ext.mpr
  intro t
  simp only [Multiset.coe_count]
  by_cases hto : t ∈ pos ++ neg
  · have h0 := hbal (tuplePoly (enc t))
    simp only [pnEntries, mult_append] at h0
    rw [mult_map_on' _ _ _ (fun u hu h => hinj u (by simp [hu]) t hto h),
      mult_map_on' _ _ _ (fun u hu h => hinj u (by simp [hu]) t hto h)] at h0
    have hlt1 : List.count t pos < P := lt_of_le_of_lt (List.count_le_length) (by omega)
    have hlt2 : List.count t neg < P := lt_of_le_of_lt (List.count_le_length) (by omega)
    have hk : ((List.count t pos : ℕ) : 𝕂) = ((List.count t neg : ℕ) : 𝕂) := by linear_combination h0
    have hF : ((List.count t pos : ℕ) : F) = ((List.count t neg : ℕ) : F) := by
      apply (algebraMap F 𝕂).injective; simpa using hk
    exact natCast_inj_of_lt hlt1 hlt2 hF
  · simp only [List.mem_append, not_or] at hto
    rw [List.count_eq_zero_of_not_mem hto.1, List.count_eq_zero_of_not_mem hto.2]

end StarkedAir.Spec.Utxo
