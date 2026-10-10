/-
**Epochs from a previous coin set (M3b, D-040; the owner's "a UTXO set at one point in time that can
later be amended").** An epoch need not start at genesis: it can start from the coin set `init` after
block `a − 1` (an earlier epoch's final set, or a snapshot), with creation indices below the epoch's
first transaction index `g0`. Its sum then counts `init` as created:
`Σ init + Σ created − Σ spent − Σ final = 0`.

- `run_from_balance`: from the view holding `init`, if every claim is earlier, the keys of `init` and the
  created coins are distinct, and `init + created = spent + final`, Core's sequential update succeeds
  and ends holding exactly `final`.
- `epoch_from_sound`: the field-sum version (outside a bounded bad set of `(α, z)`), with injectivity on
  the epoch's own events (as in `epoch_sound_on`).

The verifier binds `init` into the epoch's challenge (its `hash_serialized` is in the seed), so `init` is
fixed before `(α, z)` are drawn.
-/
import StarkedAir.Spec.UtxoFingerprint

namespace StarkedAir.Spec.Utxo

open Polynomial StarkedAir.LogUpSZ

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- The view of a list of tuples (the first occurrence of a key wins; keys are distinct where used). -/
def viewOf : List (Ev K V) → View K V
  | [] => fun _ => none
  | e :: es => Function.update (viewOf es) e.1 (some (e.2.1, e.2.2))

theorem rep_viewOf : ∀ (l : List (Ev K V)), (l.map Prod.fst).Nodup → Rep (viewOf l) (l : Multiset (Ev K V))
  | [], _ => ⟨by simp, fun k v j => by simp [viewOf]⟩
  | e :: es, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hne, hnd'⟩ := hnd
    obtain ⟨-, hiff⟩ := rep_viewOf es hnd'
    refine ⟨by simpa [List.map_cons, List.nodup_cons] using And.intro hne hnd', fun k v j => ?_⟩
    simp only [viewOf]
    by_cases hk : k = e.1
    · subst hk
      rw [Function.update_self, ← Multiset.cons_coe, Multiset.mem_cons]
      constructor
      · intro h; simp only [Option.some.injEq, Prod.mk.injEq] at h; left; rw [← h.1, ← h.2]
      · rintro (h | h)
        · rw [← h]
        · exact absurd (List.mem_map.mpr ⟨(e.1, v, j), by simpa using h, rfl⟩) hne
    · rw [Function.update_of_ne hk, hiff, ← Multiset.cons_coe, Multiset.mem_cons]
      constructor
      · exact Or.inr
      · rintro (h | h)
        · exact absurd (congrArg Prod.fst h) hk
        · exact h

/-- **The multiset argument from a previous set.** -/
theorem run_from_balance (init : List (Ev K V)) (g0 : ℕ) (hidx : ∀ e ∈ init, e.2.2 < g0)
    (ts : List (Tx K V)) (fin : Multiset (Ev K V)) (hord : Ordered g0 ts)
    (hnd : (((init : Multiset (Ev K V)) + created g0 ts).map Prod.fst).Nodup)
    (hbal : (init : Multiset (Ev K V)) + created g0 ts = spent ts + fin) :
    ∃ m, run g0 (viewOf init) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  have hnd0 : (init.map Prod.fst).Nodup := by
    have := nodup_keys_le (Multiset.le_add_right (init : Multiset (Ev K V)) (created g0 ts)) hnd
    simpa using this
  obtain ⟨m, hm, hr⟩ := run_rep ts g0 _ _ (rep_viewOf init hnd0) (fun e he => hidx e (by simpa using he)) hord hnd
    (by rw [hbal]; exact Multiset.le_add_right _ _)
  refine ⟨m, hm, fun k v j => ?_⟩
  rw [hr.2, hbal, add_tsub_cancel_left]

variable {𝕂 : Type} [Field 𝕂] [DecidableEq 𝕂] [Algebra F 𝕂]

/-- The epoch's LogUp entries from a previous set: `init` and created `+1`, spent and final `−1`. -/
noncomputable def epochEntriesFrom (enc : Ev K V → List F) (init cr sp fi : List (Ev K V)) : List (Entry 𝕂) :=
  init.map (fun t => ((1 : 𝕂), fp enc t)) ++ epochEntries enc cr sp fi

/-- The epoch's events from a previous set. -/
noncomputable def occFrom (init : List (Ev K V)) (g0 : ℕ) (ts : List (Tx K V)) (fin : List (Ev K V)) : List (Ev K V) :=
  init ++ (created g0 ts).toList ++ (spent ts).toList ++ fin

/-- **Epoch soundness from a previous set.** -/
theorem epoch_from_sound [Fintype 𝕂] (enc : Ev K V → List F) (w : ℕ) (hw : ∀ t, (enc t).length = w)
    (init : List (Ev K V)) (g0 : ℕ) (ts : List (Tx K V)) (fin : List (Ev K V)) :
    ∃ Bad : Finset (𝕂 × 𝕂),
      Bad.card ≤ ((polys (epochEntriesFrom (𝕂 := 𝕂) enc init (created g0 ts).toList (spent ts).toList fin)).card ^ 2 *
        (w + 1) + 2 * (polys (epochEntriesFrom (𝕂 := 𝕂) enc init (created g0 ts).toList (spent ts).toList fin)).card) *
          Fintype.card 𝕂 ∧
      ∀ az ∉ Bad, (∀ t ∈ occFrom init g0 ts fin, ∀ u ∈ occFrom init g0 ts fin, enc t = enc u → t = u) →
        (∀ e ∈ init, e.2.2 < g0) → Ordered g0 ts →
        (((init : Multiset (Ev K V)) + created g0 ts).map Prod.fst).Nodup →
        init.length + Multiset.card (created g0 ts) + Multiset.card (spent ts) + fin.length < P →
        fracSum (epochEntriesFrom enc init (created g0 ts).toList (spent ts).toList fin) az.1 az.2 = 0 →
        ∃ m, run g0 (viewOf init) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  set es := epochEntriesFrom (𝕂 := 𝕂) enc init (created g0 ts).toList (spent ts).toList fin
  obtain ⟨Bad, hcard, hbad⟩ := logup_sz es (w + 1) (by
    intro e he'
    simp only [es, epochEntriesFrom, epochEntries, List.mem_append, List.mem_map] at he'
    rcases he' with ⟨t, _, rfl⟩ | ((⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩) <;> exact fp_deg hw t)
  refine ⟨Bad, hcard, fun az haz he hidx hord hnd hbound hsum => ?_⟩
  have hbal := (hbad az haz).2 hsum
  have hinj : ∀ t ∈ occFrom init g0 ts fin, ∀ u ∈ occFrom init g0 ts fin, fp (𝕂 := 𝕂) enc t = fp enc u → t = u :=
    fun t ht u hu h => he t ht u hu (tuplePoly_inj (by rw [hw, hw]) h)
  have hcount : ∀ t, Multiset.count t ((init : Multiset (Ev K V)) + created g0 ts) =
      Multiset.count t (spent ts + (fin : Multiset (Ev K V))) := by
    intro t
    by_cases hto : t ∈ occFrom init g0 ts fin
    · have sub : ∀ l : List (Ev K V), (∀ u ∈ l, u ∈ occFrom init g0 ts fin) → ∀ u ∈ l, fp (𝕂 := 𝕂) enc u = fp enc t → u = t :=
        fun l hl u hu h => hinj u (hl u hu) t hto h
      have h0 := hbal (fp enc t)
      simp only [es, epochEntriesFrom, epochEntries, mult_append] at h0
      rw [mult_map_on _ _ _ (sub _ (fun u hu => by simp [occFrom, hu])),
        mult_map_on _ _ _ (sub _ (fun u hu => by simp [occFrom, hu])),
        mult_map_on _ _ _ (sub _ (fun u hu => by simp [occFrom, hu])),
        mult_map_on _ _ _ (sub _ (fun u hu => by simp [occFrom, hu]))] at h0
      rw [Multiset.count_add, Multiset.count_add]
      simp only [Multiset.coe_toList] at h0
      have hc1 := Multiset.count_le_card t (init : Multiset (Ev K V))
      have hc2 := Multiset.count_le_card t (created g0 ts)
      have hc3 := Multiset.count_le_card t (spent ts)
      have hc4 := Multiset.count_le_card t (fin : Multiset (Ev K V))
      rw [Multiset.coe_card] at hc1 hc4
      have hk : ((Multiset.count t (init : Multiset (Ev K V)) + Multiset.count t (created g0 ts) : ℕ) : 𝕂) =
          ((Multiset.count t (spent ts) + Multiset.count t (fin : Multiset (Ev K V)) : ℕ) : 𝕂) := by
        push_cast; linear_combination h0
      have hF : ((Multiset.count t (init : Multiset (Ev K V)) + Multiset.count t (created g0 ts) : ℕ) : F) =
          ((Multiset.count t (spent ts) + Multiset.count t (fin : Multiset (Ev K V)) : ℕ) : F) := by
        apply (algebraMap F 𝕂).injective
        simpa using hk
      exact natCast_inj_of_lt (by omega) (by omega) hF
    · simp only [occFrom, List.mem_append, Multiset.mem_toList, not_or] at hto
      rw [Multiset.count_add, Multiset.count_add, Multiset.count_eq_zero.mpr (by simpa using hto.1.1.1),
        Multiset.count_eq_zero.mpr hto.1.1.2, Multiset.count_eq_zero.mpr hto.1.2,
        Multiset.count_eq_zero.mpr (by simpa using hto.2)]
  have hm : (init : Multiset (Ev K V)) + created g0 ts = spent ts + (fin : Multiset (Ev K V)) := Multiset.ext.mpr hcount
  obtain ⟨m, hrun, hiff⟩ := run_from_balance init g0 hidx ts fin hord hnd hm
  exact ⟨m, hrun, fun k v j => by rw [hiff]; simp⟩

end StarkedAir.Spec.Utxo
