/-
**The UTXO epoch argument (M3b, D-040): field sums to Core's coins view.** Over an epoch, every created coin
contributes `+1/(φ(t)(α) − z)`, every spent coin (its claimed tuple) and every coin of the final set
`−1/(φ(t)(α) − z)`, where `φ(t)` is the fingerprint polynomial of the coin's encoding (`tuplePoly`; its
value at `α` is Stwo's `combine`). The proofs check that these sum to zero.

**`epoch_sound`**: there is a set `Bad` of at most `(N²·(w + 1) + 2N)·|K|` challenge pairs (`N` the number
of distinct fingerprints, `w` the encoding width) such that, for `(α, z) ∉ Bad`, a zero sum implies Core's
sequential update from the empty view succeeds and ends holding exactly the final set. This needs:
- the encoding to be injective, with a fixed width;
- claimed creation indices earlier than their spends;
- distinct created outpoints;
- fewer than `p` events in all (`#created + #spent + #final < P`). Counts are only known mod `p` (the
  field's characteristic), so the aggregator must check this bound.
-/
import StarkedAir.LogUpSZ
import StarkedAir.Spec.UtxoMultiset

namespace StarkedAir.Spec.Utxo

open Polynomial StarkedAir.LogUpSZ

variable {K V : Type} [DecidableEq K] [DecidableEq V]
variable {𝕂 : Type} [Field 𝕂] [DecidableEq 𝕂] [Algebra F 𝕂]

/-- The fingerprint of a coin tuple under an encoding. -/
noncomputable def fp (enc : Ev K V → List F) (t : Ev K V) : 𝕂[X] := tuplePoly (enc t)

theorem fp_inj {enc : Ev K V → List F} {w : ℕ} (hw : ∀ t, (enc t).length = w) (he : Function.Injective enc) :
    Function.Injective (fp (𝕂 := 𝕂) enc) := fun t u h =>
  he (tuplePoly_inj (by rw [hw, hw]) h)

theorem fp_deg {enc : Ev K V → List F} {w : ℕ} (hw : ∀ t, (enc t).length = w) (t : Ev K V) :
    (fp (𝕂 := 𝕂) enc t).natDegree < w + 1 := by
  apply Nat.lt_succ_of_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [fp, coeff_tuplePoly, List.getD_eq_default _ _ (by rw [hw]; exact_mod_cast hN.le), map_zero]

/-- The epoch's LogUp entries: created `+1`, spent and final `−1`. -/
noncomputable def epochEntries (enc : Ev K V → List F) (cr sp fi : List (Ev K V)) : List (Entry 𝕂) :=
  cr.map (fun t => ((1 : 𝕂), fp enc t)) ++ sp.map (fun t => ((-1 : 𝕂), fp enc t)) ++
    fi.map (fun t => ((-1 : 𝕂), fp enc t))

theorem mult_append (a b : List (Entry 𝕂)) (u : 𝕂[X]) : mult (a ++ b) u = mult a u + mult b u := by
  simp [mult, List.filter_append]

theorem mult_map {enc : Ev K V → List F} (hinj : Function.Injective (fp (𝕂 := 𝕂) enc)) (c : 𝕂) :
    ∀ (l : List (Ev K V)) (t0 : Ev K V), mult (l.map fun t => (c, fp enc t)) (fp enc t0) =
      c * (Multiset.count t0 (l : Multiset (Ev K V)) : 𝕂)
  | [], _ => by simp [mult]
  | t :: l, t0 => by
    rw [List.map_cons, mult_cons, mult_map hinj c l t0, ← Multiset.cons_coe, Multiset.count_cons]
    by_cases h : t = t0
    · subst h; simp; ring
    · have : fp (𝕂 := 𝕂) enc t ≠ fp enc t0 := fun e => h (hinj e)
      simp [this, Ne.symm h]

/-- **Epoch soundness.** -/
theorem epoch_sound [Fintype 𝕂] (enc : Ev K V → List F) (w : ℕ) (hw : ∀ t, (enc t).length = w)
    (he : Function.Injective enc) (ts : List (Tx K V)) (fin : List (Ev K V)) :
    ∃ Bad : Finset (𝕂 × 𝕂), Bad.card ≤ ((polys (epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin)).card ^ 2 *
        (w + 1) + 2 * (polys (epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin)).card) * Fintype.card 𝕂 ∧
      ∀ az ∉ Bad, Ordered 0 ts → ((created 0 ts).map Prod.fst).Nodup →
        Multiset.card (created 0 ts) + Multiset.card (spent ts) + fin.length < P →
        fracSum (epochEntries enc (created 0 ts).toList (spent ts).toList fin) az.1 az.2 = 0 →
        ∃ m, run 0 (fun _ => none) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  set es := epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin
  obtain ⟨Bad, hcard, hbad⟩ := logup_sz es (w + 1) (by
    intro e he'
    simp only [es, epochEntries, List.mem_append, List.mem_map] at he'
    rcases he' with (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩ <;> exact fp_deg hw t)
  refine ⟨Bad, hcard, fun az haz hord hnd hbound hsum => ?_⟩
  have hbal := (hbad az haz).2 hsum
  have hinj := fp_inj (𝕂 := 𝕂) hw he
  -- per tuple: `#created = #spent + #final`
  have hcount : ∀ t, Multiset.count t (created 0 ts) = Multiset.count t (spent ts + (fin : Multiset (Ev K V))) := by
    intro t
    have h0 := hbal (fp enc t)
    simp only [es, epochEntries, mult_append, mult_map hinj] at h0
    rw [Multiset.count_add]
    simp only [Multiset.coe_toList] at h0
    have hlt1 : Multiset.count t (created 0 ts) < P :=
      lt_of_le_of_lt (Multiset.count_le_card _ _) (by omega)
    have hlt2 : Multiset.count t (spent ts) + Multiset.count t (fin : Multiset (Ev K V)) < P := by
      have := Multiset.count_le_card t (spent ts)
      have := Multiset.count_le_card t (fin : Multiset (Ev K V))
      rw [Multiset.coe_card] at this
      omega
    have hk : ((Multiset.count t (created 0 ts) : ℕ) : 𝕂) =
        ((Multiset.count t (spent ts) + Multiset.count t (fin : Multiset (Ev K V)) : ℕ) : 𝕂) := by
      push_cast; linear_combination h0
    have hF : ((Multiset.count t (created 0 ts) : ℕ) : F) =
        ((Multiset.count t (spent ts) + Multiset.count t (fin : Multiset (Ev K V)) : ℕ) : F) := by
      apply (algebraMap F 𝕂).injective
      simpa using hk
    exact natCast_inj_of_lt hlt1 hlt2 hF
  have hm : created 0 ts = spent ts + (fin : Multiset (Ev K V)) := Multiset.ext.mpr hcount
  obtain ⟨m, hrun, hiff⟩ := run_of_balance ts fin hord hnd hm
  exact ⟨m, hrun, fun k v j => by rw [hiff]; simp⟩

end StarkedAir.Spec.Utxo
