/-
**The fingerprint's Schwartz–Zippel step (M3b, D-040).** `epoch_sound` assumed an injective tuple
encoding. The coin tuple carries a coin's `serTxOut` bytes only through their length and a Horner
fingerprint `H = Σₖ bₖ γ^(len−1−k)` at a challenge `γ` (`Block/FpWalk.lean`, `seg_sound`), so the
encoding is injective only for good `γ`.

- `hornerF_eval`: the fingerprint is the value at `γ` of the reversed byte list's `tuplePoly`.
- `fp_separates`: outside `fpBad S` (at most `|S|²·(L + 1)` values, `L` bounding the lengths;
  `fpBad_card`), two byte strings of `S` with the same length and the same fingerprint are equal.
- `epoch_sound_on`: `epoch_sound` with injectivity required only on the epoch's own events.
- `epoch_sound_fp`: the two steps together. For `γ` outside `fpBad`, and then `(α, z)` outside the
  LogUp bad set, a zero epoch sum gives Core's coins view, for any encoding that records each coin's
  other fields, its byte length and its fingerprint (`Separates`).

With QM31 (`|K| ≈ 2^124`), `N ≈ 2·10⁹` coins and `L ≤ 10⁴` bytes, the `γ` step's bad fraction is about
`N²·L/|K| ≈ 2^-50`. The total bound (with the LogUp step) is what the parameters must keep small.
-/
import StarkedAir.Spec.UtxoEpoch

namespace StarkedAir.Spec.Utxo

open Polynomial StarkedAir.LogUpSZ

variable {K V : Type} [DecidableEq K] [DecidableEq V]
variable {𝕂 : Type} [Field 𝕂] [DecidableEq 𝕂] [Algebra F 𝕂]

/-! ### The Horner fingerprint -/

/-- `Σₖ bₖ γ^(len−1−k)`, as the circuit's Horner walk computes it. -/
noncomputable def hornerF (γ : 𝕂) (l : List F) : 𝕂 := l.foldl (fun h b => h * γ + algebraMap F 𝕂 b) 0

omit [DecidableEq 𝕂] in
theorem tuplePoly_nil : tuplePoly (K := 𝕂) [] = 0 := by simp [tuplePoly]

theorem tuplePoly_cons (a : F) (t : List F) : tuplePoly (K := 𝕂) (a :: t) = C (algebraMap F 𝕂 a) + X * tuplePoly t := by
  ext n
  cases n with
  | zero => simp [coeff_tuplePoly]
  | succ n => simp [coeff_tuplePoly, coeff_X_mul]

theorem hornerF_eval (γ : 𝕂) (l : List F) : hornerF γ l = (tuplePoly (K := 𝕂) l.reverse).eval γ := by
  induction l using List.reverseRecOn with
  | nil => simp [hornerF, tuplePoly_nil]
  | append_singleton l b ih =>
    rw [hornerF, List.foldl_append, ← hornerF, ih, List.reverse_append, List.reverse_singleton, List.singleton_append,
      tuplePoly_cons]
    simp only [List.foldl_cons, List.foldl_nil, eval_add, eval_C, eval_mul, eval_X]
    ring

theorem tuplePoly_natDegree (t : List F) : (tuplePoly (K := 𝕂) t).natDegree < t.length + 1 := by
  apply Nat.lt_succ_of_le
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [coeff_tuplePoly, List.getD_eq_default _ _ (by exact_mod_cast hN.le), map_zero]

/-- The challenges where two byte strings of `S` collide. -/
noncomputable def fpBad (S : Finset (List F)) : Finset 𝕂 := collSet (S.image fun b => tuplePoly (K := 𝕂) b.reverse)

theorem fpBad_card (S : Finset (List F)) (L : ℕ) (hL : ∀ b ∈ S, b.length ≤ L) :
    (fpBad (𝕂 := 𝕂) S).card ≤ S.card ^ 2 * (L + 1) := by
  refine le_trans (card_collSet _ (L + 1) ?_) (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left Finset.card_image_le 2))
  intro p hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hp
  have := tuplePoly_natDegree (𝕂 := 𝕂) b.reverse
  rw [List.length_reverse] at this
  have := hL b hb
  omega

/-- **The fingerprint separates.** Outside `fpBad S`, byte strings of `S` with the same length and the
same fingerprint are equal. -/
theorem fp_separates {S : Finset (List F)} {γ : 𝕂} (hγ : γ ∉ fpBad S) {b₁ b₂ : List F} (h₁ : b₁ ∈ S) (h₂ : b₂ ∈ S)
    (hl : b₁.length = b₂.length) (he : hornerF γ b₁ = hornerF γ b₂) : b₁ = b₂ := by
  by_contra hne
  apply hγ
  apply mem_collSet
  refine ⟨_, Finset.mem_image_of_mem _ h₁, _, Finset.mem_image_of_mem _ h₂, fun hp => hne ?_, ?_⟩
  · exact List.reverse_injective (tuplePoly_inj (by simp [hl]) hp)
  · rw [← hornerF_eval, ← hornerF_eval, he]

/-! ### `epoch_sound` with injectivity on the epoch's events -/

/-- The epoch's events: created, spent, final. -/
noncomputable def occ (ts : List (Tx K V)) (fin : List (Ev K V)) : List (Ev K V) := (created 0 ts).toList ++ (spent ts).toList ++ fin

theorem mult_map_on {enc : Ev K V → List F} (c : 𝕂) :
    ∀ (l : List (Ev K V)) (t0 : Ev K V), (∀ t ∈ l, fp (𝕂 := 𝕂) enc t = fp enc t0 → t = t0) →
      mult (l.map fun t => (c, fp enc t)) (fp enc t0) = c * (Multiset.count t0 (l : Multiset (Ev K V)) : 𝕂)
  | [], _, _ => by simp [mult]
  | t :: l, t0, hi => by
    rw [List.map_cons, mult_cons, mult_map_on c l t0 (fun u hu => hi u (List.mem_cons_of_mem _ hu)), ← Multiset.cons_coe,
      Multiset.count_cons]
    by_cases h : t = t0
    · subst h; simp; ring
    · have : fp (𝕂 := 𝕂) enc t ≠ fp enc t0 := fun e => h (hi t List.mem_cons_self e)
      simp [this, Ne.symm h]

/-- **Epoch soundness, injectivity on the epoch's events.** The bad set does not depend on the
encoding's injectivity, only on its width. -/
theorem epoch_sound_on [Fintype 𝕂] (enc : Ev K V → List F) (w : ℕ) (hw : ∀ t, (enc t).length = w)
    (ts : List (Tx K V)) (fin : List (Ev K V)) :
    ∃ Bad : Finset (𝕂 × 𝕂), Bad.card ≤ ((polys (epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin)).card ^ 2 *
        (w + 1) + 2 * (polys (epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin)).card) * Fintype.card 𝕂 ∧
      ∀ az ∉ Bad, (∀ t ∈ occ ts fin, ∀ u ∈ occ ts fin, enc t = enc u → t = u) →
        Ordered 0 ts → ((created 0 ts).map Prod.fst).Nodup →
        Multiset.card (created 0 ts) + Multiset.card (spent ts) + fin.length < P →
        fracSum (epochEntries enc (created 0 ts).toList (spent ts).toList fin) az.1 az.2 = 0 →
        ∃ m, run 0 (fun _ => none) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  set es := epochEntries (𝕂 := 𝕂) enc (created 0 ts).toList (spent ts).toList fin
  obtain ⟨Bad, hcard, hbad⟩ := logup_sz es (w + 1) (by
    intro e he'
    simp only [es, epochEntries, List.mem_append, List.mem_map] at he'
    rcases he' with (⟨t, _, rfl⟩ | ⟨t, _, rfl⟩) | ⟨t, _, rfl⟩ <;> exact fp_deg hw t)
  refine ⟨Bad, hcard, fun az haz he hord hnd hbound hsum => ?_⟩
  have hbal := (hbad az haz).2 hsum
  have hinj : ∀ t ∈ occ ts fin, ∀ u ∈ occ ts fin, fp (𝕂 := 𝕂) enc t = fp enc u → t = u := fun t ht u hu h =>
    he t ht u hu (tuplePoly_inj (by rw [hw, hw]) h)
  have hcount : ∀ t, Multiset.count t (created 0 ts) = Multiset.count t (spent ts + (fin : Multiset (Ev K V))) := by
    intro t
    by_cases hto : t ∈ occ ts fin
    · have sub : ∀ l : List (Ev K V), (∀ u ∈ l, u ∈ occ ts fin) → ∀ u ∈ l, fp (𝕂 := 𝕂) enc u = fp enc t → u = t :=
        fun l hl u hu h => hinj u (hl u hu) t hto h
      have h0 := hbal (fp enc t)
      simp only [es, epochEntries, mult_append] at h0
      rw [mult_map_on _ _ _ (sub _ (fun u hu => by simp [occ, hu])), mult_map_on _ _ _ (sub _ (fun u hu => by simp [occ, hu])),
        mult_map_on _ _ _ (sub _ (fun u hu => by simp [occ, hu]))] at h0
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
    · simp only [occ, List.mem_append, Multiset.mem_toList, not_or] at hto
      rw [Multiset.count_add, Multiset.count_eq_zero.mpr hto.1.1, Multiset.count_eq_zero.mpr hto.1.2,
        Multiset.count_eq_zero.mpr (by simpa using hto.2)]
  have hm : created 0 ts = spent ts + (fin : Multiset (Ev K V)) := Multiset.ext.mpr hcount
  obtain ⟨m, hrun, hiff⟩ := run_of_balance ts fin hord hnd hm
  exact ⟨m, hrun, fun k v j => by rw [hiff]; simp⟩

/-! ### The two steps together -/

/-- An encoding family (one per `γ`) that records each coin's other fields `pre`, its byte length and
its fingerprint at `γ`: equal encodings give equal `pre`, lengths and fingerprints. -/
def Separates (enc : 𝕂 → Ev K V → List F) (pre : Ev K V → List F) (bytes : Ev K V → List F) : Prop :=
  ∀ γ t u, enc γ t = enc γ u → pre t = pre u ∧ (bytes t).length = (bytes u).length ∧ hornerF γ (bytes t) = hornerF γ (bytes u)

/-- **Epoch soundness with the fingerprint.** For `γ` outside `fpBad` of the epoch's byte strings, and
`(α, z)` outside the LogUp bad set (both bounded), a zero epoch sum gives Core's coins view. `hdet`: a
coin is determined by its other fields and its bytes. -/
theorem epoch_sound_fp [Fintype 𝕂] (enc : 𝕂 → Ev K V → List F) (w : ℕ) (hw : ∀ γ t, (enc γ t).length = w)
    (pre bytes : Ev K V → List F) (hsep : Separates enc pre bytes)
    (hdet : ∀ t u, pre t = pre u → bytes t = bytes u → t = u)
    (ts : List (Tx K V)) (fin : List (Ev K V)) (L : ℕ) (hL : ∀ t ∈ occ ts fin, (bytes t).length ≤ L) :
    (fpBad (𝕂 := 𝕂) ((occ ts fin).map bytes).toFinset).card ≤ ((occ ts fin).map bytes).toFinset.card ^ 2 * (L + 1) ∧
    ∀ γ ∉ fpBad (𝕂 := 𝕂) ((occ ts fin).map bytes).toFinset,
      ∃ Bad : Finset (𝕂 × 𝕂), Bad.card ≤ ((polys (epochEntries (𝕂 := 𝕂) (enc γ) (created 0 ts).toList (spent ts).toList fin)).card ^ 2 *
          (w + 1) + 2 * (polys (epochEntries (𝕂 := 𝕂) (enc γ) (created 0 ts).toList (spent ts).toList fin)).card) * Fintype.card 𝕂 ∧
        ∀ az ∉ Bad, Ordered 0 ts → ((created 0 ts).map Prod.fst).Nodup →
          Multiset.card (created 0 ts) + Multiset.card (spent ts) + fin.length < P →
          fracSum (epochEntries (enc γ) (created 0 ts).toList (spent ts).toList fin) az.1 az.2 = 0 →
          ∃ m, run 0 (fun _ => none) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  refine ⟨fpBad_card _ L (fun b hb => ?_), fun γ hγ => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
    exact hL t ht
  · obtain ⟨Bad, hcard, h⟩ := epoch_sound_on (𝕂 := 𝕂) (enc γ) w (hw γ) ts fin
    refine ⟨Bad, hcard, fun az haz => h az haz (fun t ht u hu he => ?_)⟩
    obtain ⟨hp, hl, hh⟩ := hsep γ t u he
    exact hdet t u hp (fp_separates hγ (List.mem_toFinset.mpr (List.mem_map_of_mem ht))
      (List.mem_toFinset.mpr (List.mem_map_of_mem hu)) hl hh)

end StarkedAir.Spec.Utxo
