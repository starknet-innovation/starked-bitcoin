/-
**LogUp, the probabilistic step (proof review 2026-10-09, §5 item 4).** `LogUp.lean` proves that
the committed fractions sum to the claimed sums; the verifier checks those add to zero. This file
proves that, for all but few challenges `(α, z)`, fractions summing to zero imply balance.

Each lookup entry is a multiplicity `m` and a fingerprint polynomial `P` (for a tuple
`t = (rel, vals…)`, `P = Σᵢ tᵢ Xⁱ`, so `P(α)` is Stwo's `combine(α, t)`); its fraction is
`m / (P(α) − z)`. `logup_sz`: there is a set `Bad` of at most `(N²·L + 2N)·|K|` challenge pairs
(`N` distinct fingerprints, all of degree `< L`) such that for every `(α, z) ∉ Bad`, every
denominator is nonzero and, if the fractions sum to zero, the multiplicities balance per
fingerprint. So a uniformly random `(α, z)` from a field `K` is bad with probability at most
`(N²·L + 2N)/|K|` (QM31: `|K| ≈ 2^124`).

The argument: outside the `α` where two fingerprints collide (roots of their difference), the
values `fᵤ = u(α)` are distinct, and `Σᵤ cᵤ/(fᵤ − z)` is `Q(z)/Πᵤ(fᵤ − z)` with
`Q = Σᵤ cᵤ Π_{w≠u}(fᵤ… )` nonzero (it is `c_{u₀}·Π(f_w − f_{u₀}) ≠ 0` at `f_{u₀}`), so it has at most
`N` roots `z`.

`raw_balanced` turns per-fingerprint balance into per-tuple balance when each relation has one
arity and relation ids are below `P`; `balanced_of_poly` and `balancedExt_of_poly` state it for
`Lookup.Balanced` and `BalancedExt`.

The chain, end to end: `logup_sum` (LogUp.lean) gives that each component's committed fractions
sum to its claimed sum; the verifier checks the claimed sums and the public entries' fractions add
to zero; so `fracSum` over all entries is zero, and for `(α, z) ∉ Bad`, `logup_sz` and
`balancedExt_of_poly` give `BalancedExt`. What stays trusted: that the committed batch fractions
are the entries' `m / (P(α) − z)` (Stwo's encoding, tested), and that Fiat–Shamir yields `(α, z)` as
if uniform after the main commitment (the random-oracle model), with Stwo.
-/
import StarkedAir.Lookup

namespace StarkedAir.LogUpSZ

open Polynomial Finset

section Counting

variable {K : Type} [Field K] [DecidableEq K]

/-- Entries: multiplicity and fingerprint. -/
abbrev Entry (K : Type) [Field K] := K × K[X]

/-- The distinct fingerprints. -/
def polys (es : List (Entry K)) : Finset K[X] := (es.map Prod.snd).toFinset

/-- The total multiplicity of fingerprint `p`. -/
def mult (es : List (Entry K)) (p : K[X]) : K := ((es.filter fun e => e.2 = p).map Prod.fst).sum

def PolyBalanced (es : List (Entry K)) : Prop := ∀ p, mult es p = 0

/-- The LogUp sum at `(α, z)`. -/
def fracSum (es : List (Entry K)) (α z : K) : K := (es.map fun e => e.1 / (e.2.eval α - z)).sum

theorem mult_cons (e : Entry K) (rest : List (Entry K)) (u : K[X]) :
    mult (e :: rest) u = (if e.2 = u then e.1 else 0) + mult rest u := by
  unfold mult
  by_cases h : e.2 = u <;> simp [h]

theorem group_sum (es : List (Entry K)) (S : Finset K[X]) (hS : polys es ⊆ S) (g : K[X] → K) :
    (es.map fun e => e.1 * g e.2).sum = ∑ u ∈ S, mult es u * g u := by
  induction es with
  | nil => simp [mult]
  | cons e rest ih =>
    have hS' : polys rest ⊆ S := fun x hx => hS (by
      simp only [polys, List.map_cons, List.toFinset_cons, Finset.mem_insert] at hx ⊢; exact Or.inr hx)
    have he : e.2 ∈ S := hS (by simp [polys])
    simp only [List.map_cons, List.sum_cons, ih hS', mult_cons, add_mul, Finset.sum_add_distrib]
    congr 1
    simp [ite_mul, Finset.sum_ite_eq, he]

theorem mult_eq_zero_of_not_mem {es : List (Entry K)} {p : K[X]} (hp : p ∉ polys es) : mult es p = 0 := by
  unfold mult
  rw [List.filter_eq_nil_iff.mpr]
  · simp
  · intro e he h
    apply hp
    simp only [polys, List.mem_toFinset, List.mem_map]
    exact ⟨e, he, by simpa using h⟩

/-- Two distinct fingerprints agree at `α`. -/
def Coll (P : Finset K[X]) (α : K) : Prop := ∃ p ∈ P, ∃ q ∈ P, p ≠ q ∧ p.eval α = q.eval α

/-- The `α` where some pair collides: roots of the differences. -/
noncomputable def collSet (P : Finset K[X]) : Finset K :=
  ((P ×ˢ P).filter fun pq => pq.1 ≠ pq.2).biUnion fun pq => (pq.1 - pq.2).roots.toFinset

theorem mem_collSet {P : Finset K[X]} {α : K} (h : Coll P α) : α ∈ collSet P := by
  obtain ⟨p, hp, q, hq, hpq, he⟩ := h
  simp only [collSet, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product]
  refine ⟨(p, q), ⟨⟨hp, hq⟩, hpq⟩, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (sub_ne_zero.mpr hpq)]
  simp [he]

theorem card_collSet (P : Finset K[X]) (L : ℕ) (hdeg : ∀ p ∈ P, p.natDegree < L) :
    (collSet P).card ≤ P.card ^ 2 * L := by
  unfold collSet
  calc _ ≤ ∑ pq ∈ (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2), ((pq.1 - pq.2).roots.toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ (P ×ˢ P).filter (fun pq => pq.1 ≠ pq.2), L := by
        apply Finset.sum_le_sum
        intro pq hpq
        simp only [Finset.mem_filter, Finset.mem_product] at hpq
        calc _ ≤ (pq.1 - pq.2).roots.card := Multiset.toFinset_card_le _
          _ ≤ (pq.1 - pq.2).natDegree := card_roots' _
          _ ≤ max pq.1.natDegree pq.2.natDegree := natDegree_sub_le _ _
          _ ≤ L := le_of_lt (max_lt (hdeg _ hpq.1.1) (hdeg _ hpq.1.2))
    _ ≤ (P ×ˢ P).card * L := by
        rw [Finset.sum_const, smul_eq_mul]
        exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)
    _ = P.card ^ 2 * L := by rw [Finset.card_product, sq]

/-- The numerator polynomial at `α`: `Σᵤ cᵤ Π_{w≠u}(w(α) − X)`. -/
noncomputable def numer (es : List (Entry K)) (α : K) : K[X] :=
  ∑ u ∈ polys es, C (mult es u) * ∏ w ∈ (polys es).erase u, (C (w.eval α) - X)

theorem natDegree_numer (es : List (Entry K)) (α : K) : (numer es α).natDegree ≤ (polys es).card := by
  unfold numer
  apply natDegree_sum_le_of_forall_le
  intro u _
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
  have h1 : ∀ w ∈ (polys es).erase u, (C (w.eval α) - X).natDegree ≤ 1 := by
    intro w _
    refine (natDegree_sub_le _ _).trans ?_
    simp
  refine (Finset.sum_le_sum h1).trans ?_
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_erase_le

theorem eval_numer (es : List (Entry K)) (α z : K) :
    (numer es α).eval z = ∑ u ∈ polys es, mult es u * ∏ w ∈ (polys es).erase u, (w.eval α - z) := by
  simp [numer, eval_finsetSum, eval_prod]

/-- Away from collisions, an unbalanced numerator is a nonzero polynomial. -/
theorem numer_ne_zero (es : List (Entry K)) (α : K) (hc : ¬ Coll (polys es) α) (u₀ : K[X])
    (hu : mult es u₀ ≠ 0) : numer es α ≠ 0 := by
  have hu₀ : u₀ ∈ polys es := by by_contra h; exact hu (mult_eq_zero_of_not_mem h)
  intro h0
  have := congrArg (eval (u₀.eval α)) h0
  rw [eval_numer, eval_zero, Finset.sum_eq_single u₀] at this
  · rcases mul_eq_zero.mp this with h | h
    · exact hu h
    · rw [Finset.prod_eq_zero_iff] at h
      obtain ⟨w, hw, hw0⟩ := h
      have hwne : w ≠ u₀ := Finset.ne_of_mem_erase hw
      exact hc ⟨w, Finset.mem_of_mem_erase hw, u₀, hu₀, hwne, sub_eq_zero.mp hw0⟩
  · intro u _ hne
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hne, hu₀⟩) (sub_self _))
  · intro h; exact absurd hu₀ h

/-- Where every denominator is nonzero, a zero sum is a root of the numerator. -/
theorem numer_root (es : List (Entry K)) (α z : K) (hd : ∀ e ∈ es, e.2.eval α ≠ z)
    (hs : fracSum es α z = 0) : (numer es α).eval z = 0 := by
  have hdu : ∀ u ∈ polys es, u.eval α - z ≠ 0 := by
    intro u hu
    simp only [polys, List.mem_toFinset, List.mem_map] at hu
    obtain ⟨e, he, rfl⟩ := hu
    exact sub_ne_zero.mpr (hd e he)
  have hsum : fracSum es α z = ∑ u ∈ polys es, mult es u * (u.eval α - z)⁻¹ := by
    unfold fracSum
    simp only [div_eq_mul_inv]
    exact group_sum es _ (subset_refl _) (fun p => (p.eval α - z)⁻¹)
  have hprod : ∏ w ∈ polys es, (w.eval α - z) ≠ 0 := Finset.prod_ne_zero_iff.mpr hdu
  have key : fracSum es α z * ∏ w ∈ polys es, (w.eval α - z) = (numer es α).eval z := by
    rw [hsum, Finset.sum_mul, eval_numer]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.mul_prod_erase _ _ hu, mul_assoc, ← mul_assoc (u.eval α - z)⁻¹,
      inv_mul_cancel₀ (hdu u hu), one_mul]
  rw [← key, hs, zero_mul]

/-- **The LogUp Schwartz–Zippel step.** -/
theorem logup_sz [Fintype K] (es : List (Entry K)) (L : ℕ) (hdeg : ∀ e ∈ es, e.2.natDegree < L) :
    ∃ Bad : Finset (K × K), Bad.card ≤ ((polys es).card ^ 2 * L + 2 * (polys es).card) * Fintype.card K ∧
      ∀ az ∉ Bad, (∀ e ∈ es, e.2.eval az.1 ≠ az.2) ∧ (fracSum es az.1 az.2 = 0 → PolyBalanced es) := by
  classical
  set P := polys es with hP
  have hdegP : ∀ p ∈ P, p.natDegree < L := by
    intro p hp
    simp only [hP, polys, List.mem_toFinset, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact hdeg e he
  -- Colliding α (any z); a zero denominator; a zero sum away from collisions.
  let B1 : Finset (K × K) := collSet P ×ˢ Finset.univ
  let B2 : Finset (K × K) := Finset.univ.biUnion fun α => (P.image fun u => u.eval α).image fun z => (α, z)
  let B3 : Finset (K × K) := Finset.univ.biUnion fun α =>
    if Coll P α then ∅ else ((numer es α).roots.toFinset).image fun z => (α, z)
  refine ⟨B1 ∪ B2 ∪ B3, ?_, ?_⟩
  · have h1 : B1.card ≤ P.card ^ 2 * L * Fintype.card K := by
      simp only [B1, Finset.card_product, Finset.card_univ]
      exact Nat.mul_le_mul_right _ (card_collSet P L hdegP)
    have h2 : B2.card ≤ P.card * Fintype.card K := by
      calc _ ≤ ∑ α : K, ((P.image fun u => u.eval α).image fun z => (α, z)).card := Finset.card_biUnion_le
        _ ≤ ∑ _α : K, P.card := Finset.sum_le_sum fun α _ =>
            (Finset.card_image_le).trans Finset.card_image_le
        _ = P.card * Fintype.card K := by simp [mul_comm]
    have h3 : B3.card ≤ P.card * Fintype.card K := by
      calc _ ≤ ∑ α : K, (if Coll P α then (∅ : Finset (K × K)) else
              ((numer es α).roots.toFinset).image fun z => (α, z)).card := Finset.card_biUnion_le
        _ ≤ ∑ _α : K, P.card := by
            apply Finset.sum_le_sum; intro α _
            split
            · simp
            · calc _ ≤ ((numer es α).roots.toFinset).card := Finset.card_image_le
                _ ≤ (numer es α).roots.card := Multiset.toFinset_card_le _
                _ ≤ (numer es α).natDegree := card_roots' _
                _ ≤ P.card := natDegree_numer es α
        _ = P.card * Fintype.card K := by simp [mul_comm]
    calc (B1 ∪ B2 ∪ B3).card ≤ B1.card + B2.card + B3.card :=
          (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ P.card ^ 2 * L * Fintype.card K + P.card * Fintype.card K + P.card * Fintype.card K := by omega
      _ = (P.card ^ 2 * L + 2 * P.card) * Fintype.card K := by ring
  · rintro ⟨α, z⟩ hbad
    simp only [Finset.mem_union, not_or] at hbad
    obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hbad
    have hd : ∀ e ∈ es, e.2.eval α ≠ z := by
      intro e he h
      apply hb2
      simp only [B2, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
      exact ⟨α, z, ⟨e.2, by simp [hP, polys]; exact ⟨e.1, he⟩, h⟩, rfl⟩
    refine ⟨hd, fun hs => ?_⟩
    have hc : ¬ Coll P α := fun h => hb1 (by simp [B1, mem_collSet h])
    by_contra hnb
    simp only [PolyBalanced, not_forall] at hnb
    obtain ⟨u₀, hu₀⟩ := hnb
    apply hb3
    simp only [B3, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨α, ?_⟩
    rw [if_neg hc, Finset.mem_image]
    refine ⟨z, ?_, rfl⟩
    rw [Multiset.mem_toFinset, mem_roots (numer_ne_zero es α hc u₀ hu₀)]
    exact numer_root es α z hd hs

end Counting

/-! ### From fingerprints to `Lookup.Balanced` -/

section System

variable {K : Type} [Field K] [DecidableEq K] [Algebra F K]

/-- The fingerprint of a tuple: `Σᵢ tᵢ Xⁱ` (its value at `α` is Stwo's `combine(α, t)`). -/
noncomputable def tuplePoly (t : List F) : K[X] :=
  ∑ i ∈ Finset.range t.length, C (algebraMap F K (t.getD i 0)) * X ^ i

theorem coeff_tuplePoly (t : List F) (n : ℕ) : (tuplePoly (K := K) t).coeff n = algebraMap F K (t.getD n 0) := by
  unfold tuplePoly
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split
  · rfl
  · rename_i h
    rw [Finset.mem_range, not_lt] at h
    rw [List.getD_eq_default _ _ h]; simp

/-- Same-length tuples with the same fingerprint are equal. -/
theorem tuplePoly_inj {t u : List F} (hl : t.length = u.length) (h : tuplePoly (K := K) t = tuplePoly u) :
    t = u := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_tuplePoly] at this
  have := (algebraMap F K).injective this
  rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- A raw lookup entry: relation, values, multiplicity (a site's, or a public one). -/
abbrev Raw := ℕ × List F × F

/-- Its LogUp entry: the multiplicity and the fingerprint of `(rel, vals…)`. -/
noncomputable def toEntry (e : Raw) : Entry K := (algebraMap F K e.2.2, tuplePoly ((e.1 : F) :: e.2.1))

/-- Total multiplicity of `(R, v)` among raw entries. -/
def rawTotal (es : List Raw) (R : ℕ) (v : List F) : F := ((es.filter fun e => e.1 = R ∧ e.2.1 = v).map (·.2.2)).sum

/-- **Per-fingerprint balance gives per-tuple balance**, when each relation has one arity and
relation ids are below `P` (so distinct tuples have distinct fingerprints). -/
theorem raw_balanced (es : List Raw) (har : ∀ e ∈ es, ∀ e' ∈ es, e.1 = e'.1 → e.2.1.length = e'.2.1.length)
    (hrs : ∀ e ∈ es, e.1 < P) (hb : PolyBalanced (es.map (toEntry (K := K)))) (R : ℕ) (v : List F) :
    rawTotal es R v = 0 := by
  by_cases hex : ∃ e₀ ∈ es, e₀.1 = R ∧ e₀.2.1 = v
  · obtain ⟨e₀, he₀, hR₀, hv₀⟩ := hex
    have hsame : ∀ e ∈ es, (toEntry (K := K) e).2 = tuplePoly ((R : F) :: v) ↔ e.1 = R ∧ e.2.1 = v := by
      intro e he
      constructor
      · intro h
        have h0 := congrArg (fun p => p.coeff 0) h
        simp only [toEntry, coeff_tuplePoly, List.getD_cons_zero] at h0
        have hRF : ((e.1 : ℕ) : F) = ((R : ℕ) : F) := (algebraMap F K).injective h0
        have hR : e.1 = R := by
          have h1 := hrs e he
          have h2 := hrs e₀ he₀
          rw [hR₀] at h2
          have := (ZMod.natCast_eq_natCast_iff' e.1 R P).mp hRF
          rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
        have hlen : e.2.1.length = v.length := by rw [← hv₀]; exact har e he e₀ he₀ (hR.trans hR₀.symm)
        refine ⟨hR, ?_⟩
        have := tuplePoly_inj (K := K) (by simp [hlen]) h
        exact (List.cons.inj this).2
      · rintro ⟨hR, hv⟩; simp [toEntry, hR, hv]
    have hp := hb (tuplePoly ((R : F) :: v))
    unfold mult at hp
    rw [List.filter_map, List.map_map] at hp
    have hfilter : es.filter ((fun e : Entry K => decide (e.2 = tuplePoly ((R : F) :: v))) ∘ toEntry) =
        es.filter fun e => e.1 = R ∧ e.2.1 = v := by
      apply List.filter_congr
      intro e he
      simp only [Function.comp, decide_eq_decide]
      exact hsame e he
    rw [hfilter] at hp
    have : algebraMap F K (rawTotal es R v) = 0 := by
      rw [rawTotal, ← hp, map_list_sum, List.map_map]; rfl
    exact (map_eq_zero_iff _ (algebraMap F K).injective).mp this
  · unfold rawTotal
    rw [List.filter_eq_nil_iff.mpr]
    · simp
    · intro e he h
      exact hex ⟨e, he, by simpa using h⟩

variable (sys : System) (inst : ℕ → Inst) (pub : ℕ → F)

/-- A system instance's raw entries: one per site. -/
def siteRaw : List Raw := (sites sys inst).map fun s => (siteRel sys s, siteVals sys inst pub s, siteMult sys inst pub s)

theorem total_eq_raw (R : ℕ) (v : List F) : total sys inst pub R v = rawTotal (siteRaw sys inst pub) R v := by
  unfold total rawTotal siteRaw
  rw [List.filter_map, List.map_map]
  rfl

/-- **`Balanced` from per-fingerprint balance** (relations of one arity, small ids). -/
theorem balanced_of_poly (har : ∀ e ∈ siteRaw sys inst pub, ∀ e' ∈ siteRaw sys inst pub, e.1 = e'.1 → e.2.1.length = e'.2.1.length)
    (hrs : ∀ e ∈ siteRaw sys inst pub, e.1 < P)
    (hb : PolyBalanced ((siteRaw sys inst pub).map (toEntry (K := K)))) : Balanced sys inst pub := by
  intro R v
  rw [total_eq_raw]
  exact raw_balanced _ har hrs hb R v

/-- **`BalancedExt` from per-fingerprint balance**, the public entries included. -/
theorem balancedExt_of_poly (ext : PubEntries)
    (har : ∀ e ∈ siteRaw sys inst pub ++ ext, ∀ e' ∈ siteRaw sys inst pub ++ ext, e.1 = e'.1 → e.2.1.length = e'.2.1.length)
    (hrs : ∀ e ∈ siteRaw sys inst pub ++ ext, e.1 < P)
    (hb : PolyBalanced ((siteRaw sys inst pub ++ ext).map (toEntry (K := K)))) : BalancedExt sys inst pub ext := by
  intro R v
  have := raw_balanced _ har hrs hb R v
  rw [total_eq_raw]
  unfold rawTotal at this ⊢
  unfold extTotal
  rw [List.filter_append, List.map_append, List.sum_append] at this
  exact this

/-! ### Static side conditions (decidable per system) -/

/-- Lookup shapes: `(relation, arity)` of every lookup of every component. -/
def shapes (sys : System) : List (ℕ × ℕ) :=
  (List.range sys.m).flatMap fun i => (sys.comp i).lookups.map fun l => (l.rel, l.vals.length)

/-- Each relation has one arity, and ids are below `P`: checkable by `decide` on a concrete system. -/
def StaticOk (sys : System) : Bool :=
  (shapes sys).all fun a => decide (a.1 < P) && (shapes sys).all fun b => a.1 != b.1 || a.2 == b.2

theorem siteRaw_shape {sys : System} {inst : ℕ → Inst} {pub : ℕ → F} {e : Raw} (he : e ∈ siteRaw sys inst pub) :
    (e.1, e.2.1.length) ∈ shapes sys := by
  simp only [siteRaw, List.mem_map] at he
  obtain ⟨s, hs, rfl⟩ := he
  simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map] at hs
  obtain ⟨i, hi, r, -, k, hk, rfl⟩ := hs
  simp only [shapes, List.mem_flatMap, List.mem_range, List.mem_map]
  refine ⟨i, hi, (sys.comp i).lookups[k], List.getElem_mem hk, ?_⟩
  simp [siteRel, siteVals, siteLookup, List.getElem?_eq_getElem hk]

theorem static_ok {sys : System} (h : StaticOk sys = true) {inst : ℕ → Inst} {pub : ℕ → F} :
    (∀ e ∈ siteRaw sys inst pub, ∀ e' ∈ siteRaw sys inst pub, e.1 = e'.1 → e.2.1.length = e'.2.1.length) ∧
    (∀ e ∈ siteRaw sys inst pub, e.1 < P) := by
  simp only [StaticOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at h
  refine ⟨fun e he e' he' hr => ?_, fun e he => (h _ (siteRaw_shape he)).1⟩
  rcases (h _ (siteRaw_shape he)).2 _ (siteRaw_shape he') with h1 | h1
  · exact absurd hr h1
  · exact h1

end System

end StarkedAir.LogUpSZ
