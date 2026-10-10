/-
**Balance gives multiset equality.** For a relation whose sites all have multiplicity `0`, `1` or `−1`,
balance says: for every tuple, as many sites yield it with multiplicity `1` as use it with `−1` (when
fewer than `P` sites take part). So the multiset of yielded tuples equals the multiset of used ones, and
any function sums to the same total over both.
-/
import StarkedAir.Lookup

namespace StarkedAir

section Count

variable {sys : System} {inst : ℕ → Inst} {pub : ℕ → F}

/-- The tuples of relation `R` at the sites with multiplicity `m`. -/
def tuplesWith (sys : System) (inst : ℕ → Inst) (pub : ℕ → F) (R : ℕ) (m : F) : Multiset (List F) :=
  (((sites sys inst).filter fun s => siteRel sys s = R ∧ siteMult sys inst pub s = m).map (siteVals sys inst pub) : List _)

theorem count_map_filter {α β : Type} [DecidableEq β] (p : α → Prop) [DecidablePred p] (f : α → β) (v : β) :
    ∀ l : List α, List.count v ((l.filter p).map f) = (l.filter fun a => p a ∧ f a = v).length
  | [] => by simp
  | a :: l => by
    have ih := count_map_filter p f v l
    by_cases hp : p a <;> by_cases hv : f a = v <;> simp [List.filter_cons, hp, hv, ih, List.count_cons]

theorem count_tuplesWith (R : ℕ) (m : F) (v : List F) :
    (tuplesWith sys inst pub R m).count v =
      ((sites sys inst).filter fun s => (siteRel sys s = R ∧ siteMult sys inst pub s = m) ∧ siteVals sys inst pub s = v).length := by
  classical
  rw [tuplesWith, Multiset.coe_count, count_map_filter]

/-- **Yields equal uses**, as multisets. -/
theorem yields_eq_uses (hb : Balanced sys inst pub) {R : ℕ}
    (hm : ∀ s ∈ sites sys inst, siteRel sys s = R →
      siteMult sys inst pub s = 0 ∨ siteMult sys inst pub s = 1 ∨ siteMult sys inst pub s = -1)
    (hP : (sites sys inst).length < P) :
    tuplesWith sys inst pub R 1 = tuplesWith sys inst pub R (-1) := by
  classical
  ext v
  rw [count_tuplesWith, count_tuplesWith]
  -- the total for `(R, v)`: the yields' count minus the uses' count
  set L := (sites sys inst).filter fun s => siteRel sys s = R ∧ siteVals sys inst pub s = v
  have ht := hb R v
  unfold total at ht
  have hsplit : ∀ (l : List Site), (∀ s ∈ l, siteRel sys s = R ∧ siteVals sys inst pub s = v) → (∀ s ∈ l, s ∈ sites sys inst) →
      (l.map (siteMult sys inst pub)).sum =
        ((l.filter fun s => siteMult sys inst pub s = 1).length : F) -
          ((l.filter fun s => siteMult sys inst pub s = -1).length : F) := by
    intro l hl hs
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha := hm a (hs a (List.mem_cons_self ..)) (hl a (List.mem_cons_self ..)).1
      rw [List.map_cons, List.sum_cons, ih (fun s h => hl s (List.mem_cons_of_mem _ h)) (fun s h => hs s (List.mem_cons_of_mem _ h))]
      have n1 : ¬ ((1 : F) = -1) := by
        intro h
        have : (2 : F) = 0 := by linear_combination h
        have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) (by simpa using this)
        omega
      rcases ha with h | h | h
      · simp [List.filter_cons, h]
      · simp [List.filter_cons, h, n1]; ring
      · simp [List.filter_cons, h, n1, Ne.symm n1]; ring
  rw [hsplit L (fun s h => by simpa using (List.mem_filter.mp h).2) (fun s h => (List.mem_filter.mp h).1)] at ht
  have e : ((L.filter fun s => siteMult sys inst pub s = 1).length : F) = ((L.filter fun s => siteMult sys inst pub s = -1).length : F) := by
    linear_combination ht
  have l1 : (L.filter fun s => siteMult sys inst pub s = 1).length < P :=
    lt_of_le_of_lt (le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)) hP
  have l2 : (L.filter fun s => siteMult sys inst pub s = -1).length < P :=
    lt_of_le_of_lt (le_trans (List.length_filter_le _ _) (List.length_filter_le _ _)) hP
  have := natCast_inj_of_lt l1 l2 e
  have c1 : (L.filter fun s => siteMult sys inst pub s = 1).length =
      ((sites sys inst).filter fun s => (siteRel sys s = R ∧ siteMult sys inst pub s = 1) ∧ siteVals sys inst pub s = v).length := by
    simp only [L, List.filter_filter]; congr 1; apply List.filter_congr; intro s _
    by_cases h1 : siteRel sys s = R <;> by_cases h2 : siteMult sys inst pub s = 1 <;>
      by_cases h3 : siteVals sys inst pub s = v <;> simp [h1, h2, h3]
  have c2 : (L.filter fun s => siteMult sys inst pub s = -1).length =
      ((sites sys inst).filter fun s => (siteRel sys s = R ∧ siteMult sys inst pub s = -1) ∧ siteVals sys inst pub s = v).length := by
    simp only [L, List.filter_filter]; congr 1; apply List.filter_congr; intro s _
    by_cases h1 : siteRel sys s = R <;> by_cases h2 : siteMult sys inst pub s = -1 <;>
      by_cases h3 : siteVals sys inst pub s = v <;> simp [h1, h2, h3]
  rw [← c1, ← c2]; exact this

end Count

end StarkedAir
