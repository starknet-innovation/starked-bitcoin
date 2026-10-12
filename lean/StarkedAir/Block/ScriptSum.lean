/-
**The block's sigops (M3a.5d), system level.** The walker's script uses and the fields' script yields
balance, so they are the same multiset of `(start, length)` tuples; summing the scripts' legacy sigops
over both, the walker's total is the tokens' `sumSig`, the block's legacy sigop count.
-/
import StarkedAir.Block.SysLink
import StarkedAir.Block.FieldsScripts
import StarkedAir.LookupCount
import StarkedAir.Spec.SigBound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

/-- The script relation's sites: the fields' yield (lookup 30) and the walker's use (lookup 0). -/
def scriptOK : Bool :=
  (List.range 15).all fun i => (List.range (hashSys.comp i).lookups.length).all fun k =>
    relAt i k != 11 || (i == 1 && k == 30) || (i == 6 && k == 0)

theorem scriptOK_true : scriptOK = true := by decide

theorem script_rel {i k : ℕ} (hi : i < 15) (hk : k < (hashSys.comp i).lookups.length) (h : relAt i k = 11) :
    (i = 1 ∧ k = 30) ∨ (i = 6 ∧ k = 0) := by
  have hh := scriptOK_true
  simp only [scriptOK, List.all_eq_true, List.mem_range] at hh
  have := hh i hi k hk
  simp only [h, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

theorem list_sum_filter_range {β : Type} [AddCommMonoid β] (p : ℕ → Prop) [DecidablePred p] (f : ℕ → β) :
    ∀ n, (((List.range n).filter p).map f).sum = ∑ r ∈ (Finset.range n).filter p, f r
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, list_sum_filter_range p f n,
      Finset.range_add_one, Finset.filter_insert]
    by_cases hp : p n
    · rw [if_pos hp, Finset.sum_insert (by simp)]; simp [hp, add_comm]
    · rw [if_neg hp]; simp [hp]

theorem eq_single_of_nodup {l : List ℕ} {a : ℕ} (hn : l.Nodup) (ha : a ∈ l) (hall : ∀ x ∈ l, x = a) : l = [a] := by
  match l, hn, ha with
  | b :: t, hn, _ =>
    have hb := hall b (by simp); subst hb
    cases t with
    | nil => rfl
    | cons c t =>
      have hc := hall c (by simp); subst hc
      simp at hn

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

/-- **Sites of one lookup.** Filtering the sites by a predicate true only at lookup `k0` of component `i0`
leaves that lookup's rows. -/
theorem filter_sites {P : Site → Prop} [DecidablePred P] {i0 k0 : ℕ} (hi0 : i0 < 15)
    (hP : ∀ i r k, i < 15 → r < 2 ^ Ls i → k < (hashSys.comp i).lookups.length → P (i, r, k) → i = i0 ∧ k = k0)
    (hk0 : k0 < (hashSys.comp i0).lookups.length) :
    (sites hashSys inst).filter P = ((List.range (2 ^ Ls i0)).filter fun r => P (i0, r, k0)).map fun r => (i0, r, k0) := by
  unfold sites
  rw [show hashSys.m = 15 from rfl, List.filter_flatMap]
  have inner : ∀ i < 15, ((List.range (2 ^ (inst i).logSize)).flatMap fun r =>
      (List.range (hashSys.comp i).lookups.length).map fun k => ((i, r, k) : Site)).filter P =
      if i = i0 then ((List.range (2 ^ Ls i0)).filter fun r => P (i0, r, k0)).map fun r => (i0, r, k0) else [] := by
    intro i hi
    rw [hL i hi, List.filter_flatMap]
    have hk : ∀ r < 2 ^ Ls i, ((List.range (hashSys.comp i).lookups.length).map fun k => ((i, r, k) : Site)).filter P =
        if i = i0 ∧ P (i0, r, k0) then [(i0, r, k0)] else [] := by
      intro r hr
      rw [List.filter_map]
      split_ifs with hc
      · obtain ⟨rfl, hp⟩ := hc
        have e : (List.range (hashSys.comp i).lookups.length).filter (P ∘ fun k => ((i, r, k) : Site)) = [k0] := by
          refine eq_single_of_nodup (List.nodup_range.filter _)
            (List.mem_filter.mpr ⟨List.mem_range.mpr hk0, by simpa using hp⟩) (fun k hk => ?_)
          obtain ⟨hkr, hkp⟩ := List.mem_filter.mp hk
          exact (hP i r k hi hr (List.mem_range.mp hkr) (by simpa using hkp)).2
        rw [e]; rfl
      · apply List.eq_nil_of_length_eq_zero
        rw [List.length_map, List.length_eq_zero_iff, List.filter_eq_nil_iff]
        intro k hk hpk
        have := hP i r k hi hr (List.mem_range.mp hk) (by simpa using hpk)
        obtain ⟨rfl, rfl⟩ := this
        exact hc ⟨rfl, by simpa using hpk⟩
    rw [List.flatMap_congr (fun r hr => hk r (List.mem_range.mp hr))]
    split_ifs with hi0'
    · subst hi0'
      simp only [true_and]
      induction (2 ^ Ls i) with
      | zero => simp
      | succ q ih =>
        rw [List.range_succ, List.flatMap_append, ih, List.filter_append, List.map_append]
        by_cases h : P (i, q, k0) <;> simp [h]
    · simp [hi0']
  rw [List.flatMap_congr (fun i hi => inner i (List.mem_range.mp hi))]
  interval_cases i0 <;> simp [List.range_succ]

theorem balanced : Balanced hashSys inst pub := fun R v => by
  have := hsat.2 R v; simpa [extTotal] using this

/-- **Script multiplicities**: the fields' yield is `smult ∈ {0, 1}`, the walker's use `−FS ∈ {0, −1}`. -/
theorem script_mult1 {r : ℕ} (hr : r < 2 ^ Ls 1) :
    siteMult hashSys inst pub (1, r, 30) = Fields.smult (inst 1).main r := by
  simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
  simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, Fields.oneMinus, Fields.one,
    StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, Fields.smult]

theorem script_mult6 {r : ℕ} (hr : r < 2 ^ Ls 6) :
    siteMult hashSys inst pub (6, r, 0) = -(inst 6).main Walk.FS r := by
  simp only [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide)]
  simp [Walk.walk, Walk.lookups, Expr.eval, Walk.k, StarkedAir.Sha256.eval_col, wrap_zero hr]

theorem script_vals1 {r : ℕ} (hr : r < 2 ^ Ls 1) :
    siteVals hashSys inst pub (1, r, 30) = [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r] := by
  simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
    Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]

theorem script_vals6 {r : ℕ} (hr : r < 2 ^ Ls 6) :
    siteVals hashSys inst pub (6, r, 0) = [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r] := by
  simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
    StarkedAir.Sha256.eval_col, wrap_zero hr]

/-- **The script multiset**: for any `g`, summing over the fields' yielded scripts equals summing over the
walker's first rows. -/
theorem script_sum (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => Fields.smult (inst 1).main r = 1),
      g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r] =
    ∑ r ∈ (Finset.range (2 ^ Ls 6)).filter (fun r => (inst 6).main Walk.FS r = 1),
      g [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r] := by
  classical
  have fs := hash_fields_sat' hL hsat
  have ws : ∀ r < 2 ^ Ls 6, ∀ c ∈ Walk.constraints, c.eval (2 ^ Ls 6) Walk.preCols pub (inst 6).main r = 0 := by
    have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this
  have n1 : (1 : F) ≠ -1 := by
    intro h
    have : (2 : F) = 0 := by linear_combination h
    have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) (by simpa using this)
    omega
  -- the relation's sites
  have rel11 : ∀ i r k, i < 15 → r < 2 ^ Ls i → k < (hashSys.comp i).lookups.length →
      siteRel hashSys (i, r, k) = 11 → (i = 1 ∧ k = 30) ∨ (i = 6 ∧ k = 0) := fun i r k hi _ hk h =>
    script_rel hi hk h
  have hm : ∀ s ∈ sites hashSys inst, siteRel hashSys s = 11 →
      siteMult hashSys inst pub s = 0 ∨ siteMult hashSys inst pub s = 1 ∨ siteMult hashSys inst pub s = -1 := by
    rintro ⟨i, r, k⟩ hs h
    obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
    rcases rel11 i r k hi hr hk h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [script_mult1 hL hsat hL24 hr]
      rcases Fields.smult01 fs hr with e | e <;> simp [e]
    · rw [script_mult6 hL hsat hL24 hr]
      rcases Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hr with e | e <;> simp [e]
  have hP : (sites hashSys inst).length < P := by rw [hash_sites_len hL]; exact hash_rows_lt_P hL24
  have heq := yields_eq_uses (balanced hL hsat hL24) hm hP
  have hsum := congrArg (fun M : Multiset (List F) => (M.map g).sum) heq
  simp only [tuplesWith, Multiset.map_coe, Multiset.sum_coe, List.map_map] at hsum
  -- the yields
  rw [filter_sites hL hsat hL24 (i0 := 1) (k0 := 30) (by decide) (fun i r k hi hr hk hp => by
      rcases rel11 i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exfalso
        have := hp.2; rw [script_mult6 hL hsat hL24 hr] at this
        rcases Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hr with e | e <;> rw [e] at this
        · simp at this
        · exact n1 this.symm)
    (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])] at hsum
  rw [filter_sites hL hsat hL24 (i0 := 6) (k0 := 0) (by decide) (fun i r k hi hr hk hp => by
      rcases rel11 i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have := hp.2; rw [script_mult1 hL hsat hL24 hr] at this
        rcases Fields.smult01 fs hr with e | e <;> rw [e] at this
        · have : (1 : F) = 0 := by linear_combination this
          exact one_ne_zero this
        · exact n1 this
      · exact ⟨rfl, rfl⟩)
    (by simp [hashSys, Walk.walk, Walk.lookups])] at hsum
  simp only [List.map_map] at hsum
  rw [list_sum_filter_range, list_sum_filter_range] at hsum
  simp only [Function.comp_def] at hsum
  have e1 : ∀ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => siteRel hashSys (1, r, 30) = 11 ∧
      siteMult hashSys inst pub (1, r, 30) = 1), g (siteVals hashSys inst pub (1, r, 30)) =
      g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r] := by
    intro r hr; rw [script_vals1 hL hsat hL24 (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)]
  have e2 : ∀ r ∈ (Finset.range (2 ^ Ls 6)).filter (fun r => siteRel hashSys (6, r, 0) = 11 ∧
      siteMult hashSys inst pub (6, r, 0) = -1), g (siteVals hashSys inst pub (6, r, 0)) =
      g [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r] := by
    intro r hr; rw [script_vals6 hL hsat hL24 (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at hsum
  have f1 : (Finset.range (2 ^ Ls 1)).filter (fun r => siteRel hashSys (1, r, 30) = 11 ∧
      siteMult hashSys inst pub (1, r, 30) = 1) = (Finset.range (2 ^ Ls 1)).filter (fun r => Fields.smult (inst 1).main r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, -, h⟩; exact ⟨hr, by rw [← script_mult1 hL hsat hL24 hr]; exact h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, rfl, by rw [script_mult1 hL hsat hL24 hr]; exact h⟩
  have f2 : (Finset.range (2 ^ Ls 6)).filter (fun r => siteRel hashSys (6, r, 0) = 11 ∧
      siteMult hashSys inst pub (6, r, 0) = -1) = (Finset.range (2 ^ Ls 6)).filter (fun r => (inst 6).main Walk.FS r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, -, h⟩; rw [script_mult6 hL hsat hL24 hr, neg_inj] at h; exact ⟨hr, h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, rfl, by rw [script_mult6 hL hsat hL24 hr, h]⟩
  rw [f1, f2] at hsum
  exact hsum

end System

end StarkedAir.Block
