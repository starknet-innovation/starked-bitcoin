/-
**What the composition program computes (VERIFIER-LEAN step 2c).** For a system of components, the
plain verifier's composition value is the Horner combination, with the random coefficient, of every
component's constraint values at the OODS samples followed by its LogUp batch terms, times `1/Z(oods)`
(the hook). `part_sound` is one component; `sys_sound` the system.
-/
import StarkedAir.Circuit.CompositionLogUp

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

variable {ρ : ℕ → Q}

/-! ### Running gadgets in sequence -/

/-- **Gadgets in sequence.** If each gadget's result holds `spec` of its index whenever its ops hold
(from any start register), so do the sequence's results. -/
theorem seqOuts_sound {spec : ℕ → QM} : ∀ (fs : List (ℕ → Out ℕ)) (n j0 : ℕ),
    (∀ j (hj : j < fs.length), ∀ m, Holds ρ ((fs[j]'hj) m).ops → val ρ ((fs[j]'hj) m).res = spec (j0 + j)) →
    Holds ρ (seqOuts n fs).1 →
    ∀ j < fs.length, val ρ ((seqOuts n fs).2.1.getD j 0) = spec (j0 + j)
  | [], _, _, _, _ => fun j hj => absurd hj (by simp)
  | f :: fs, n, j0, hs, h => by
    simp only [seqOuts] at h ⊢
    rw [holds_append] at h
    intro j hj
    rcases j with _ | j
    · have h0 := hs 0 (by simp) n (by simpa using h.1)
      simpa using h0
    · have := seqOuts_sound fs (f n).next (j0 + 1) (fun j hj m hm => by
        have := hs (j + 1) (by simp; omega) m hm
        simpa [show j0 + (j + 1) = j0 + 1 + j by omega] using this) h.2 j (by simpa using hj)
      simpa [show j0 + 1 + j = j0 + (j + 1) by omega] using this

/-! ### The batches -/

/-- The batch loop of `partProg`. -/
def batchFold (coeff : ℕ) (bx : BatchIn) (acc1 q : ℕ) (B : ℕ) : List Op × ℕ × ℕ :=
  (List.range B).foldl (fun (acc : List Op × ℕ × ℕ) b =>
    let o := batchOps acc.2.2 acc.2.1 coeff b bx; (acc.1 ++ o.ops, o.res, o.next)) ([], acc1, q)

theorem batchFold_sound {coeff : ℕ} {bx : BatchIn} {acc1 q : ℕ} :
    ∀ B, Holds ρ (batchFold coeff bx acc1 q B).1 →
    val ρ (batchFold coeff bx acc1 q B).2.1 = horner (val ρ coeff) (val ρ acc1) ((List.range B).map fun b =>
      batchTerm (fun i => val ρ (bx.m i)) (fun i => val ρ (bx.d i)) (fun i => val ρ (bx.S i)) (val ρ bx.sprev)
        (val ρ bx.shift) bx.L bx.B b) := by
  intro B
  induction B with
  | zero => intro _; simp [batchFold, horner]
  | succ B ih =>
    intro h
    have e : batchFold coeff bx acc1 q (B + 1) =
        let p := batchFold coeff bx acc1 q B
        let o := batchOps p.2.2 p.2.1 coeff B bx
        (p.1 ++ o.ops, o.res, o.next) := by
      unfold batchFold; rw [List.range_succ, List.foldl_append]; rfl
    rw [e] at h ⊢
    simp only at h ⊢
    rw [holds_append] at h
    rw [batch_sound h.2, ih h.1, List.range_succ, List.map_append, List.map_singleton, horner_append]

/-! ### Where a lookup's expressions sit among the roots -/

def lkExprs (l : Lookup) : List Expr := l.mult :: l.vals

theorem flatMap_getElem? : ∀ (ls : List Lookup) (j : ℕ) (hj : j < ls.length) (i : ℕ),
    (ls.flatMap lkExprs)[((ls.take j).map fun l => l.vals.length + 1).sum + i]? =
      if i < (ls[j]'hj).vals.length + 1 then (lkExprs (ls[j]'hj))[i]? else
        (ls.flatMap lkExprs)[((ls.take j).map fun l => l.vals.length + 1).sum + i]?
  | [], _, hj, _ => absurd hj (by simp)
  | l :: ls, 0, _, i => by
    by_cases hi : i < l.vals.length + 1
    · rw [show ((l :: ls)[0]'(by simp)) = l from rfl, if_pos hi, List.take_zero, List.map_nil, List.sum_nil,
        Nat.zero_add, List.flatMap_cons, List.getElem?_append_left (by simpa [lkExprs] using hi)]
    · rw [show ((l :: ls)[0]'(by simp)) = l from rfl, if_neg hi]
  | l :: ls, j + 1, hj, i => by
    have hj' : j < ls.length := by simpa using hj
    have ih := flatMap_getElem? ls j hj' i
    have hl : (lkExprs l).length = l.vals.length + 1 := by simp [lkExprs]
    have e1 : (((l :: ls).take (j + 1)).map fun l => l.vals.length + 1).sum =
        l.vals.length + 1 + ((ls.take j).map fun l => l.vals.length + 1).sum := by simp
    rw [e1, List.flatMap_cons, show (l :: ls)[j + 1]'hj = ls[j]'hj' from rfl, add_assoc,
      List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
    exact ih

/-- Lookup `j`'s entry `i` (`0` the multiplicity, `1 + i` value `i`) is root `lookupAt c j + i`. -/
theorem roots_lookup (c : Comp) (j : ℕ) (hj : j < c.lookups.length) (i : ℕ)
    (hi : i < (c.lookups[j]'hj).vals.length + 1) :
    (compRoots c)[lookupAt c j + i]? = (lkExprs (c.lookups[j]'hj))[i]? := by
  unfold compRoots lookupAt
  rw [add_assoc, List.getElem?_append_right (by omega), show c.air.constraints.length +
    (((c.lookups.take j).map fun l => l.vals.length + 1).sum + i) - c.air.constraints.length =
    ((c.lookups.take j).map fun l => l.vals.length + 1).sum + i by omega]
  have := flatMap_getElem? c.lookups j hj i
  rw [if_pos hi] at this
  exact this

/-! ### One component -/

/-- A root expression's value at the OODS samples. -/
noncomputable def rootVal (ρ : ℕ → Q) (pr : PartRegs) (e : Expr) : QM := e.evalR cstQ (leafQ ρ pr.ci) (pubQ ρ pr.ci)

noncomputable def secureVal (l : ℕ → QM) : QM := l 0 + l 1 * e1 + l 2 * e2 + l 3 * e3

def lk (c : Comp) (j : ℕ) : Lookup := c.lookups.getD j ⟨0, .const 0, []⟩

/-- **A component's terms**: its constraints, then (with lookups) its batch terms, over QM31. -/
noncomputable def partTerms (ρ : ℕ → Q) (c : Comp) (pr : PartRegs) (sh : Shared) : List QM :=
  c.air.constraints.map (rootVal ρ pr) ++
  if c.lookups.isEmpty then [] else
    let L := c.lookups.length
    let B := (L + 1) / 2
    (List.range B).map (batchTerm (fun j => rootVal ρ pr (lk c j).mult)
      (fun j => fingerprint (val ρ sh.alpha) (emb ((lk c j).rel : F)) ((lk c j).vals.map (rootVal ρ pr)) - val ρ sh.z)
      (fun b => secureVal fun k => val ρ (pr.inter (4 * b + k) (if b + 1 = B then 1 else 0)))
      (secureVal fun k => val ρ (pr.inter (4 * (B - 1) + k) 0))
      (val ρ pr.claimed * emb (ninv sh.logSize : F)) L B)

theorem batchTerm_congr {m m' d d' S S' : ℕ → QM} {sp sh sp' sh' : QM} {L B b : ℕ} (hb : b < B) (hBL : B = (L + 1) / 2)
    (hm : ∀ j < L, m j = m' j) (hd : ∀ j < L, d j = d' j) (hS : ∀ i < B, S i = S' i) (hsp : sp = sp') (hsh : sh = sh') :
    batchTerm m d S sp sh L B b = batchTerm m' d' S' sp' sh' L B b := by
  have h2b : 2 * b < L := by omega
  subst hsp hsh
  unfold batchTerm
  simp only
  rw [hm _ h2b, hd _ h2b, hS _ hb]
  by_cases hp : 2 * b + 1 < L
  · simp only [if_pos hp]; rw [hm _ hp, hd _ hp]
    by_cases hl : b + 1 < B
    · simp only [if_pos hl]; split_ifs with h0
      · rfl
      · rw [hS _ (by omega)]
    · simp only [if_neg hl]; split_ifs with h1
      · rfl
      · rw [hS _ (by omega)]
  · simp only [if_neg hp]
    by_cases hl : b + 1 < B
    · simp only [if_pos hl]; split_ifs with h0
      · rfl
      · rw [hS _ (by omega)]
    · simp only [if_neg hl]; split_ifs with h1
      · rfl
      · rw [hS _ (by omega)]

section PartSound

variable {c : Comp} {pr : PartRegs} {sh : Shared} {n accIn : ℕ}
  (hwf : WF (pNodes c)) (hids : ∀ id ∈ pIds c, id < (pNodes c).size)
include hwf hids

/-- Each root's register holds the root's value. -/
theorem root_val (h : Holds ρ (dagOps n (pNodes c) pr.ci)) :
    ∀ r (hr : r < (compRoots c).length), val ρ (pReg c pr n ((pIds c).getD r 0)) = rootVal ρ pr ((compRoots c)[r]'hr) := by
  intro r hr
  have h0 : Inv cstQ (leafQ ρ pr.ci) (pubQ ρ pr.ci) ({} : DagState) := fun e id h => by simp at h
  obtain ⟨-, -, hlen, hv⟩ := emitAll_correct cstQ (leafQ ρ pr.ci) (pubQ ρ pr.ci) (compRoots c) {} h0
  obtain ⟨id, hid, hval⟩ := hv r hr
  have hg : (pIds c).getD r 0 = id := by
    simp only [pIds, compDag, List.getD_eq_getElem?_getD, hid, Option.getD_some]
  rw [hg]
  have hmem : id ∈ pIds c := by
    simp only [pIds, compDag]; exact List.mem_of_getElem? hid
  rw [val, pReg, dag_regs hwf h id (hids id hmem)]
  exact hval

theorem cops_sound (h : Holds ρ (pCOps c pr sh n accIn)) :
    val ρ (pAcc1 c n accIn) = horner (val ρ sh.coeff) (val ρ accIn) (c.air.constraints.map (rootVal ρ pr)) := by
  rw [pCOps, holds_append] at h
  have hlenIds : (pIds c).length = (compRoots c).length := by
    have h0 : Inv cstQ (leafQ ρ pr.ci) (pubQ ρ pr.ci) ({} : DagState) := fun e id h => by simp at h
    exact (emitAll_correct cstQ (leafQ ρ pr.ci) (pubQ ρ pr.ci) (compRoots c) {} h0).2.2.1
  have hnc : pNc c ≤ (compRoots c).length := by simp [pNc, compRoots]
  have hh := horner_regs h.2 (pNc c) (by simp only [List.length_map, List.length_take]; omega)
  rw [pAcc1]
  simp only [val]
  rw [hh, List.take_of_length_le (by simp [List.length_take])]
  congr 1
  have hpn : pNc c = c.air.constraints.length := rfl
  apply List.ext_getElem (by simp only [List.length_map, List.length_take]; rw [hlenIds]; omega)
  intro k h1 h2
  have hk : k < pNc c := by simpa [pNc] using h2
  simp only [List.getElem_map, List.getElem_take]
  have := root_val hwf hids h.1 k (by omega)
  rw [show (pIds c)[k] = (pIds c).getD k 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < (pIds c).length by omega)]]
  simp only [val] at this
  rw [this]
  congr 1
  simp [compRoots, List.getElem_append_left (show k < c.air.constraints.length by simpa [pNc] using hk)]

theorem mults_val (h : Holds ρ (dagOps n (pNodes c) pr.ci)) {j : ℕ} (hj : j < c.lookups.length) :
    val ρ (pMults c pr n j) = rootVal ρ pr (lk c j).mult := by
  have hr := roots_lookup c j hj 0 (by omega)
  have hlt : lookupAt c j + 0 < (compRoots c).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hr; simp [lkExprs] at hr
  rw [pMults, pIdAt, show lookupAt c j = lookupAt c j + 0 from rfl, root_val hwf hids h _ hlt]
  rw [List.getElem?_eq_getElem hlt] at hr
  simp only [lkExprs, List.getElem?_cons_zero, Option.some.injEq] at hr
  rw [hr, lk, List.getD_eq_getElem _ _ hj]

theorem vals_val (h : Holds ρ (dagOps n (pNodes c) pr.ci)) {j : ℕ} (hj : j < c.lookups.length) :
    (pValsOf c pr n j).map (val ρ) = (lk c j).vals.map (rootVal ρ pr) := by
  have hlk : lk c j = c.lookups[j] := by rw [lk, List.getD_eq_getElem _ _ hj]
  apply List.ext_getElem (by simp [pValsOf, hlk, List.getElem?_eq_getElem hj])
  intro i h1 h2
  have hi : i < (c.lookups[j]).vals.length := by simpa [pValsOf, List.getElem?_eq_getElem hj] using h1
  have hr := roots_lookup c j hj (1 + i) (by omega)
  have hlt : lookupAt c j + (1 + i) < (compRoots c).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hr
    rw [show 1 + i = i + 1 by omega] at hr; simp [lkExprs, hi] at hr
  simp only [List.getElem_map, pValsOf, List.getElem_range]
  rw [pIdAt, show lookupAt c j + 1 + i = lookupAt c j + (1 + i) by omega, root_val hwf hids h _ hlt]
  have hr2 : (lkExprs (c.lookups[j]))[1 + i]? = some ((c.lookups[j]).vals[i]) := by
    rw [show 1 + i = i + 1 by omega]; simp [lkExprs, hi]
  rw [List.getElem?_eq_getElem hlt, hr2, Option.some.injEq] at hr
  rw [hr]; simp [hlk]

theorem bt_eq : pBt c pr sh n accIn = batchFold sh.coeff (pBx c pr sh n) (pAcc1 c n accIn) (pQ c pr sh n + 2) (pB c) := rfl

set_option maxHeartbeats 400000 in
/-- **A component's composition terms are sound.** If its ops hold, the accumulator after it is the
Horner combination, from the incoming accumulator, of its constraints' values and its LogUp batch
terms at the OODS samples. -/
theorem part_sound (h : Holds ρ (partProg c pr sh n accIn).ops)
    (hq : c.lookups.isEmpty = false → val ρ (pQ c pr sh n) = emb (ninv sh.logSize : F)) :
    val ρ (partProg c pr sh n accIn).res = horner (val ρ sh.coeff) (val ρ accIn) (partTerms ρ c pr sh) := by
  unfold partProg at h
  unfold partProg partTerms
  by_cases hE : c.lookups.isEmpty
  · simp only [hE, if_true, List.append_nil] at h ⊢
    exact cops_sound hwf hids h
  simp only [hE, if_false, Bool.false_eq_true] at h ⊢
  rw [holds_append, holds_append, holds_append, holds_append, holds_append] at h
  obtain ⟨⟨⟨⟨⟨hc, hd⟩, hs⟩, hp⟩, hsh⟩, hb⟩ := h
  have hdag : Holds ρ (dagOps n (pNodes c) pr.ci) := by rw [pCOps, holds_append] at hc; exact hc.1
  have hL : 0 < c.lookups.length := by
    rcases hl : c.lookups with _ | ⟨x, xs⟩
    · simp [hl] at hE
    · simp
  rw [bt_eq hwf hids] at hb ⊢
  rw [batchFold_sound _ hb, cops_sound hwf hids hc, horner_concat]
  refine congrArg _ ?_
  apply List.ext_getElem (by simp [pB, pL])
  intro b h1 h2
  have hbB : b < pB c := by simpa using h1
  simp only [List.getElem_map, List.getElem_range]
  refine batchTerm_congr (sp := val ρ (pBx c pr sh n).sprev) (sh := val ρ (pBx c pr sh n).shift) hbB rfl ?_ ?_ ?_ ?_ ?_
  · intro j hj; exact mults_val hwf hids hdag hj
  · intro j hj
    have hj' : j < c.lookups.length := hj
    have hseq := seqOuts_sound (ρ := ρ) (spec := fun j => fingerprint (val ρ sh.alpha) (emb ((lk c j).rel : F))
      ((lk c j).vals.map (rootVal ρ pr)) - val ρ sh.z) _ (pP0 c n) 0 (fun j' hj' m hm => by
        simp only [List.getElem_map, List.getElem_range] at hm ⊢
        have hj'' : j' < c.lookups.length := by simpa [pL] using hj'
        rw [den_sound hm, vals_val hwf hids hdag hj'', zero_add, lk]) hd j (by simpa [pL] using hj')
    simp only [pBx, pDens] at hseq ⊢
    simpa using hseq
  · intro i hi
    have hi' : i < pB c := hi
    have hseq := seqOuts_sound (ρ := ρ) (spec := fun b => secureVal fun k =>
      val ρ (pr.inter (4 * b + k) (if b + 1 = pB c then 1 else 0))) _ _ 0 (fun j' hj' m hm => by
        simp only [List.getElem_map, List.getElem_range] at hm ⊢
        rw [secure_sound hm, zero_add, secureVal]) hs i (by simpa using hi')
    simp only [pBx, pSS] at hseq ⊢
    simpa [pB, pL] using hseq
  · simp only [pBx]
    unfold pSp at hp ⊢
    rw [secure_sound hp, secureVal]
    simp [pB, pL]
  · simp only [pBx]
    have m1 := hsh (.mul (pQ c pr sh n + 1) pr.claimed (pQ c pr sh n)) (by simp [pShOps])
    simp only [Op.holds] at m1
    have hq' := hq (by simpa using hE)
    simp only [val] at hq' ⊢
    rw [m1, toQ_mul, hq']

end PartSound

end StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

variable {ρ : ℕ → Q}

/-! ### The system -/

/-- `sysProg`'s fold over components. -/
def partFold (sh : Shared) (parts : List (Comp × PartRegs)) (s : List Op × ℕ × ℕ) : List Op × ℕ × ℕ :=
  parts.foldl (fun (acc : List Op × ℕ × ℕ) p =>
    let o := partProg p.1 p.2 sh acc.2.2 acc.2.1; (acc.1 ++ o.ops, o.res, o.next)) s

theorem partFold_prefix (sh : Shared) : ∀ (parts : List (Comp × PartRegs)) (s : List Op × ℕ × ℕ),
    ∃ rest, (partFold sh parts s).1 = s.1 ++ rest
  | [], s => ⟨[], by simp [partFold]⟩
  | p :: ps, s => by
    obtain ⟨rest, hr⟩ := partFold_prefix sh ps (s.1 ++ (partProg p.1 p.2 sh s.2.2 s.2.1).ops,
      (partProg p.1 p.2 sh s.2.2 s.2.1).res, (partProg p.1 p.2 sh s.2.2 s.2.1).next)
    exact ⟨(partProg p.1 p.2 sh s.2.2 s.2.1).ops ++ rest, by
      simp only [partFold, List.foldl_cons] at hr ⊢; rw [hr, List.append_assoc]⟩

theorem partFold_sound (sh : Shared) : ∀ (parts : List (Comp × PartRegs)) (s : List Op × ℕ × ℕ),
    (∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size) →
    (∀ q, Op.hook 2 [] [q] ∈ (partFold sh parts s).1 → val ρ q = emb (ninv sh.logSize : F)) →
    Holds ρ (partFold sh parts s).1 →
    val ρ (partFold sh parts s).2.1 = horner (val ρ sh.coeff) (val ρ s.2.1) (parts.flatMap fun p => partTerms ρ p.1 p.2 sh)
  | [], s, _, _, _ => by simp [partFold, horner]
  | p :: ps, s, hw, hn, h => by
    set o := partProg p.1 p.2 sh s.2.2 s.2.1 with ho
    have e : partFold sh (p :: ps) s = partFold sh ps (s.1 ++ o.ops, o.res, o.next) := by
      simp [partFold, ho]
    rw [e] at h hn ⊢
    obtain ⟨rest, hr⟩ := partFold_prefix sh ps (s.1 ++ o.ops, o.res, o.next)
    have hops : Holds ρ o.ops := by
      rw [hr] at h; simp only at h
      rw [holds_append, holds_append] at h; exact h.1.2
    obtain ⟨hwf, hids⟩ := hw p (by simp)
    rw [partFold_sound sh ps _ (fun q hq => hw q (by simp [hq])) hn h]
    simp only
    have hq : p.1.lookups.isEmpty = false → val ρ (pQ p.1 p.2 sh s.2.2) = emb (ninv sh.logSize : F) := by
      intro hE
      exact hn _ (by
        rw [hr]; simp only
        apply List.mem_append_left; apply List.mem_append_right
        simp only [ho, partProg, hE, if_false, Bool.false_eq_true, pShOps]
        simp)
    rw [part_sound hwf hids hops hq, List.flatMap_cons, horner_concat]

/-- **The composition check is sound.** If the system program holds, its result is the Horner
combination, from 0 with the coefficient, of every component's constraint values and LogUp batch terms at
the OODS samples, in component order, times the value of hook 1 (stwo-zig's `1/Z(oods)`). -/
theorem sys_sound {parts : List (Comp × PartRegs)} {sh : Shared} {nIn oodsX : ℕ}
    (hw : ∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size)
    (hninv : ∀ q, Op.hook 2 [] [q] ∈ (sysProg parts sh nIn oodsX).1 → val ρ q = emb (ninv sh.logSize : F))
    (h : Holds ρ (sysProg parts sh nIn oodsX).1) :
    val ρ (sysProg parts sh nIn oodsX).2 =
      horner (val ρ sh.coeff) 0 (parts.flatMap fun p => partTerms ρ p.1 p.2 sh) *
        val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2 := by
  have e : sysProg parts sh nIn oodsX =
      ([.hook 0 [] (List.range nIn), .zero nIn] ++ (partFold sh parts ([], nIn, nIn + 1)).1 ++
        [.hook 1 [oodsX] [(partFold sh parts ([], nIn, nIn + 1)).2.2],
         .mul ((partFold sh parts ([], nIn, nIn + 1)).2.2 + 1) (partFold sh parts ([], nIn, nIn + 1)).2.1
           (partFold sh parts ([], nIn, nIn + 1)).2.2], (partFold sh parts ([], nIn, nIn + 1)).2.2 + 1) := rfl
  rw [e] at h hninv ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨⟨h0, hf⟩, h1⟩ := h
  have hz : val ρ nIn = 0 := by
    have := h0 (.zero nIn) (by simp); simp only [Op.holds] at this; rw [val, this, toQ_lit0]
  have hm := h1 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Op.holds] at hm
  simp only [val] at hz ⊢
  rw [hm, toQ_mul]
  have := partFold_sound sh parts ([], nIn, nIn + 1) hw (fun q hq => hninv q (by
    apply List.mem_append_left; apply List.mem_append_right; exact hq)) hf
  simp only [val] at this
  rw [this, hz]

/-! ### Per-component trace sizes (D-045)

The composition program never contains a size: hook 2 (`1/2^L`) is the host's constant. With
per-component sizes the host answers part `i`'s hook 2 with `1/2^(Ls i)`; `HookOk` states that, and the
terms of part `i` use `Ls i` (`shAt`). The ops are those of `sysProg` unchanged (`partProg_shAt`). -/

/-- The shared registers with part `k`'s size. -/
def shAt (sh : Shared) (k : ℕ) : Shared := { sh with logSize := k }

theorem shAt_self (sh : Shared) : shAt sh sh.logSize = sh := rfl

/-- A part's program does not depend on the size. -/
theorem partProg_shAt (c : Comp) (pr : PartRegs) (sh : Shared) (k n accIn : ℕ) :
    partProg c pr (shAt sh k) n accIn = partProg c pr sh n accIn := rfl

/-- **The host's hook 2, per part**: along `sysProg`'s fold from state `s`, part `i` (with lookups) has its
hook-2 register holding `1/2^(Ls i)`. -/
def HookOk (ρ : ℕ → Q) (sh : Shared) : (ℕ → ℕ) → List (Comp × PartRegs) → List Op × ℕ × ℕ → Prop
  | _, [], _ => True
  | Ls, p :: ps, s => (p.1.lookups.isEmpty = false → val ρ (pQ p.1 p.2 sh s.2.2) = emb (ninv (Ls 0) : F)) ∧
      HookOk ρ sh (fun j => Ls (j + 1)) ps (s.1 ++ (partProg p.1 p.2 sh s.2.2 s.2.1).ops,
        (partProg p.1 p.2 sh s.2.2 s.2.1).res, (partProg p.1 p.2 sh s.2.2 s.2.1).next)

/-- Part `i`'s terms, at its own size. -/
noncomputable def termsV (ρ : ℕ → Q) (sh : Shared) (Ls : ℕ → ℕ) (parts : List (Comp × PartRegs)) : List QM :=
  (parts.mapIdx fun i p => partTerms ρ p.1 p.2 (shAt sh (Ls i))).flatten

theorem termsV_cons (ρ : ℕ → Q) (sh : Shared) (Ls : ℕ → ℕ) (p : Comp × PartRegs) (ps : List (Comp × PartRegs)) :
    termsV ρ sh Ls (p :: ps) = partTerms ρ p.1 p.2 (shAt sh (Ls 0)) ++ termsV ρ sh (fun j => Ls (j + 1)) ps := by
  simp [termsV, List.mapIdx_cons]

theorem mapIdx_const {α β : Type} (f : α → β) : ∀ l : List α, l.mapIdx (fun _ a => f a) = l.map f
  | [] => rfl
  | a :: l => by rw [List.mapIdx_cons, List.map_cons, mapIdx_const f l]

/-- At one size the terms are `sys_sound`'s. -/
theorem termsV_const (ρ : ℕ → Q) (sh : Shared) (parts : List (Comp × PartRegs)) :
    termsV ρ sh (fun _ => sh.logSize) parts = parts.flatMap fun p => partTerms ρ p.1 p.2 sh := by
  have h := mapIdx_const (fun p : Comp × PartRegs => partTerms ρ p.1 p.2 sh) parts
  simp only [termsV, shAt_self]
  rw [h]; exact List.flatMap_def.symm

theorem partFold_soundV (sh : Shared) : ∀ (Ls : ℕ → ℕ) (parts : List (Comp × PartRegs)) (s : List Op × ℕ × ℕ),
    (∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size) →
    HookOk ρ sh Ls parts s →
    Holds ρ (partFold sh parts s).1 →
    val ρ (partFold sh parts s).2.1 = horner (val ρ sh.coeff) (val ρ s.2.1) (termsV ρ sh Ls parts)
  | _, [], s, _, _, _ => by simp [partFold, horner, termsV]
  | Ls, p :: ps, s, hw, hk, h => by
    set o := partProg p.1 p.2 sh s.2.2 s.2.1 with ho
    have e : partFold sh (p :: ps) s = partFold sh ps (s.1 ++ o.ops, o.res, o.next) := by
      simp [partFold, ho]
    rw [e] at h ⊢
    obtain ⟨hq, hk'⟩ := hk
    obtain ⟨rest, hr⟩ := partFold_prefix sh ps (s.1 ++ o.ops, o.res, o.next)
    have hops : Holds ρ o.ops := by
      rw [hr] at h; simp only at h
      rw [holds_append, holds_append] at h; exact h.1.2
    obtain ⟨hwf, hids⟩ := hw p (by simp)
    rw [partFold_soundV sh _ ps _ (fun q hq => hw q (by simp [hq])) hk' h]
    simp only
    rw [termsV_cons, horner_concat]
    congr 1
    exact part_sound (sh := shAt sh (Ls 0)) hwf hids hops hq

/-- At one size, today's hook hypothesis (every hook 2 gives `1/2^L`) is `HookOk` at the constant vector. -/
theorem hookOk_of_const (sh : Shared) : ∀ (parts : List (Comp × PartRegs)) (s : List Op × ℕ × ℕ),
    (∀ q, Op.hook 2 [] [q] ∈ (partFold sh parts s).1 → val ρ q = emb (ninv sh.logSize : F)) →
    HookOk ρ sh (fun _ => sh.logSize) parts s
  | [], _, _ => trivial
  | p :: ps, s, hn => by
    set o := partProg p.1 p.2 sh s.2.2 s.2.1 with ho
    have e : partFold sh (p :: ps) s = partFold sh ps (s.1 ++ o.ops, o.res, o.next) := by
      simp [partFold, ho]
    rw [e] at hn
    obtain ⟨rest, hr⟩ := partFold_prefix sh ps (s.1 ++ o.ops, o.res, o.next)
    refine ⟨fun hE => hn _ ?_, hookOk_of_const sh ps _ hn⟩
    rw [hr]; simp only
    apply List.mem_append_left; apply List.mem_append_right
    simp only [ho, partProg, hE, if_false, Bool.false_eq_true, pShOps]
    simp

/-- **The composition check is sound, per-component sizes.** As `sys_sound`, with part `i`'s claimed sum
shared over its own `2^(Ls i)` rows (`HookOk`). -/
theorem sys_soundV {parts : List (Comp × PartRegs)} {sh : Shared} {nIn oodsX : ℕ} (Ls : ℕ → ℕ)
    (hw : ∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size)
    (hk : HookOk ρ sh Ls parts ([], nIn, nIn + 1))
    (h : Holds ρ (sysProg parts sh nIn oodsX).1) :
    val ρ (sysProg parts sh nIn oodsX).2 =
      horner (val ρ sh.coeff) 0 (termsV ρ sh Ls parts) * val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2 := by
  have e : sysProg parts sh nIn oodsX =
      ([.hook 0 [] (List.range nIn), .zero nIn] ++ (partFold sh parts ([], nIn, nIn + 1)).1 ++
        [.hook 1 [oodsX] [(partFold sh parts ([], nIn, nIn + 1)).2.2],
         .mul ((partFold sh parts ([], nIn, nIn + 1)).2.2 + 1) (partFold sh parts ([], nIn, nIn + 1)).2.1
           (partFold sh parts ([], nIn, nIn + 1)).2.2], (partFold sh parts ([], nIn, nIn + 1)).2.2 + 1) := rfl
  rw [e] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨⟨h0, hf⟩, h1⟩ := h
  have hz : val ρ nIn = 0 := by
    have := h0 (.zero nIn) (by simp); simp only [Op.holds] at this; rw [val, this, toQ_lit0]
  have hm := h1 _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Op.holds] at hm
  simp only [val] at hz ⊢
  rw [hm, toQ_mul]
  have := partFold_soundV sh Ls parts ([], nIn, nIn + 1) hw hk hf
  simp only [val] at this
  rw [this, hz]

end StarkedAir.Circuit.Composition
