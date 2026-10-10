/-
**The composition check's LogUp part, Lean-first (VERIFIER-LEAN step 2b).** For a component with lookups,
`compositionAtOods` (`src/recursion/plain_verifier.zig`) adds, after the constraints, one term per batch
of two lookups. The gadgets here follow its builder calls one for one:
- `denOps`: `Σᵢ vᵢ αⁱ⁺¹ + rel − z` (Horner from the last value), the lookup's denominator at `(α, z)`;
- `secureOps`: four limb samples as one QM31 value (`fromPartialEvals`);
- `batchOps`: with the batch's numerator `N` and denominator `D`, the cumulative-sum step `diff` (on the
  last batch also minus the previous row's sum, plus the claimed sum's share `claimed / 2^L`), then
  `acc ← acc·coeff + (diff·D − N)`.

Each gadget's lemma says what its result register holds, over QM31.
-/
import StarkedAir.Circuit.Composition
import StarkedAir.Circuit.Gadgets
import StarkedAir.Lookup

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

variable {ρ : ℕ → Q}

/-- The value of register `r`. -/
noncomputable abbrev val (ρ : ℕ → Q) (r : ℕ) : QM := toQ (ρ r)

/-! ### The denominator -/

/-- `acc ← acc·α + v` over `vs` (registers `n + 2k`, `n + 2k + 1`), from `acc0`. -/
def hornerRegs (n acc0 alpha : ℕ) (vs : List ℕ) : List Op :=
  (List.range vs.length).flatMap fun k =>
    [.mul (n + 2 * k) (accReg acc0 n k) alpha, .add (n + 2 * k + 1) (n + 2 * k) (vs.getD k 0)]

/-- `denominatorVar`: zero, Horner over the values from the last, then `rel`, then `− z`. -/
def denOps (n rel z alpha : ℕ) (vals : List ℕ) : Out ℕ :=
  let vs := vals.reverse ++ [n + 1]
  let k := vs.length
  ⟨[.zero n, .const (n + 1) rel 0 0 0] ++ hornerRegs (n + 2) n alpha vs ++ [.sub (n + 2 + 2 * k) (accReg n (n + 2) k) z],
    n + 2 + 2 * k, n + 3 + 2 * k⟩

/-- The tuple's fingerprint at `α`: `rel + Σᵢ vᵢ αⁱ⁺¹`. -/
noncomputable def fingerprint (a : QM) (rel : QM) (vs : List QM) : QM :=
  horner a 0 (vs.reverse ++ [rel])

theorem den_sound {n rel z alpha : ℕ} {vals : List ℕ} (h : Holds ρ (denOps n rel z alpha vals).ops) :
    val ρ (denOps n rel z alpha vals).res =
      fingerprint (val ρ alpha) (emb (rel : F)) (vals.map (val ρ)) - val ρ z := by
  simp only [denOps] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨⟨h0, hh⟩, hs⟩ := h
  have hz : val ρ n = 0 := by
    have := h0 (.zero n) (by simp); simp only [Op.holds] at this; rw [val, this, toQ_lit0]
  have hr : val ρ (n + 1) = emb (rel : F) := by
    have := h0 (.const (n + 1) rel 0 0 0) (by simp); simp only [Op.holds] at this; rw [val, this, toQ_lit]
  have hsub := hs _ (List.mem_singleton_self _)
  simp only [Op.holds] at hsub
  rw [val, hsub, toQ_sub]
  congr 1
  have := horner_regs (ρ := ρ) (accIn := n) (hb := n + 2) (coeff := alpha) (rootRegs := vals.reverse ++ [n + 1])
    (by simpa [hornerOps, hornerRegs] using hh) _ le_rfl
  have hz' : toQ (ρ n) = 0 := hz
  have hr' : toQ (ρ (n + 1)) = emb (rel : F) := hr
  rw [this, List.take_of_length_le le_rfl, hz', fingerprint]
  simp [List.map_append, List.map_reverse, hr', val]

/-! ### Secure columns -/

/-- `secure`: `l₀ + l₁·e₁ + l₂·e₂ + l₃·e₃` with the basis constants. Registers `n … n + 8`. -/
def secureOps (n : ℕ) (l : ℕ → ℕ) : Out ℕ :=
  ⟨[.const n 0 1 0 0, .mul (n + 1) (l 1) n, .add (n + 2) (l 0) (n + 1),
    .const (n + 3) 0 0 1 0, .mul (n + 4) (l 2) (n + 3), .add (n + 5) (n + 2) (n + 4),
    .const (n + 6) 0 0 0 1, .mul (n + 7) (l 3) (n + 6), .add (n + 8) (n + 5) (n + 7)], n + 8, n + 9⟩

/-- The basis elements `e₁, e₂, e₃` in QM31. -/
noncomputable def e1 : QM := toQ (Q.lit 0 1 0 0)
noncomputable def e2 : QM := toQ (Q.lit 0 0 1 0)
noncomputable def e3 : QM := toQ (Q.lit 0 0 0 1)

theorem secure_sound {n : ℕ} {l : ℕ → ℕ} (h : Holds ρ (secureOps n l).ops) :
    val ρ (secureOps n l).res = val ρ (l 0) + val ρ (l 1) * e1 + val ρ (l 2) * e2 + val ρ (l 3) * e3 := by
  have g := fun (o : Op) (ho : o ∈ (secureOps n l).ops) => h o ho
  have c1 := g (.const n 0 1 0 0) (by simp [secureOps])
  have m1 := g (.mul (n + 1) (l 1) n) (by simp [secureOps])
  have a1 := g (.add (n + 2) (l 0) (n + 1)) (by simp [secureOps])
  have c2 := g (.const (n + 3) 0 0 1 0) (by simp [secureOps])
  have m2 := g (.mul (n + 4) (l 2) (n + 3)) (by simp [secureOps])
  have a2 := g (.add (n + 5) (n + 2) (n + 4)) (by simp [secureOps])
  have c3 := g (.const (n + 6) 0 0 0 1) (by simp [secureOps])
  have m3 := g (.mul (n + 7) (l 3) (n + 6)) (by simp [secureOps])
  have a3 := g (.add (n + 8) (n + 5) (n + 7)) (by simp [secureOps])
  simp only [Op.holds] at c1 m1 a1 c2 m2 a2 c3 m3 a3
  simp only [secureOps, val]
  rw [a3, toQ_add, a2, toQ_add, a1, toQ_add, m1, toQ_mul, m2, toQ_mul, m3, toQ_mul, c1, c2, c3, e1, e2, e3]

/-! ### One batch -/

/-- What a batch reads: the lookups' multiplicity and denominator registers, the cumulative sums. -/
structure BatchIn where
  m : ℕ → ℕ
  d : ℕ → ℕ
  S : ℕ → ℕ
  sprev : ℕ
  shift : ℕ
  L : ℕ
  B : ℕ

/-- Batch `b`'s ops from register `n`, accumulating from `acc` with `coeff`. Result `n + 13`. -/
def batchOps (n acc coeff b : ℕ) (x : BatchIn) : Out ℕ :=
  let j := 2 * b
  let pair := decide (j + 1 < x.L)
  let nOps : List Op := if pair then [.mul n (x.m j) (x.d (j + 1)), .mul (n + 1) (x.m (j + 1)) (x.d j), .add (n + 2) n (n + 1)] else []
  let nReg := if pair then n + 2 else x.m j
  let dOps : List Op := if pair then [.mul (n + 3) (x.d j) (x.d (j + 1))] else []
  let dReg := if pair then n + 3 else x.d j
  let diffOps : List Op :=
    if b + 1 < x.B then
      (if b = 0 then [.zero (n + 4), .sub (n + 9) (x.S b) (n + 4)] else [.sub (n + 9) (x.S b) (x.S (b - 1))])
    else
      [.sub (n + 6) (x.S b) x.sprev] ++
      (if x.B = 1 then [.zero (n + 7), .sub (n + 8) (n + 6) (n + 7)] else [.sub (n + 8) (n + 6) (x.S (x.B - 2))]) ++
      [.add (n + 9) (n + 8) x.shift]
  ⟨nOps ++ dOps ++ diffOps ++
    [.mul (n + 10) acc coeff, .mul (n + 11) (n + 9) dReg, .sub (n + 12) (n + 11) nReg, .add (n + 13) (n + 10) (n + 12)],
    n + 13, n + 14⟩

/-- Batch `b`'s term: `diff·D − N` over QM31. -/
noncomputable def batchTerm (m d S : ℕ → QM) (sprev shift : QM) (L B b : ℕ) : QM :=
  let j := 2 * b
  let N := if j + 1 < L then m j * d (j + 1) + m (j + 1) * d j else m j
  let D := if j + 1 < L then d j * d (j + 1) else d j
  let diff := if b + 1 < B then S b - (if b = 0 then 0 else S (b - 1))
    else S b - sprev - (if B = 1 then 0 else S (B - 2)) + shift
  diff * D - N

theorem batch_sound {n acc coeff b : ℕ} {x : BatchIn} (h : Holds ρ (batchOps n acc coeff b x).ops) :
    val ρ (batchOps n acc coeff b x).res = val ρ acc * val ρ coeff +
      batchTerm (fun i => val ρ (x.m i)) (fun i => val ρ (x.d i)) (fun i => val ρ (x.S i)) (val ρ x.sprev)
        (val ρ x.shift) x.L x.B b := by
  have g := fun (o : Op) (ho : o ∈ (batchOps n acc coeff b x).ops) => h o ho
  have gd := fun (o : Op) (ho : o ∈ (if b + 1 < x.B then
      (if b = 0 then [Op.zero (n + 4), .sub (n + 9) (x.S b) (n + 4)] else [Op.sub (n + 9) (x.S b) (x.S (b - 1))])
    else
      [Op.sub (n + 6) (x.S b) x.sprev] ++
      (if x.B = 1 then [Op.zero (n + 7), .sub (n + 8) (n + 6) (n + 7)] else [Op.sub (n + 8) (n + 6) (x.S (x.B - 2))]) ++
      [Op.add (n + 9) (n + 8) x.shift])) =>
    g o (by simp only [batchOps]; exact List.mem_append_left _ (List.mem_append_right _ ho))
  have tail : ∀ o ∈ [Op.mul (n + 10) acc coeff, .mul (n + 11) (n + 9) (if decide (2 * b + 1 < x.L) then n + 3 else x.d (2 * b)),
      .sub (n + 12) (n + 11) (if decide (2 * b + 1 < x.L) then n + 2 else x.m (2 * b)), .add (n + 13) (n + 10) (n + 12)],
      o.holds ρ := fun o ho => g o (by simp only [batchOps]; exact List.mem_append_right _ ho)
  have t1 := tail (.mul (n + 10) acc coeff) (by simp)
  have t2 := tail (.mul (n + 11) (n + 9) (if decide (2 * b + 1 < x.L) then n + 3 else x.d (2 * b))) (by simp)
  have t3 := tail (.sub (n + 12) (n + 11) (if decide (2 * b + 1 < x.L) then n + 2 else x.m (2 * b))) (by simp)
  have t4 := tail (.add (n + 13) (n + 10) (n + 12)) (by simp)
  simp only [Op.holds] at t1 t2 t3 t4
  -- N and D
  have hN : val ρ (if decide (2 * b + 1 < x.L) then n + 2 else x.m (2 * b)) =
      if 2 * b + 1 < x.L then val ρ (x.m (2 * b)) * val ρ (x.d (2 * b + 1)) + val ρ (x.m (2 * b + 1)) * val ρ (x.d (2 * b))
      else val ρ (x.m (2 * b)) := by
    by_cases hp : 2 * b + 1 < x.L
    · have a := g (.mul n (x.m (2 * b)) (x.d (2 * b + 1))) (by simp [batchOps, hp])
      have c := g (.mul (n + 1) (x.m (2 * b + 1)) (x.d (2 * b))) (by simp [batchOps, hp])
      have e := g (.add (n + 2) n (n + 1)) (by simp [batchOps, hp])
      simp only [Op.holds] at a c e
      simp only [hp, decide_true, if_true, val]
      rw [e, toQ_add, a, toQ_mul, c, toQ_mul]
    · simp [hp]
  have hD : val ρ (if decide (2 * b + 1 < x.L) then n + 3 else x.d (2 * b)) =
      if 2 * b + 1 < x.L then val ρ (x.d (2 * b)) * val ρ (x.d (2 * b + 1)) else val ρ (x.d (2 * b)) := by
    by_cases hp : 2 * b + 1 < x.L
    · have a := g (.mul (n + 3) (x.d (2 * b)) (x.d (2 * b + 1))) (by simp [batchOps, hp])
      simp only [Op.holds] at a
      simp only [hp, decide_true, if_true, val]; rw [a, toQ_mul]
    · simp [hp]
  -- diff
  have hdiff : val ρ (n + 9) = if b + 1 < x.B then val ρ (x.S b) - (if b = 0 then 0 else val ρ (x.S (b - 1)))
      else val ρ (x.S b) - val ρ x.sprev - (if x.B = 1 then 0 else val ρ (x.S (x.B - 2))) + val ρ x.shift := by
    by_cases hb : b + 1 < x.B
    · simp only [hb, if_true]
      by_cases h0 : b = 0
      · have z := gd (.zero (n + 4)) (by rw [if_pos hb, if_pos h0]; simp)
        have s := gd (.sub (n + 9) (x.S b) (n + 4)) (by rw [if_pos hb, if_pos h0]; simp)
        simp only [Op.holds] at z s
        simp only [h0, if_true, val] at s ⊢
        rw [s, toQ_sub, z, toQ_lit0]
      · have s := g (.sub (n + 9) (x.S b) (x.S (b - 1))) (by simp [batchOps, hb, h0])
        simp only [Op.holds] at s
        simp only [h0, if_false, val]; rw [s, toQ_sub]
    · simp only [hb, if_false]
      have s1 := gd (.sub (n + 6) (x.S b) x.sprev) (by rw [if_neg hb]; simp)
      have a := gd (.add (n + 9) (n + 8) x.shift) (by rw [if_neg hb]; simp)
      simp only [Op.holds] at s1 a
      by_cases h1 : x.B = 1
      · have z := gd (.zero (n + 7)) (by rw [if_neg hb, if_pos h1]; simp)
        have s2 := gd (.sub (n + 8) (n + 6) (n + 7)) (by rw [if_neg hb, if_pos h1]; simp)
        simp only [Op.holds] at z s2
        simp only [h1, if_true, val]
        rw [a, toQ_add, s2, toQ_sub, s1, toQ_sub, z, toQ_lit0]
      · have s2 := g (.sub (n + 8) (n + 6) (x.S (x.B - 2))) (by simp [batchOps, hb, h1])
        simp only [Op.holds] at s2
        simp only [h1, if_false, val]
        rw [a, toQ_add, s2, toQ_sub, s1, toQ_sub]
  simp only [batchOps, val] at hN hD hdiff ⊢
  rw [t4, toQ_add, t1, toQ_mul, t3, toQ_sub, t2, toQ_mul, hdiff, hD, hN, batchTerm]

theorem horner_concat (c a : QM) (xs ys : List QM) : horner c a (xs ++ ys) = horner c (horner c a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [horner, ih]

end StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit

/-! ### A component, and the whole system -/

/-- A component's DAG roots: constraints, then per lookup its multiplicity and values (as exported). -/
def compRoots (c : Comp) : List Expr := c.air.constraints ++ c.lookups.flatMap fun l => l.mult :: l.vals
def compDag (c : Comp) : List ℕ × DagState := emitAll (compRoots c) {}

/-- Where lookup `j`'s multiplicity id sits among the roots' ids. -/
def lookupAt (c : Comp) (j : ℕ) : ℕ :=
  c.air.constraints.length + ((c.lookups.take j).map fun l => l.vals.length + 1).sum

/-- A component's input registers: samples and public inputs (`Inputs`), interaction samples, its
claimed sum. -/
structure PartRegs where
  ci : Inputs
  inter : ℕ → ℕ → ℕ
  claimed : ℕ

/-- Shared registers: coefficient, lookup elements, trace size. -/
structure Shared where
  coeff : ℕ
  z : ℕ
  alpha : ℕ
  logSize : ℕ

/-- `1/2^L` in M31 (the claimed sum's share per row). -/
def ninv (L : ℕ) : ℕ := (((2 : F) ^ L)⁻¹).val

/-- Run a list of gadgets, each from the previous one's next register. -/
def seqOuts : ℕ → List (ℕ → Out ℕ) → List Op × List ℕ × ℕ
  | n, [] => ([], [], n)
  | n, f :: fs => let o := f n; let r := seqOuts o.next fs; (o.ops ++ r.1, o.res :: r.2.1, r.2.2)

section Part

variable (c : Comp) (pr : PartRegs) (sh : Shared) (n accIn : ℕ)

def pIds : List ℕ := (compDag c).1
def pNodes : Array Node := (compDag c).2.out
def pReg : ℕ → ℕ := nodeReg n (pNodes c) pr.ci
def pNc : ℕ := c.air.constraints.length
def pHb : ℕ := n + 2 * (pNodes c).size
def pCOps : List Op := dagOps n (pNodes c) pr.ci ++ hornerOps accIn (pHb c n) sh.coeff (((pIds c).take (pNc c)).map (pReg c pr n))
def pAcc1 : ℕ := accReg accIn (pHb c n) (pNc c)
def pP0 : ℕ := pHb c n + 2 * pNc c
def pL : ℕ := c.lookups.length
def pB : ℕ := (pL c + 1) / 2
def pIdAt (i : ℕ) : ℕ := pReg c pr n ((pIds c).getD i 0)
def pMults (j : ℕ) : ℕ := pIdAt c pr n (lookupAt c j)
def pValsOf (j : ℕ) : List ℕ :=
  (List.range ((c.lookups.getD j ⟨0, .const 0, []⟩).vals.length)).map fun i => pIdAt c pr n (lookupAt c j + 1 + i)
def pDens : List Op × List ℕ × ℕ :=
  seqOuts (pP0 c n) ((List.range (pL c)).map fun j => fun m =>
    denOps m (c.lookups.getD j ⟨0, .const 0, []⟩).rel sh.z sh.alpha (pValsOf c pr n j))
def pSS : List Op × List ℕ × ℕ :=
  seqOuts (pDens c pr sh n).2.2 ((List.range (pB c)).map fun b => fun m =>
    secureOps m (fun k => pr.inter (4 * b + k) (if b + 1 = pB c then 1 else 0)))
def pSp : Out ℕ := secureOps (pSS c pr sh n).2.2 (fun k => pr.inter (4 * (pB c - 1) + k) 0)
def pQ : ℕ := (pSp c pr sh n).next
/-- `1/2^L` (hook 2: the host's interned constant, so one program serves every trace size), then
`claimed · 1/2^L`. -/
def pShOps : List Op := [.hook 2 [] [pQ c pr sh n], .mul (pQ c pr sh n + 1) pr.claimed (pQ c pr sh n)]
def pBx : BatchIn := ⟨pMults c pr n, fun j => (pDens c pr sh n).2.1.getD j 0, fun b => (pSS c pr sh n).2.1.getD b 0,
  (pSp c pr sh n).res, pQ c pr sh n + 1, pL c, pB c⟩
def pBt : List Op × ℕ × ℕ :=
  (List.range (pB c)).foldl (fun (acc : List Op × ℕ × ℕ) b =>
    let o := batchOps acc.2.2 acc.2.1 sh.coeff b (pBx c pr sh n); (acc.1 ++ o.ops, o.res, o.next))
    (([] : List Op), pAcc1 c n accIn, pQ c pr sh n + 2)

end Part

/-- A component's program from register `n`, accumulating from `accIn`. -/
def partProg (c : Comp) (pr : PartRegs) (sh : Shared) (n accIn : ℕ) : Out ℕ :=
  if c.lookups.isEmpty then ⟨pCOps c pr sh n accIn, pAcc1 c n accIn, pP0 c n⟩ else
  ⟨pCOps c pr sh n accIn ++ (pDens c pr sh n).1 ++ (pSS c pr sh n).1 ++ (pSp c pr sh n).ops ++ pShOps c pr sh n ++
    (pBt c pr sh n accIn).1, (pBt c pr sh n accIn).2.1, (pBt c pr sh n accIn).2.2⟩

/-- The system's program: input hook, zero accumulator, components in order, `1/Z(oods)`, product. -/
def sysProg (parts : List (Comp × PartRegs)) (sh : Shared) (nIn oodsX : ℕ) : List Op × ℕ :=
  let r := parts.foldl (fun (acc : List Op × ℕ × ℕ) p =>
    let o := partProg p.1 p.2 sh acc.2.2 acc.2.1; (acc.1 ++ o.ops, o.res, o.next)) ([], nIn, nIn + 1)
  let w := r.2.2
  ([.hook 0 [] (List.range nIn), .zero nIn] ++ r.1 ++ [.hook 1 [oodsX] [w], .mul (w + 1) r.2.1 w], w + 1)

/-! ### The input layout of `plain_verifier.zig` -/

/-- Per component: preprocessed count, main offsets per column, interaction column count, pubs count. -/
structure PartShape where
  nPre : ℕ
  offs : List (List ℤ)
  nInter : ℕ
  nPub : ℕ
  lookups : Bool

/-- Registers, in Zig's order: all preprocessed samples, all main samples, all interaction samples
(two for a component's last four columns), all public inputs, the claimed sums, the coefficient, `z`,
`α`, the OODS `x`. -/
def layoutRegs (shapes : List PartShape) : List PartRegs × Shared × ℕ × ℕ :=
  let nPreAll := (shapes.map (·.nPre)).sum
  let mainLen := fun (s : PartShape) => (s.offs.map List.length).sum
  let interLen := fun (s : PartShape) => if s.nInter = 0 then 0 else s.nInter + 4
  let nMainAll := (shapes.map mainLen).sum
  let nInterAll := (shapes.map interLen).sum
  let nPubAll := (shapes.map (·.nPub)).sum
  let nSums := (shapes.filter (·.lookups)).length
  let pubBase := nPreAll + nMainAll + nInterAll
  let sumBase := pubBase + nPubAll
  let coeff := sumBase + nSums
  let go := shapes.foldl (fun (acc : List PartRegs × ℕ × ℕ × ℕ × ℕ × ℕ) s =>
    let (out, pre, main, inter, pubb, sums) := acc
    let mainStart := fun i => main + ((s.offs.take i).map List.length).sum
    let ci : Inputs := ⟨fun t i off => match t with
      | .pre => pre + i
      | .main => mainStart i + ((s.offs.getD i []).idxOf off), fun j => pubb + j⟩
    -- column c's samples: one, or two (prev, cur) for the last four columns
    let interAt := fun c j => inter + c + (c - (s.nInter - 4)) + j
    let pr : PartRegs := ⟨ci, interAt, sums⟩
    (out ++ [pr], pre + s.nPre, main + mainLen s, inter + interLen s, pubb + s.nPub, if s.lookups then sums + 1 else sums))
    ([], 0, nPreAll, nPreAll + nMainAll, pubBase, sumBase)
  (go.1, ⟨coeff, coeff + 1, coeff + 2, 0⟩, coeff + 4, coeff + 3)

def sysJson (parts : List Comp) (shapes : List PartShape) (logSize : ℕ) : String :=
  let (regs, sh, nIn, oodsX) := layoutRegs shapes
  let (ops, res) := sysProg (parts.zip regs) { sh with logSize := logSize } nIn oodsX
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{res}]}"

end StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Composition

def compShape (c : Comp) (nPub : ℕ) : PartShape :=
  let nodes := (compDag c).2.out
  ⟨c.air.pre.length, (List.range c.air.nMain).map (mainOffsets nodes), if c.lookups.isEmpty then 0 else 4 * ((c.lookups.length + 1) / 2),
    nPub, !c.lookups.isEmpty⟩

end StarkedAir.Circuit.Composition
