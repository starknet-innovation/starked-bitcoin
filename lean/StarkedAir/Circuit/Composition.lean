/-
**The composition check, Lean-first (VERIFIER-LEAN step 2).** `compositionAtOods` in the plain verifier
(`src/recursion/plain_verifier.zig`) evaluates every constraint of every component at the OODS point,
through the AIR's exported DAG (`Air.toDag`), Horner-combines them with the random coefficient, and
multiplies by `1/Z(oods)` (stwo-zig's `denomInverse`, a hook here).

This file defines that computation as a program of `Op`s, in the order of the builder calls (so the
replay is gate-for-gate the hand-written code), and proves what it computes:
- `dag_regs`: each node's register holds the node's value, run over QM31 (`Spec/QM31.lean`) with the
  OODS samples as leaves;
- `horner_regs`: the accumulator is the Horner combination of the roots;
- `constraints_sound`: for an AIR, the accumulator is `Σ_k coeff^(K−1−k) · C_k(samples)` (`evalR` of
  the constraints), using `dag_correct`.

Components with lookups add the LogUp batches (next step); this covers the constraint part.
-/
import StarkedAir.Circuit.Ops
import StarkedAir.Dag
import StarkedAir.Spec.QM31

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

/-- Where a component's inputs live: OODS samples per `(tree, column, offset)`, public inputs. -/
structure Inputs where
  leaf : Tree → ℕ → ℤ → ℕ
  pub : ℕ → ℕ

/-- Node `i`'s register: an input for a column or public input, else `base + 2i`. -/
def nodeReg (base : ℕ) (nodes : Array Node) (ci : Inputs) (i : ℕ) : ℕ :=
  match nodes[i]? with
  | some (.col t j off) => ci.leaf t j off
  | some (.pub j) => ci.pub j
  | _ => base + 2 * i

/-- Node `i`'s ops (`plain_verifier.zig`: constants, add, sub, mul; `neg x` is `0 − x`). -/
def nodeOps (base : ℕ) (nodes : Array Node) (ci : Inputs) (i : ℕ) : List Op :=
  match nodes[i]? with
  | some (.const v) => [.const (base + 2 * i) v 0 0 0]
  | some (.add a b) => [.add (base + 2 * i) (nodeReg base nodes ci a) (nodeReg base nodes ci b)]
  | some (.sub a b) => [.sub (base + 2 * i) (nodeReg base nodes ci a) (nodeReg base nodes ci b)]
  | some (.mul a b) => [.mul (base + 2 * i) (nodeReg base nodes ci a) (nodeReg base nodes ci b)]
  | some (.neg a) => [.zero (base + 2 * i + 1), .sub (base + 2 * i) (base + 2 * i + 1) (nodeReg base nodes ci a)]
  | _ => []

def dagOps (base : ℕ) (nodes : Array Node) (ci : Inputs) : List Op :=
  (List.range nodes.size).flatMap (nodeOps base nodes ci)

/-- Horner over the roots: `acc ← acc·coeff + root`, registers `hb + 2k` (product) and `hb + 2k + 1`. -/
def accReg (accIn hb : ℕ) : ℕ → ℕ
  | 0 => accIn
  | k + 1 => hb + 2 * k + 1

def hornerOps (accIn hb coeff : ℕ) (rootRegs : List ℕ) : List Op :=
  (List.range rootRegs.length).flatMap fun k =>
    [.mul (hb + 2 * k) (accReg accIn hb k) coeff, .add (hb + 2 * k + 1) (hb + 2 * k) (rootRegs.getD k 0)]

/-- Children come before their node. -/
def WF (nodes : Array Node) : Prop :=
  ∀ i < nodes.size, match nodes[i]? with
    | some (.add a b) | some (.sub a b) | some (.mul a b) => a < i ∧ b < i
    | some (.neg a) => a < i
    | _ => True

/-! ### `runDag` reads a prefix -/

section Run

variable {R : Type*} [CommRing R] (cst : ℕ → R) (leaf : Tree → ℕ → ℤ → R) (pub : ℕ → R)

theorem runDag_list (l : List Node) : runDag cst leaf pub l.toArray =
    l.foldl (fun acc nd => acc.push (nd.val cst leaf pub acc)) #[] := by
  simp [runDag, Array.foldl_toList]

theorem runDag_append_single (l : List Node) (nd : Node) : runDag cst leaf pub (l ++ [nd]).toArray =
    (runDag cst leaf pub l.toArray).push (nd.val cst leaf pub (runDag cst leaf pub l.toArray)) := by
  rw [show (l ++ [nd]).toArray = l.toArray.push nd by simp]
  exact runDag_push cst leaf pub _ nd

theorem getD_push_lt (A : Array R) (x : R) {i : ℕ} (h : i < A.size) : (A.push x).getD i 0 = A.getD i 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt h]

theorem getD_push_eq (A : Array R) (x : R) : (A.push x).getD A.size 0 = x := by
  simp [Array.getD_eq_getD_getElem?]

theorem runDag_size' (l : List Node) : (runDag cst leaf pub l.toArray).size = l.length := by
  rw [runDag_size]; simp

/-- **Node `i`'s value** is its rule applied to the values before it. -/
theorem runDag_getD : ∀ (l : List Node) (i : ℕ) (hi : i < l.length),
    (runDag cst leaf pub l.toArray).getD i 0 = (l[i]'hi).val cst leaf pub (runDag cst leaf pub (l.take i).toArray) ∧
    ∀ j < i, (runDag cst leaf pub (l.take i).toArray).getD j 0 = (runDag cst leaf pub l.toArray).getD j 0 := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro i hi; simp at hi
  | append_singleton l nd ih =>
    intro i hi
    rw [runDag_append_single]
    have hs := runDag_size' cst leaf pub l
    rcases Nat.lt_or_ge i l.length with h | h
    · obtain ⟨h1, h2⟩ := ih i h
      have ht : (l ++ [nd]).take i = l.take i := List.take_append_of_le_length h.le
      refine ⟨?_, fun j hj => ?_⟩
      · rw [getD_push_lt _ _ (by omega), h1, ht]
        congr 1
        exact (List.getElem_append_left h).symm
      · rw [ht, h2 j hj, getD_push_lt _ _ (by omega)]
    · have hi' : i = l.length := by simp at hi; omega
      subst hi'
      have ht : (l ++ [nd]).take l.length = l := List.take_left
      refine ⟨?_, fun j hj => ?_⟩
      · have e : ((runDag cst leaf pub l.toArray).push (Node.val cst leaf pub (runDag cst leaf pub l.toArray) nd)).getD
            l.length 0 = Node.val cst leaf pub (runDag cst leaf pub l.toArray) nd := by
          rw [← hs]; exact getD_push_eq _ _
        rw [e]
        congr 1 <;> simp
      · rw [ht, getD_push_lt _ _ (by omega)]

end Run

/-! ### Soundness -/

variable {ρ : ℕ → Q}

/-- The leaf and public-input values the registers hold. -/
noncomputable def leafQ (ρ : ℕ → Q) (ci : Inputs) : Tree → ℕ → ℤ → QM := fun t j off => toQ (ρ (ci.leaf t j off))
noncomputable def pubQ (ρ : ℕ → Q) (ci : Inputs) : ℕ → QM := fun j => toQ (ρ (ci.pub j))
noncomputable def cstQ : ℕ → QM := fun v => emb (v : F)

theorem toQ_lit (v : ℕ) : toQ (Q.lit v 0 0 0) = emb (v : F) := by simp [toQ, Q.lit]

theorem toQ_lit0 : toQ (Q.lit 0 0 0 0) = 0 := by simp [toQ, Q.lit]
theorem toQ_lit1 : toQ (Q.lit 1 0 0 0) = 1 := by simp [toQ, Q.lit]

theorem mem_dagOps {base : ℕ} {nodes : Array Node} {ci : Inputs} {i : ℕ} (hi : i < nodes.size) {op : Op}
    (h : op ∈ nodeOps base nodes ci i) : op ∈ dagOps base nodes ci := by
  simp only [dagOps, List.mem_flatMap, List.mem_range]; exact ⟨i, hi, h⟩

/-- **Every node's register holds its value** (over QM31, with the samples as leaves). -/
theorem dag_regs {base : ℕ} {nodes : Array Node} {ci : Inputs} (hwf : WF nodes) (h : Holds ρ (dagOps base nodes ci)) :
    ∀ i < nodes.size, toQ (ρ (nodeReg base nodes ci i)) = (runDag cstQ (leafQ ρ ci) (pubQ ρ ci) nodes).getD i 0 := by
  obtain ⟨l⟩ := nodes
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hi' : i < l.length := by simpa using hi
    obtain ⟨hv, hpre⟩ := runDag_getD cstQ (leafQ ρ ci) (pubQ ρ ci) l i hi'
    rw [hv]
    have hget : (⟨l⟩ : Array Node)[i]? = some (l[i]'hi') := by simp [hi']
    have hw := hwf i hi
    rw [hget] at hw
    -- a child's register, from the induction
    have child : ∀ a < i, toQ (ρ (nodeReg base ⟨l⟩ ci a)) =
        (runDag cstQ (leafQ ρ ci) (pubQ ρ ci) (l.take i).toArray).getD a 0 := by
      intro a ha
      rw [hpre a ha]; exact ih a ha (by simp; omega)
    have op := fun (o : Op) (ho : o ∈ nodeOps base ⟨l⟩ ci i) => h o (mem_dagOps hi ho)
    unfold nodeReg
    rw [hget]
    cases hn : l[i]'hi' with
    | col t j off => simp [Node.val, leafQ]
    | pub j => simp [Node.val, pubQ]
    | const v =>
      have := op (.const (base + 2 * i) v 0 0 0) (by simp [nodeOps, hget, hn])
      simp only [Op.holds] at this
      simp [Node.val, this, toQ_lit, cstQ]
    | add a b =>
      rw [hn] at hw
      have := op (.add (base + 2 * i) (nodeReg base ⟨l⟩ ci a) (nodeReg base ⟨l⟩ ci b)) (by simp [nodeOps, hget, hn])
      simp only [Op.holds] at this
      simp only [Node.val]
      rw [this, toQ_add, child a hw.1, child b hw.2]
    | sub a b =>
      rw [hn] at hw
      have := op (.sub (base + 2 * i) (nodeReg base ⟨l⟩ ci a) (nodeReg base ⟨l⟩ ci b)) (by simp [nodeOps, hget, hn])
      simp only [Op.holds] at this
      simp only [Node.val]
      rw [this, toQ_sub, child a hw.1, child b hw.2]
    | mul a b =>
      rw [hn] at hw
      have := op (.mul (base + 2 * i) (nodeReg base ⟨l⟩ ci a) (nodeReg base ⟨l⟩ ci b)) (by simp [nodeOps, hget, hn])
      simp only [Op.holds] at this
      simp only [Node.val]
      rw [this, toQ_mul, child a hw.1, child b hw.2]
    | neg a =>
      rw [hn] at hw
      have hz := op (.zero (base + 2 * i + 1)) (by simp [nodeOps, hget, hn])
      have hs := op (.sub (base + 2 * i) (base + 2 * i + 1) (nodeReg base ⟨l⟩ ci a)) (by simp [nodeOps, hget, hn])
      simp only [Op.holds] at hz hs
      simp only [Node.val]
      rw [hs, toQ_sub, hz, toQ_lit0, child a hw, zero_sub]

/-- The Horner value of `vals` from `a`: `(…(a·c + v₀)·c + v₁ …)`. -/
noncomputable def horner (c a : QM) : List QM → QM
  | [] => a
  | v :: vs => horner c (a * c + v) vs

theorem horner_append (c a : QM) (vs : List QM) (v : QM) : horner c a (vs ++ [v]) = horner c a vs * c + v := by
  induction vs generalizing a with
  | nil => rfl
  | cons x xs ih => simp [horner, ih]

/-- **The accumulator** after the Horner ops is the Horner combination of the roots' values. -/
theorem horner_regs {accIn hb coeff : ℕ} {rootRegs : List ℕ} (h : Holds ρ (hornerOps accIn hb coeff rootRegs)) :
    ∀ k ≤ rootRegs.length, toQ (ρ (accReg accIn hb k)) =
      horner (toQ (ρ coeff)) (toQ (ρ accIn)) ((rootRegs.take k).map fun r => toQ (ρ r)) := by
  intro k
  induction k with
  | zero => intro _; simp [accReg, horner]
  | succ k ih =>
    intro hk
    have hm := h (.mul (hb + 2 * k) (accReg accIn hb k) coeff) (by
      simp only [hornerOps, List.mem_flatMap, List.mem_range]; exact ⟨k, by omega, by simp⟩)
    have ha := h (.add (hb + 2 * k + 1) (hb + 2 * k) (rootRegs.getD k 0)) (by
      simp only [hornerOps, List.mem_flatMap, List.mem_range]; exact ⟨k, by omega, by simp⟩)
    simp only [Op.holds] at hm ha
    simp only [accReg]
    rw [ha, toQ_add, hm, toQ_mul, ih (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega),
      Option.toList_some, List.map_append, List.map_singleton, horner_append,
      List.getD_eq_getElem _ _ (by omega)]

/-! ### An AIR's constraints -/

/-- A component's constraint program: the DAG of `air`, then the Horner ops over its roots. -/
def constraintOps (base accIn hb coeff : ℕ) (air : Air) (ci : Inputs) : List Op :=
  dagOps base air.toDag.1 ci ++ hornerOps accIn hb coeff (air.toDag.2.map (nodeReg base air.toDag.1 ci))

/-- **The constraint part of the composition check is sound.** If the ops hold, the accumulator after
the AIR's `K` constraints is the Horner combination, from the incoming accumulator, of the constraints'
values `evalR` at the OODS samples (over QM31). -/
theorem constraints_sound {base accIn hb coeff : ℕ} {air : Air} {ci : Inputs} (hwf : WF air.toDag.1)
    (hroots : ∀ id ∈ air.toDag.2, id < air.toDag.1.size)
    (h : Holds ρ (constraintOps base accIn hb coeff air ci)) :
    toQ (ρ (accReg accIn hb air.toDag.2.length)) =
      horner (toQ (ρ coeff)) (toQ (ρ accIn)) (air.constraints.map (Expr.evalR cstQ (leafQ ρ ci) (pubQ ρ ci))) := by
  rw [constraintOps, holds_append] at h
  have hd := dag_regs hwf h.1
  have hh := horner_regs h.2 air.toDag.2.length (by simp)
  rw [hh, List.take_of_length_le (by simp), List.map_map]
  congr 1
  have hlen : air.toDag.2.length = air.constraints.length := by
    have h0 : Inv cstQ (leafQ ρ ci) (pubQ ρ ci) ({} : DagState) := fun e id h => by simp at h
    exact (emitAll_correct cstQ (leafQ ρ ci) (pubQ ρ ci) air.constraints {} h0).2.2.1
  apply List.ext_getElem (by simp [hlen])
  intro k h1 h2
  simp only [List.getElem_map, Function.comp]
  have hk : k < air.constraints.length := by simpa using h2
  obtain ⟨id, hid, hv⟩ := dag_correct cstQ (leafQ ρ ci) (pubQ ρ ci) air k hk
  have hid' : air.toDag.2[k] = id := by
    rw [List.getElem?_eq_getElem (by simpa [hlen] using hk)] at hid; exact Option.some.inj hid
  rw [hid', hd id (hroots id (by rw [← hid']; exact List.getElem_mem _)), hv]

end StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

/-! ### The whole single-component program (no lookups) -/

/-- The sorted, distinct offsets at which the DAG reads main column `i`. -/
def mainOffsets (nodes : Array Node) (i : ℕ) : List ℤ :=
  ((nodes.toList.filterMap fun nd => match nd with
    | .col .main j off => if j = i then some off else none
    | _ => none).dedup).mergeSort (fun a b => decide (a ≤ b))

/-- The input layout: preprocessed samples `0 … nPre − 1`, then main samples (column by column, offset
by offset), public inputs, the coefficient, the OODS `x`. -/
structure Layout where
  nPre : ℕ
  nMain : ℕ
  offs : ℕ → List ℤ
  nPub : ℕ

def Layout.mainStart (lay : Layout) (i : ℕ) : ℕ := lay.nPre + ((List.range i).map fun j => (lay.offs j).length).sum
def Layout.nSamples (lay : Layout) : ℕ := lay.mainStart lay.nMain
def Layout.coeff (lay : Layout) : ℕ := lay.nSamples + lay.nPub
def Layout.oodsX (lay : Layout) : ℕ := lay.coeff + 1
def Layout.nIn (lay : Layout) : ℕ := lay.oodsX + 1

def Layout.inputs (lay : Layout) : Inputs where
  leaf := fun t i off => match t with
    | .pre => i
    | .main => lay.mainStart i + (lay.offs i).idxOf off
  pub := fun j => lay.nSamples + j

/-- The program: bind the inputs (hook 0), the zero accumulator, the DAG and Horner ops, `1/Z(oods)`
(hook 1, stwo-zig's `denomInverse`), and the product. Result: `res`. -/
def program (air : Air) (lay : Layout) : List Op × ℕ :=
  let nodes := air.toDag.1
  let n := lay.nIn
  let base := n + 1
  let hb := base + 2 * nodes.size
  let K := air.toDag.2.length
  let w := hb + 2 * K
  let res := w + 1
  ([.hook 0 [] (List.range n), .zero n] ++ constraintOps base n hb lay.coeff air lay.inputs ++
    [.hook 1 [lay.oodsX] [w], .mul res (accReg n hb K) w], res)

def programJson (air : Air) (lay : Layout) : String :=
  let (ops, res) := program air lay
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{res}]}"

/-- **The single-component composition program is sound.** Its result is the Horner combination
(from 0, with the coefficient) of the AIR's constraints at the OODS samples, times the hook's value
(`1/Z(oods)`, from stwo-zig). -/
theorem program_sound {ρ : ℕ → Q} {air : Air} {lay : Layout} (hwf : WF air.toDag.1)
    (hroots : ∀ id ∈ air.toDag.2, id < air.toDag.1.size) (h : Holds ρ (program air lay).1) :
    toQ (ρ (program air lay).2) =
      horner (toQ (ρ lay.coeff)) 0 (air.constraints.map (Expr.evalR cstQ (leafQ ρ lay.inputs) (pubQ ρ lay.inputs))) *
        toQ (ρ (lay.nIn + 1 + 2 * air.toDag.1.size + 2 * air.toDag.2.length)) := by
  simp only [program] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨⟨h0, hc⟩, h1⟩ := h
  have hz : toQ (ρ lay.nIn) = 0 := by
    have := h0 (.zero lay.nIn) (by simp)
    simp only [Op.holds] at this
    rw [this, toQ_lit0]
  have hm := h1 (.mul _ _ _) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  simp only [Op.holds] at hm
  rw [hm, toQ_mul, constraints_sound hwf hroots hc, hz]

end StarkedAir.Circuit.Composition
