/-
The exported expression DAG, and its correctness (roadmap REC-STMT-EQ, trust-base item
"exporter is a faithful printer").

`Air.toJson` (Export.lean) prints the node array built here: expressions in post-order
(children before parents), structurally equal subexpressions shared. Both the Zig interpreter
(trace rows, over M31) and the in-circuit verifier statement (the OODS point, over QM31) run
this DAG. `dag_correct` proves that running it in ANY commutative ring, from leaf values for
columns, constants and public inputs, yields exactly `Expr.evalR` of each constraint; and
`eval_eq_evalR` shows `Expr.eval` (the semantics the soundness theorems use) is the instance
for trace rows over `F`.
-/
import StarkedAir.IR
import Std.Data.HashMap

namespace StarkedAir

/-! ## Evaluation in any commutative ring -/

section EvalR

variable {R : Type*} [CommRing R]

/-- Value of an expression in `R`, given leaf values for columns (`tree`, `index`, `offset`),
constants and public inputs. -/
def Expr.evalR (cst : ℕ → R) (leaf : Tree → ℕ → ℤ → R) (pub : ℕ → R) : Expr → R
  | .col t i off => leaf t i off
  | .const v => cst v
  | .add a b => a.evalR cst leaf pub + b.evalR cst leaf pub
  | .sub a b => a.evalR cst leaf pub - b.evalR cst leaf pub
  | .mul a b => a.evalR cst leaf pub * b.evalR cst leaf pub
  | .neg a => -(a.evalR cst leaf pub)
  | .pub i => pub i

end EvalR

/-- `Expr.eval` at a trace row is `Expr.evalR` over `F` with the row's leaf values. -/
theorem eval_eq_evalR (n : ℕ) (pre : List PreCol) (pub : ℕ → F) (main : ℕ → ℕ → F) (r : ℕ) (e : Expr) :
    e.eval n pre pub main r = e.evalR (fun v => (v : F))
      (fun t i off => match t with
        | .pre => (pre.getD i (.periodic [0])).eval n (wrap n r off)
        | .main => main i (wrap n r off)) pub := by
  induction e with
  | col t i off => cases t <;> rfl
  | const v => rfl
  | add a b iha ihb => simp [Expr.eval, Expr.evalR, iha, ihb]
  | sub a b iha ihb => simp [Expr.eval, Expr.evalR, iha, ihb]
  | mul a b iha ihb => simp [Expr.eval, Expr.evalR, iha, ihb]
  | neg a iha => simp [Expr.eval, Expr.evalR, iha]
  | pub i => rfl

/-! ## The DAG -/

/-- A DAG node; children are indices of earlier nodes. -/
inductive Node where
  | col (t : Tree) (i : ℕ) (off : ℤ)
  | const (v : ℕ)
  | add (a b : ℕ)
  | sub (a b : ℕ)
  | mul (a b : ℕ)
  | neg (a : ℕ)
  | pub (i : ℕ)
  deriving Repr

section Run

variable {R : Type*} [CommRing R] (cst : ℕ → R) (leaf : Tree → ℕ → ℤ → R) (pub : ℕ → R)

/-- Value of a node, reading children from the values computed so far. -/
def Node.val (acc : Array R) : Node → R
  | .col t i off => leaf t i off
  | .const v => cst v
  | .add a b => acc.getD a 0 + acc.getD b 0
  | .sub a b => acc.getD a 0 - acc.getD b 0
  | .mul a b => acc.getD a 0 * acc.getD b 0
  | .neg a => -(acc.getD a 0)
  | .pub i => pub i

/-- Values of all nodes, in order (a straight-line program). -/
def runDag (nodes : Array Node) : Array R :=
  nodes.foldl (fun acc nd => acc.push (nd.val cst leaf pub acc)) #[]

theorem runDag_push (nodes : Array Node) (nd : Node) :
    runDag cst leaf pub (nodes.push nd) =
      (runDag cst leaf pub nodes).push (nd.val cst leaf pub (runDag cst leaf pub nodes)) := by
  simp [runDag, Array.foldl_push]

theorem runDag_size (nodes : Array Node) : (runDag cst leaf pub nodes).size = nodes.size := by
  have h : ∀ (l : List Node) (acc : Array R),
      (l.foldl (fun acc nd => acc.push (nd.val cst leaf pub acc)) acc).size = acc.size + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => intro acc; simp only [List.foldl_cons, ih, Array.size_push, List.length_cons]; ring
  unfold runDag
  rw [← Array.foldl_toList, h]; simp

end Run

/-! ## The emitter (state-passing; `Export.lean` prints its output) -/

structure DagState where
  ids : Std.HashMap Expr ℕ := {}
  out : Array Node := #[]

/-- Emits `e` (children first), sharing structurally equal subexpressions; returns its index. -/
def emitN : Expr → DagState → ℕ × DagState
  | e@(.col t i off), s => match s.ids[e]? with
    | some id => (id, s)
    | none => (s.out.size, { ids := s.ids.insert e s.out.size, out := s.out.push (.col t i off) })
  | e@(.const v), s => match s.ids[e]? with
    | some id => (id, s)
    | none => (s.out.size, { ids := s.ids.insert e s.out.size, out := s.out.push (.const v) })
  | e@(.pub i), s => match s.ids[e]? with
    | some id => (id, s)
    | none => (s.out.size, { ids := s.ids.insert e s.out.size, out := s.out.push (.pub i) })
  | e@(.neg a), s => match s.ids[e]? with
    | some id => (id, s)
    | none =>
      let (ia, s1) := emitN a s
      (s1.out.size, { ids := s1.ids.insert e s1.out.size, out := s1.out.push (.neg ia) })
  | e@(.add a b), s => match s.ids[e]? with
    | some id => (id, s)
    | none =>
      let (ia, s1) := emitN a s
      let (ib, s2) := emitN b s1
      (s2.out.size, { ids := s2.ids.insert e s2.out.size, out := s2.out.push (.add ia ib) })
  | e@(.sub a b), s => match s.ids[e]? with
    | some id => (id, s)
    | none =>
      let (ia, s1) := emitN a s
      let (ib, s2) := emitN b s1
      (s2.out.size, { ids := s2.ids.insert e s2.out.size, out := s2.out.push (.sub ia ib) })
  | e@(.mul a b), s => match s.ids[e]? with
    | some id => (id, s)
    | none =>
      let (ia, s1) := emitN a s
      let (ib, s2) := emitN b s1
      (s2.out.size, { ids := s2.ids.insert e s2.out.size, out := s2.out.push (.mul ia ib) })

/-- Emits every constraint; returns their root indices and the final state. -/
def emitAll : List Expr → DagState → List ℕ × DagState
  | [], s => ([], s)
  | e :: es, s =>
    let (id, s1) := emitN e s
    let (ids, s2) := emitAll es s1
    (id :: ids, s2)

/-- The DAG of an AIR's constraints: node array and constraint roots. -/
def Air.toDag (air : Air) : Array Node × List ℕ :=
  let (roots, s) := emitAll air.constraints {}
  (s.out, roots)

/-! ## Correctness -/

section Correct

variable {R : Type*} [CommRing R] (cst : ℕ → R) (leaf : Tree → ℕ → ℤ → R) (pub : ℕ → R)

/-- Every shared id denotes an emitted node whose value is that expression's value. -/
abbrev Inv (s : DagState) : Prop :=
  ∀ (e : Expr) (id : ℕ), s.ids[e]? = some id → id < s.out.size ∧
    (runDag cst leaf pub s.out).getD id 0 = e.evalR cst leaf pub

/-- `s'` extends `s`: earlier nodes and their values are unchanged. -/
abbrev Ext (s s' : DagState) : Prop :=
  s.out.size ≤ s'.out.size ∧
    ∀ k < s.out.size, (runDag cst leaf pub s'.out).getD k 0 = (runDag cst leaf pub s.out).getD k 0

theorem ext_refl (s : DagState) : Ext cst leaf pub s s := ⟨le_rfl, fun _ _ => rfl⟩

theorem ext_trans {s1 s2 s3 : DagState} (h12 : Ext cst leaf pub s1 s2) (h23 : Ext cst leaf pub s2 s3) :
    Ext cst leaf pub s1 s3 :=
  ⟨le_trans h12.1 h23.1, fun k hk => by rw [h23.2 k (by have := h12.1; omega), h12.2 k hk]⟩

/-- Pushing one node and recording its id. -/
theorem push_step {s : DagState} (hs : Inv cst leaf pub s) (e : Expr) (nd : Node)
    (hval : nd.val cst leaf pub (runDag cst leaf pub s.out) = e.evalR cst leaf pub) :
    let s' : DagState := { ids := s.ids.insert e s.out.size, out := s.out.push nd }
    Inv cst leaf pub s' ∧ Ext cst leaf pub s s' ∧ s.out.size < s'.out.size ∧
      (runDag cst leaf pub s'.out).getD s.out.size 0 = e.evalR cst leaf pub := by
  intro s'
  have hsize := runDag_size cst leaf pub s.out
  have hget : ∀ k, k < s.out.size →
      (runDag cst leaf pub (s.out.push nd)).getD k 0 = (runDag cst leaf pub s.out).getD k 0 := by
    intro k hk
    rw [runDag_push]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, show k ≠ (runDag cst leaf pub s.out).size by omega,
      if_false]
  have hnew : (runDag cst leaf pub (s.out.push nd)).getD s.out.size 0 = e.evalR cst leaf pub := by
    rw [runDag_push]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize, if_true, Option.getD_some]
    exact hval
  refine ⟨fun e' id h => ?_, ⟨by simp [s'], hget⟩, by simp [s'], hnew⟩
  simp only [s', Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have : e = e' := by simpa using heq
    subst this
    cases h
    exact ⟨by simp only [s', Array.size_push]; omega, hnew⟩
  · obtain ⟨hlt, hv⟩ := hs e' id h
    exact ⟨by simp only [s', Array.size_push]; omega, by rw [hget id hlt, hv]⟩

/-- **Emitter correctness.** -/
theorem emitN_correct (e : Expr) : ∀ s, Inv cst leaf pub s →
    Inv cst leaf pub (emitN e s).2 ∧ Ext cst leaf pub s (emitN e s).2 ∧
      (emitN e s).1 < (emitN e s).2.out.size ∧
      (runDag cst leaf pub (emitN e s).2.out).getD (emitN e s).1 0 = e.evalR cst leaf pub := by
  induction e with
  | col t i off =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨a, b, c, d⟩ := push_step cst leaf pub hs (.col t i off) (.col t i off) rfl; exact ⟨a, b, c, d⟩
  | const v =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨a, b, c, d⟩ := push_step cst leaf pub hs (.const v) (.const v) rfl; exact ⟨a, b, c, d⟩
  | pub i =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨a, b, c, d⟩ := push_step cst leaf pub hs (.pub i) (.pub i) rfl; exact ⟨a, b, c, d⟩
  | neg a iha =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨i1, x1, l1, v1⟩ := iha s hs
      obtain ⟨a', b', c', d'⟩ := push_step cst leaf pub i1 (.neg a) (.neg (emitN a s).1)
        (by simp [Node.val, v1, Expr.evalR])
      exact ⟨a', ext_trans _ _ _ x1 b', c', d'⟩
  | add a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨i1, x1, l1, v1⟩ := iha s hs
      obtain ⟨i2, x2, l2, v2⟩ := ihb _ i1
      obtain ⟨a', b', c', d'⟩ := push_step cst leaf pub i2 (.add a b) (.add (emitN a s).1 (emitN b (emitN a s).2).1)
        (by simp only [Node.val, Expr.evalR]; rw [x2.2 _ l1, v1, v2])
      exact ⟨a', ext_trans _ _ _ (ext_trans _ _ _ x1 x2) b', c', d'⟩
  | sub a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨i1, x1, l1, v1⟩ := iha s hs
      obtain ⟨i2, x2, l2, v2⟩ := ihb _ i1
      obtain ⟨a', b', c', d'⟩ := push_step cst leaf pub i2 (.sub a b) (.sub (emitN a s).1 (emitN b (emitN a s).2).1)
        (by simp only [Node.val, Expr.evalR]; rw [x2.2 _ l1, v1, v2])
      exact ⟨a', ext_trans _ _ _ (ext_trans _ _ _ x1 x2) b', c', d'⟩
  | mul a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h; obtain ⟨h1, h2⟩ := hs _ id h; exact ⟨hs, ext_refl _ _ _ s, h1, h2⟩
    · obtain ⟨i1, x1, l1, v1⟩ := iha s hs
      obtain ⟨i2, x2, l2, v2⟩ := ihb _ i1
      obtain ⟨a', b', c', d'⟩ := push_step cst leaf pub i2 (.mul a b) (.mul (emitN a s).1 (emitN b (emitN a s).2).1)
        (by simp only [Node.val, Expr.evalR]; rw [x2.2 _ l1, v1, v2])
      exact ⟨a', ext_trans _ _ _ (ext_trans _ _ _ x1 x2) b', c', d'⟩

theorem emitAll_correct : ∀ (es : List Expr) (s : DagState), Inv cst leaf pub s →
    Inv cst leaf pub (emitAll es s).2 ∧ Ext cst leaf pub s (emitAll es s).2 ∧
      (emitAll es s).1.length = es.length ∧
      ∀ k (hk : k < es.length), ∃ id, (emitAll es s).1[k]? = some id ∧
        (runDag cst leaf pub (emitAll es s).2.out).getD id 0 = (es[k]'hk).evalR cst leaf pub
  | [], s, hs => ⟨hs, ext_refl _ _ _ s, rfl, fun k hk => absurd hk (by simp)⟩
  | e :: es, s, hs => by
    have hE : emitAll (e :: es) s = ((emitN e s).1 :: (emitAll es (emitN e s).2).1, (emitAll es (emitN e s).2).2) := rfl
    rw [hE]
    obtain ⟨i1, x1, l1, v1⟩ := emitN_correct cst leaf pub e s hs
    obtain ⟨i2, x2, len2, v2⟩ := emitAll_correct es _ i1
    refine ⟨i2, ext_trans _ _ _ x1 x2, by simp [len2], fun k hk => ?_⟩
    rcases k with _ | k
    · exact ⟨(emitN e s).1, rfl, by rw [x2.2 _ l1, v1]; rfl⟩
    · obtain ⟨id, h1, h2⟩ := v2 k (by simpa using hk)
      exact ⟨id, by simpa using h1, by simpa using h2⟩

/-- **DAG correctness.** For every constraint `k` of the AIR, the DAG node at its root evaluates,
in any commutative ring, to the constraint's value. -/
theorem dag_correct (air : Air) (k : ℕ) (hk : k < air.constraints.length) :
    ∃ id, air.toDag.2[k]? = some id ∧
      (runDag cst leaf pub air.toDag.1).getD id 0 = (air.constraints[k]'hk).evalR cst leaf pub := by
  have h0 : Inv cst leaf pub ({} : DagState) := fun e id h => by simp at h
  obtain ⟨-, -, -, hv⟩ := emitAll_correct cst leaf pub air.constraints {} h0
  exact hv k hk

end Correct

end StarkedAir
