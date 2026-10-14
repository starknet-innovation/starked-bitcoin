/-
**The header MMR and its inclusion proofs (D-033, PROOF-STORE).** The canonical Merkle Mountain
Range over leaves `L`, as `HeaderTree.HTree`: perfect trees over the binary decomposition of `|L|`
(largest first), bagged right to left. An inclusion proof is a list of steps, leaf to root, each a
sibling and its side; the verifier recomputes the root and checks the sides against the leaf's
position (`HTree.sides`; Zig `header_tree.inclusionSides`, cross-checked on `testdata/mmr_sides.txt`).

`inclusion_sound`: a path whose sides are leaf `h`'s and whose recomputed root is the tree's root
proves `leaf = leaves[h]`, unless the node hash has a collision. `Collision` is provable
(`collision_true`), so use `inclusion_soundC` / `mmr_inclusionC`, which name the colliding inputs. It holds for every tree; for the
chain proof the tree is `mmr` of the block hashes (`mmr_leaves`, `mmr_inclusion`).

`fold_eq_mmr`: folding an aligned segment plan with the prover's push-and-merge stack and bagging
gives `mmr`. The outer verifier fixes the plan through the root key and checks it is aligned
(`store.verifyChain`, `HT.validPlan`); that the Zig fold is this model stays trusted (tested).
-/
import StarkedAir.Spec.HeaderTree

namespace StarkedAir.Spec.Mmr

open StarkedAir.Spec.Sha256 (State)
open StarkedAir.Spec.HeaderTree (HTree hnode)

/-! ### Paths -/

/-- One step of a path: the sibling, and whether it sits on the left. -/
structure Step where
  sibling : State
  left : Bool

/-- Hash `x` with a step's sibling, on the step's side. -/
def Step.up (s : Step) (x : State) : State := if s.left then hnode s.sibling x else hnode x s.sibling

/-- The root a path (leaf to root) recomputes, as Zig's `verifyInclusion`. -/
def pathRoot (leaf : State) (steps : List Step) : State := steps.foldl (fun x s => s.up x) leaf

/-- Number of leaves. -/
def _root_.StarkedAir.Spec.HeaderTree.HTree.size (t : HTree) : ℕ := t.leaves.length

/-- The sides of leaf `h`'s path in `t`, root first (`false`: the sibling is on the right). -/
def _root_.StarkedAir.Spec.HeaderTree.HTree.sidesRev : HTree → ℕ → List Bool
  | .leaf _, _ => []
  | .node l r, h => if h < l.size then false :: l.sidesRev h else true :: r.sidesRev (h - l.size)

/-- The sides of leaf `h`'s path, leaf to root (the order of a path). -/
def _root_.StarkedAir.Spec.HeaderTree.HTree.sides (t : HTree) (h : ℕ) : List Bool := (t.sidesRev h).reverse

/-- A collision of the node hash. -/
def Collision : Prop := ∃ a b c d : State, (a, b) ≠ (c, d) ∧ hnode a b = hnode c d

/-- The root-first form of `pathRoot`. -/
def pathRootRev (leaf : State) : List Step → State
  | [] => leaf
  | s :: r => s.up (pathRootRev leaf r)

theorem pathRoot_rev (leaf : State) (steps : List Step) : pathRoot leaf steps = pathRootRev leaf steps.reverse := by
  unfold pathRoot
  induction steps using List.reverseRecOn with
  | nil => rfl
  | append_singleton r s ih => simp [List.foldl_append, ih, pathRootRev]

theorem inclusion_sound_rev : ∀ (t : HTree) (h : ℕ) (leaf : State) (rs : List Step),
    h < t.size → rs.map Step.left = t.sidesRev h → pathRootRev leaf rs = t.root →
    t.leaves[h]? = some leaf ∨ Collision
  | .leaf s, h, leaf, rs, hh, hs, hr => by
    simp only [HTree.size, HTree.leaves, List.length_singleton, Nat.lt_one_iff] at hh
    subst hh
    simp only [HTree.sidesRev, List.map_eq_nil_iff] at hs
    subst hs
    simp only [pathRootRev, HTree.root] at hr
    simp [HTree.leaves, hr]
  | .node l r, h, leaf, rs, hh, hs, hr => by
    match rs with
    | [] => simp [HTree.sidesRev] at hs; split at hs <;> simp at hs
    | s :: rest =>
      simp only [pathRootRev, HTree.root, Step.up] at hr
      simp only [List.map_cons, HTree.sidesRev] at hs
      by_cases hl : h < l.size
      · simp only [hl, ite_true, List.cons.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, Bool.false_eq_true, ite_false] at hr
        by_cases he : (pathRootRev leaf rest, s.sibling) = (l.root, r.root)
        · simp only [Prod.mk.injEq] at he
          rcases inclusion_sound_rev l h leaf rest hl hs2 he.1 with h1 | h1
          · left; simp only [HTree.leaves]; rw [List.getElem?_append_left (by simpa [HTree.size] using hl)]; exact h1
          · exact Or.inr h1
        · exact Or.inr ⟨_, _, _, _, he, hr⟩
      · simp only [hl, ite_false, List.cons.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, ite_true] at hr
        have hl' : l.size ≤ h := Nat.le_of_not_lt hl
        have hrs : h - l.size < r.size := by
          simp only [HTree.size, HTree.leaves, List.length_append] at hh ⊢; unfold HTree.size at hl'; omega
        by_cases he : (s.sibling, pathRootRev leaf rest) = (l.root, r.root)
        · simp only [Prod.mk.injEq] at he
          rcases inclusion_sound_rev r (h - l.size) leaf rest hrs hs2 he.2 with h1 | h1
          · left; simp only [HTree.leaves]
            rw [List.getElem?_append_right (by simpa [HTree.size] using hl')]; exact h1
          · exact Or.inr h1
        · exact Or.inr ⟨_, _, _, _, he, hr⟩

/-- **Inclusion soundness.** A path (leaf to root) whose sides are leaf `h`'s in `t` and whose
recomputed root is `t`'s proves that leaf `h` of `t` is `leaf`, unless the node hash collides. -/
theorem inclusion_sound (t : HTree) (h : ℕ) (leaf : State) (steps : List Step)
    (hh : h < t.size) (hs : steps.map Step.left = t.sides h) (hr : pathRoot leaf steps = t.root) :
    t.leaves[h]? = some leaf ∨ Collision := by
  rw [pathRoot_rev] at hr
  refine inclusion_sound_rev t h leaf steps.reverse hh ?_ hr
  rw [List.map_reverse, hs, HTree.sides, List.reverse_reverse]

/-! ### The canonical MMR -/

/-- A filler for the empty list (never reached for non-empty leaves). -/
def zeroState : State := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- The perfect tree over `L` (`|L| = 2^k`): halves, recursively. -/
def bal : ℕ → List State → HTree
  | 0, L => .leaf (L.headD zeroState)
  | k + 1, L => .node (bal k (L.take (2 ^ k))) (bal k (L.drop (2 ^ k)))

theorem bal_leaves : ∀ (k : ℕ) (L : List State), L.length = 2 ^ k → (bal k L).leaves = L
  | 0, L, h => by
    match L, h with
    | [x], _ => rfl
  | k + 1, L, h => by
    simp only [bal, HTree.leaves]
    rw [bal_leaves k _ (by rw [List.length_take, h, pow_succ]; omega),
      bal_leaves k _ (by rw [List.length_drop, h, pow_succ]; omega), List.take_append_drop]

/-- **The canonical MMR** over a non-empty `L`: the perfect tree over the first `2^k` leaves
(`2^k` the largest power of two at most `|L|`), bagged with the MMR of the rest. -/
def mmr (L : List State) : HTree :=
  if h : L.length ≤ 1 then .leaf (L.headD zeroState)
  else
    let k := Nat.log 2 L.length
    if L.length = 2 ^ k then bal k L
    else .node (bal k (L.take (2 ^ k))) (mmr (L.drop (2 ^ k)))
termination_by L.length
decreasing_by
  simp only [List.length_drop]
  have : 0 < 2 ^ Nat.log 2 L.length := Nat.two_pow_pos _
  omega

theorem mmr_leaves (L : List State) (hL : L ≠ []) : (mmr L).leaves = L := by
  induction L using WellFounded.induction (InvImage.wf List.length Nat.lt_wfRel.wf) with
  | _ L ih =>
    unfold mmr
    split
    · match L, hL with
      | [x], _ => rfl
      | _ :: _ :: _, _ => simp_all
    · rename_i h1
      have hn : 2 ≤ L.length := by omega
      have hle : 2 ^ Nat.log 2 L.length ≤ L.length := Nat.pow_log_le_self 2 (by omega)
      have hlt : L.length < 2 ^ (Nat.log 2 L.length + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      simp only
      split
      · rename_i heq; exact bal_leaves _ _ heq
      · rename_i hne
        simp only [HTree.leaves]
        rw [bal_leaves _ _ (by simp; omega), ih _ (by simp only [InvImage, List.length_drop]; have := Nat.two_pow_pos (Nat.log 2 L.length); show _ < _; omega)
          (by intro h; simp [List.drop_eq_nil_iff] at h; omega), List.take_append_drop]

/-- **The MMR inclusion statement.** For non-empty leaves `L`, a path whose sides are leaf `h`'s
in `mmr L` and whose recomputed root is `mmr L`'s proves `L[h] = leaf`, unless the node hash
collides. -/
theorem mmr_inclusion (L : List State) (hL : L ≠ []) (h : ℕ) (leaf : State) (steps : List Step)
    (hh : h < L.length) (hs : steps.map Step.left = (mmr L).sides h) (hr : pathRoot leaf steps = (mmr L).root) :
    L[h]? = some leaf ∨ Collision := by
  have := inclusion_sound (mmr L) h leaf steps (by rw [HTree.size, mmr_leaves L hL]; exact hh) hs hr
  rwa [mmr_leaves L hL] at this

/-! ### Inclusion with a named collision

`Collision` is a pigeonhole fact (pairs of states outnumber states: `collision_true`), so the
`… ∨ Collision` forms above say nothing. The forms below name the colliding inputs: the pairs a
path's check compares (`pathPairsRev`), all computed from the tree, the leaf and the path. -/

/-- `Collision` is provable: `hnode` maps pairs of states to states, so it is not injective. -/
theorem collision_true : Collision := by
  have hfin : Finite State := Finite.of_injective
    (fun s : State => (s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h)) fun x y e => by
      cases x; cases y; simp only [Prod.mk.injEq] at e; obtain ⟨_, _, _, _, _, _, _, _⟩ := e; subst_vars; rfl
  by_contra hc
  have hinj : Function.Injective (fun p : State × State => hnode p.1 p.2) := fun p q e => by
    by_contra hne
    exact hc ⟨p.1, p.2, q.1, q.2, hne, e⟩
  have h2 : 1 < Nat.card State := Finite.one_lt_card_iff_nontrivial.mpr
    ⟨⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0, 0, 0, 0⟩, by simp⟩⟩
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hle
  nlinarith

/-- A node-hash collision among the given pairs of inputs. -/
def CollidesIn (ps : List ((State × State) × (State × State))) : Prop :=
  ∃ pq ∈ ps, pq.1 ≠ pq.2 ∧ hnode pq.1.1 pq.1.2 = hnode pq.2.1 pq.2.2

/-- The inputs a root-first path's check compares: at each node, the recomputed (child, sibling) in
the step's order against the tree's children's roots. -/
def pathPairsRev : HTree → ℕ → State → List Step → List ((State × State) × (State × State))
  | .node l r, h, leaf, s :: rest =>
    if h < l.size then ((pathRootRev leaf rest, s.sibling), (l.root, r.root)) :: pathPairsRev l h leaf rest
    else ((s.sibling, pathRootRev leaf rest), (l.root, r.root)) :: pathPairsRev r (h - l.size) leaf rest
  | _, _, _, _ => []

theorem inclusion_sound_revC : ∀ (t : HTree) (h : ℕ) (leaf : State) (rs : List Step),
    h < t.size → rs.map Step.left = t.sidesRev h → pathRootRev leaf rs = t.root →
    t.leaves[h]? = some leaf ∨ CollidesIn (pathPairsRev t h leaf rs)
  | .leaf s, h, leaf, rs, hh, hs, hr => by
    simp only [HTree.size, HTree.leaves, List.length_singleton, Nat.lt_one_iff] at hh
    subst hh
    simp only [HTree.sidesRev, List.map_eq_nil_iff] at hs
    subst hs
    simp only [pathRootRev, HTree.root] at hr
    simp [HTree.leaves, hr]
  | .node l r, h, leaf, rs, hh, hs, hr => by
    match rs with
    | [] => simp [HTree.sidesRev] at hs; split at hs <;> simp at hs
    | s :: rest =>
      simp only [pathRootRev, HTree.root, Step.up] at hr
      simp only [List.map_cons, HTree.sidesRev] at hs
      by_cases hl : h < l.size
      · simp only [hl, ite_true, List.cons.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, Bool.false_eq_true, ite_false] at hr
        simp only [pathPairsRev, hl, ite_true]
        by_cases he : (pathRootRev leaf rest, s.sibling) = (l.root, r.root)
        · simp only [Prod.mk.injEq] at he
          rcases inclusion_sound_revC l h leaf rest hl hs2 he.1 with h1 | ⟨pq, hm, hc⟩
          · left; simp only [HTree.leaves]; rw [List.getElem?_append_left (by simpa [HTree.size] using hl)]; exact h1
          · exact Or.inr ⟨pq, List.mem_cons_of_mem _ hm, hc⟩
        · exact Or.inr ⟨_, List.mem_cons_self .., he, hr⟩
      · simp only [hl, ite_false, List.cons.injEq] at hs
        obtain ⟨hs1, hs2⟩ := hs
        simp only [hs1, ite_true] at hr
        simp only [pathPairsRev, hl, ite_false]
        have hl' : l.size ≤ h := Nat.le_of_not_lt hl
        have hrs : h - l.size < r.size := by
          simp only [HTree.size, HTree.leaves, List.length_append] at hh ⊢; unfold HTree.size at hl'; omega
        by_cases he : (s.sibling, pathRootRev leaf rest) = (l.root, r.root)
        · simp only [Prod.mk.injEq] at he
          rcases inclusion_sound_revC r (h - l.size) leaf rest hrs hs2 he.2 with h1 | ⟨pq, hm, hc⟩
          · left; simp only [HTree.leaves]
            rw [List.getElem?_append_right (by simpa [HTree.size] using hl')]; exact h1
          · exact Or.inr ⟨pq, List.mem_cons_of_mem _ hm, hc⟩
        · exact Or.inr ⟨_, List.mem_cons_self .., he, hr⟩

/-- **Inclusion soundness, with a named collision** (`inclusion_sound`): the path proves leaf `h` of
`t` is `leaf`, or two of the inputs it compares collide. -/
theorem inclusion_soundC (t : HTree) (h : ℕ) (leaf : State) (steps : List Step)
    (hh : h < t.size) (hs : steps.map Step.left = t.sides h) (hr : pathRoot leaf steps = t.root) :
    t.leaves[h]? = some leaf ∨ CollidesIn (pathPairsRev t h leaf steps.reverse) := by
  rw [pathRoot_rev] at hr
  refine inclusion_sound_revC t h leaf steps.reverse hh ?_ hr
  rw [List.map_reverse, hs, HTree.sides, List.reverse_reverse]

/-- **The MMR inclusion statement, with a named collision** (`mmr_inclusion`). -/
theorem mmr_inclusionC (L : List State) (hL : L ≠ []) (h : ℕ) (leaf : State) (steps : List Step)
    (hh : h < L.length) (hs : steps.map Step.left = (mmr L).sides h) (hr : pathRoot leaf steps = (mmr L).root) :
    L[h]? = some leaf ∨ CollidesIn (pathPairsRev (mmr L) h leaf steps.reverse) := by
  have := inclusion_soundC (mmr L) h leaf steps (by rw [HTree.size, mmr_leaves L hL]; exact hh) hs hr
  rwa [mmr_leaves L hL] at this

/-! ### Folding an aligned segment plan (the prover's stack, Zig `pushPeak`/`bagPeaks`)

A stack entry `(k, A)` is the perfect tree `bal k A` over `|A| = 2^k` leaves. Pushing merges the top
two while their sizes are equal; bagging joins the peaks right to left. A plan of segment sizes
`2^k` is aligned when each segment's start is a multiple of its size (Zig `validPlan`:
`n ≤ lowbit(start)`, the same for powers of two). -/

/-- Push onto a stack (top first), merging equal sizes. -/
def push : List (ℕ × List State) → ℕ × List State → List (ℕ × List State)
  | [], x => [x]
  | (k, A) :: rest, (j, B) => if k = j then push rest (k + 1, A ++ B) else (j, B) :: (k, A) :: rest

/-- Bag a stack given bottom first: `node p₀ (node p₁ (… pₙ))`. -/
def bagB : List (ℕ × List State) → HTree
  | [] => .leaf zeroState
  | [e] => bal e.1 e.2
  | e :: rest => .node (bal e.1 e.2) (bagB rest)

/-- Bag a stack (top first), as Zig `bagPeaks`. -/
def bag (st : List (ℕ × List State)) : HTree := bagB st.reverse

/-- Fold a plan of segment log sizes from position `m` onto `st`. -/
def foldPlan (L : List State) : ℕ → List ℕ → List (ℕ × List State) → List (ℕ × List State)
  | _, [], st => st
  | m, k :: ks, st => foldPlan L (m + 2 ^ k) ks (push st (k, (L.drop m).take (2 ^ k)))

/-- Each segment starts at a multiple of its size. -/
def Aligned : ℕ → List ℕ → Prop
  | _, [] => True
  | m, k :: ks => 2 ^ k ∣ m ∧ Aligned (m + 2 ^ k) ks

/-- The stack invariant: the peaks' leaves, bottom first, are `P`; each peak is perfect; sizes
strictly increase from top to bottom. -/
structure Inv (st : List (ℕ × List State)) (P : List State) : Prop where
  leaves : (st.reverse.map Prod.snd).flatten = P
  perfect : ∀ e ∈ st, e.2.length = 2 ^ e.1
  sorted : st.Pairwise (fun a b => a.1 < b.1)

theorem bal_append (k : ℕ) (A B : List State) (hA : A.length = 2 ^ k) :
    bal (k + 1) (A ++ B) = .node (bal k A) (bal k B) := by
  have h1 : A.take (2 ^ k) = A := List.take_of_length_le (le_of_eq hA)
  have h2 : A.drop (2 ^ k) = [] := List.drop_eq_nil_of_le (le_of_eq hA)
  simp only [bal, List.take_append_of_le_length (le_of_eq hA.symm), List.drop_append_of_le_length (le_of_eq hA.symm),
    h1, h2, List.nil_append]

theorem inv_length {st : List (ℕ × List State)} {P : List State} (h : Inv st P) :
    P.length = (st.map fun e => 2 ^ e.1).sum := by
  rw [← h.leaves, List.length_flatten, List.map_map, List.map_reverse, List.sum_reverse]
  congr 1
  apply List.map_congr_left
  intro e he
  exact h.perfect e he

theorem push_inv : ∀ (st : List (ℕ × List State)) (P B : List State) (j : ℕ), Inv st P →
    B.length = 2 ^ j → (∀ e ∈ st.head?, j ≤ e.1) → Inv (push st (j, B)) (P ++ B)
  | [], P, B, j, h, hB, _ => by
    have : P = [] := by simpa using h.leaves.symm
    subst this
    exact ⟨by simp [push], by simp [push, hB], by simp [push]⟩
  | (k, A) :: rest, P, B, j, h, hB, htop => by
    have hk : j ≤ k := htop (k, A) (by simp)
    have hA : A.length = 2 ^ k := h.perfect (k, A) (by simp)
    have hP : P = (rest.reverse.map Prod.snd).flatten ++ A := by
      rw [← h.leaves]; simp
    have hsorted := h.sorted
    rw [List.pairwise_cons] at hsorted
    by_cases hkj : k = j
    · subst hkj
      simp only [push, ite_true]
      have hrest : Inv rest (rest.reverse.map Prod.snd).flatten :=
        ⟨rfl, fun e he => h.perfect e (by simp [he]), hsorted.2⟩
      have := push_inv rest _ (A ++ B) (k + 1) hrest (by simp [hA, hB, pow_succ]; ring)
        (fun e he => by
          have := hsorted.1 e (List.mem_of_mem_head? he)
          omega)
      rwa [hP, List.append_assoc]
    · have hlt : j < k := lt_of_le_of_ne hk (Ne.symm hkj)
      simp only [push, hkj, ite_false]
      refine ⟨?_, ?_, ?_⟩
      · rw [← h.leaves]; simp
      · intro e he
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hB
        · exact h.perfect e (List.mem_cons.mpr he)
      · rw [List.pairwise_cons]
        refine ⟨fun e he => ?_, h.sorted⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact hlt
        · exact lt_trans hlt (hsorted.1 e he)

/-- The top peak bounds an aligned next segment. -/
theorem top_le {st : List (ℕ × List State)} {P : List State} (h : Inv st P) {j : ℕ}
    (hj : 2 ^ j ∣ P.length) : ∀ e ∈ st.head?, j ≤ e.1 := by
  intro e he
  match st, he with
  | (k, A) :: rest, he =>
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at he
    subst he
    by_contra hlt
    push_neg at hlt
    have hsorted := h.sorted
    rw [List.pairwise_cons] at hsorted
    rw [inv_length h] at hj
    simp only [List.map_cons, List.sum_cons] at hj
    -- Every deeper peak is a multiple of `2^(k+1)`, and so is `2^j`.
    have hrest : 2 ^ (k + 1) ∣ (rest.map fun e => 2 ^ e.1).sum := by
      apply List.dvd_sum
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨e, he, rfl⟩ := hx
      exact Nat.pow_dvd_pow 2 (hsorted.1 e he)
    have hkj : 2 ^ (k + 1) ∣ 2 ^ j := Nat.pow_dvd_pow 2 hlt
    have h3 := dvd_trans hkj hj
    rw [Nat.add_comm (2 ^ k)] at h3
    have : 2 ^ (k + 1) ∣ 2 ^ k := (Nat.dvd_add_right hrest).mp h3
    have := Nat.le_of_dvd (Nat.two_pow_pos _) this
    rw [pow_succ] at this
    have := Nat.two_pow_pos k
    omega

theorem foldPlan_inv (L : List State) : ∀ (ks : List ℕ) (m : ℕ) (st : List (ℕ × List State)),
    Inv st (L.take m) → Aligned m ks → m + (ks.map (2 ^ ·)).sum ≤ L.length →
    Inv (foldPlan L m ks st) (L.take (m + (ks.map (2 ^ ·)).sum))
  | [], m, st, h, _, _ => by simpa [foldPlan] using h
  | k :: ks, m, st, h, ha, hl => by
    simp only [List.map_cons, List.sum_cons] at hl ⊢
    simp only [foldPlan]
    have := Nat.two_pow_pos k
    have hm : (L.take m).length = m := by simp; omega
    have hseg : ((L.drop m).take (2 ^ k)).length = 2 ^ k := by
      simp only [List.length_take, List.length_drop]; have := Nat.two_pow_pos k; omega
    have h1 := push_inv st (L.take m) ((L.drop m).take (2 ^ k)) k h hseg (top_le h (by rw [hm]; exact ha.1))
    rw [← List.take_add] at h1
    have := foldPlan_inv L ks (m + 2 ^ k) _ h1 ha.2 (by omega)
    rwa [show m + 2 ^ k + (ks.map (2 ^ ·)).sum = m + (2 ^ k + (ks.map (2 ^ ·)).sum) by ring] at this

/-- Strictly decreasing powers (bottom first), all below `2^K`, sum below `2^K`. -/
theorem sum_lt : ∀ (B : List (ℕ × List State)) (K : ℕ), B.Pairwise (fun a b => b.1 < a.1) →
    (∀ e ∈ B, e.1 < K) → (B.map fun e => 2 ^ e.1).sum < 2 ^ K
  | [], K, _, _ => by simp
  | e :: rest, K, hs, hK => by
    rw [List.pairwise_cons] at hs
    have h1 := sum_lt rest e.1 hs.2 hs.1
    have h2 : e.1 < K := hK e (by simp)
    simp only [List.map_cons, List.sum_cons]
    have : 2 ^ (e.1 + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) h2
    rw [pow_succ] at this
    omega

theorem bagB_mmr : ∀ (B : List (ℕ × List State)) (L : List State), B ≠ [] →
    (B.map Prod.snd).flatten = L → (∀ e ∈ B, e.2.length = 2 ^ e.1) →
    B.Pairwise (fun a b => b.1 < a.1) → bagB B = mmr L
  | [], _, hB, _, _, _ => (hB rfl).elim
  | e :: rest, L, _, hl, hp, hs => by
    have he : e.2.length = 2 ^ e.1 := hp e (by simp)
    rw [List.pairwise_cons] at hs
    have hR : ((rest.map Prod.snd).flatten).length = (rest.map fun e => 2 ^ e.1).sum := by
      rw [List.length_flatten, List.map_map]; congr 1
      apply List.map_congr_left; intro x hx; exact hp x (by simp [hx])
    have hlt := sum_lt rest e.1 hs.2 hs.1
    simp only [List.map_cons, List.flatten_cons] at hl
    subst hl
    have hpos := Nat.two_pow_pos e.1
    rcases rest with _ | ⟨f, rest'⟩
    · -- One peak: `L` is the perfect tree.
      simp only [List.map_nil, List.flatten_nil, List.append_nil] at he ⊢
      simp only [bagB]
      unfold mmr
      split
      · rename_i h1
        have : e.1 = 0 := by
          by_contra h0; have : 2 ≤ 2 ^ e.1 := by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ e.1 := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [this]; simp [bal]
      · rw [he, Nat.log_pow (by norm_num)]; simp
    · have hne : ((f :: rest').map Prod.snd).flatten ≠ [] := by
        intro h0
        have := congrArg List.length h0
        rw [hR] at this
        simp only [List.length_nil, List.map_cons, List.sum_cons] at this
        have := Nat.two_pow_pos f.1
        omega
      have hRpos : 0 < (((f :: rest').map Prod.snd).flatten).length := List.length_pos_of_ne_nil hne
      have hlog : Nat.log 2 (e.2 ++ ((f :: rest').map Prod.snd).flatten).length = e.1 := by
        rw [List.length_append, he]
        apply Nat.log_eq_of_pow_le_of_lt_pow (by omega)
        rw [pow_succ]; omega
      have ih := bagB_mmr (f :: rest') _ (by simp) rfl (fun x hx => hp x (by simp [hx])) hs.2
      simp only [bagB]
      rw [ih]
      conv_rhs => unfold mmr
      rw [dif_neg (by rw [List.length_append]; omega)]
      simp only [hlog]
      rw [if_neg (by rw [List.length_append, he]; omega)]
      rw [List.take_append_of_le_length (le_of_eq he.symm), List.take_of_length_le (le_of_eq he),
        List.drop_append_of_le_length (le_of_eq he.symm), List.drop_of_length_le (le_of_eq he), List.nil_append]

/-- **The prover's fold is the canonical MMR.** Folding an aligned plan of segments that covers
`L` (non-empty) with the push-and-merge stack, then bagging, gives `mmr L`. -/
theorem fold_eq_mmr (L : List State) (hL : L ≠ []) (ks : List ℕ) (ha : Aligned 0 ks)
    (hs : (ks.map (2 ^ ·)).sum = L.length) : bag (foldPlan L 0 ks []) = mmr L := by
  have h := foldPlan_inv L ks 0 [] ⟨by simp, by simp, by simp⟩ ha (by omega)
  rw [zero_add, hs, List.take_length] at h
  unfold bag
  refine bagB_mmr _ L ?_ ?_ ?_ ?_
  · intro h0
    have := congrArg List.length h.leaves
    simp only [List.reverse_eq_nil_iff.mp h0, List.reverse_nil, List.map_nil, List.flatten_nil, List.length_nil] at this
    exact hL (List.length_eq_zero_iff.mp this.symm)
  · exact h.leaves
  · intro e he; exact h.perfect e (List.mem_reverse.mp he)
  · rw [List.pairwise_reverse]; exact h.sorted

end StarkedAir.Spec.Mmr
