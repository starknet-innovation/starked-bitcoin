/-
**The header MMR and its inclusion proofs (D-033, PROOF-STORE).** The canonical Merkle Mountain
Range over leaves `L`, as `HeaderTree.HTree`: perfect trees over the binary decomposition of `|L|`
(largest first), bagged right to left. An inclusion proof is a list of steps, leaf to root, each a
sibling and its side; the verifier recomputes the root and checks the sides against the leaf's
position (`HTree.sides`; Zig `header_tree.inclusionSides`, cross-checked on `testdata/mmr_sides.txt`).

`inclusion_sound`: a path whose sides are leaf `h`'s and whose recomputed root is the tree's root
proves `leaf = leaves[h]`, unless the node hash has a collision. It holds for every tree; for the
chain proof the tree is `mmr` of the block hashes (`mmr_leaves`), whose shape the outer verifier
fixes through the root key and the segment plan (`store.verifyChain`; trusted, Zig).
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

end StarkedAir.Spec.Mmr
