/-
**Aggregation with the header commitment tree (HC-HASHTREE, D-033).** Public inputs gain the tree
root `T` as 16 limbs at indices 108–123 (`pubT`). `PubValidT` extends `PubValid`: the segment's
headers `hs` are also the leaves (as block hashes, in height order) of a binary tree whose root's
limbs are `pubT`. Leaves get it from `tree_root_limbs` (the root entry `node(K, 0, pubT)` balances
the (headers, tree) system); nodes from `NodeOut`, the node circuit's specification: indices below
108 are `combine`'s, and the root limbs are those of `hnode` of the children's roots (the circuit
range-checks the children's limbs, packs them into words, hashes, and splits the output back).

The tree's shape is whatever the recursion built; the verifier pins it through the identity key
(`expectedRoot` in `src/recursion/node.zig`), which is where an inclusion proof reads it from.
-/
import StarkedAir.Gadgets.Aggregate
import StarkedAir.Gadgets.HeaderTreeSound

namespace StarkedAir.HeaderTree

open StarkedAir StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin Spec.HeaderTree

/-- The tree-root limbs of public inputs `p`. -/
def pubT (p : ℕ → F) : List F := (List.range 16).map fun i => p (108 + i)

/-- **Proven public inputs with a tree.** -/
def PubValidT (p : ℕ → F) : Prop :=
  WorkInOk p → WorkOutOk p ∧ ∃ H hs, PubSeg p H hs ∧ ∃ t : HTree,
    t.leaves = (List.range H).map (fun j => sha256d (hs j)) ∧ pubT p = limbsOf t.root

theorem PubValidT.toPubValid {p : ℕ → F} (v : PubValidT p) : PubValid p := fun hin =>
  let ⟨o, H, hs, f, _⟩ := v hin; ⟨o, H, hs, f⟩

/-! ### Public inputs that agree below index 108 -/

def Low (p q : ℕ → F) : Prop := ∀ k < 108, p k = q k

section Low

variable {p q : ℕ → F} (h : Low p q)
include h

theorem pubWord_low {i : ℕ} (hi : i + 1 < 108) : pubWord p i = pubWord q i := by
  unfold pubWord; rw [h i (by omega), h (i + 1) hi]

theorem pubState_low {b : ℕ} (hb : b + 16 ≤ 108) : pubState p b = pubState q b := by
  unfold pubState; congr 1 <;> exact pubWord_low h (by omega)

theorem pubWork_low {b : ℕ} (hb : b + 10 ≤ 108) : pubWork p b = pubWork q b := by
  unfold pubWork
  exact Finset.sum_congr rfl (fun l hl => by rw [h _ (by have := Finset.mem_range.mp hl; omega)])

theorem pubWindow_low : pubWindow p = pubWindow q := by
  unfold pubWindow
  rw [pubWord_low h (by norm_num)]
  congr 1
  exact List.map_congr_left (fun k hk => by rw [pubWord_low h (by have := List.mem_range.mp hk; omega)])

theorem decodeIn_low (w : List ℕ) : decodeIn p w = decodeIn q w := by
  unfold decodeIn
  rw [pubState_low h (by norm_num), pubWord_low h (i := 32) (by norm_num), pubWord_low h (i := 34) (by norm_num),
    pubWord_low h (i := 44) (by norm_num), pubWord_low h (i := 36) (by norm_num), pubWork_low h (by norm_num)]

theorem decodeOut_low : decodeOut p = decodeOut q := by
  unfold decodeOut
  rw [pubState_low h (by norm_num), pubWord_low h (i := 38) (by norm_num), pubWord_low h (i := 40) (by norm_num),
    pubWord_low h (i := 46) (by norm_num), pubWord_low h (i := 42) (by norm_num), pubWork_low h (by norm_num)]
  congr 1
  exact List.map_congr_left (fun k hk => by rw [pubWord_low h (by have := List.mem_range.mp hk; omega)])

theorem workIn_low : WorkInOk p ↔ WorkInOk q :=
  forall_congr' fun l => imp_congr_right fun hl => by rw [h _ (by omega)]

theorem workOut_low : WorkOutOk p ↔ WorkOutOk q :=
  forall_congr' fun l => imp_congr_right fun hl => by rw [h _ (by omega)]

theorem pubSeg_low {H : ℕ} {hs : ℕ → ℕ → Word} : PubSeg p H hs ↔ PubSeg q H hs := by
  unfold PubSeg
  simp only [pubWindow_low h, decodeIn_low h, decodeOut_low h]

end Low

/-! ### Nodes -/

/-- **The node circuit's output** `out` over children `pL`, `pR`. -/
def NodeOut (pL pR out : ℕ → F) : Prop :=
  Low out (combine pL pR) ∧
  ∀ a b, pubT pL = limbsOf a → pubT pR = limbsOf b → pubT out = limbsOf (hnode a b)

theorem leaves_cat (H1 H2 : ℕ) (hs1 hs2 : ℕ → ℕ → Word) :
    (List.range H1).map (fun j => sha256d (hs1 j)) ++ (List.range H2).map (fun j => sha256d (hs2 j)) =
      (List.range (H1 + H2)).map (fun j => sha256d (catHs H1 hs1 hs2 j)) := by
  rw [List.range_add, List.map_append, List.map_map]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · exact List.map_congr_left (fun j hj => by simp only [catHs, if_pos (List.mem_range.mp hj)])
  · exact List.map_congr_left (fun j _ => by
      simp only [Function.comp, catHs, if_neg (show ¬ H1 + j < H1 by omega), Nat.add_sub_cancel_left])

/-- **Composition.** -/
theorem pub_compose_T {pL pR out : ℕ → F} (vL : PubValidT pL) (vR : PubValidT pR) (l : PubLink pL pR)
    (n : NodeOut pL pR out) : PubValidT out := by
  intro hin
  rw [workIn_low n.1, workIn_combine] at hin
  obtain ⟨outL, H1, hs1, fL, t1, lv1, rt1⟩ := vL hin
  have hinR : WorkInOk pR := fun k hk => by rw [l.2.2.2.2.2.2.2.2.1 k hk]; exact outL k hk
  obtain ⟨outR, H2, hs2, fR, t2, lv2, rt2⟩ := vR hinR
  refine ⟨(workOut_low n.1).mpr (workOut_combine.mpr outR), H1 + H2, catHs H1 hs1 hs2,
    (pubSeg_low n.1).mpr (seg_compose fL fR l), .node t1 t2, ?_, n.2 _ _ rt1 rt2⟩
  rw [HTree.leaves, lv1, lv2, leaves_cat]

/-! ### Leaves -/

/-- **Leaves.** Public inputs `pub` (header-chain inputs, then `T`'s limbs) of a satisfied (headers,
tree) system with `2^L` rows that balances with the root entry `node(L − 8, 0, pubT pub)`. -/
theorem leaf_valid_T {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
    (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) (hL : 8 ≤ L) (hL28 : L ≤ 28)
    (hsat : sys.SatisfiedExt inst pub [(REL_NODE, ((L - 8 : ℕ) : F) :: 0 :: pubT pub, -1)]) :
    PubValidT pub := by
  have hh : HeaderChain.air.Satisfied L pub (inst 0).main := by
    have := hsat.1 0 (by decide); rw [h0L] at this; exact this
  have hx := tree_root_limbs h0L h1L hL hL28 hsat
  have hhash := (chain_sound_v2 hh hL).1
  have hK : 2 ^ (L - 8) = 2 ^ L / 256 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.pow_div hL (by norm_num)]
  intro hin
  refine ⟨(leaf_valid hh hL hin).1, 2 ^ L / 256, headerWord (inst 0).main,
    fun w hw => header_chain_sound hh hL w hw hin, perfect (leafHash inst) (L - 8) 0, ?_, ?_⟩
  · rw [perfect_leaves, hK]
    exact List.map_congr_left (fun j hj => by
      rw [Nat.mul_zero, Nat.zero_add]; exact ((hhash j (List.mem_range.mp hj)).1).symm)
  · rw [perfect_root]; exact hx

/-! ### The root -/

/-- **The root.** Proven public inputs whose input state is genesis' give a valid chain of headers
from genesis to the decoded tip, and a binary tree over those headers' block hashes, in height
order, whose root's limbs are `pubT p`. -/
theorem chain_from_genesis_T {p : ℕ → F} (v : PubValidT p)
    (hhash : ∀ k < 16, p k = 0) (hh : p 32 = 0 ∧ p 33 = 0) (hwin : pubWindow p = sentinel)
    (hwork : ∀ l < 10, p (88 + l) = 0) :
    ∃ H hs, SegmentValid H hs
      ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 ∧
      ∃ t : HTree, t.leaves = (List.range H).map (fun j => sha256d (hs j)) ∧ pubT p = limbsOf t.root := by
  obtain ⟨-, H, hs, f, t, lv, rt⟩ := v (fun l hl => by rw [hwork l hl]; simp)
  exact ⟨H, hs, seg_from_genesis f hh hwin hwork, genesis_prev hhash, t, lv, rt⟩

end StarkedAir.HeaderTree
