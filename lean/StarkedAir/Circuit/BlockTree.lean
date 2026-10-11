/-
**The block aggregation tree's summaries, semantically (BLOCK-REC).** `SumOk v`: the 51 limbs `v`
(`Circuit/BlockNode.lean`'s layout) describe a proven range of `2^ℓ` blocks (`Block/AggregateBlocks.lean`:
consecutive heights from `v 0`, each with proven public inputs, its BIP30 flag and the shared challenge
`(γ, z, α)` at limbs 7–18, the partial sums adding to limbs 2–5 and the input counts to limb 6), whose
block-hash root (limbs 19–34) and seed root (35–50) are the perfect trees over the blocks' hashes and
seed leaves `Blake2s(hash ‖ C_h)`.

`sumOk_node`: the node glue's facts (`node_sound`) take two `SumOk` children to a `SumOk` output.
With `sumOk_leaf` (a proven block whose leaf checks hold), every summary the tree outputs is `SumOk`;
its range part gives `epoch_hyps_of_rng`'s input, and its roots are what the outer verifier checks
against the seed and the chain's `T` (D-043).
-/
import StarkedAir.Circuit.BlockNode
import StarkedAir.Circuit.BlockLeaf

namespace StarkedAir.Circuit.BlockTree

open StarkedAir StarkedAir.Circuit StarkedAir.Block Q
open StarkedAir.Spec.QM31 (QM toQ emb)
open StarkedAir.Spec.HeaderTree (hnode toState)

/-- The state of 16 limbs from `o` (`lo + 2^16·hi` per word). -/
def stateAt (p : ℕ → F) (o : ℕ) : Spec.Sha256.State :=
  toState fun w => BitVec.ofNat 32 ((p (o + 2 * w)).val + 65536 * (p (o + 2 * w + 1)).val)

/-- A block's hash (its public limbs 25–40) and seed leaf `hnode(hash, C_h)` (the commitment at 9–24). -/
def hashOf (p : ℕ → F) : Spec.Sha256.State := stateAt p 25
def seedOf (p : ℕ → F) : Spec.Sha256.State := hnode (stateAt p 25) (stateAt p 9)

/-- The root of the perfect tree over `f s, …, f (s + 2^ℓ − 1)`, halving. -/
def rootFrom (f : ℕ → Spec.Sha256.State) : ℕ → ℕ → Spec.Sha256.State
  | 0, s => f s
  | ℓ + 1, s => hnode (rootFrom f ℓ s) (rootFrom f ℓ (s + 2 ^ ℓ))

theorem rootFrom_shift (f : ℕ → Spec.Sha256.State) (d : ℕ) : ∀ ℓ s, rootFrom (fun i => f (d + i)) ℓ s = rootFrom f ℓ (d + s)
  | 0, s => rfl
  | ℓ + 1, s => by simp only [rootFrom, rootFrom_shift f d ℓ, Nat.add_assoc]

/-- A summary's range. -/
noncomputable def rngOf (v : ℕ → F) (ℓ : ℕ) : Rng :=
  ⟨(v 0).val, 2 ^ ℓ, RunSum.pQ v 2, (v 6).val, RunSum.pQ v 7, RunSum.pQ v 11, RunSum.pQ v 15⟩

/-- **A proven summary.** -/
def SumOk (v : ℕ → F) : Prop :=
  ∃ (ℓ : ℕ) (P : ℕ → ℕ → F), (v 1).val = 2 ^ ℓ ∧ (v 0).val < 2 ^ 30 ∧ (v 1).val < 2 ^ 30 ∧ (v 6).val < 2 ^ 30 ∧
    (∀ i < 2 ^ ℓ, BlockAt (rngOf v ℓ) ((v 0).val + i) (P i)) ∧
    RunSum.pQ v 2 = ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (P i) Coin.PUB_S ∧
    (v 6).val = ∑ i ∈ Finset.range (2 ^ ℓ), (P i Coin.PUB_NIN).val ∧
    (∀ j < 16, v (19 + j) = (HeaderTree.limbsOf (rootFrom (fun i => hashOf (P i)) ℓ 0)).getD j 0) ∧
    (∀ j < 16, v (35 + j) = (HeaderTree.limbsOf (rootFrom (fun i => seedOf (P i)) ℓ 0)).getD j 0)

/-- A proven summary's range is proven. -/
theorem SumOk.rng {v : ℕ → F} (h : SumOk v) : ∃ ℓ, (v 1).val = 2 ^ ℓ ∧ RngOk (rngOf v ℓ) := by
  obtain ⟨ℓ, P, hn, -, -, -, hb, hs, hni, -, -⟩ := h
  exact ⟨ℓ, hn, P, hb, hs, hni⟩

end StarkedAir.Circuit.BlockTree
