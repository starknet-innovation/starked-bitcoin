/-
**Aggregating block proofs (BLOCK-REC), at the level of public inputs.** The statement a tree of block
proofs establishes, and that it is what the epoch theorem consumes.

- `BlockPubOk p`: what a block leaf proves about public inputs `p` (the block system satisfied by
  traces of one log size `≤ 23`, with a block setup): the plain verifier's guarantee for the block
  system (`plain_sound`, `Circuit/EndToEnd.lean`).
- `Rng`: a range summary (first height, block count, summed partial sum and input count, the shared
  challenge `(γ, z, α)`); `RngOk r`: every height of the range has proven public inputs with that
  height, the height's BIP30 flag and the shared challenge (with `αₖ = αᵏ`), and the sums add.
- `rng_leaf`: one proven block whose leaf checks its height-derived flag and its powers of `α` is a
  proven one-block range. `rng_node`: two proven ranges, the right one starting after the left and
  with the same challenge, give their union (what a node checks: heights link, challenges equal; it
  adds the sums). `epoch_hyps_of_rng`: a proven range gives exactly the block hypotheses of
  `epoch_systems_core` (CoinEpochCore.lean), with its summed partial sum.

What this file does not cover: the seed and the binding of block hashes to the chain (the outer verifier,
`BlockTree.lean`). The previous-block MTP is bound inside each block proof (`BlockPubOk.mtp`, D-043 part 3).
-/
import StarkedAir.Block.CoinEpochCore
import StarkedAir.Block.BlockAnc

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Spec.QM31 (QM)

/-- What a block leaf proves about public inputs `p`: the 16-component block system (`BlockAnc.lean`). -/
def BlockPubOk (p : ℕ → F) : Prop :=
  ∃ (inst : ℕ → Inst) (L : ℕ), (∀ c < 16, (inst c).logSize = L) ∧ 8 ≤ L ∧ L ≤ 23 ∧ blockSys.SatisfiedExt inst p [] ∧
    Nonempty (Setup inst p L)

/-- **The previous MTP of a proven block** (`block_mtp`): 0 below the CSV height; at and above it the
median time past of 11 headers hash-chained, in order, to a header with the block's SHA256d. -/
theorem BlockPubOk.mtp {p : ℕ → F} (hp : BlockPubOk p) :
    (p Anc.PUB_CSV = 0 ∧ p Anc.PUB_MLO = 0 ∧ p Anc.PUB_MHI = 0) ∨
    (p Anc.PUB_CSV = 1 ∧ ∃ (inst : ℕ → Inst) (b : Spec.Block.Blk) (hw : ℕ → ℕ → Spec.Sha256.Word),
      Spec.Block.parseBlock (Rb inst p) = some b ∧
      Spec.Block.stateBytes (Spec.Bitcoin.sha256d (hw Anc.NANC)) = Spec.Block.sha256d b.header ∧
      (∀ j, 1 ≤ j → j ≤ Anc.NANC → Spec.Bitcoin.prevHash (hw j) = Spec.Bitcoin.sha256d (hw (j - 1))) ∧
      (p Anc.PUB_MLO).val < 65536 ∧ (p Anc.PUB_MHI).val < 65536 ∧
      Anc.mtpOf p = Spec.Bitcoin.medianTimePast
        ((List.range Anc.NANC).map (fun k => Spec.Bitcoin.timeOf (hw k))).reverse) := by
  obtain ⟨inst, L, hL, hL8, hL24, hsat, -⟩ := hp
  rcases block_mtp hL hsat hL24 hL8 with h0 | ⟨h1, b, hw, h⟩
  · exact Or.inl h0
  · exact Or.inr ⟨h1, inst, b, hw, h⟩

/-- A range summary: blocks `lo … lo + n − 1`. -/
structure Rng where
  lo : ℕ
  n : ℕ
  s : QM
  nin : ℕ
  γ : QM
  z : QM
  α : QM

/-- One block's obligations within a range: proven inputs at height `h`, its BIP30 flag, the challenge. -/
def BlockAt (r : Rng) (h : ℕ) (p : ℕ → F) : Prop :=
  BlockPubOk p ∧ p 2 = (h : F) ∧ p Coin.PUB_LOST = (if Spec.Coins.bip30Lost h then 1 else 0) ∧
    FpWalk.gQ p = r.γ ∧ RunSum.pQ p Coin.PUB_Z = r.z ∧ ∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = r.α ^ k

/-- **A proven range.** -/
def RngOk (r : Rng) : Prop :=
  ∃ P : ℕ → ℕ → F, (∀ i < r.n, BlockAt r (r.lo + i) (P i)) ∧
    r.s = ∑ i ∈ Finset.range r.n, RunSum.pQ (P i) Coin.PUB_S ∧
    r.nin = ∑ i ∈ Finset.range r.n, (P i Coin.PUB_NIN).val

/-- The one-block summary of public inputs `p` at height `h`. -/
noncomputable def leafRng (h : ℕ) (p : ℕ → F) : Rng :=
  ⟨h, 1, RunSum.pQ p Coin.PUB_S, (p Coin.PUB_NIN).val, FpWalk.gQ p, RunSum.pQ p Coin.PUB_Z,
    RunSum.pQ p (Coin.PUB_ALPHA 1)⟩

/-- **Leaves.** A proven block at height `h` whose leaf checks its BIP30 flag and `αₖ = α₁ᵏ`. -/
theorem rng_leaf {h : ℕ} {p : ℕ → F} (hp : BlockPubOk p) (h2 : p 2 = (h : F))
    (hlost : p Coin.PUB_LOST = if Spec.Coins.bip30Lost h then 1 else 0)
    (hα : ∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ p (Coin.PUB_ALPHA 1) ^ k) :
    RngOk (leafRng h p) := by
  refine ⟨fun _ => p, fun i hi => ?_, by simp [leafRng], by simp [leafRng]⟩
  have hi0 : i = 0 := by simp [leafRng] at hi; omega
  subst hi0
  exact ⟨hp, by simpa [leafRng] using h2, by simpa [leafRng] using hlost, rfl, rfl, hα⟩

/-- The union of two consecutive ranges with one challenge. -/
noncomputable def joinRng (l r : Rng) : Rng := ⟨l.lo, l.n + r.n, l.s + r.s, l.nin + r.nin, l.γ, l.z, l.α⟩

/-- **Nodes.** Two proven ranges, the right one starting where the left one ends, with the same
challenge, give their union. -/
theorem rng_node {l r : Rng} (hl : RngOk l) (hr : RngOk r) (hlink : r.lo = l.lo + l.n)
    (hγ : r.γ = l.γ) (hz : r.z = l.z) (hα : r.α = l.α) : RngOk (joinRng l r) := by
  obtain ⟨PL, hPL, hsL, hnL⟩ := hl
  obtain ⟨PR, hPR, hsR, hnR⟩ := hr
  have eB : ∀ h p, BlockAt (joinRng l r) h p ↔ BlockAt l h p := fun _ _ => Iff.rfl
  have eBr : ∀ h p, BlockAt r h p → BlockAt l h p := by
    intro h p hb
    obtain ⟨a, b, c, d, e, f⟩ := hb
    exact ⟨a, b, c, d.trans hγ, e.trans hz, fun k hk => (f k hk).trans (by rw [hα])⟩
  have hlo : (joinRng l r).lo = l.lo := rfl
  have hn : (joinRng l r).n = l.n + r.n := rfl
  have hs : (joinRng l r).s = l.s + r.s := rfl
  have hni : (joinRng l r).nin = l.nin + r.nin := rfl
  refine ⟨fun i => if i < l.n then PL i else PR (i - l.n), fun i hi => ?_, ?_, ?_⟩
  · rw [hn] at hi
    rw [eB, hlo]
    by_cases hil : i < l.n
    · simp only [if_pos hil]
      exact hPL i hil
    · simp only [if_neg hil]
      have := eBr _ _ (hPR (i - l.n) (by omega))
      rwa [hlink, show l.lo + l.n + (i - l.n) = l.lo + i by omega] at this
  · have h1 : ∑ i ∈ Finset.range l.n, RunSum.pQ (if i < l.n then PL i else PR (i - l.n)) Coin.PUB_S =
        ∑ i ∈ Finset.range l.n, RunSum.pQ (PL i) Coin.PUB_S :=
      Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]
    have h2 : ∑ i ∈ Finset.range r.n, RunSum.pQ (if l.n + i < l.n then PL (l.n + i) else PR (l.n + i - l.n)) Coin.PUB_S =
        ∑ i ∈ Finset.range r.n, RunSum.pQ (PR i) Coin.PUB_S :=
      Finset.sum_congr rfl fun i _ => by rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rw [hs, hn, Finset.sum_range_add, h1, h2, hsL, hsR]
  · have h1 : ∑ i ∈ Finset.range l.n, ((if i < l.n then PL i else PR (i - l.n)) Coin.PUB_NIN).val =
        ∑ i ∈ Finset.range l.n, (PL i Coin.PUB_NIN).val :=
      Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]
    have h2 : ∑ i ∈ Finset.range r.n, ((if l.n + i < l.n then PL (l.n + i) else PR (l.n + i - l.n)) Coin.PUB_NIN).val =
        ∑ i ∈ Finset.range r.n, (PR i Coin.PUB_NIN).val :=
      Finset.sum_congr rfl fun i _ => by rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rw [hni, hn, Finset.sum_range_add, h1, h2, hnL, hnR]

/-- **The root.** A proven nonempty range gives the block hypotheses of `epoch_systems_core`: block
systems at the range's consecutive heights, satisfied, with their BIP30 flags and the shared
challenge, whose partial sums add to the summary's. -/
theorem epoch_hyps_of_rng {r : Rng} (hr : RngOk r) (hn : 0 < r.n) :
    ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i)),
      (∀ i < r.n, ∀ c < 15, (inst i c).logSize = L i) ∧ (∀ i < r.n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < r.n, L i ≤ 23) ∧ (∀ i < r.n, pub i 2 = ((r.lo + i : ℕ) : F)) ∧
      (∀ i < r.n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost (r.lo + i) then 1 else 0) ∧
      (∀ i < r.n, FpWalk.gQ (pub i) = r.γ) ∧ (∀ i < r.n, RunSum.pQ (pub i) Coin.PUB_Z = r.z) ∧
      (∀ i < r.n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = r.α ^ k) ∧
      ∑ i ∈ Finset.range r.n, RunSum.pQ (pub i) Coin.PUB_S = r.s := by
  obtain ⟨P, hP, hs, -⟩ := hr
  -- Beyond the range, repeat the last block (the epoch theorem wants a setup at every index).
  let idx : ℕ → ℕ := fun i => if i < r.n then i else r.n - 1
  have hidx : ∀ i, idx i < r.n := fun i => by simp only [idx]; split <;> omega
  have hok : ∀ i, BlockPubOk (P (idx i)) := fun i => (hP _ (hidx i)).1
  let inst : ℕ → ℕ → Inst := fun i => Classical.choose (hok i)
  let L : ℕ → ℕ := fun i => Classical.choose (Classical.choose_spec (hok i))
  have hspec' : ∀ i, (∀ c < 16, (inst i c).logSize = L i) ∧ 8 ≤ L i ∧ L i ≤ 23 ∧
      blockSys.SatisfiedExt (inst i) (P (idx i)) [] ∧ Nonempty (Setup (inst i) (P (idx i)) (L i)) :=
    fun i => Classical.choose_spec (Classical.choose_spec (hok i))
  have hspec : ∀ i, (∀ c < 15, (inst i c).logSize = L i) ∧ L i ≤ 23 ∧ hashSys.SatisfiedExt (inst i) (P (idx i)) [] ∧
      Nonempty (Setup (inst i) (P (idx i)) (L i)) := fun i =>
    ⟨fun c hc => (hspec' i).1 c (by omega), (hspec' i).2.2.1, (blockSys_sat (hspec' i).2.2.2.1).1, (hspec' i).2.2.2.2⟩
  have hid : ∀ i < r.n, idx i = i := fun i hi => by simp only [idx]; rw [if_pos hi]
  refine ⟨fun i => P (idx i), inst, L, fun i => Classical.choice (hspec i).2.2.2, fun i _ => (hspec i).1,
    fun i _ => (hspec i).2.2.1, fun i _ => (hspec i).2.1, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, ?_⟩
  · simp only [hid i hi]; exact (hP i hi).2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.2.2
  · rw [hs]; exact Finset.sum_congr rfl fun i hi => by simp only [hid i (Finset.mem_range.mp hi)]

end StarkedAir.Block
