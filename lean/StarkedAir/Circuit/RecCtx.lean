/-
**The recursion's guarantee reaches the connect rules** (CONNECT-RULES, step 6 of the plan's "carry").

`Block.epoch_systems_coreS` (`Block/SigEpoch.lean`: BIP68 by height and by time, the full sigop cost) asks
two things of each block beyond `epoch_systems_core`: public input 5 is the height's CSV bit, and the
context component has at least `2^8` rows. Until now the recursion's composed statement
(`RecCR.forest_epochVW`) delivered `epoch_systems_core`'s hypotheses only.

- `CtxOk p`: the block leaf's height-derived context (`BlockCtx.ctx_sound`): the BIP34, CSV and segwit
  bits and the subsidy's limbs are the height's. `ctxOk_of_ctx`: the leaf's context program gives it.
- `BlockPubOkC p`: `BlockPubOk' p` and `CtxOk p`: what a block leaf proves, with its context.
- `MtpOk inst p`: `block_mtp`'s conclusion for the block `inst` holds (ANC-PRE-CSV: from height 11 the
  previous median time past, public inputs 3 and 7, is the median of 11 hash-chained predecessors).
- `epoch_hyps_of_rngC`: a proven range of such blocks gives every block hypothesis of
  `epoch_systems_coreS`, and `MtpOk` of every block.
- `forest_epochCW`: the same from the recursion's trust statement, with leaves guaranteeing
  `LeafAt BlockPubOkC` (or a named Blake2s collision).

The seal (`ChainSealCompose.seal_soundW`) is stated for any per-block statement `ok`; it holds at
`ok := BlockPubOkC` unchanged.
-/
import StarkedAir.Circuit.RecCR
import StarkedAir.Circuit.BlockCtx
import StarkedAir.Block.SigEpoch

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Spec.QM31 (QM)

/-- **The leaf's height-derived context**: public inputs 4, 5, 6 are the BIP34, CSV and segwit bits of
the height (input 2), and inputs 159, 160 the limbs of its subsidy. -/
def CtxOk (p : ℕ → F) : Prop :=
  ∀ H : ℕ, H < 2 ^ 30 → p 2 = (H : F) →
    p 4 = (if Spec.Block.BIP34_HEIGHT ≤ H then 1 else 0) ∧ p 5 = (if Spec.Block.CSV_HEIGHT ≤ H then 1 else 0) ∧
    p 6 = (if Spec.Block.SEGWIT_HEIGHT ≤ H then 1 else 0) ∧
    p Coin.PUB_SUBL = ((Circuit.BlockCtx.subsidy H % 2 ^ 24 : ℕ) : F) ∧
    p Coin.PUB_SUBH = ((Circuit.BlockCtx.subsidy H / 2 ^ 24 : ℕ) : F)

/-- **The leaf's context program gives `CtxOk`** (`BlockCtx.ctx_sound`): its six inputs are public inputs
2, 4, 5, 6, 159 and 160 (`block_leaf.leafCtx`). -/
theorem ctxOk_of_ctx {ρ : ℕ → Circuit.Q} {p : ℕ → F} (h : Circuit.Holds ρ Circuit.BlockCtx.ctxOps)
    (h0 : ρ 0 = ⟨p 2, 0, 0, 0⟩) (hb : ∀ j < 4, 1 ≤ j → Circuit.Q.IsBase (ρ j))
    (h1 : (ρ 1).a = p 4) (h2 : (ρ 2).a = p 5) (h3 : (ρ 3).a = p 6)
    (h4 : (ρ 4).a = p Coin.PUB_SUBL) (h5 : (ρ 5).a = p Coin.PUB_SUBH) : CtxOk p := by
  intro H hH hp
  obtain ⟨a, b, c, d, e⟩ := Circuit.BlockCtx.ctx_sound h hH (by rw [h0, hp]) hb
  exact ⟨h1 ▸ a, h2 ▸ b, h3 ▸ c, h4 ▸ d, h5 ▸ e⟩

/-- **What a block leaf proves, with its context**: the block system (`BlockPubOk'`) and the
height-derived context. -/
def BlockPubOkC (p : ℕ → F) : Prop := BlockPubOk' p ∧ CtxOk p

theorem BlockPubOkC.toV {p : ℕ → F} (h : BlockPubOkC p) : BlockPubOk' p := h.1

/-- **The previous median time past of block `inst`** (`block_mtp`'s conclusion): at heights 0–10 its
public limbs are 0; from height 11 it is the median of the times of 11 headers hash-chained, in order, to
the block's header. -/
def MtpOk (inst : ℕ → Inst) (p : ℕ → F) : Prop :=
  ((p Anc.PUB_H).val < Anc.NANC ∧ p Anc.PUB_MLO = 0 ∧ p Anc.PUB_MHI = 0) ∨
  (Anc.NANC ≤ (p Anc.PUB_H).val ∧ ∃ (b : Spec.Block.Blk) (hw : ℕ → ℕ → Spec.Sha256.Word),
    Spec.Block.parseBlock (Rb inst p) = some b ∧
    Spec.Block.stateBytes (Spec.Bitcoin.sha256d (hw Anc.NANC)) = Spec.Block.sha256d b.header ∧
    (∀ j, 1 ≤ j → j ≤ Anc.NANC → Spec.Bitcoin.prevHash (hw j) = Spec.Bitcoin.sha256d (hw (j - 1))) ∧
    (p Anc.PUB_MLO).val < 65536 ∧ (p Anc.PUB_MHI).val < 65536 ∧
    Anc.mtpOf p = Spec.Bitcoin.medianTimePast
      ((List.range Anc.NANC).map (fun k => Spec.Bitcoin.timeOf (hw k))).reverse)

/-- **The root, with the context.** A proven nonempty range of blocks with their context, below height
`2^30`, gives every block hypothesis of `epoch_systems_coreS`: those of `epoch_systems_core`
(`epoch_hyps_of_rng'`), each context component of at least `2^8` rows, and public input 5 the height's
CSV bit; and each block's previous median time past is proven (`MtpOk`). -/
theorem epoch_hyps_of_rngC {r : Rng} (hr : RngOkP BlockPubOkC r) (hn : 0 < r.n) (hh : r.lo + r.n ≤ 2 ^ 30) :
    ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < r.n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < r.n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < r.n, SizeOk (L i)) ∧ (∀ i < r.n, 8 ≤ L i 7) ∧ (∀ i < r.n, pub i 2 = ((r.lo + i : ℕ) : F)) ∧
      (∀ i < r.n, pub i 5 = if Spec.Block.CSV_HEIGHT ≤ r.lo + i then 1 else 0) ∧
      (∀ i < r.n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost (r.lo + i) then 1 else 0) ∧
      (∀ i < r.n, FpWalk.gQ (pub i) = r.γ) ∧ (∀ i < r.n, RunSum.pQ (pub i) Coin.PUB_Z = r.z) ∧
      (∀ i < r.n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = r.α ^ k) ∧
      ∑ i ∈ Finset.range r.n, RunSum.pQ (pub i) Coin.PUB_S = r.s ∧
      (∀ i < r.n, MtpOk (inst i) (pub i)) := by
  obtain ⟨P, hP, hs, -⟩ := hr
  -- Beyond the range, repeat the last block (the epoch theorem wants a setup at every index).
  let idx : ℕ → ℕ := fun i => if i < r.n then i else r.n - 1
  have hidx : ∀ i, idx i < r.n := fun i => by simp only [idx]; split <;> omega
  have hok : ∀ i, BlockPubOk' (P (idx i)) := fun i => (hP _ (hidx i)).1.1
  let inst : ℕ → ℕ → Inst := fun i => Classical.choose (hok i)
  let L : ℕ → ℕ → ℕ := fun i => Classical.choose (Classical.choose_spec (hok i))
  have hspec' : ∀ i, (∀ c < 16, (inst i c).logSize = L i c) ∧ 8 ≤ L i 7 ∧ 8 ≤ L i 11 ∧ 8 ≤ L i 15 ∧
      SizeOk (L i) ∧ blockSys.SatisfiedExt (inst i) (P (idx i)) [] ∧
      Nonempty (Setup (inst i) (P (idx i)) (L i 1)) :=
    fun i => Classical.choose_spec (Classical.choose_spec (hok i))
  have hspec : ∀ i, (∀ c < 15, (inst i c).logSize = L i c) ∧ SizeOk (L i) ∧
      hashSys.SatisfiedExt (inst i) (P (idx i)) [] ∧ Nonempty (Setup (inst i) (P (idx i)) (L i 1)) := fun i =>
    ⟨fun c hc => (hspec' i).1 c (by omega), (hspec' i).2.2.2.2.1,
      (blockSys_sat (hspec' i).2.2.2.2.2.1).1, (hspec' i).2.2.2.2.2.2⟩
  have hid : ∀ i < r.n, idx i = i := fun i hi => by simp only [idx]; rw [if_pos hi]
  refine ⟨fun i => P (idx i), inst, L, fun i => Classical.choice (hspec i).2.2.2, fun i _ => (hspec i).1,
    fun i _ => (hspec i).2.2.1, fun i _ => (hspec i).2.1, fun i _ => (hspec' i).2.1, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, fun i _ => ?_⟩
  · simp only [hid i hi]; exact (hP i hi).2.1
  · simp only [hid i hi]
    exact ((hP i hi).1.2 (r.lo + i) (by omega) (hP i hi).2.1).2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.2.1
  · simp only [hid i hi]; exact (hP i hi).2.2.2.2.2
  · rw [hs]; exact Finset.sum_congr rfl fun i hi => by simp only [hid i (Finset.mem_range.mp hi)]
  · exact block_mtp (hspec' i).1 (hspec' i).2.2.2.2.2.1 (hspec' i).2.2.2.2.1 (hspec' i).2.2.2.1

end StarkedAir.Block

namespace StarkedAir.Circuit.RecCR

open StarkedAir StarkedAir.Circuit StarkedAir.Block Q Spec.Blake2s
open StarkedAir.Circuit.BlockTree (SumOkP leafVec Linked')
open StarkedAir.Circuit.BlockRec
open StarkedAir.Circuit.BlockNode

variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **The epoch's blocks are proven with the connect rules' hypotheses, up to a named collision.** With
block leaves guaranteeing `LeafAt BlockPubOkC` (the block system and the height-derived context), a
verified forest of `n ≥ 1` blocks from height `(v₀ 0)`, below height `2^30`, gives every block hypothesis
of `Block.epoch_systems_coreS` (so BIP68 by height and by time and the full sigop cost follow, with the
set balance, as that theorem states), and each block's previous median time past is proven (`MtpOk`). -/
theorem forest_epochCW (T : TrustW Acc SatC VGates leafH nodeH blockNodeProgram (LeafAt BlockPubOkC) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : BlockRec.Tree) (v0 : ℕ → F) (rest : List (BlockRec.Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ((v0 0).val + n ≤ 2 ^ 30 →
      ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, SizeOk (L i)) ∧ (∀ i < n, 8 ≤ L i 7) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i 5 = if Spec.Block.CSV_HEIGHT ≤ (v0 0).val + i then 1 else 0) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum ∧
      (∀ i < n, MtpOk (inst i) (pub i)))) ∨
      Collides (forestPairs leafH nodeH nw lw t0 v0 rest) := by
  rcases forest_soundW (ok := BlockPubOkC) T hl hn t0 v0 rest h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, fun hh => epoch_hyps_of_rngC hr hn0 hh⟩
  · exact Or.inr c

end StarkedAir.Circuit.RecCR
