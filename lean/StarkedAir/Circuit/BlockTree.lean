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

/-! ### Helpers -/

theorem rootFrom_congr {f g : ℕ → Spec.Sha256.State} : ∀ ℓ s, (∀ i < 2 ^ ℓ, f (s + i) = g (s + i)) →
    rootFrom f ℓ s = rootFrom g ℓ s
  | 0, s, h => by simpa [rootFrom] using h 0 (by norm_num)
  | ℓ + 1, s, h => by
    have e1 := rootFrom_congr ℓ s (fun i hi => h i (by rw [pow_succ]; omega))
    have e2 := rootFrom_congr ℓ (s + 2 ^ ℓ) (fun i hi => by
      have := h (2 ^ ℓ + i) (by rw [pow_succ]; omega)
      simpa [Nat.add_assoc] using this)
    simp only [rootFrom]
    rw [e1, e2]

theorem val_add_lt30 {x y : F} (hx : x.val < 2 ^ 30) (hy : y.val < 2 ^ 30) : (x + y).val = x.val + y.val := by
  have hP : P = 2147483647 := rfl
  exact ZMod.val_add_of_lt (by omega)

theorem limbs_ext {X : Spec.Sha256.State} {g : ℕ → F} (h : ∀ j < 16, g j = (HeaderTree.limbsOf X).getD j 0) :
    HeaderTree.pubT (fun k => g (k - TB)) = HeaderTree.limbsOf X := by
  apply List.ext_getElem (by simp [HeaderTree.pubT, HeaderTree.limbsOf])
  intro j h1 h2
  have hj : j < 16 := by simpa [HeaderTree.pubT] using h1
  simp only [HeaderTree.pubT, List.getElem_map, List.getElem_range]
  rw [show 108 + j - TB = j by unfold TB; omega, h j hj, List.getD_eq_getElem _ _ h2]

theorem out_getD {pl pr : ℕ → ℕ} {b : ℕ} (i : ℕ) (hi : i < BlockNode.NSUM) :
    (BlockNode.nodeOut pl pr b).res.getD i 0 = BlockNode.outReg pl pr b i := by
  simp [BlockNode.nodeOut, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]

theorem blockAt_congr {r r' : Rng} {h : ℕ} {p : ℕ → F} (hγ : r'.γ = r.γ) (hz : r'.z = r.z) (hα : r'.α = r.α)
    (hb : BlockAt r h p) : BlockAt r' h p := by
  obtain ⟨a, b, c, d, e, f⟩ := hb
  exact ⟨a, b, c, d.trans hγ.symm, e.trans hz.symm, fun k hk => (f k hk).trans (by rw [hα])⟩

theorem pQ_congr {v w : ℕ → F} {i : ℕ} (h : ∀ j < 4, v (i + j) = w (i + j)) : RunSum.pQ v i = RunSum.pQ w i := by
  unfold RunSum.pQ
  rw [show v i = w i by simpa using h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]

theorem root_join (g : (ℕ → F) → Spec.Sha256.State) (PL PR : ℕ → ℕ → F) (ℓ : ℕ) :
    rootFrom (fun i => g (if i < 2 ^ ℓ then PL i else PR (i - 2 ^ ℓ))) (ℓ + 1) 0 =
      hnode (rootFrom (fun i => g (PL i)) ℓ 0) (rootFrom (fun i => g (PR i)) ℓ 0) := by
  simp only [rootFrom]
  congr 1
  · exact rootFrom_congr ℓ 0 fun i hi => by simp [hi]
  · rw [Nat.zero_add, rootFrom_congr (g := fun i => g (PR (i - 2 ^ ℓ))) ℓ (2 ^ ℓ) fun i _ => by simp]
    have := rootFrom_shift (fun i => g (PR (i - 2 ^ ℓ))) (2 ^ ℓ) ℓ 0
    simp only [Nat.add_sub_cancel_left, Nat.add_zero] at this
    exact this.symm

variable {ρ : ℕ → Q}

/-- **Nodes keep summaries proven.** If the node glue holds over two proven children, its output
summary is proven: the joined range of `2^(ℓ+1)` blocks, with both roots folded. -/
theorem sumOk_node {pl pr : ℕ → ℕ} {b : ℕ} (h : Holds ρ (BlockNode.nodeOut pl pr b).ops)
    (hL : SumOk (fun i => (ρ (pl i)).a)) (hR : SumOk (fun i => (ρ (pr i)).a)) :
    SumOk (fun i => (ρ (BlockNode.outReg pl pr b i)).a) := by
  obtain ⟨eN, eLo, eCh, eN2, eS, eNin, ⟨-, lLo⟩, ⟨-, lN⟩, ⟨-, lNin⟩, hH, hSd⟩ := BlockNode.node_sound h
  obtain ⟨ℓ, PL, hnL, hloL, hnLb, hniL, hbL, hsL, hnnL, hhL, hsdL⟩ := hL
  obtain ⟨ℓR, PR, hnR, hloR, hnRb, hniR, hbR, hsR, hnnR, hhR, hsdR⟩ := hR
  have aN : (ρ (pr 1)).a = (ρ (pl 1)).a := congrArg Q.a eN
  have hℓ : ℓR = ℓ := Nat.pow_right_injective le_rfl (by
    show 2 ^ ℓR = 2 ^ ℓ
    rw [← hnR, ← hnL]; simp only at aN ⊢; rw [aN])
  subst ℓR
  have v0 : (ρ (BlockNode.outReg pl pr b 0)).a = (ρ (pl 0)).a := by simp [BlockNode.outReg, BlockNode.LO]
  have v1 : (ρ (BlockNode.outReg pl pr b 1)).a = (ρ (pl 1)).a + (ρ (pl 1)).a := by
    simp only [BlockNode.outReg, if_neg (show (1 : ℕ) ≠ 0 by decide), if_true]
    exact congrArg Q.a eN2
  have vS : ∀ i < 4, (ρ (BlockNode.outReg pl pr b (2 + i))).a = (ρ (pl (2 + i))).a + (ρ (pr (2 + i))).a := by
    intro i hi
    simp only [BlockNode.outReg, if_neg (show 2 + i ≠ 0 by omega), if_neg (show 2 + i ≠ 1 by omega),
      if_pos (show 2 + i < 6 by omega)]
    rw [show b + (2 + i) = b + 2 + i by omega]
    exact congrArg Q.a (eS i hi)
  have v6 : (ρ (BlockNode.outReg pl pr b 6)).a = (ρ (pl 6)).a + (ρ (pr 6)).a := by
    simp only [BlockNode.outReg]; simp
    exact congrArg Q.a eNin
  have vCh : ∀ i < 12, (ρ (BlockNode.outReg pl pr b (7 + i))).a = (ρ (pl (7 + i))).a := by
    intro i hi
    simp only [BlockNode.outReg, if_neg (show 7 + i ≠ 0 by omega), if_neg (show 7 + i ≠ 1 by omega),
      if_neg (show ¬ (7 + i < 6) by omega), if_neg (show 7 + i ≠ 6 by omega), if_pos (show 7 + i < 19 by omega)]
  have rCh : ∀ i < 12, (ρ (pr (7 + i))).a = (ρ (pl (7 + i))).a := fun i hi => congrArg Q.a (eCh i hi)
  have vH : ∀ j < 16, (ρ (BlockNode.outReg pl pr b (19 + j))).a = (ρ ((BlockNode.hrNode pl pr (b + 34)).res.getD j 0)).a := by
    intro j hj
    simp only [BlockNode.outReg, if_neg (show 19 + j ≠ 0 by omega), if_neg (show 19 + j ≠ 1 by omega),
      if_neg (show ¬ (19 + j < 6) by omega), if_neg (show 19 + j ≠ 6 by omega), if_neg (show ¬ (19 + j < 19) by omega),
      if_pos (show 19 + j < 35 by omega), Nat.add_sub_cancel_left]
  have vSd : ∀ j < 16, (ρ (BlockNode.outReg pl pr b (35 + j))).a =
      (ρ ((BlockNode.srNode pl pr (BlockNode.hrNode pl pr (b + 34)).next).res.getD j 0)).a := by
    intro j hj
    simp only [BlockNode.outReg, if_neg (show 35 + j ≠ 0 by omega), if_neg (show 35 + j ≠ 1 by omega),
      if_neg (show ¬ (35 + j < 6) by omega), if_neg (show 35 + j ≠ 6 by omega), if_neg (show ¬ (35 + j < 19) by omega),
      if_neg (show ¬ (35 + j < 35) by omega), Nat.add_sub_cancel_left]
  -- the challenge of the joined range is the left one's, and the right one's
  have cL : ∀ k ∈ [7, 11, 15], RunSum.pQ (fun i => (ρ (BlockNode.outReg pl pr b i)).a) k = RunSum.pQ (fun i => (ρ (pl i)).a) k := by
    intro k hk
    apply pQ_congr
    intro j hj
    have : k + j = 7 + (k - 7 + j) := by simp at hk; omega
    rw [this, vCh _ (by simp at hk; omega)]
  have cR : ∀ k ∈ [7, 11, 15], RunSum.pQ (fun i => (ρ (pr i)).a) k = RunSum.pQ (fun i => (ρ (pl i)).a) k := by
    intro k hk
    apply pQ_congr
    intro j hj
    have : k + j = 7 + (k - 7 + j) := by simp at hk; omega
    rw [this, rCh _ (by simp at hk; omega)]
  have loR : (ρ (pr 0)).a.val = (ρ (pl 0)).a.val + 2 ^ ℓ := by
    have := congrArg Q.a eLo
    simp only [BlockNode.LO, BlockNode.NN, Q.add_a] at this
    rw [this, val_add_lt30 hloL hnLb, hnL]
  refine ⟨ℓ + 1, fun i => if i < 2 ^ ℓ then PL i else PR (i - 2 ^ ℓ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (ρ (BlockNode.outReg pl pr b 1)).a.val = _
    rw [v1, val_add_lt30 hnLb hnLb, hnL, pow_succ]; ring
  · show (ρ (BlockNode.outReg pl pr b 0)).a.val < _
    rw [v0]; simpa [BlockNode.LO] using lLo
  · exact lN
  · exact lNin
  · intro i hi
    show BlockAt (rngOf _ (ℓ + 1)) ((ρ (BlockNode.outReg pl pr b 0)).a.val + i) _
    rw [v0]
    by_cases hil : i < 2 ^ ℓ
    · simp only [if_pos hil]
      exact blockAt_congr (r := rngOf (fun i => (ρ (pl i)).a) ℓ) (cL 7 (by simp)) (cL 11 (by simp)) (cL 15 (by simp)) (hbL i hil)
    · simp only [if_neg hil]
      have := hbR (i - 2 ^ ℓ) (by rw [pow_succ] at hi; omega)
      rw [loR, show (ρ (pl 0)).a.val + 2 ^ ℓ + (i - 2 ^ ℓ) = (ρ (pl 0)).a.val + i by omega] at this
      exact blockAt_congr (r := rngOf (fun i => (ρ (pr i)).a) ℓ) ((cL 7 (by simp)).trans (cR 7 (by simp)).symm) ((cL 11 (by simp)).trans (cR 11 (by simp)).symm)
        ((cL 15 (by simp)).trans (cR 15 (by simp)).symm) this
  · have hv : RunSum.pQ (fun i => (ρ (BlockNode.outReg pl pr b i)).a) 2 =
        RunSum.pQ (fun i => (ρ (pl i)).a) 2 + RunSum.pQ (fun i => (ρ (pr i)).a) 2 := by
      unfold RunSum.pQ
      rw [← Spec.QM31.toQ_add]
      have s0 := vS 0 (by norm_num)
      have s1 := vS 1 (by norm_num)
      have s2 := vS 2 (by norm_num)
      have s3 := vS 3 (by norm_num)
      simp only [Nat.add_zero] at s0
      exact congrArg toQ (Q.ext s0 s1 s2 s3)
    have h1 : ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (if i < 2 ^ ℓ then PL i else PR (i - 2 ^ ℓ)) Coin.PUB_S =
        ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (PL i) Coin.PUB_S :=
      Finset.sum_congr rfl fun i hi => by rw [if_pos (Finset.mem_range.mp hi)]
    have h2 : ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (if 2 ^ ℓ + i < 2 ^ ℓ then PL (2 ^ ℓ + i) else PR (2 ^ ℓ + i - 2 ^ ℓ)) Coin.PUB_S =
        ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (PR i) Coin.PUB_S :=
      Finset.sum_congr rfl fun i _ => by rw [if_neg (by omega), Nat.add_sub_cancel_left]
    rw [hv, hsL, hsR, pow_succ, mul_two, Finset.sum_range_add, h1, h2]
  · show (ρ (BlockNode.outReg pl pr b 6)).a.val = _
    rw [v6, val_add_lt30 hniL hniR, hnnL, hnnR, pow_succ, mul_two, Finset.sum_range_add]
    congr 1
    · exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.mp hi]
    · exact Finset.sum_congr rfl fun i _ => by simp
  · intro j hj
    show (ρ (BlockNode.outReg pl pr b (19 + j))).a = _
    rw [vH j hj, root_join hashOf PL PR ℓ]
    exact hH (limbs_ext (g := fun j => (ρ (pl (BlockNode.HR + j))).a) hhL)
      (limbs_ext (g := fun j => (ρ (pr (BlockNode.HR + j))).a) hhR) j hj
  · intro j hj
    show (ρ (BlockNode.outReg pl pr b (35 + j))).a = _
    rw [vSd j hj, root_join seedOf PL PR ℓ]
    exact hSd (limbs_ext (g := fun j => (ρ (pl (BlockNode.SR + j))).a) hsdL)
      (limbs_ext (g := fun j => (ρ (pr (BlockNode.SR + j))).a) hsdR) j hj

/-! ### Leaves -/

/-- 16-bit limbs reassemble: the limbs of the state of limbs `o …` are those limbs. -/
theorem limbsOf_stateAt {p : ℕ → F} {o : ℕ} (hl : ∀ j < 16, (p (o + j)).val < 65536) :
    ∀ j < 16, (HeaderTree.limbsOf (stateAt p o)).getD j 0 = p (o + j) := by
  intro j hj
  rw [HeaderTree.limbsOf_get hj]
  have h0 := hl (2 * (j / 2)) (by omega)
  have h1 := hl (2 * (j / 2) + 1) (by omega)
  have hw : Spec.HeaderTree.stWord (stateAt p o) (j / 2) =
      BitVec.ofNat 32 ((p (o + 2 * (j / 2))).val + 65536 * (p (o + 2 * (j / 2) + 1)).val) := by
    have hk : j / 2 < 8 := by omega
    unfold stateAt toState
    interval_cases (j / 2) <;> rfl
  rw [hw]
  have hlt : (p (o + 2 * (j / 2))).val + 65536 * (p (o + 2 * (j / 2) + 1)).val < 2 ^ 32 := by
    rw [← Nat.add_assoc] at h1; omega
  rcases Nat.mod_two_eq_zero_or_one j with hm | hm
  · rw [hm]
    simp only [Sha256.half16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [show (p (o + 2 * (j / 2))).val + 65536 * (p (o + 2 * (j / 2) + 1)).val = (p (o + 2 * (j / 2))).val + (p (o + 2 * (j / 2) + 1)).val * 65536 by ring,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h0, ZMod.natCast_zmod_val, show 2 * (j / 2) = j by omega]
  · rw [hm]
    simp only [Sha256.half16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    rw [show (p (o + 2 * (j / 2))).val + 65536 * (p (o + 2 * (j / 2) + 1)).val = (p (o + 2 * (j / 2))).val + (p (o + 2 * (j / 2) + 1)).val * 65536 by ring,
      Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt h0, Nat.zero_add, ZMod.natCast_zmod_val]
    congr 1; omega

/-- A block's summary, as the block leaf outputs it from public inputs `p`. -/
noncomputable def leafVec (p : ℕ → F) (i : ℕ) : F :=
  if i = 0 then p 2 else if i = 1 then 1 else if i < 6 then p (Coin.PUB_S + (i - 2)) else if i = 6 then p Coin.PUB_NIN
  else if i < 15 then p (41 + (i - 7)) else if i < 19 then p (Coin.PUB_ALPHA 1 + (i - 15))
  else if i < 35 then p (25 + (i - 19)) else (HeaderTree.limbsOf (seedOf p)).getD (i - 35) 0

/-- **Leaves.** A proven block at height `H < 2^30` whose leaf checks hold (its BIP30 flag, `αₖ = α₁ᵏ`,
the input count below `2^30`), with 16-bit hash limbs, has a proven summary. -/
theorem sumOk_leaf {p : ℕ → F} (hp : BlockPubOk p) {H : ℕ} (hH : H < 2 ^ 30) (h2 : p 2 = (H : F))
    (hlost : p Coin.PUB_LOST = if Spec.Coins.bip30Lost H then 1 else 0)
    (hα : ∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ p (Coin.PUB_ALPHA 1) ^ k)
    (hnin : (p Coin.PUB_NIN).val < 2 ^ 30) (hlimbs : ∀ j < 16, (p (25 + j)).val < 65536) :
    SumOk (leafVec p) := by
  have hHP : H < P := by unfold P; omega
  have v0 : (leafVec p 0).val = H := by
    simp only [leafVec, if_true]; rw [h2, ZMod.val_natCast_of_lt hHP]
  have q : ∀ (o o' : ℕ), (∀ j < 4, leafVec p (o + j) = p (o' + j)) → RunSum.pQ (leafVec p) o = RunSum.pQ p o' := by
    intro o o' h
    unfold RunSum.pQ
    rw [show leafVec p o = p o' by simpa using h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num)]
  have qS : RunSum.pQ (leafVec p) 2 = RunSum.pQ p Coin.PUB_S := q 2 _ fun j hj => by
    simp only [leafVec, if_neg (show 2 + j ≠ 0 by omega), if_neg (show 2 + j ≠ 1 by omega), if_pos (show 2 + j < 6 by omega)]
    congr 1; omega
  have qG : RunSum.pQ (leafVec p) 7 = FpWalk.gQ p := q 7 41 fun j hj => by
    simp only [leafVec, if_neg (show 7 + j ≠ 0 by omega), if_neg (show 7 + j ≠ 1 by omega), if_neg (show ¬ (7 + j < 6) by omega),
      if_neg (show 7 + j ≠ 6 by omega), if_pos (show 7 + j < 15 by omega)]
    congr 1; omega
  have qZ : RunSum.pQ (leafVec p) 11 = RunSum.pQ p Coin.PUB_Z := q 11 _ fun j hj => by
    simp only [leafVec, if_neg (show 11 + j ≠ 0 by omega), if_neg (show 11 + j ≠ 1 by omega), if_neg (show ¬ (11 + j < 6) by omega),
      if_neg (show 11 + j ≠ 6 by omega), if_pos (show 11 + j < 15 by omega), Coin.PUB_Z]
    congr 1; omega
  have qA : RunSum.pQ (leafVec p) 15 = RunSum.pQ p (Coin.PUB_ALPHA 1) := q 15 _ fun j hj => by
    simp only [leafVec, if_neg (show 15 + j ≠ 0 by omega), if_neg (show 15 + j ≠ 1 by omega), if_neg (show ¬ (15 + j < 6) by omega),
      if_neg (show 15 + j ≠ 6 by omega), if_neg (show ¬ (15 + j < 15) by omega), if_pos (show 15 + j < 19 by omega)]
    congr 1; omega
  have v1 : (leafVec p 1).val = 1 := by simp only [leafVec]; simp; rfl
  refine ⟨0, fun _ => p, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [v1]; rfl
  · rw [v0]; exact hH
  · rw [v1]; norm_num
  · simpa [leafVec] using hnin
  · have hi0 : i = 0 := by simpa using hi
    subst hi0
    rw [v0, Nat.add_zero]
    refine ⟨hp, h2, hlost, qG.symm, ?_, fun k hk => ?_⟩
    · show RunSum.pQ p Coin.PUB_Z = RunSum.pQ (leafVec p) 11; exact qZ.symm
    · show RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ (leafVec p) 15 ^ k; rw [qA]; exact hα k hk
  · simp [qS]
  · simp [leafVec]
  · show leafVec p (19 + j) = _
    simp only [leafVec, if_neg (show 19 + j ≠ 0 by omega), if_neg (show 19 + j ≠ 1 by omega), if_neg (show ¬ (19 + j < 6) by omega),
      if_neg (show 19 + j ≠ 6 by omega), if_neg (show ¬ (19 + j < 15) by omega), if_neg (show ¬ (19 + j < 19) by omega),
      if_pos (show 19 + j < 35 by omega), rootFrom, hashOf]
    rw [limbsOf_stateAt hlimbs j hj]; congr 1; omega
  · show leafVec p (35 + j) = _
    simp only [leafVec, if_neg (show 35 + j ≠ 0 by omega), if_neg (show 35 + j ≠ 1 by omega), if_neg (show ¬ (35 + j < 6) by omega),
      if_neg (show 35 + j ≠ 6 by omega), if_neg (show ¬ (35 + j < 15) by omega), if_neg (show ¬ (35 + j < 19) by omega),
      if_neg (show ¬ (35 + j < 35) by omega), rootFrom, Nat.add_sub_cancel_left]

/-- **The root.** A proven summary gives `epoch_systems_core`'s block hypotheses over its `2^ℓ` blocks,
with its partial sum (`epoch_hyps_of_rng`). -/
theorem epoch_hyps_of_sum {v : ℕ → F} (h : SumOk v) : ∃ ℓ, (v 1).val = 2 ^ ℓ ∧
    ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i)),
      (∀ i < 2 ^ ℓ, ∀ c < 15, (inst i c).logSize = L i) ∧ (∀ i < 2 ^ ℓ, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < 2 ^ ℓ, L i ≤ 23) ∧ (∀ i < 2 ^ ℓ, pub i 2 = (((v 0).val + i : ℕ) : F)) ∧
      (∀ i < 2 ^ ℓ, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v 0).val + i) then 1 else 0) ∧
      (∀ i < 2 ^ ℓ, FpWalk.gQ (pub i) = RunSum.pQ v 7) ∧ (∀ i < 2 ^ ℓ, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v 11) ∧
      (∀ i < 2 ^ ℓ, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v 15 ^ k) ∧
      ∑ i ∈ Finset.range (2 ^ ℓ), RunSum.pQ (pub i) Coin.PUB_S = RunSum.pQ v 2 := by
  obtain ⟨ℓ, hn, hr⟩ := h.rng
  exact ⟨ℓ, hn, epoch_hyps_of_rng hr (by show 0 < 2 ^ ℓ; positivity)⟩

end StarkedAir.Circuit.BlockTree
