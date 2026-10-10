/-
**Block soundness (M3a.5, D-035).** A satisfied 9-component block system, with the block's public inputs
for context `c`, proves that its bytes parse as a block `b` that passes `checkBlock c` (Core's
`CheckBlock` without the header's proof of work, which the header chain proves, and
`ContextualCheckBlock`), given that no transaction spends the same prevout twice (M3b's obligation,
D-031).

Side conditions on the context: `height < 2^23` (the BIP34 push is then 3 bytes) and `prevMtp < 2^32`.
Public inputs: `pub 2 = height`, `pub 3`/`pub 7` the previous MTP's low/high 16 bits, `pub 4..6` the
BIP34, CSV and segwit activation bits. (`pub 0` is the block's length and `pub 1` its transaction count;
the trace fixes both.)
-/
import StarkedAir.Block.BlockCommit

namespace StarkedAir.Block

open StarkedAir
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

/-- The block system's public inputs for context `c`. -/
def BlockPubs (c : Spec.Block.Ctx) (pub : ℕ → F) : Prop :=
  pub 2 = (c.height : F) ∧ pub 3 = ((c.prevMtp % 65536 : ℕ) : F) ∧
  pub 4 = (if Spec.Block.BIP34_HEIGHT ≤ c.height then 1 else 0) ∧
  pub 5 = (if Spec.Block.CSV_HEIGHT ≤ c.height then 1 else 0) ∧
  pub 6 = (if Spec.Block.SEGWIT_HEIGHT ≤ c.height then 1 else 0) ∧
  pub 7 = ((c.prevMtp / 65536 : ℕ) : F)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **Block soundness.** -/
theorem block_sound (hL8 : 8 ≤ L) {c : Spec.Block.Ctx} (hh : c.height < 2 ^ 23) (hmtp : c.prevMtp < 2 ^ 32)
    (hpub : BlockPubs c pub) :
    ∃ b, Spec.Block.parseBlock (Rb inst pub) = some b ∧
      ((∀ t ∈ b.txs, Spec.Block.nodupBy (t.vin.map (·.prevout)) = true) →
        Spec.Block.checkBlock c (Rb inst pub) = none) := by
  obtain ⟨p2, p3, p4, p5, p6, p7⟩ := hpub
  obtain ⟨S⟩ := setup_exists hL hsat hL24
  refine ⟨S.b, S.hparse, fun hnd => ?_⟩
  rw [Spec.Block.checkBlock_none_iff]
  refine ⟨S.b, S.hparse, ?_, ?_⟩
  · -- `CheckBlock`
    have hw := weight_ok hL hsat hL24 hL8 S
    obtain ⟨hst, hcnt, htx⟩ := Spec.Block.size_of_weight S.b hw
    obtain ⟨ρ0, t0, inp, -, -, -, hget0, -, -, -, -, -, hv0, hnull, hss, hfss, -, hslo, hshi, -⟩ :=
      cb_facts hL hsat hL24 hL8 S
    have hcb0 : t0.isCoinbase = true := by unfold Spec.Block.Tx.isCoinbase; rw [hv0]; exact hnull
    -- transaction `j ≥ 1` is not a coinbase
    have hlater : ∀ j, 1 ≤ j → ∀ t, S.b.txs[j]? = some t → t.isCoinbase = false := by
      intro j hj t ht
      have hjl : j < S.b.txs.length := (List.getElem?_eq_some_iff.mp ht).1
      exact Spec.Block.not_coinbase_of_inputs t (txs_later hL hsat hL24 S hj hjl ht)
    refine ⟨?_, ?_, hcnt, hst, ?_, ?_, ?_, sigops_ok hL hsat hL24 hL8 S⟩
    · obtain ⟨b', hp', hm⟩ := merkle_sound hL hsat hL24
      have : b' = S.b := by have := S.hparse; rw [hp'] at this; exact Option.some.inj this
      subst this; exact hm
    · intro h; have := S.hN1; rw [h] at this; simp at this
    · match h : S.b.txs, hget0 with
      | a :: _, hg => simp at hg; simp [hg, hcb0]
    · intro t ht
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      have hj1 : 1 ≤ j + 1 := by omega
      simp only [List.getElem_drop]
      exact hlater (1 + j) (by omega) _ (List.getElem?_eq_getElem _)
    · intro t ht
      obtain ⟨hvin, hvout, hpos, hsum⟩ := txs_basic hL hsat hL24 S t ht
      refine ⟨hvin, hvout, htx t ht, hpos, hsum, hnd t ht, ?_⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
      rcases Nat.eq_zero_or_pos j with h0 | hpos'
      · subst h0
        have e : S.b.txs[0] = t0 := by
          rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hget0; exact hget0
        rw [e, if_pos hcb0]
        unfold Spec.Block.CbLenOK
        rw [hv0]
        show 2 ≤ inp.scriptSig.length ∧ inp.scriptSig.length ≤ 100
        rw [hss, Fields.slice_length hfss]
        omega
      · have hf := hlater j hpos' _ (List.getElem?_eq_getElem hj)
        rw [hf, if_neg (by simp)]
        exact txs_later hL hsat hL24 S hpos' hj (List.getElem?_eq_getElem hj)
  · -- `ContextualCheckBlock`
    exact ⟨final_ok hL hsat hL24 hL8 S hh hmtp p2 p3 p5 p7, bip34_ok hL hsat hL24 hL8 S hh p2 p4,
      commit_ok hL hsat hL24 hL8 S p6, weight_ok hL hsat hL24 hL8 S⟩

end System

end StarkedAir.Block
