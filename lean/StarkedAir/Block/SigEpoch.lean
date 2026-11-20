/-
**The full sigop cost, for the epoch (CONNECT-RULES step 3).** `block_factsS` is `block_factsL` with one
more fact about the same claims: when they are real outputs' serializations, the block's sigop cost is
at most 80,000 (`block_sigop_cost`). `epoch_systems_coreS` carries it through the epoch: in a balanced
epoch every spent claim is an initial or a created coin, so every block's cost, counted on the scripts
of the coins it spends, is within the limit.
-/
import StarkedAir.Block.SigCost
import StarkedAir.Block.CoinEpochCore

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.LogUpSZ

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

/-- **One block's coin facts, with the relative locks and the sigop cost.** `block_factsL`, and for the
same claims: if every non-coinbase input's claim is a real output's serialization, the block's full
sigop cost, with the claims' scripts as the spent scripts, is at most `MAX_BLOCK_SIGOPS_COST`. -/
theorem block_factsS (S : Setup inst pub (Ls 1)) {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23) {lost : Bool}
    (hlost : pub Coin.PUB_LOST = if lost then 1 else 0) {α : QM}
    (hα : ∀ k < Coin.W, RunSum.pQ pub (Coin.PUB_ALPHA k) = α ^ k)
    (hne : ∀ (t' : ℕ) (tx' : Spec.Block.Tx), S.b.txs[t']? = some tx' → tx'.vin ≠ [] ∧ tx'.vout ≠ []) :
    ∃ claim : ℕ → ℕ → Claim,
      (∀ N : ℕ → ℕ, RunSum.pQ pub Coin.PUB_S =
        blockSum N (efrac N (FpWalk.gQ pub) α (RunSum.pQ pub Coin.PUB_Z)) ⟨h, S.b.txs, lost, claim⟩) ∧
      (∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx →
        ∀ ev ∈ txIns N ⟨h, S.b.txs, lost, claim⟩ t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
          (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < h ∨ (c.code / 2 = h ∧ c.ctx < t))) ∧
          c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ c.ser.length < P) ∧
      (∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
        (∀ k < tx.vin.length, 8 ≤ (claim t k).ser.length ∧
          Spec.Block.le ((claim t k).ser.take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO ∧ (claim t k).code < 2 ^ 30) →
        Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY →
        Spec.Coins.ClaimsOK (txcOf N ⟨h, S.b.txs, lost, claim⟩ t tx)) ∧
      (pub 5 = (if Spec.Block.CSV_HEIGHT ≤ h then 1 else 0) →
        ∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
          (∀ k < tx.vin.length, (claim t k).code < 2 ^ 30) →
          Spec.Coins.ClaimsLockOK (txcOf N ⟨h, S.b.txs, lost, claim⟩ t tx)) ∧
      (8 ≤ Ls 7 →
        (∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t → ∀ k < tx.vin.length,
          ∃ o : Spec.Block.TxOut, (claim t k).ser = Spec.Block.serTxOut o) →
        Spec.ConnectRules.SigOpCostOK true ((S.b.txs.zipIdx).map fun p =>
          (p.1, if p.2 = 0 then [] else
            (List.range p.1.vin.length).map fun k => (Spec.CoinEpoch.decSer (claim p.2 k).ser).2))) := by
  obtain ⟨e, he, hon, hlen, hst⟩ := coin_align hL hsat hL24 S
  obtain ⟨parts, hf, htg⟩ := Spec.Block.io_toksBlock_tag S.htok
  obtain ⟨claim, hcl⟩ := block_claims hL hsat hL24 S he hon hlen hst hf htg hp2 hh
  refine ⟨claim, fun N => ?_, fun N t tx htx ev hev => ?_, fun N t tx htx ht1 hcv hout => ?_,
    fun hp5 N t tx htx ht1 hcv => ?_, fun hL8 hreal => ?_⟩
  · have hs := block_event_sum hL hsat hL24 S he hon hlen hst hf htg hp2 hh hlost N claim
      (fun t tx htx ht1 k i hi => (hcl t tx htx ht1 k i hi).1)
    rw [hs]
    unfold blockSum efrac
    congr 1 <;> congr 1 <;> apply Multiset.map_congr rfl <;> intro ev _ <;>
      rw [phiOf_poly pub α hα _ (by rw [encE_length]; rfl)]
  · unfold txIns at hev
    split_ifs at hev with ht0
    · simp at hev
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hev
      have hk := List.mem_zipIdx' hp
      have hi : tx.vin[p.2]? = some p.1 := by rw [hk.2]; exact List.getElem?_eq_getElem hk.1
      obtain ⟨-, hlex, hctx, hat⟩ := hcl t tx htx (by omega) p.2 p.1 hi
      obtain ⟨-, -, rj, -, -, -, -, u0, -, h9, hlen8, -, hcode, -⟩ := hat
      refine ⟨claim t p.2, rfl, hlex, ?_, hctx, ?_⟩
      · rw [hcode]; exact le4_lt' _
      · have hv : (pub 8).val < P := ZMod.val_lt _
        omega
  · exact tx_claims_ok hL hsat hL24 S he hon hlen hst hf htg hne hp2 hh N ⟨h, S.b.txs, lost, claim⟩ rfl htx ht1
      (fun k hk => by
        obtain ⟨i, hi⟩ : ∃ i, tx.vin[k]? = some i := ⟨_, List.getElem?_eq_getElem hk⟩
        exact (hcl t tx htx ht1 k i hi).2.2.2)
      hcv hout
  · exact tx_locks_ok hL hsat hL24 S he hon hlen hst hf htg hne hp2 hh hp5 N ⟨h, S.b.txs, lost, claim⟩ rfl htx ht1
      (fun k hk => by
        obtain ⟨i, hi⟩ : ∃ i, tx.vin[k]? = some i := ⟨_, List.getElem?_eq_getElem hk⟩
        exact (hcl t tx htx ht1 k i hi).2.2.2)
      hcv
  · exact block_sigop_cost hL hsat hL24 hL8 S he hon hlen hst hf htg claim (fun t tx htx ht1 k hk => by
      obtain ⟨i, hi⟩ : ∃ i, tx.vin[k]? = some i := ⟨_, List.getElem?_eq_getElem hk⟩
      exact (hcl t tx htx ht1 k i hi).2.2.2) hreal

end System

end StarkedAir.Block
