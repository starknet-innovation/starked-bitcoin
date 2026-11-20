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

/-- **Created coins are serialized outputs.** -/
theorem created_ser (N : ℕ → ℕ) (blocks : List BlockC) (g : ℕ) :
    ∀ e ∈ created g (allTxs N blocks), ∃ o : Spec.Block.TxOut, e.2.1.2 = Spec.Block.serTxOut o := by
  intro e he
  obtain ⟨T, hT, o, ho, -, he2⟩ := mem_created_outs g _ he
  unfold allTxs at hT
  obtain ⟨B, hB, hT⟩ := List.mem_flatMap.mp hT
  unfold blockTxs at hT
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hT
  simp only [txOuts, List.mem_map] at ho
  obtain ⟨q, hq, rfl⟩ := ho
  rw [he2]
  exact ⟨q.1, rfl⟩

/-- **A balanced epoch runs** (`epoch_core_run`, with the spent values serialized outputs when the
initial ones are). `epoch_core`'s first half: outside the bad set, a balanced epoch sum
gives a successful run of the epoch's events from the initial set, ending at exactly the final set, and
every spent value is a real coin's. -/
theorem epoch_core_runS (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    {S : Finset (List F)} (hγ : γ ∉ fpBad (𝕂 := QM) S)
    (hwf : ∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
      WFE N e ∧ bytesF e ∈ S)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i'))
    (hbnd : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25)
    (hinit : ∀ e ∈ init, e.2.2 < g0) (hinitR : ∀ e ∈ init, RealVal e.2.1)
    (hinitS : ∀ e ∈ init, ∃ o : Spec.Block.TxOut, e.2.1.2 = Spec.Block.serTxOut o)
    (hnd : (((init : Multiset CEv) + created g0 (allTxs N blocks)).map Prod.fst).Nodup)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ Spec.Block.MAX_MONEY)
    (hlexB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t)))) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
        2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
      ∀ az ∉ Bad,
        init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
          fin.length < P →
        (blocks.map (blockSum N (efrac N γ az.1 az.2))).sum + (init.map (efrac N γ az.1 az.2)).sum =
          (fin.map (efrac N γ az.1 az.2)).sum →
        ∃ m, run g0 (viewOf init) (allTxs N blocks) = some m ∧ (∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin) ∧
          ∀ e ∈ spent (allTxs N blocks), RealVal e.2.1 ∧ ∃ o : Spec.Block.TxOut, e.2.1.2 = Spec.Block.serTxOut o := by
  obtain ⟨Bad, hcard, hb⟩ := epoch_balance N γ blocks g0 init fin
  refine ⟨Bad, hcard, fun az haz hlen hsum => ?_⟩
  have hbal := hb az haz (fun e he e' he' h =>
    encE_inj N hγ (hwf e he).1 (hwf e' he').1 (hwf e he).2 (hwf e' he').2 h) hlen hpos hsum
  obtain ⟨m, hm, hiff⟩ := epoch_run N blocks g0 init fin hpos hinc hbnd hlexB hinit hnd hbal
  have hhB : ∀ B ∈ blocks, B.h < 2 ^ 24 := by
    intro B hB
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    exact (hbnd i _ (List.getElem?_eq_getElem hi)).1
  -- every spend's value is an initial or created coin's, so real
  have hspR : ∀ e ∈ spent (allTxs N blocks), RealVal e.2.1 := by
    intro e he
    have : e ∈ (init : Multiset CEv) + created g0 (allTxs N blocks) := by
      rw [hbal]; exact Multiset.mem_add.mpr (Or.inl he)
    rcases Multiset.mem_add.mp this with h | h
    · exact hinitR e (by simpa using h)
    · exact created_real N blocks g0 hval hhB e h
  have hspS : ∀ e ∈ spent (allTxs N blocks), ∃ o : Spec.Block.TxOut, e.2.1.2 = Spec.Block.serTxOut o := by
    intro e he
    have : e ∈ (init : Multiset CEv) + created g0 (allTxs N blocks) := by
      rw [hbal]; exact Multiset.mem_add.mpr (Or.inl he)
    rcases Multiset.mem_add.mp this with h | h
    · exact hinitS e (by simpa using h)
    · exact created_ser N blocks g0 e h
  exact ⟨m, hm, hiff, fun e he => ⟨hspR e he, hspS e he⟩⟩

/-- **The epoch connects as Core does, with the relative locks and the sigop cost** (`epoch_coreL`; and
every block's full sigop cost, on its claims' scripts, is within the limit, when the initial coins are
serialized outputs and each block has the fact `block_factsS` gives). Original statement: with the relative locks (`epoch_core` for `connectTxsL`, BIP68's
height half). With, in addition, each non-coinbase transaction with real claims passing `ClaimsLockOK`:
outside the same bad set, a balanced epoch sum means Core's connect with the height-based relative
locks checked succeeds, ending at a view holding exactly the final set. -/
theorem epoch_coreS (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    {S : Finset (List F)} (hγ : γ ∉ fpBad (𝕂 := QM) S)
    (hwf : ∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
      WFE N e ∧ bytesF e ∈ S)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i'))
    (hbnd : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25)
    (hinit : ∀ e ∈ init, e.2.2 < g0) (hinitR : ∀ e ∈ init, RealVal e.2.1)
    (hinitS : ∀ e ∈ init, ∃ o : Spec.Block.TxOut, e.2.1.2 = Spec.Block.serTxOut o)
    (hnd : (((init : Multiset CEv) + created g0 (allTxs N blocks)).map Prod.fst).Nodup)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ Spec.Block.MAX_MONEY)
    (hlost : ∀ B ∈ blocks, B.lost = Spec.Coins.bip30Lost B.h)
    (hout : ∀ B ∈ blocks, ∀ tx ∈ B.txs, Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY)
    (hlexB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t))))
    (hokB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      1 ≤ t → (∀ k < tx.vin.length, RealVal ((B.claim t k).code, (B.claim t k).ser)) →
      Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY → Spec.Coins.ClaimsOK (txcOf N B t tx))
    (hokLB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      1 ≤ t → (∀ k < tx.vin.length, RealVal ((B.claim t k).code, (B.claim t k).ser)) →
      Spec.Coins.ClaimsLockOK (txcOf N B t tx))
    (hsigB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B →
        (∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx → 1 ≤ t → ∀ k < tx.vin.length,
          ∃ o : Spec.Block.TxOut, (B.claim t k).ser = Spec.Block.serTxOut o) →
        Spec.ConnectRules.SigOpCostOK true ((B.txs.zipIdx).map fun p =>
          (p.1, if p.2 = 0 then [] else
            (List.range p.1.vin.length).map fun k => (Spec.CoinEpoch.decSer (B.claim p.2 k).ser).2))) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
        2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
      ∀ az ∉ Bad,
        init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
          fin.length < P →
        (blocks.map (blockSum N (efrac N γ az.1 az.2))).sum + (init.map (efrac N γ az.1 az.2)).sum =
          (fin.map (efrac N γ az.1 az.2)).sum →
        (∃ m, Spec.Coins.connectTxsL (Spec.Coins.untag (vmap coinOfVal (viewOf init))) (allTxC N blocks) =
            some (Spec.Coins.untag (vmap coinOfVal m), (allTxC N blocks).map Spec.Coins.claimFee) ∧
          ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin) ∧
        (∀ B ∈ blocks, ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx → 1 ≤ t →
          Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true) ∧
        ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B →
        Spec.ConnectRules.SigOpCostOK true ((B.txs.zipIdx).map fun p =>
          (p.1, if p.2 = 0 then [] else
            (List.range p.1.vin.length).map fun k => (Spec.CoinEpoch.decSer (B.claim p.2 k).ser).2)) := by
  obtain ⟨Bad, hcard, hb⟩ := epoch_core_runS N γ blocks g0 init fin hγ hwf hpos hinc hbnd hinit hinitR hinitS hnd hval
    hlexB
  refine ⟨Bad, hcard, fun az haz hlen hsum => ?_⟩
  obtain ⟨m, hm, hiff, hspRS⟩ := hb az haz hlen hsum
  have hspR := fun e he => (hspRS e he).1
  refine ⟨⟨m, epoch_connectL N blocks g0 init hlost
    (fun B hB tx htx o ho => ⟨(hval B hB tx htx o ho).1,
      lt_of_le_of_lt (hval B hB tx htx o ho).2 (by unfold Spec.Block.MAX_MONEY; norm_num)⟩) hm ?_ ?_, hiff⟩,
    epoch_nodup_prevouts N blocks g0 hm, ?_⟩
  · intro x hx
    unfold allTxC at hx
    obtain ⟨B, hB, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    have hBi : blocks[i]? = some blocks[i] := List.getElem?_eq_getElem hi
    unfold blockTxC at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hpt, hpe⟩ := List.mem_zipIdx' hp
    have htx : blocks[i].txs[p.2]? = some p.1 := by rw [hpe]; exact List.getElem?_eq_getElem hpt
    by_cases ht0 : p.2 = 0
    · left; simp [txcOf, ht0]
    · refine hokB i _ hBi p.2 p.1 htx (by omega) (fun k hk => ?_)
        (hout _ hB p.1 (by rw [hpe]; exact List.getElem_mem _))
      have hin : ((p.1.vin[k]).prevout, ((blocks[i].claim p.2 k).code, (blocks[i].claim p.2 k).ser),
          N ((blocks[i].claim p.2 k).code / 2) + (blocks[i].claim p.2 k).ctx) ∈ txIns N blocks[i] p.2 p.1 := by
        unfold txIns
        rw [if_neg ht0]
        exact List.mem_map.mpr ⟨(p.1.vin[k], k), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩
      exact hspR _ (mem_spent_all N blocks hBi htx hin)

  · intro x hx
    unfold allTxC at hx
    obtain ⟨B, hB, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hB
    have hBi : blocks[i]? = some blocks[i] := List.getElem?_eq_getElem hi
    unfold blockTxC at hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨hpt, hpe⟩ := List.mem_zipIdx' hp
    have htx : blocks[i].txs[p.2]? = some p.1 := by rw [hpe]; exact List.getElem?_eq_getElem hpt
    by_cases ht0 : p.2 = 0
    · left; simp [txcOf, ht0]
    · refine hokLB i _ hBi p.2 p.1 htx (by omega) (fun k hk => ?_)
      have hin : ((p.1.vin[k]).prevout, ((blocks[i].claim p.2 k).code, (blocks[i].claim p.2 k).ser),
          N ((blocks[i].claim p.2 k).code / 2) + (blocks[i].claim p.2 k).ctx) ∈ txIns N blocks[i] p.2 p.1 := by
        unfold txIns
        rw [if_neg ht0]
        exact List.mem_map.mpr ⟨(p.1.vin[k], k), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩
      exact hspR _ (mem_spent_all N blocks hBi htx hin)
  · intro i B hBi
    refine hsigB i B hBi (fun t tx htx ht1 k hk => ?_)
    have hin : ((tx.vin[k]).prevout, ((B.claim t k).code, (B.claim t k).ser),
        N ((B.claim t k).code / 2) + (B.claim t k).ctx) ∈ txIns N B t tx := by
      unfold txIns
      rw [if_neg (by omega)]
      exact List.mem_map.mpr ⟨(tx.vin[k], k), List.mem_zipIdx_iff_getElem?.mpr (by simp), rfl⟩
    exact (hspRS _ (mem_spent_all N blocks hBi htx hin)).2

end StarkedAir.Block
