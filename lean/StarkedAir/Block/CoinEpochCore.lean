/-
**An epoch, as Core connects it (M3b, layer 5).** The epoch theorem from the blocks' coin facts
(`block_facts`): for `γ` outside the fingerprint bad set and `(α, z)` outside a bad set fixed by the
epoch's events, a balanced epoch sum (the blocks' public partial sums plus the initial set's fractions
equal the final set's) means Core's connect of the epoch's transactions, from the initial coins view,
succeeds and ends holding exactly the final set (`epoch_core`).

Every claim is a real coin's value (`RealVal`): the balance makes each claim an initial or created coin,
and those are real (`created_real`), so each transaction's `ClaimsOK` follows from its block's facts.
-/
import StarkedAir.Block.CoinClaims

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.LogUpSZ

/-- A value with a real coin's shape: at least 8 bytes, its amount within `MAX_MONEY`, its code below
`2^30`. -/
def RealVal (v : Val) : Prop :=
  8 ≤ v.2.length ∧ Spec.Block.le (v.2.take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO ∧ v.1 < 2 ^ 30

theorem mem_created_outs {K V : Type} [DecidableEq K] [DecidableEq V] :
    ∀ (g : ℕ) (ts : List (Spec.Utxo.Tx K V)) {e : Ev K V}, e ∈ created g ts →
      ∃ T ∈ ts, ∃ o ∈ T.outs, e.1 = o.1 ∧ e.2.1 = o.2
  | _, [], e, h => by simp [created] at h
  | g, T :: ts, e, h => by
    simp only [created, Multiset.mem_add] at h
    rcases h with h | h
    · simp only [outsT, Multiset.mem_coe, List.mem_map] at h
      obtain ⟨o, ho, rfl⟩ := h
      exact ⟨T, List.mem_cons_self, o, ho, rfl, rfl⟩
    · obtain ⟨T', hT', o, ho, h1, h2⟩ := mem_created_outs (g + 1) ts h
      exact ⟨T', List.mem_cons_of_mem _ hT', o, ho, h1, h2⟩

theorem serTxOut_real {o : Spec.Block.TxOut} (h0 : 0 ≤ o.value) (hm : o.value ≤ Spec.Block.MAX_MONEY) :
    8 ≤ (Spec.Block.serTxOut o).length ∧
      Spec.Block.le ((Spec.Block.serTxOut o).take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO := by
  have hl := Spec.Block.leBytes_length 8 (o.value % 2 ^ 64).toNat
  unfold Spec.Block.serTxOut
  refine ⟨by rw [List.length_append, hl]; omega, ?_⟩
  rw [List.take_left' hl, Spec.Block.le_leBytes]
  have h64 : o.value < 2 ^ 64 := lt_of_le_of_lt hm (by unfold Spec.Block.MAX_MONEY; norm_num)
  rw [Int.emod_eq_of_lt h0 h64]
  have : o.value.toNat ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO := by
    have := max_money_eq ▸ hm
    omega
  exact le_trans (Nat.mod_le _ _) this

/-- **Created coins are real**, given the outputs' amounts within `[0, MAX_MONEY]` and heights below
`2^24`. -/
theorem created_real (N : ℕ → ℕ) (blocks : List BlockC) (g : ℕ)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ Spec.Block.MAX_MONEY)
    (hh : ∀ B ∈ blocks, B.h < 2 ^ 24) :
    ∀ e ∈ created g (allTxs N blocks), RealVal e.2.1 := by
  intro e he
  obtain ⟨T, hT, o, ho, -, he2⟩ := mem_created_outs g _ he
  unfold allTxs at hT
  obtain ⟨B, hB, hT⟩ := List.mem_flatMap.mp hT
  unfold blockTxs at hT
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hT
  have htx : p.1 ∈ B.txs := (List.mem_zipIdx' hp).2 ▸ List.getElem_mem _
  simp only [txOuts, List.mem_map] at ho
  obtain ⟨q, hq, rfl⟩ := ho
  have hout : q.1 ∈ p.1.vout := (List.mem_zipIdx' (List.mem_of_mem_filter hq)).2 ▸ List.getElem_mem _
  obtain ⟨h0, hm⟩ := hval B hB p.1 htx q.1 hout
  obtain ⟨r1, r2⟩ := serTxOut_real h0 hm
  rw [he2]
  refine ⟨r1, r2, ?_⟩
  have := hh B hB
  show codeOf B.h p.2 < 2 ^ 30
  unfold codeOf; split_ifs <;> omega

/-- **The epoch connects as Core does.** Given the blocks' coin facts (each block's spends pass the
circuit's order check, and its non-coinbase transactions with real claims and outputs within
`MAX_MONEY` pass `ClaimsOK`), well-formed events whose bytes `γ` separates, the blocks' positions,
increasing and bounded heights, an initial set of real coins created before the epoch, distinct
created outpoints, and the outputs' amounts within `[0, MAX_MONEY]` with the lost-coinbase flags Core's:
outside a bad set of `(α, z)` fixed by the epoch's events, a balanced epoch sum means Core's connect of
the epoch's transactions from the initial view succeeds, ending at a view holding exactly the final
set. -/
theorem epoch_core (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    {S : Finset (List F)} (hγ : γ ∉ fpBad (𝕂 := QM) S)
    (hwf : ∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
      WFE N e ∧ bytesF e ∈ S)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i'))
    (hbnd : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25)
    (hinit : ∀ e ∈ init, e.2.2 < g0) (hinitR : ∀ e ∈ init, RealVal e.2.1)
    (hnd : (((init : Multiset CEv) + created g0 (allTxs N blocks)).map Prod.fst).Nodup)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ Spec.Block.MAX_MONEY)
    (hlost : ∀ B ∈ blocks, B.lost = Spec.Coins.bip30Lost B.h)
    (hout : ∀ B ∈ blocks, ∀ tx ∈ B.txs, Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY)
    (hlexB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t))))
    (hokB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      1 ≤ t → (∀ k < tx.vin.length, RealVal ((B.claim t k).code, (B.claim t k).ser)) →
      Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY → Spec.Coins.ClaimsOK (txcOf N B t tx)) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
        2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
      ∀ az ∉ Bad,
        init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
          fin.length < P →
        (blocks.map (blockSum N (efrac N γ az.1 az.2))).sum + (init.map (efrac N γ az.1 az.2)).sum =
          (fin.map (efrac N γ az.1 az.2)).sum →
        ∃ m, Spec.Coins.connectTxs (Spec.Coins.untag (vmap coinOfVal (viewOf init))) (allTxC N blocks) =
            some (Spec.Coins.untag (vmap coinOfVal m), (allTxC N blocks).map Spec.Coins.claimFee) ∧
          ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
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
  refine ⟨m, epoch_connect N blocks g0 init hlost
    (fun B hB tx htx o ho => ⟨(hval B hB tx htx o ho).1,
      lt_of_le_of_lt (hval B hB tx htx o ho).2 (by unfold Spec.Block.MAX_MONEY; norm_num)⟩) hm ?_, hiff⟩
  intro x hx
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

/-- **An epoch's block systems.** Block systems `i < nb` at heights `h0 + i` sharing the epoch's
challenge (`γ`, `z`, weights `αᵏ`) give the epoch's blocks: their public partial sums add up to the
blocks' sum at `(α, z)`, and their spends and transactions satisfy `epoch_core`'s block facts. -/
theorem epoch_blocks (nb : ℕ) (inst : ℕ → ℕ → Inst) (pub : ℕ → ℕ → F) (L : ℕ → ℕ)
    (hL : ∀ i < nb, ∀ c < 15, (inst i c).logSize = L i) (hsat : ∀ i < nb, hashSys.SatisfiedExt (inst i) (pub i) [])
    (hL24 : ∀ i < nb, L i ≤ 23) (S : ∀ i, Setup (inst i) (pub i) (L i)) (h0 : ℕ) (hh : h0 + nb ≤ 2 ^ 23)
    (hp2 : ∀ i < nb, pub i 2 = ((h0 + i : ℕ) : F)) (lost : ℕ → Bool)
    (hlost : ∀ i < nb, pub i Coin.PUB_LOST = if lost i then 1 else 0)
    (γ α z : QM) (hγ : ∀ i < nb, FpWalk.gQ (pub i) = γ) (hz : ∀ i < nb, RunSum.pQ (pub i) Coin.PUB_Z = z)
    (hα : ∀ i < nb, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = α ^ k)
    (hne : ∀ i < nb, ∀ (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx → tx.vin ≠ [] ∧ tx.vout ≠ []) :
    ∃ blocks : List BlockC, blocks.length = nb ∧
      (∀ i < nb, ∃ B, blocks[i]? = some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs ∧ B.lost = lost i) ∧
      ∀ N : ℕ → ℕ,
        ∑ i ∈ Finset.range nb, RunSum.pQ (pub i) Coin.PUB_S = (blocks.map (blockSum N (efrac N γ α z))).sum ∧
        (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
          ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
            (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t)))) ∧
        (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
          1 ≤ t → (∀ k < tx.vin.length, RealVal ((B.claim t k).code, (B.claim t k).ser)) →
          Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY → Spec.Coins.ClaimsOK (txcOf N B t tx)) := by
  have key : ∀ i, ∃ claim : ℕ → ℕ → Claim, i < nb →
      (∀ N : ℕ → ℕ, RunSum.pQ (pub i) Coin.PUB_S =
        blockSum N (efrac N γ α z) ⟨h0 + i, (S i).b.txs, lost i, claim⟩) ∧
      (∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx →
        ∀ ev ∈ txIns N ⟨h0 + i, (S i).b.txs, lost i, claim⟩ t tx, ∃ c : Claim,
          ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
          (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < h0 + i ∨ (c.code / 2 = h0 + i ∧ c.ctx < t)))) ∧
      (∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx → 1 ≤ t →
        (∀ k < tx.vin.length, 8 ≤ (claim t k).ser.length ∧
          Spec.Block.le ((claim t k).ser.take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO ∧ (claim t k).code < 2 ^ 30) →
        Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY →
        Spec.Coins.ClaimsOK (txcOf N ⟨h0 + i, (S i).b.txs, lost i, claim⟩ t tx)) := by
    intro i
    by_cases hi : i < nb
    · obtain ⟨claim, h1, h2, h3⟩ := block_facts (hL i hi) (hsat i hi) (hL24 i hi) (S i) (hp2 i hi) (by omega)
        (hlost i hi) (hα i hi) (hne i hi)
      refine ⟨claim, fun _ => ⟨fun N => ?_, h2, h3⟩⟩
      rw [h1 N, hγ i hi, hz i hi]
    · exact ⟨fun _ _ => default, fun h => absurd h hi⟩
  choose claim hclaim using key
  refine ⟨(List.range nb).map fun i => ⟨h0 + i, (S i).b.txs, lost i, claim i⟩, by simp,
    fun i hi => ⟨⟨h0 + i, (S i).b.txs, lost i, claim i⟩, by rw [List.getElem?_map, List.getElem?_range hi]; rfl,
      rfl, rfl, rfl⟩, fun N => ⟨?_, ?_, ?_⟩⟩
  · rw [List.map_map, list_sum_range_qm]
    exact Finset.sum_congr rfl fun i hi => (hclaim i (Finset.mem_range.mp hi)).1 N
  · intro i B hB t tx htx ev hev
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hB)
    exact (hclaim j (List.mem_range.mp hj)).2.1 N t tx htx ev hev
  · intro i B hB t tx htx ht1 hcv hout
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hB)
    exact (hclaim j (List.mem_range.mp hj)).2.2 N t tx htx ht1 hcv hout

end StarkedAir.Block
