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
import StarkedAir.Block.BlockTxs
import StarkedAir.Block.BlockSound

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

theorem nodupBy_of_nodup {α : Type} [DecidableEq α] : ∀ l : List α, l.Nodup → Spec.Block.nodupBy l = true
  | [], _ => rfl
  | a :: r, h => by
    rw [List.nodup_cons] at h
    simp [Spec.Block.nodupBy, h.1, nodupBy_of_nodup r h.2]

/-- **No repeated prevouts (D-031).** In a successful run of the epoch, each block's non-coinbase
transactions spend distinct outpoints (`block_sound`'s hypothesis for them). -/
theorem epoch_nodup_prevouts (N : ℕ → ℕ) (blocks : List BlockC) (g0 : ℕ) {m0 m : View Spec.Block.OutPoint Val}
    (hrun : run g0 m0 (allTxs N blocks) = some m) :
    ∀ B ∈ blocks, ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx → 1 ≤ t →
      Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true := by
  intro B hB t tx htx ht1
  have hT : (⟨txIns N B t tx, txOuts B t tx⟩ : Spec.Utxo.Tx Spec.Block.OutPoint Val) ∈ allTxs N blocks := by
    unfold allTxs blockTxs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_map.mpr ⟨(tx, t), ?_, rfl⟩⟩
    exact List.mem_zipIdx_iff_getElem?.mpr (by simpa using htx)
  have hnd := run_ins_nodup g0 m0 m _ hrun _ hT
  have he : (txIns N B t tx).map Prod.fst = tx.vin.map (·.prevout) := by
    unfold txIns
    rw [if_neg (by omega), List.map_map]
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [he] at hnd
  exact nodupBy_of_nodup _ hnd

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
        (∃ m, Spec.Coins.connectTxs (Spec.Coins.untag (vmap coinOfVal (viewOf init))) (allTxC N blocks) =
            some (Spec.Coins.untag (vmap coinOfVal m), (allTxC N blocks).map Spec.Coins.claimFee) ∧
          ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin) ∧
        ∀ B ∈ blocks, ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx → 1 ≤ t →
          Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true := by
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
  refine ⟨⟨m, epoch_connect N blocks g0 init hlost
    (fun B hB tx htx o ho => ⟨(hval B hB tx htx o ho).1,
      lt_of_le_of_lt (hval B hB tx htx o ho).2 (by unfold Spec.Block.MAX_MONEY; norm_num)⟩) hm ?_, hiff⟩,
    epoch_nodup_prevouts N blocks g0 hm⟩
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

/-- **An epoch's block systems.** Block systems `i < nb` (component `c` of block `i` with `2^(L i c)` rows) at heights `h0 + i` sharing the epoch's
challenge (`γ`, `z`, weights `αᵏ`) give the epoch's blocks: their public partial sums add up to the
blocks' sum at `(α, z)`, and their spends and transactions satisfy `epoch_core`'s block facts. -/
theorem epoch_blocks (nb : ℕ) (inst : ℕ → ℕ → Inst) (pub : ℕ → ℕ → F) (L : ℕ → ℕ → ℕ)
    (hL : ∀ i < nb, ∀ c < 15, (inst i c).logSize = L i c) (hsat : ∀ i < nb, hashSys.SatisfiedExt (inst i) (pub i) [])
    (hL24 : ∀ i < nb, ∀ c < 15, L i c ≤ 23) (S : ∀ i, Setup (inst i) (pub i) (L i 1)) (h0 : ℕ) (hh : h0 + nb ≤ 2 ^ 23)
    (hp2 : ∀ i < nb, pub i 2 = ((h0 + i : ℕ) : F)) (lost : ℕ → Bool)
    (hlost : ∀ i < nb, pub i Coin.PUB_LOST = if lost i then 1 else 0)
    (γ α z : QM) (hγ : ∀ i < nb, FpWalk.gQ (pub i) = γ) (hz : ∀ i < nb, RunSum.pQ (pub i) Coin.PUB_Z = z)
    (hα : ∀ i < nb, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = α ^ k) :
    ∃ blocks : List BlockC, blocks.length = nb ∧
      (∀ i < nb, ∃ B, blocks[i]? = some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs ∧ B.lost = lost i) ∧
      (∀ B ∈ blocks, ∀ tx ∈ B.txs, (∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ Spec.Block.MAX_MONEY) ∧
        Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY) ∧
      ∀ N : ℕ → ℕ,
        ∑ i ∈ Finset.range nb, RunSum.pQ (pub i) Coin.PUB_S = (blocks.map (blockSum N (efrac N γ α z))).sum ∧
        (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
          ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
            (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t))) ∧
            c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ c.ser.length < P) ∧
        (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
          1 ≤ t → (∀ k < tx.vin.length, RealVal ((B.claim t k).code, (B.claim t k).ser)) →
          Spec.Coins.outSum tx ≤ Spec.Block.MAX_MONEY → Spec.Coins.ClaimsOK (txcOf N B t tx)) := by
  have hne : ∀ i < nb, ∀ (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx → tx.vin ≠ [] ∧ tx.vout ≠ [] :=
    fun i hi t tx htx => by
      obtain ⟨h1, h2, -, -⟩ := txs_basic (hL i hi) (hsat i hi) (hL24 i hi) (S i) tx (List.mem_of_getElem? htx)
      exact ⟨h1, h2⟩
  have key : ∀ i, ∃ claim : ℕ → ℕ → Claim, i < nb →
      (∀ N : ℕ → ℕ, RunSum.pQ (pub i) Coin.PUB_S =
        blockSum N (efrac N γ α z) ⟨h0 + i, (S i).b.txs, lost i, claim⟩) ∧
      (∀ (N : ℕ → ℕ) (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx →
        ∀ ev ∈ txIns N ⟨h0 + i, (S i).b.txs, lost i, claim⟩ t tx, ∃ c : Claim,
          ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
          (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < h0 + i ∨ (c.code / 2 = h0 + i ∧ c.ctx < t))) ∧
          c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ c.ser.length < P) ∧
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
      rfl, rfl, rfl⟩, ?_, fun N => ⟨?_, ?_, ?_⟩⟩
  · intro B hB tx htx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
    have hi' := List.mem_range.mp hi
    obtain ⟨-, -, hpos, hsum⟩ := txs_basic (hL i hi') (hsat i hi') (hL24 i hi') (S i) tx htx
    refine ⟨fun o ho => ⟨hpos o ho, le_trans ?_ hsum⟩, hsum⟩
    exact List.single_le_sum (fun x hx => by
      obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hx; exact hpos o' ho') _ (List.mem_map_of_mem ho)
  · rw [List.map_map, list_sum_range_qm]
    exact Finset.sum_congr rfl fun i hi => (hclaim i (Finset.mem_range.mp hi)).1 N
  · intro i B hB t tx htx ev hev
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hB)
    exact (hclaim j (List.mem_range.mp hj)).2.1 N t tx htx ev hev
  · intro i B hB t tx htx ht1 hcv hout
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hB)
    exact (hclaim j (List.mem_range.mp hj)).2.2 N t tx htx ht1 hcv hout

/-- **An epoch from its block systems, as Core connects it.** Block systems `i < nb` at heights `h0 + i`,
sharing the epoch's challenge, with Core's lost-coinbase flags, give the epoch's blocks (their
transactions the systems' parsed blocks). For positions `N` from `g0`, an initial set of real coins
created before the epoch, well-formed events whose bytes `γ` separates and distinct created outpoints:
outside a bad set of `(α, z)` fixed by the events, if the blocks' public partial sums plus the initial
set's fractions equal the final set's, Core's connect of the epoch's transactions from the initial view
succeeds and ends at exactly the final set. -/
theorem epoch_systems_core (nb : ℕ) (inst : ℕ → ℕ → Inst) (pub : ℕ → ℕ → F) (L : ℕ → ℕ → ℕ)
    (hL : ∀ i < nb, ∀ c < 15, (inst i c).logSize = L i c) (hsat : ∀ i < nb, hashSys.SatisfiedExt (inst i) (pub i) [])
    (hL24 : ∀ i < nb, ∀ c < 15, L i c ≤ 23) (S : ∀ i, Setup (inst i) (pub i) (L i 1)) (h0 : ℕ) (hh : h0 + nb ≤ 2 ^ 23)
    (hp2 : ∀ i < nb, pub i 2 = ((h0 + i : ℕ) : F))
    (hlost : ∀ i < nb, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost (h0 + i) then 1 else 0)
    (γ α z : QM) (hγ : ∀ i < nb, FpWalk.gQ (pub i) = γ) (hz : ∀ i < nb, RunSum.pQ (pub i) Coin.PUB_Z = z)
    (hα : ∀ i < nb, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = α ^ k) :
    ∃ blocks : List BlockC, blocks.length = nb ∧
      (∀ i < nb, ∃ B, blocks[i]? = some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs) ∧
      (∀ (N : ℕ → ℕ) (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
        ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
          c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ c.ser.length < P) ∧
      ∀ (N : ℕ → ℕ) (g0 : ℕ) (init fin : List CEv) (Sb : Finset (List F)), γ ∉ fpBad (𝕂 := QM) Sb →
        (∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
          WFE N e ∧ bytesF e ∈ Sb) →
        (∀ i < nb, N (h0 + i) = g0 + ∑ i' ∈ Finset.range i, (S i').b.txs.length) →
        (∀ e ∈ init, e.2.2 < g0) → (∀ e ∈ init, RealVal e.2.1) →
        (((init : Multiset CEv) + created g0 (allTxs N blocks)).map Prod.fst).Nodup →
        ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
            2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
          ((α, z) ∉ Bad →
            init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
              fin.length < P →
            ∑ i ∈ Finset.range nb, RunSum.pQ (pub i) Coin.PUB_S + (init.map (efrac N γ α z)).sum =
              (fin.map (efrac N γ α z)).sum →
            (∃ m, Spec.Coins.connectTxs (Spec.Coins.untag (vmap coinOfVal (viewOf init))) (allTxC N blocks) =
                some (Spec.Coins.untag (vmap coinOfVal m), (allTxC N blocks).map Spec.Coins.claimFee) ∧
              ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin) ∧
            ∀ i < nb, ∀ (t : ℕ) (tx : Spec.Block.Tx), (S i).b.txs[t]? = some tx → 1 ≤ t →
              Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true) := by
  obtain ⟨blocks, hlen, hat, hvo, hfacts⟩ := epoch_blocks nb inst pub L hL hsat hL24 S h0 hh hp2
    (fun i => Spec.Coins.bip30Lost (h0 + i)) hlost γ α z hγ hz hα
  refine ⟨blocks, hlen, fun i hi => by obtain ⟨B, h1, h2, h3, -⟩ := hat i hi; exact ⟨B, h1, h2, h3⟩,
    fun N i B hB t tx htx ev hev => by
      obtain ⟨c, h1, -, h2⟩ := (hfacts N).2.1 i B hB t tx htx ev hev; exact ⟨c, h1, h2⟩,
    fun N g0 init fin Sb hγS hwf hN hinit hinitR hnd => ?_⟩
  obtain ⟨hsum, hlexB, hokB⟩ := hfacts N
  -- the blocks' heights, positions and bounds
  have hB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → i < nb ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs ∧
      B.lost = Spec.Coins.bip30Lost (h0 + i) := by
    intro i B hBi
    have hi : i < nb := by have := (List.getElem?_eq_some_iff.mp hBi).1; omega
    obtain ⟨B', h1, h2, h3, h4⟩ := hat i hi
    rw [hBi] at h1; obtain rfl := Option.some.inj h1
    exact ⟨hi, h2, h3, h4⟩
  have hpre : ∀ i ≤ nb, ((blocks.take i).map (·.txs.length)).sum = ∑ i' ∈ Finset.range i, (S i').b.txs.length := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨B, h1, -, h3, -⟩ := hat i (by omega)
      rw [List.take_add_one, h1, List.map_append, List.sum_append, ih (by omega), Finset.sum_range_succ]
      simp [h3]
  have hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum := by
    intro i B hBi
    obtain ⟨hi, h2, -, -⟩ := hB i B hBi
    rw [h2, hN i hi, hpre i (by omega)]
  have hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i') := by
    intro i i' B B' h1 h2
    rw [(hB i B h1).2.1, (hB i' B' h2).2.1]; omega
  have hbnd : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25 := by
    intro i B hBi
    obtain ⟨hi, h2, h3, -⟩ := hB i B hBi
    have hLb : 2 ^ L i 1 ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) (hL24 i hi 1 (by decide))
    have := (S i).hN25
    refine ⟨by rw [h2]; omega, by rw [h3]; omega⟩
  have hmem : ∀ B ∈ blocks, ∃ i, blocks[i]? = some B := fun B hBm => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hBm; exact ⟨i, List.getElem?_eq_getElem hi⟩
  obtain ⟨Bad, hcard, hcore⟩ := epoch_core N γ blocks g0 init fin hγS hwf hpos hinc hbnd hinit hinitR hnd
    (fun B hBm tx htx => (hvo B hBm tx htx).1)
    (fun B hBm => by obtain ⟨i, hi⟩ := hmem B hBm; rw [(hB i B hi).2.1]; exact (hB i B hi).2.2.2)
    (fun B hBm tx htx => (hvo B hBm tx htx).2)
    (fun i B hB t tx htx ev hev => by obtain ⟨c, h1, h2, -⟩ := hlexB i B hB t tx htx ev hev; exact ⟨c, h1, h2⟩) hokB
  refine ⟨Bad, hcard, fun haz hcnt hbal => ?_⟩
  obtain ⟨hc, hnd'⟩ := hcore (α, z) haz hcnt (by rw [← hsum]; exact hbal)
  refine ⟨hc, fun i hi t tx htx ht1 => ?_⟩
  obtain ⟨B, h1, -, h3, -⟩ := hat i hi
  exact hnd' B (List.mem_of_getElem? h1) t tx (by rw [h3]; exact htx) ht1

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

/-- **An epoch block passes Core's checks.** A block system whose non-coinbase transactions spend
distinct outpoints (as `epoch_systems_core` gives for every block of a balanced epoch) passes Core's
`CheckBlock` and `ContextualCheckBlock` (`block_sound`). -/
theorem epoch_block_valid (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) {c : Spec.Block.Ctx} (hh : c.height < 2 ^ 23)
    (hmtp : c.prevMtp < 2 ^ 32) (hpub : BlockPubs c pub)
    (hnd : ∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
      Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true) :
    Spec.Block.checkBlock c (Rb inst pub) = none := by
  obtain ⟨b, hp, himp⟩ := block_sound hL hsat hL24 hL8 hh hmtp hpub
  have hb : b = S.b := by rw [S.hparse] at hp; exact (Option.some.inj hp).symm
  subst hb
  apply himp
  intro tx htx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem htx
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    obtain ⟨-, t0, inp, -, -, -, hget0, -, -, -, -, -, hv0, -⟩ := cb_facts hL hsat hL24 hL8 S
    rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hget0
    rw [hget0, hv0]; rfl
  · exact hnd j _ (List.getElem?_eq_getElem hj) hpos

end System

end StarkedAir.Block
