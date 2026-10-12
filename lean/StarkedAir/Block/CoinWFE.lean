/-
**Discharging `WFE` for created events.** `epoch_systems_core` assumes every event well formed (`WFE`,
CoinEpochSound.lean: a 32-byte txid, 32-bit index and code, the index offset and the script length below
P). For the events the blocks *create*, this follows from the blocks: the txid is a SHA256d digest,
each block is well formed (`Blk.WF`, from the fields AIR's tokens: counts and scripts at most
`MAX_SIZE`), heights are below `2^23`, and the creation index of transaction `t` of block `i` is
`N h_i + t`. `created_wfe` states it for any list of blocks with those properties.
-/
import StarkedAir.Block.CoinEpochCore

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo StarkedAir.Spec.Block
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.LogUpSZ

theorem txid_length (t : Tx) : (txid t).length = 32 := by
  simp [txid, sha256d, sha256, stateBytes, beBytes]

theorem serCompact_length_le (n : ℕ) : (serCompact n).length ≤ 9 := by
  unfold serCompact; split_ifs <;> simp [leBytes]

theorem serTxOut_length (o : TxOut) (h : o.scriptPubKey.length ≤ MAX_SIZE) : (serTxOut o).length < P := by
  have := serCompact_length_le o.scriptPubKey.length
  simp only [serTxOut, serVarBytes, List.length_append, leBytes, List.length_map, List.length_range]
  unfold MAX_SIZE at h; unfold P; omega

/-- A created event of a block: transaction `t`, output `q`. -/
theorem mem_created_block' (N : ℕ → ℕ) (B : BlockC) (g : ℕ) {e : CEv} (he : e ∈ created g (blockTxs N B)) :
    ∃ t < B.txs.length, ∃ tx, B.txs[t]? = some tx ∧ ∃ q < tx.vout.length, ∃ o, tx.vout[q]? = some o ∧
      e = (⟨txid tx, q⟩, (codeOf B.h t, serTxOut o), g + t) := by
  have gen : ∀ (l : List (Tx × ℕ)) (g : ℕ), e ∈ created g (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ :
      Spec.Utxo.Tx OutPoint Val)) → ∃ k < l.length, ∃ p, l[k]? = some p ∧ ∃ q < p.1.vout.length, ∃ o, p.1.vout[q]? = some o ∧
        e = (⟨txid p.1, q⟩, (codeOf B.h p.2, serTxOut o), g + k) := by
    intro l
    induction l with
    | nil => intro g h; simp [created] at h
    | cons p l ih =>
      intro g h
      simp only [List.map_cons, created, Multiset.mem_add] at h
      rcases h with h | h
      · simp only [Spec.Utxo.outsT, Multiset.mem_coe] at h
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h
        simp only [txOuts] at ho
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
        obtain ⟨hrm, -⟩ := List.mem_filter.mp hr
        have hq := List.mem_zipIdx hrm
        refine ⟨0, by simp, p, by simp, r.2, by simpa using hq.2.1, r.1, ?_, by simp⟩
        rw [List.getElem?_eq_some_iff]
        exact ⟨by simpa using hq.2.1, by simpa using hq.2.2.symm⟩
      · obtain ⟨k, hk, p', hp', q, hq, o, ho, rfl⟩ := ih (g + 1) h
        exact ⟨k + 1, by simp; omega, p', by simpa using hp', q, hq, o, ho, by simp; omega⟩
  obtain ⟨k, hk, p, hp, q, hq, o, ho, rfl⟩ := gen B.txs.zipIdx g he
  have hk' : k < B.txs.length := by simpa using hk
  rw [List.getElem?_zipIdx, Option.map_eq_some_iff] at hp
  obtain ⟨tx, htx, rfl⟩ := hp
  exact ⟨k, hk', tx, htx, q, hq, o, ho, by simp⟩

/-- A created event of a list of blocks: block `i`'s, with its first index the transactions before it. -/
theorem mem_created_blocks (N : ℕ → ℕ) : ∀ (blocks : List BlockC) (g : ℕ) {e : CEv},
    e ∈ created g (allTxs N blocks) → ∃ i B, blocks[i]? = some B ∧
      e ∈ created (g + ((blocks.take i).map (·.txs.length)).sum) (blockTxs N B)
  | [], g, e, h => by simp [allTxs, created] at h
  | B :: bs, g, e, h => by
    simp only [allTxs, List.flatMap_cons] at h
    rw [created_append, Multiset.mem_add] at h
    rcases h with h | h
    · exact ⟨0, B, rfl, by simpa using h⟩
    · rw [blockTxs_length] at h
      obtain ⟨i, B', hB', h'⟩ := mem_created_blocks N bs (g + B.txs.length) h
      refine ⟨i + 1, B', by simpa using hB', ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      rwa [← Nat.add_assoc]

/-- **Created events are well formed.** For blocks with heights below `2^23`, well formed (counts and
scripts at most `MAX_SIZE`), and `N` giving each block's first transaction index. -/
theorem created_wfe (N : ℕ → ℕ) (blocks : List BlockC) (g0 : ℕ)
    (hB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 23 ∧ B.txs.length ≤ MAX_SIZE ∧ ∀ tx ∈ B.txs, Tx.WF tx)
    (hN : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum) :
    ∀ e ∈ created g0 (allTxs N blocks), WFE N e := by
  intro e he
  obtain ⟨i, B, hBi, he'⟩ := mem_created_blocks N blocks g0 he
  obtain ⟨hh, hlen, hwf⟩ := hB i B hBi
  obtain ⟨t, ht, tx, htx, q, hq, o, ho, rfl⟩ := mem_created_block' N B _ he'
  have hwt : Tx.WF tx := hwf tx (List.mem_of_getElem? htx)
  obtain ⟨-, -, -, -, hvl, -, hwo⟩ := hwt
  have hso : TxOut.WF o := hwo o (List.mem_of_getElem? ho)
  have hcode : codeOf B.h t / 2 = B.h := by unfold codeOf; split <;> omega
  have hcl : codeOf B.h t < 2 ^ 32 := by unfold codeOf; split <;> omega
  refine ⟨txid_length tx, ?_, hcl, ?_, ?_, serTxOut_length o hso.2.2⟩
  · dsimp only; unfold MAX_SIZE at hvl; omega
  · dsimp only; rw [hcode, hN i B hBi]; omega
  · dsimp only; rw [hcode, hN i B hBi]; unfold MAX_SIZE at hlen; unfold P; omega

/-- **Created events of an epoch's block systems are well formed**: for the blocks `epoch_systems_core`
returns (heights `h0 + i < 2^23`, transactions the systems' parsed blocks), with `N` the epoch's
transaction offsets. So that hypothesis of `epoch_systems_core` is left for the initial set, the spent
events and the final set only. -/
theorem created_wfe_systems {nb : ℕ} {inst : ℕ → ℕ → Inst} {pub : ℕ → ℕ → F} {L : ℕ → ℕ}
    (S : ∀ i, Setup (inst i) (pub i) (L i)) {h0 : ℕ} (hh : h0 + nb ≤ 2 ^ 23) {blocks : List BlockC}
    (hlen : blocks.length = nb) (hat : ∀ i < nb, ∃ B, blocks[i]? = some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs)
    (N : ℕ → ℕ) (g0 : ℕ) (hN : ∀ i < nb, N (h0 + i) = g0 + ∑ i' ∈ Finset.range i, (S i').b.txs.length) :
    ∀ e ∈ created g0 (allTxs N blocks), WFE N e := by
  have hB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → i < nb ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs := by
    intro i B hBi
    have hi : i < nb := by have := (List.getElem?_eq_some_iff.mp hBi).1; omega
    obtain ⟨B', h1, h2, h3⟩ := hat i hi
    rw [hBi] at h1; obtain rfl := Option.some.inj h1
    exact ⟨hi, h2, h3⟩
  have hpre : ∀ i ≤ nb, ((blocks.take i).map (·.txs.length)).sum = ∑ i' ∈ Finset.range i, (S i').b.txs.length := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      obtain ⟨B, h1, -, h3⟩ := hat i (by omega)
      rw [List.take_add_one, List.map_append, List.sum_append, ih (by omega), Finset.sum_range_succ, h1]
      simp [h3]
  refine created_wfe N blocks g0 (fun i B hBi => ?_) (fun i B hBi => ?_)
  · obtain ⟨hi, h2, h3⟩ := hB i B hBi
    obtain ⟨⟨-, hn, hw⟩, -⟩ := Spec.Block.toksBlock_sound (S i).htok
    exact ⟨by omega, by rw [h3]; exact hn, by rw [h3]; exact hw⟩
  · obtain ⟨hi, h2, -⟩ := hB i B hBi
    rw [h2, hN i hi, hpre i hi.le]

/-! ### Spent events -/

theorem mem_spent_txs (N : ℕ → ℕ) (B : BlockC) : ∀ (l : List (Tx × ℕ)) {e : CEv},
    e ∈ spent (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ : Spec.Utxo.Tx OutPoint Val)) →
    ∃ p ∈ l, e ∈ txIns N B p.2 p.1
  | [], e, h => by simp [spent] at h
  | p :: l, e, h => by
    simp only [List.map_cons, spent, Multiset.mem_add, Multiset.mem_coe] at h
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, h'⟩ := mem_spent_txs N B l h
      exact ⟨q, List.mem_cons_of_mem _ hq, h'⟩

/-- A spent event of a list of blocks: an input of block `i`'s transaction `t`. -/
theorem mem_spent_blocks (N : ℕ → ℕ) : ∀ (blocks : List BlockC) {e : CEv}, e ∈ spent (allTxs N blocks) →
    ∃ (i : ℕ) (B : BlockC), blocks[i]? = some B ∧ ∃ (t : ℕ) (tx : Tx), B.txs[t]? = some tx ∧ e ∈ txIns N B t tx
  | [], e, h => by simp [allTxs, spent] at h
  | B :: bs, e, h => by
    simp only [allTxs, List.flatMap_cons] at h
    rw [mem_spent_append, Multiset.mem_add] at h
    rcases h with h | h
    · obtain ⟨p, hp, h'⟩ := mem_spent_txs N B B.txs.zipIdx h
      have hk := List.mem_zipIdx' hp
      exact ⟨0, B, rfl, p.2, p.1, by rw [hk.2]; exact List.getElem?_eq_getElem hk.1, h'⟩
    · obtain ⟨i, B', hB', rest⟩ := mem_spent_blocks N bs h
      exact ⟨i + 1, B', by simpa using hB', rest⟩

/-- **Spent events are well formed**, for well-formed blocks whose input claims have bounded fields
(`epoch_blocks` gives the claim bounds). -/
theorem spent_wfe (N : ℕ → ℕ) (blocks : List BlockC)
    (hB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ tx ∈ B.txs, Tx.WF tx)
    (hc : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Tx), B.txs[t]? = some tx →
      ∀ ev ∈ txIns N B t tx, ∃ c : Claim, ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ c.ser.length < P) :
    ∀ e ∈ spent (allTxs N blocks), WFE N e := by
  intro e he
  obtain ⟨i, B, hBi, t, tx, htx, hin⟩ := mem_spent_blocks N blocks he
  obtain ⟨c, hce, hcode, hctx, hser⟩ := hc i B hBi t tx htx e hin
  have hwt : Tx.WF tx := hB i B hBi tx (List.mem_of_getElem? htx)
  obtain ⟨-, -, -, -, -, hwi, -⟩ := hwt
  -- the outpoint is an input's prevout
  have hpv : ∃ inp ∈ tx.vin, e.1 = inp.prevout := by
    unfold txIns at hin
    split_ifs at hin
    · simp at hin
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hin
      exact ⟨p.1, (List.mem_zipIdx' hp).2 ▸ List.getElem_mem _, rfl⟩
  obtain ⟨inp, hinp, hpo⟩ := hpv
  obtain ⟨hh32, hn32, -⟩ := hwi inp hinp
  rw [hce]
  refine ⟨by rw [hpo]; exact hh32, by rw [hpo]; exact hn32, hcode, by simp, by simp; unfold P; omega, hser⟩

/-- **`epoch_systems_core` with `WFE` assumed for the initial and final sets only**: the created and spent
events' well-formedness is proven (`created_wfe_systems`, `spent_wfe`). -/
theorem epoch_systems_wf (nb : ℕ) (inst : ℕ → ℕ → Inst) (pub : ℕ → ℕ → F) (L : ℕ → ℕ)
    (hL : ∀ i < nb, ∀ c < 15, (inst i c).logSize = L i) (hsat : ∀ i < nb, hashSys.SatisfiedExt (inst i) (pub i) [])
    (hL24 : ∀ i < nb, L i ≤ 23) (S : ∀ i, Setup (inst i) (pub i) (L i)) (h0 : ℕ) (hh : h0 + nb ≤ 2 ^ 23)
    (hp2 : ∀ i < nb, pub i 2 = ((h0 + i : ℕ) : F))
    (hlost : ∀ i < nb, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost (h0 + i) then 1 else 0)
    (γ α z : QM) (hγ : ∀ i < nb, FpWalk.gQ (pub i) = γ) (hz : ∀ i < nb, RunSum.pQ (pub i) Coin.PUB_Z = z)
    (hα : ∀ i < nb, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = α ^ k) :
    ∃ blocks : List BlockC, blocks.length = nb ∧
      (∀ i < nb, ∃ B, blocks[i]? = some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs) ∧
      ∀ (N : ℕ → ℕ) (g0 : ℕ) (init fin : List CEv) (Sb : Finset (List F)), γ ∉ fpBad (𝕂 := QM) Sb →
        (∀ e ∈ init ++ fin, WFE N e) →
        (∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
          bytesF e ∈ Sb) →
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
              Spec.Block.nodupBy (tx.vin.map (·.prevout)) = true)  := by
  obtain ⟨blocks, hlen, hat, hcl, hmain⟩ := epoch_systems_core nb inst pub L hL hsat hL24 S h0 hh hp2 hlost γ α z hγ hz hα
  have hwfB : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ tx ∈ B.txs, Tx.WF tx := by
    intro i B hBi tx htx
    have hi : i < nb := by have := (List.getElem?_eq_some_iff.mp hBi).1; omega
    obtain ⟨B', h1, -, h3⟩ := hat i hi
    rw [hBi] at h1; obtain rfl := Option.some.inj h1
    rw [h3] at htx
    exact (Spec.Block.toksBlock_sound (S i).htok).1.2.2 tx htx
  refine ⟨blocks, hlen, hat, fun N g0 init fin Sb hγS hwfIF hby hN => hmain N g0 init fin Sb hγS (fun e he => ⟨?_, hby e he⟩) hN⟩
  simp only [List.mem_append, Multiset.mem_toList] at he
  rcases he with (h | h) | (h | h)
  · exact hwfIF e (List.mem_append_left _ h)
  · exact created_wfe_systems S hh hlen hat N g0 hN e h
  · exact spent_wfe N blocks hwfB (hcl N) e h
  · exact hwfIF e (List.mem_append_right _ h)

/-! ### Distinct created outpoints from distinct txids -/

/-- The txids of an epoch's transactions, in order. -/
def epochTxids (blocks : List BlockC) : List Spec.Block.Bytes := blocks.flatMap fun B => B.txs.map txid

theorem outs_keys_nodup (B : BlockC) (t : ℕ) (tx : Tx) : (((txOuts B t tx).map Prod.fst)).Nodup := by
  unfold txOuts
  rw [List.map_map]
  apply List.Nodup.map_on _ (((List.nodup_zipIdx_map_snd tx.vout).of_map _).filter _)
  intro x hx y hy h
  simp only [Function.comp, OutPoint.mk.injEq] at h
  have ex := List.mem_zipIdx' (List.mem_filter.mp hx).1
  have ey := List.mem_zipIdx' (List.mem_filter.mp hy).1
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  simp only at h ex ey
  obtain rfl := h.2
  exact Prod.ext (ex.2.trans ey.2.symm) rfl

theorem key_hash_of_created (N : ℕ → ℕ) (B : BlockC) : ∀ (l : List (Tx × ℕ)) (g : ℕ) {e : CEv},
    e ∈ created g (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ : Spec.Utxo.Tx OutPoint Val)) →
    ∃ p ∈ l, e.1.hash = txid p.1
  | [], g, e, h => by simp [created] at h
  | p :: l, g, e, h => by
    simp only [List.map_cons, created, Multiset.mem_add] at h
    rcases h with h | h
    · simp only [Spec.Utxo.outsT, Multiset.mem_coe] at h
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h
      simp only [txOuts] at ho
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ho
      exact ⟨p, List.mem_cons_self, rfl⟩
    · obtain ⟨p', hp', hh⟩ := key_hash_of_created N B l (g + 1) h
      exact ⟨p', List.mem_cons_of_mem _ hp', hh⟩

theorem created_txs_nodup (N : ℕ → ℕ) (B : BlockC) : ∀ (l : List (Tx × ℕ)) (g : ℕ), (l.map fun p => txid p.1).Nodup →
    ((created g (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ : Spec.Utxo.Tx OutPoint Val))).map Prod.fst).Nodup
  | [], g, _ => by simp [created]
  | p :: l, g, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.map_cons, created, Multiset.map_add]
    refine Multiset.nodup_add.mpr ⟨?_, created_txs_nodup N B l (g + 1) hn.2, Multiset.disjoint_left.mpr fun {k} hk1 hk2 => ?_⟩
    · simp only [Spec.Utxo.outsT, Multiset.map_coe, Multiset.coe_nodup, List.map_map]
      have := outs_keys_nodup B p.2 p.1
      convert this using 2
      funext o; rfl
    · simp only [Spec.Utxo.outsT, Multiset.map_coe, Multiset.mem_coe, List.map_map] at hk1
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hk1
      obtain ⟨e', he', hke⟩ := Multiset.mem_map.mp hk2
      obtain ⟨p', hp', hh⟩ := key_hash_of_created N B l (g + 1) he'
      simp only [txOuts] at ho
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp ho
      apply hn.1
      rw [List.mem_map]
      refine ⟨p', hp', ?_⟩
      rw [← hh, hke]; rfl

/-- **Distinct txids give distinct created outpoints**: the epoch theorem's remaining assumption on
created coins is no repeated txid among the epoch's transactions — SHA256d collision resistance plus
BIP34/BIP30 (utxo.md). -/
theorem created_nodup_of_txids (N : ℕ → ℕ) : ∀ (blocks : List BlockC) (g : ℕ), (epochTxids blocks).Nodup →
    ((created g (allTxs N blocks)).map Prod.fst).Nodup
  | [], g, _ => by simp [allTxs, created]
  | B :: bs, g, hn => by
    simp only [epochTxids, List.flatMap_cons, List.nodup_append] at hn
    obtain ⟨hB, hbs, hdis⟩ := hn
    simp only [allTxs, List.flatMap_cons]
    rw [created_append, Multiset.map_add]
    have hBz : (B.txs.zipIdx.map fun p => txid p.1).Nodup := by
      have : (B.txs.zipIdx.map fun p => txid p.1) = B.txs.map txid := by
        rw [show (B.txs.zipIdx.map fun p => txid p.1) = (B.txs.zipIdx.map Prod.fst).map txid by rw [List.map_map]; rfl,
          List.zipIdx_map_fst 0]
      rwa [this]
    refine Multiset.nodup_add.mpr ⟨created_txs_nodup N B B.txs.zipIdx g hBz,
      created_nodup_of_txids N bs (g + (blockTxs N B).length) hbs, Multiset.disjoint_left.mpr fun {k} hk1 hk2 => ?_⟩
    obtain ⟨e1, he1, rfl⟩ := Multiset.mem_map.mp hk1
    obtain ⟨p, hp, hh⟩ := key_hash_of_created N B B.txs.zipIdx g he1
    obtain ⟨e2, he2, hk⟩ := Multiset.mem_map.mp hk2
    obtain ⟨i, B', hB', he'⟩ := mem_created_blocks N bs _ he2
    obtain ⟨t, -, tx, htx, q, -, o, -, he2eq⟩ := mem_created_block' N B' _ he'
    have hk' : e1.1.hash = txid tx := by rw [← hk, he2eq]
    have hin1 : txid p.1 ∈ B.txs.map txid := List.mem_map.mpr ⟨p.1, by
      have := List.mem_zipIdx' hp; rw [this.2]; exact List.getElem_mem _, rfl⟩
    have hin2 : txid tx ∈ bs.flatMap fun B => B.txs.map txid :=
      List.mem_flatMap.mpr ⟨B', List.mem_of_getElem? hB', List.mem_map.mpr ⟨tx, List.mem_of_getElem? htx, rfl⟩⟩
    exact hdis _ hin1 _ hin2 (by rw [← hh, hk'])

end StarkedAir.Block
