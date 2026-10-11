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
      rw [List.take_succ, List.map_append, List.sum_append, ih (by omega), Finset.sum_range_succ, h1]
      simp [h3]
  refine created_wfe N blocks g0 (fun i B hBi => ?_) (fun i B hBi => ?_)
  · obtain ⟨hi, h2, h3⟩ := hB i B hBi
    obtain ⟨⟨-, hn, hw⟩, -⟩ := Spec.Block.toksBlock_sound (S i).htok
    exact ⟨by omega, by rw [h3]; exact hn, by rw [h3]; exact hw⟩
  · obtain ⟨hi, h2, -⟩ := hB i B hBi
    rw [h2, hN i hi, hpre i hi.le]

end StarkedAir.Block
