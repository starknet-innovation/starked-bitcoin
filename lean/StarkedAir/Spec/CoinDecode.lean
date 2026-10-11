/-
**From the circuit's coin values to Core's coins (M3b, layer 5).** A coin value is `(code, serTxOut)`.
`coinOfVal` decodes it: height `code / 2`, coinbase `code % 2`, the amount from the first 8 bytes, the
script after the length prefix. `decSer_ser`: a real output's serialization decodes to its amount and
script (amount in `[0, 2^64)`).
-/
import StarkedAir.Spec.CoinEpoch
import StarkedAir.Spec.BlockSer
import StarkedAir.Spec.UtxoMap

namespace StarkedAir.Spec.CoinEpoch

open StarkedAir.Spec.Block StarkedAir.Spec.Utxo

/-- The CompactSize prefix's length, from its first byte. -/
def compactLen (b : UInt8) : ℕ := if b.toNat < 253 then 1 else if b.toNat = 253 then 3 else if b.toNat = 254 then 5 else 9

/-- Decode a `serTxOut`: the amount and the script. -/
def decSer (s : Bytes) : ℤ × Bytes := ((le (s.take 8) : ℕ), s.drop (8 + compactLen (s.getD 8 0)))

/-- A coin value as Core's coin. -/
def coinOfVal (v : Val) : Coins.Coin := ⟨v.1 / 2, v.1 % 2 == 1, (decSer v.2).1, (decSer v.2).2⟩

theorem compactLen_ser (n : ℕ) : compactLen ((serCompact n).getD 0 0) = (serCompact n).length := by
  have hm : ∀ k, (UInt8.ofNat k).toNat = k % 256 := fun k => rfl
  by_cases h1 : n < 253
  · simp [serCompact, h1, compactLen, hm, Nat.mod_eq_of_lt (show n < 256 by omega)]
  by_cases h2 : n < 0x10000
  · simp [serCompact, h1, h2, compactLen, leBytes_length]
  by_cases h3 : n < 0x100000000
  · simp [serCompact, h1, h2, h3, compactLen, leBytes_length]
  · simp [serCompact, h1, h2, h3, compactLen, leBytes_length]

/-- **A real output's serialization decodes to it.** -/
theorem decSer_ser (o : TxOut) (h0 : 0 ≤ o.value) (h1 : o.value < 2 ^ 64) :
    decSer (serTxOut o) = (o.value, o.scriptPubKey) := by
  unfold decSer serTxOut serVarBytes
  have hv : (o.value % 2 ^ 64).toNat = o.value.toNat := by rw [Int.emod_eq_of_lt h0 h1]
  rw [hv]
  have hl := leBytes_length 8 o.value.toNat
  have hc : (leBytes 8 o.value.toNat ++ (serCompact o.scriptPubKey.length ++ o.scriptPubKey)).getD 8 0 =
      (serCompact o.scriptPubKey.length).getD 0 0 := by
    rw [List.getD_append_right _ _ _ _ (by omega), hl]
    have hne : (serCompact o.scriptPubKey.length) ≠ [] := by unfold serCompact; split_ifs <;> simp
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
    rw [hal]; simp
  rw [hc, compactLen_ser, List.take_left' hl, le_leBytes, ← List.drop_drop, List.drop_left' hl, List.drop_left]
  have : o.value.toNat < 256 ^ 8 := by omega
  rw [Nat.mod_eq_of_lt this, Int.toNat_of_nonneg h0]

/-! ### The epoch's transactions as Core's -/

/-- Transaction `t` of block `B` in context, with its claims decoded. -/
def txcOf (N : ℕ → ℕ) (B : BlockC) (t : ℕ) (tx : Tx) : Coins.TxC :=
  ⟨B.h, t == 0, txid tx, tx, if t = 0 then [] else
    (tx.vin.zipIdx).map fun p => (coinOfVal ((B.claim t p.2).code, (B.claim t p.2).ser),
      N ((B.claim t p.2).code / 2) + (B.claim t p.2).ctx)⟩

def blockTxC (N : ℕ → ℕ) (B : BlockC) : List Coins.TxC := (B.txs.zipIdx).map fun p => txcOf N B p.2 p.1

def allTxC (N : ℕ → ℕ) (blocks : List BlockC) : List Coins.TxC := blocks.flatMap (blockTxC N)

theorem zip_zipIdx_map {α β : Type} (l : List α) (f : α × ℕ → β) :
    l.zip (l.zipIdx.map f) = l.zipIdx.map fun p => (p.1, f p) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- **The decoded events are Core's.** With the lost-coinbase flag Core's (`bip30Lost`) and every output's
amount in `[0, 2^64)`, a transaction's events, decoded, are its `TxC`'s. -/
theorem tmap_txEvents (N : ℕ → ℕ) (B : BlockC) (hlost : B.lost = Coins.bip30Lost B.h)
    (t : ℕ) (tx : Tx) (hval : ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value < 2 ^ 64) :
    tmap coinOfVal (⟨txIns N B t tx, txOuts B t tx⟩ : Utxo.Tx OutPoint Val) = Coins.events (txcOf N B t tx) := by
  unfold tmap Coins.events txcOf
  congr 1
  · by_cases ht : t = 0
    · simp [txIns, ht]
    · simp only [txIns, if_neg ht, beq_iff_eq, ht, Bool.false_eq_true, if_false, List.map_map]
      rw [zip_zipIdx_map, List.map_map]
      rfl
  · unfold txOuts Coins.created
    simp only [beq_iff_eq, List.map_map]
    by_cases hc : (t = 0 ∧ Coins.bip30Lost B.h = true)
    · rw [if_pos (by simp [hc.1, hc.2])]
      apply List.eq_nil_of_length_eq_zero
      simp only [List.length_map]
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro p _
      simp [live, hlost, hc.1, hc.2]
    · rw [if_neg (by simpa using hc)]
      have hf : ((tx.vout.zipIdx).filter fun p => live B.lost t p.1) =
          (tx.vout.zipIdx).filter fun p => !Coins.unspendable p.1 := by
        apply List.filter_congr
        intro p _
        simp only [live, hlost]
        by_cases ht : t = 0
        · simp [ht, show Coins.bip30Lost B.h = false by simpa [ht] using hc]
        · simp [ht]
      rw [hf]
      apply List.map_congr_left
      intro p hp
      have hmem : p.1 ∈ tx.vout := (List.mem_zipIdx' (List.mem_of_mem_filter hp)).2 ▸ List.getElem_mem _
      obtain ⟨h0, h1⟩ := hval p.1 hmem
      simp only [Function.comp, coinOfVal, decSer_ser p.1 h0 h1, codeOf]
      congr 2
      · split_ifs <;> omega
      · by_cases ht : t = 0 <;> simp [ht]

theorem allTxs_map (N : ℕ → ℕ) (blocks : List BlockC)
    (hlost : ∀ B ∈ blocks, B.lost = Coins.bip30Lost B.h)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value < 2 ^ 64) :
    (allTxs N blocks).map (tmap coinOfVal) = (allTxC N blocks).map Coins.events := by
  unfold allTxs allTxC
  simp only [List.map_flatMap]
  apply List.flatMap_congr
  intro B hB
  unfold blockTxs blockTxC
  simp only [List.map_map]
  apply List.map_congr_left
  intro p hp
  have hmem : p.1 ∈ B.txs := (List.mem_zipIdx' hp).2 ▸ List.getElem_mem _
  exact tmap_txEvents N B (hlost B hB) p.2 p.1 (hval B hB p.1 hmem)

/-- **The epoch connects as Core does.** A successful run of the epoch's events from the initial set,
decoded, is Core's connect of the epoch's transactions from the decoded initial view, given each
transaction's claim checks (`ClaimsOK`). -/
theorem epoch_connect (N : ℕ → ℕ) (blocks : List BlockC) (g0 : ℕ) (init : List CEv) {m : View OutPoint Val}
    (hlost : ∀ B ∈ blocks, B.lost = Coins.bip30Lost B.h)
    (hval : ∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value < 2 ^ 64)
    (hrun : run g0 (viewOf init) (allTxs N blocks) = some m) (hok : ∀ x ∈ allTxC N blocks, Coins.ClaimsOK x) :
    Coins.connectTxs (Coins.untag (vmap coinOfVal (viewOf init))) (allTxC N blocks) =
      some (Coins.untag (vmap coinOfVal m), (allTxC N blocks).map Coins.claimFee) := by
  have h := run_map coinOfVal g0 _ _ _ hrun
  rw [allTxs_map N blocks hlost hval] at h
  exact Coins.connect_of_run _ g0 _ _ h hok

end StarkedAir.Spec.CoinEpoch
