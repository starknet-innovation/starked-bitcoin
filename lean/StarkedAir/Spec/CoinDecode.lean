/-
**From the circuit's coin values to Core's coins (M3b, layer 5).** A coin value is `(code, serTxOut)`.
`coinOfVal` decodes it: height `code / 2`, coinbase `code % 2`, the amount from the first 8 bytes, the
script after the length prefix. `decSer_ser`: a real output's serialization decodes to its amount and
script (amount in `[0, 2^64)`).
-/
import StarkedAir.Spec.CoinEpoch
import StarkedAir.Spec.BlockSer

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

end StarkedAir.Spec.CoinEpoch
