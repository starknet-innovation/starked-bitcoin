/-
**The BIP34 height push for 3-byte heights.** For `2^16 ≤ h < 2^23`, `CScript() << h` is
`03 h0 h1 h2` (little-endian, the top byte below `0x80`, so no sign byte).
-/
import BitcoinConsensus.Block

namespace BitcoinConsensus.Block

theorem and80 : ∀ x < 128, (UInt8.ofNat x &&& 0x80) = 0 := by decide

theorem pushHeight_3 {h : ℕ} (h1 : 65536 ≤ h) (h2 : h < 2 ^ 23) :
    pushHeight h = [3, UInt8.ofNat h, UInt8.ofNat (h / 256), UInt8.ofNat (h / 65536)] := by
  have hlog : Nat.log 256 h = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num; omega) (by norm_num; omega)
  have hs : scriptNum h = [UInt8.ofNat h, UInt8.ofNat (h / 256), UInt8.ofNat (h / 65536)] := by
    unfold scriptNum
    rw [if_neg (by omega), hlog]
    simp only [leBytes, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
    norm_num
    exact and80 _ (by omega)
  unfold pushHeight
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [hs]
  rfl

end BitcoinConsensus.Block
