/-
**SHA-256 on bytes, block by block (M3a.3).** Bridges `Spec.Block.sha256d` (bytes, `compressAll` over
`pad`) to the AIR's view: compressions over 16-word blocks, then a second hash over the digest block.
-/
import StarkedAir.Spec.Block

namespace StarkedAir.Block.HashSpec

open StarkedAir.Spec.Sha256
open StarkedAir.Spec.Block

/-- `compressAll` peels one 64-byte chunk. -/
theorem compressAll_cons (H : State) {m : Bytes} (hm : m ≠ []) :
    compressAll H m = compressAll (compress H (chunkWords (m.take 64))) (m.drop 64) := by
  cases m with
  | nil => exact absurd rfl hm
  | cons x xs => rw [compressAll]

/-- Compressions over chunks `0..b−1` of `m`. -/
def chunkFold (H : State) (m : Bytes) : ℕ → State
  | 0 => H
  | b + 1 => compress (chunkFold H m b) (chunkWords ((m.drop (64 * b)).take 64))

theorem compressAll_fold (H : State) (m : Bytes) (b : ℕ) (hm : m.length = 64 * b) :
    compressAll H m = chunkFold H m b := by
  have key : ∀ k ≤ b, compressAll (chunkFold H m k) (m.drop (64 * k)) = compressAll H m := by
    intro k hk
    induction k with
    | zero => simp [chunkFold]
    | succ k ih =>
      have hne : m.drop (64 * k) ≠ [] := by
        intro h; have := congrArg List.length h; rw [List.length_drop, hm] at this; simp at this; omega
      rw [← ih (by omega)]
      conv_rhs => rw [compressAll_cons _ hne]
      simp only [chunkFold, List.drop_drop]
      congr 2
  rw [← key b le_rfl, show m.drop (64 * b) = [] by simp [hm]]
  rw [compressAll]

theorem stateBytes_length (h : State) : (stateBytes h).length = 32 := by
  simp [stateBytes, beBytes]

theorem pad_length (m : Bytes) : (pad m).length = m.length + 1 + (119 - m.length % 64) % 64 + 8 := by
  simp [pad, beBytes]; omega

/-- Four big-endian bytes of a word recombine to it. -/
theorem be4 (w : Word) :
    BitVec.ofNat 32 ((UInt8.ofNat (w.toNat / 2 ^ 24)).toNat * 2 ^ 24 + (UInt8.ofNat (w.toNat / 2 ^ 16)).toNat * 2 ^ 16 +
      (UInt8.ofNat (w.toNat / 2 ^ 8)).toNat * 2 ^ 8 + (UInt8.ofNat (w.toNat / 2 ^ 0)).toNat) = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp; omega

theorem be4' (w : Word) :
    BitVec.ofNat 32 (w.toNat / 16777216 % 256 * 16777216 + w.toNat / 65536 % 256 * 65536 +
      w.toNat / 256 % 256 * 256 + w.toNat % 256) = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp; omega

/-- The second hash's message block: the digest's words, then the padding of a 32-byte message. -/
theorem chunk_state (h : State) :
    chunkWords ((pad (stateBytes h)).take 64) = StarkedAir.Spec.Bitcoin.digestBlock h := by
  funext t
  obtain ⟨a, b, c, d, e, f, g, hh⟩ := h
  by_cases ht : t < 16
  · interval_cases t <;>
      simp [chunkWords, pad, stateBytes, beBytes, StarkedAir.Spec.Bitcoin.digestBlock,
        StarkedAir.Spec.Bitcoin.stateWord, be4']
  · have hl : ((pad (stateBytes ⟨a, b, c, d, e, f, g, hh⟩)).take 64).length ≤ 64 := List.length_take_le _ _
    have z : ∀ k, 64 ≤ k → ((pad (stateBytes ⟨a, b, c, d, e, f, g, hh⟩)).take 64).toArray.getD k 0 = 0 := by
      intro k hk; simp [Array.getD]; intro hp; omega
    simp only [chunkWords, z (4 * t) (by omega), z (4 * t + 1) (by omega), z (4 * t + 2) (by omega),
      z (4 * t + 3) (by omega), StarkedAir.Spec.Bitcoin.digestBlock, if_neg (by omega : ¬ t < 8),
      if_neg (by omega : ¬ t = 8), if_neg (by omega : ¬ t = 15)]
    rfl

/-- **SHA256d, as the AIR computes it**: compressions over the padded message's `b` blocks, then one
compression of the digest block. -/
theorem sha256d_eq (m : Bytes) (b : ℕ) (hm : (pad m).length = 64 * b) :
    sha256d m = stateBytes (compress IV (StarkedAir.Spec.Bitcoin.digestBlock (chunkFold IV (pad m) b))) := by
  have h2 : (pad (stateBytes (chunkFold IV (pad m) b))).length = 64 * 1 := by
    rw [pad_length, stateBytes_length]
  have h1 : sha256 m = stateBytes (chunkFold IV (pad m) b) := by rw [sha256, compressAll_fold IV (pad m) b hm]
  rw [sha256d, h1, sha256, compressAll_fold IV _ 1 h2]
  simp only [chunkFold, Nat.mul_zero, List.drop_zero, chunk_state]

end StarkedAir.Block.HashSpec
