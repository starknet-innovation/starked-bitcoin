/-
**SHA-256 on bytes, block by block (M3a.3).** Bridges `Spec.Block.sha256d` (bytes, `compressAll` over
`pad`) to the AIR's view: compressions over 16-word blocks, then a second hash over the digest block.
-/
import StarkedAir.Spec.Block
import StarkedAir.Gadgets.HeaderChainSound

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

/-- Two states' words: a Merkle node's message block. -/
def pairWords (A B : State) (t : ℕ) : Word :=
  if t < 8 then StarkedAir.Spec.Bitcoin.stateWord A t else StarkedAir.Spec.Bitcoin.stateWord B (t - 8)

/-- The padding block of a 64-byte message. -/
def npadBlk (t : ℕ) : Word := if t = 0 then 0x80000000#32 else if t = 15 then 512#32 else 0#32

set_option maxHeartbeats 4000000 in
/-- **A Merkle node's hash**: SHA256d of two digests is two compressions (the digests' words, then the
padding) and the second hash. -/
theorem sha256d_pair (A B : State) :
    sha256d (stateBytes A ++ stateBytes B) =
      stateBytes (compress IV (StarkedAir.Spec.Bitcoin.digestBlock (compress (compress IV (pairWords A B)) npadBlk))) := by
  have hl : (pad (stateBytes A ++ stateBytes B)).length = 64 * 2 := by
    rw [pad_length]; simp [stateBytes_length]
  rw [sha256d_eq _ 2 hl]
  simp only [chunkFold, Nat.mul_zero, List.drop_zero, Nat.mul_one]
  have h1 : compress IV (chunkWords ((pad (stateBytes A ++ stateBytes B)).take 64)) = compress IV (pairWords A B) := by
    apply StarkedAir.HeaderChain.compress_congr
    intro t ht
    obtain ⟨a, b, c, d, e, f, g, h⟩ := A
    obtain ⟨a', b', c', d', e', f', g', h'⟩ := B
    interval_cases t <;>
      simp [chunkWords, pad, stateBytes, beBytes, pairWords, StarkedAir.Spec.Bitcoin.stateWord, be4']
  have h2 : chunkWords (((pad (stateBytes A ++ stateBytes B)).drop 64).take 64) = npadBlk := by
    funext t
    by_cases ht : t < 16
    · interval_cases t <;> simp [chunkWords, pad, stateBytes, beBytes, npadBlk]
    · have z : ∀ k, 64 ≤ k → ((List.drop 64 (pad (stateBytes A ++ stateBytes B))).take 64).toArray.getD k 0 = 0 := by
        intro k hk; simp [Array.getD]; intro hp; omega
      simp only [chunkWords, z (4 * t) (by omega), z (4 * t + 1) (by omega), z (4 * t + 2) (by omega),
        z (4 * t + 3) (by omega), npadBlk, if_neg (by omega : ¬ t = 0), if_neg (by omega : ¬ t = 15)]
      rfl
  rw [h1, h2]

/-- A state's word `t` from its bytes (big-endian, bytes `4t … 4t + 3`). -/
theorem stateWord_bytes (S : State) {t : ℕ} (ht : t < 8) :
    StarkedAir.Spec.Bitcoin.stateWord S t = BitVec.ofNat 32
      (((stateBytes S).getD (4 * t) 0).toNat * 2 ^ 24 + ((stateBytes S).getD (4 * t + 1) 0).toNat * 2 ^ 16 +
        ((stateBytes S).getD (4 * t + 2) 0).toNat * 2 ^ 8 + ((stateBytes S).getD (4 * t + 3) 0).toNat) := by
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  interval_cases t <;> simp [stateBytes, beBytes, StarkedAir.Spec.Bitcoin.stateWord, be4']

theorem stateBytes_inj {A B : State} (h : stateBytes A = stateBytes B) : A = B := by
  have w : ∀ t < 8, StarkedAir.Spec.Bitcoin.stateWord A t = StarkedAir.Spec.Bitcoin.stateWord B t := fun t ht => by
    rw [stateWord_bytes A ht, stateWord_bytes B ht, h]
  obtain ⟨a, b, c, d, e, f, g, hh⟩ := A
  obtain ⟨a', b', c', d', e', f', g', hh'⟩ := B
  have h0 := w 0 (by norm_num); have h1 := w 1 (by norm_num); have h2 := w 2 (by norm_num)
  have h3 := w 3 (by norm_num); have h4 := w 4 (by norm_num); have h5 := w 5 (by norm_num)
  have h6 := w 6 (by norm_num); have h7 := w 7 (by norm_num)
  simp only [StarkedAir.Spec.Bitcoin.stateWord] at h0 h1 h2 h3 h4 h5 h6 h7
  subst h0 h1 h2 h3 h4 h5 h6 h7; rfl

end StarkedAir.Block.HashSpec
