/-
**Streaming SHA-256, block by block (the segment system's SHA side).** `shaFeed` compresses the whole
64-byte blocks of `pend ++ x` and keeps the rest: with `m = |pend ++ x| / 64`, the chaining value is
`wfold` over the blocks' big-endian words (`shaFeed_eq`). `chunkWords_half`: a block word's 16-bit
halves are its bytes, two by two.
-/
import StarkedAir.Spec.SetFile
import StarkedAir.Gadgets.HeaderChainSound

namespace StarkedAir.SetPass

open StarkedAir.Spec.Sha256 StarkedAir.Spec.Block StarkedAir.Spec.SetFile

/-- Compressions of blocks `0 … k − 1` with words `wd b`. -/
def wfold (H : State) (wd : ℕ → ℕ → Word) : ℕ → State
  | 0 => H
  | b + 1 => compress (wfold H wd b) (wd b)

/-- The big-endian words of block `b` of a byte string. -/
def blockWords (m : Bytes) (b : ℕ) : ℕ → Word := chunkWords ((m.drop (64 * b)).take 64)

theorem wfold_cons (H : State) (m : Bytes) :
    ∀ k, wfold H (blockWords m) (k + 1) = wfold (compress H (blockWords m 0)) (blockWords (m.drop 64)) k
  | 0 => rfl
  | k + 1 => by
    have e : (m.drop 64).drop (64 * k) = m.drop (64 * (k + 1)) := by
      rw [List.drop_drop]; congr 1; ring
    show compress (wfold H (blockWords m) (k + 1)) (blockWords m (k + 1)) =
      compress (wfold (compress H (blockWords m 0)) (blockWords (m.drop 64)) k) (blockWords (m.drop 64) k)
    rw [wfold_cons H m k]
    unfold blockWords; rw [e]

theorem shaAbsorb_blocks (H : State) (b : Bytes) :
    shaAbsorb H b = (wfold H (blockWords b) (b.length / 64), b.drop (64 * (b.length / 64))) := by
  induction H, b using shaAbsorb.induct with
  | case1 H b hb ih =>
    rw [shaAbsorb_pos hb, ih, List.length_drop, show b.length / 64 = (b.length - 64) / 64 + 1 by omega,
      wfold_cons, List.drop_drop]
    simp only [blockWords, Nat.mul_zero, List.drop_zero]
    congr 2; ring
  | case2 H b hb =>
    rw [shaAbsorb_neg hb, show b.length / 64 = 0 by omega]
    simp [wfold]

/-- **`shaFeed` block by block.** -/
theorem shaFeed_eq (s : Sha) (x : Bytes) :
    shaFeed s x = ⟨wfold s.H (blockWords (s.pend ++ x)) ((s.pend ++ x).length / 64),
      (s.pend ++ x).drop (64 * ((s.pend ++ x).length / 64)), s.len + x.length⟩ := by
  simp only [shaFeed, shaAbsorb_blocks]

/-- A block word's halves: the low half is bytes `4t + 2`, `4t + 3`, the high half bytes `4t`, `4t + 1`. -/
theorem chunkWords_half (c : Bytes) (t : ℕ) :
    Sha256.half16 (chunkWords c t) 0 = 256 * (c.getD (4 * t + 2) 0).toNat + (c.getD (4 * t + 3) 0).toNat ∧
    Sha256.half16 (chunkWords c t) 1 = 256 * (c.getD (4 * t) 0).toNat + (c.getD (4 * t + 1) 0).toNat := by
  have e : ∀ i, c.toArray.getD i 0 = c.getD i 0 := fun i => by
    by_cases h : i < c.length <;> simp [Array.getD, List.getD_eq_getElem?_getD, h]
  have b0 := UInt8.toNat_lt (c.getD (4 * t) 0)
  have b1 := UInt8.toNat_lt (c.getD (4 * t + 1) 0)
  have b2 := UInt8.toNat_lt (c.getD (4 * t + 2) 0)
  have b3 := UInt8.toNat_lt (c.getD (4 * t + 3) 0)
  simp only [chunkWords, e, Sha256.half16, BitVec.toNat_ofNat]
  constructor <;> omega

end StarkedAir.SetPass
