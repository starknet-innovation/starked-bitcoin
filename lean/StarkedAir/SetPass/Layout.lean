/-
**The coin-set pass segment system: public inputs and relations (step 3, docs/design/set-pass.md).**
A segment proves `s' = seg.foldl step s` (`Spec/SetFile.lean`) for the records `seg` of its bytes; the
incoming and outgoing states are public. The layout keeps the reused components' inputs where they
read them: the segment length at 0 (`block_bytes`), `γ` at 41 (`block_fpwalk`), the coin challenge's
`z` at 45 and `α` at 49–152 (as `block_coin`).

A hash state block (Blake2s or SHA-256) is 82 inputs from its base: the chaining value's 16 limbs
(word `w` low limb first), the compressed block count `nb`, the pending length, 64 pending bytes.
-/
import StarkedAir.Block.Coin

namespace StarkedAir.SetPass

def PUB_LEN : ℕ := 0
def PUB_I_IN : ℕ := 1
def PUB_I_OUT : ℕ := 2
def PUB_HASLAST : ℕ := 3
/-- The incoming last key: txid bytes, then `vout` big-endian (36 bytes). -/
def PUB_LAST_IN (j : ℕ) : ℕ := 4 + j
def PUB_MAXH_IN : ℕ := 40
def PUB_G : ℕ := 41
def PUB_Z : ℕ := 45
def PUB_ALPHA (j : ℕ) : ℕ := 49 + 4 * j
def PUB_SUM_IN : ℕ := 153
def PUB_SUM_OUT : ℕ := 157
def PUB_MAXH_OUT : ℕ := 161
def PUB_AMT_IN (j : ℕ) : ℕ := 162 + j
def PUB_AMT_OUT (j : ℕ) : ℕ := 174 + j
def PUB_LAST_OUT (j : ℕ) : ℕ := 186 + j
def B2_IN : ℕ := 222
def B2_OUT : ℕ := 304
def SHA_IN : ℕ := 386
def SHA_OUT : ℕ := 468
/-- Within a hash state block. -/
def H_LIMB (base i : ℕ) : ℕ := base + i
def H_NB (base : ℕ) : ℕ := base + 16
def H_PLEN (base : ℕ) : ℕ := base + 17
def H_PEND (base j : ℕ) : ℕ := base + 18 + j
/-- The segment's Merkle root over its records (16 limbs, D-050) and the tree's half width `HALF`. -/
def PUB_ROOT (i : ℕ) : ℕ := 550 + i
def PUB_HALF : ℕ := 566
def N_PUB : ℕ := 567

#guard PUB_G = Block.FpWalk.PUB_G
#guard PUB_Z = Block.Coin.PUB_Z
#guard (List.range 26).all fun j => PUB_ALPHA j = Block.Coin.PUB_ALPHA j
#guard H_PEND SHA_OUT 63 + 1 = PUB_ROOT 0
#guard PUB_HALF + 1 = N_PUB

/-- Relations (the reused ones keep theirs: byte 3, r8 9, seg 21, fp 22). -/
def REL_PB2I : ℕ := 26
def REL_PB2O : ℕ := 27
def REL_PSHI : ℕ := 28
def REL_PSHO : ℕ := 29
def REL_SB2W : ℕ := 30
/-- The hashes' end tokens: the compression component yields one at its last block, the walker consumes it. -/
def REL_B2END : ℕ := 31
def REL_REC : ℕ := 32
def REL_CODE : ℕ := 33
def REL_SW : ℕ := 34
def REL_SHEND : ℕ := 35
/-- The Merkle root (D-050): a record's previous key as words; leaf-message words and blocks; leaf and
node digests (as `(id, word, lo, hi)`). -/
def REL_PKEY : ℕ := 36
def REL_LW : ℕ := 37
def REL_LB : ℕ := 38
def REL_LEAF : ℕ := 39
def REL_NODE : ℕ := 40

end StarkedAir.SetPass
