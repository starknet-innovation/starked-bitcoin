/-
Bitcoin block-header hashing, over 32-bit words.

A header is 80 bytes; `hw t` is its `t`-th 4-byte word read big-endian (t < 20), i.e. the
words SHA-256 consumes. The block hash is SHA256d of the header (FIPS 180-4 padding for 80
and then 32 bytes). Its 8 big-endian state words are the hash in Bitcoin's internal byte
order. The prev-hash field (bytes 4..35) is therefore header words 1..8.
-/
import BitcoinConsensus.Sha256

namespace BitcoinConsensus.Bitcoin

open BitcoinConsensus.Sha256

/-- First block: header words 0..15. -/
def block0 (hw : ℕ → Word) : ℕ → Word := hw

/-- Second block: header words 16..19, then padding for an 80-byte message. -/
def block1 (hw : ℕ → Word) (t : ℕ) : Word :=
  if t < 4 then hw (16 + t) else if t = 4 then 0x80000000#32 else if t = 15 then 640#32 else 0#32

def stateWord (s : State) (k : ℕ) : Word :=
  match k with
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d | 4 => s.e | 5 => s.f | 6 => s.g | _ => s.h

/-- A 32-byte digest followed by padding for a 32-byte message. -/
def digestBlock (H : State) (t : ℕ) : Word :=
  if t < 8 then stateWord H t else if t = 8 then 0x80000000#32 else if t = 15 then 256#32 else 0#32

/-- SHA256d of an 80-byte header. -/
def sha256d (hw : ℕ → Word) : State :=
  compress IV (digestBlock (compress (compress IV (block0 hw)) (block1 hw)))

/-- The prev-hash field as a state (8 words). -/
def prevHash (hw : ℕ → Word) : State :=
  ⟨hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7, hw 8⟩

/-- Mainnet genesis header, as 20 big-endian words. -/
def genesis : ℕ → Word := fun t => BitVec.ofNat 32 <| [
  0x01000000, 0, 0, 0, 0, 0, 0, 0, 0, 0x3ba3edfd, 0x7a7b12b2, 0x7ac72c3e, 0x67768f61, 0x7fc81bc3,
  0x888a5132, 0x3a9fb8aa, 0x4b1e5e4a, 0x29ab5f49, 0xffff001d, 0x1dac2b7c].getD t 0

-- Genesis block hash (internal byte order) as state words; displayed reversed it is
-- 000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f.
#guard sha256d genesis ==
  ⟨0x6fe28c0a#32, 0xb6f1b372#32, 0xc1a6a246#32, 0xae63f74f#32,
   0x931e8365#32, 0xe15a089c#32, 0x68d61900#32, 0x00000000#32⟩

/-! ## Proof of work (Bitcoin Core `CheckProofOfWork`) -/

/-- Byte `i` (0..31) of a digest in internal order: the big-endian bytes of `H0, …, H7`. -/
def hashByte (H : State) (i : ℕ) : ℕ := (stateWord H (i / 4)).toNat / 2 ^ (8 * (3 - i % 4)) % 256

/-- `UintToArith256(hash)`: the digest bytes read as a little-endian 256-bit integer. -/
def hashNat (H : State) : ℕ := ∑ i ∈ Finset.range 32, hashByte H i * 256 ^ i

/-- The header's `nBits` field: bytes 72..75 read little-endian, i.e. header word 18
byte-swapped. -/
def nBitsOf (hw : ℕ → Word) : ℕ :=
  let w := (hw 18).toNat
  (w / 2 ^ 24) % 256 + 256 * ((w / 2 ^ 16) % 256) + 65536 * ((w / 2 ^ 8) % 256) + 2 ^ 24 * (w % 256)

/-- `arith_uint256::SetCompact`, returning `none` when Bitcoin Core's `CheckProofOfWork`
rejects the encoding itself (negative, overflow, or zero target). -/
def compactTarget (n : ℕ) : Option ℕ :=
  let nSize := n / 2 ^ 24
  let nWord := n % 2 ^ 23
  let negative := nWord ≠ 0 ∧ (n / 2 ^ 23) % 2 = 1
  let overflow := nWord ≠ 0 ∧ (34 < nSize ∨ (0xff < nWord ∧ 33 < nSize) ∨ (0xffff < nWord ∧ 32 < nSize))
  let target := if nSize ≤ 3 then nWord / 256 ^ (3 - nSize) else nWord * 256 ^ (nSize - 3)
  if negative ∨ overflow ∨ target = 0 then none else some target

/-- Mainnet `powLimit` = 0x00000000ffff…ff. -/
def powLimit : ℕ := 2 ^ 224 - 1

/-- `CheckProofOfWork(hash, nBits, mainnet)`. -/
def powOk (H : State) (nBits : ℕ) : Prop :=
  ∃ t, compactTarget nBits = some t ∧ t ≤ powLimit ∧ hashNat H ≤ t

instance (H : State) (n : ℕ) : Decidable (powOk H n) := by
  unfold powOk
  cases h : compactTarget n with
  | none => exact isFalse (by simp)
  | some t => exact decidable_of_iff (t ≤ powLimit ∧ hashNat H ≤ t) (by simp)

#guard nBitsOf genesis == 0x1d00ffff
#guard compactTarget 0x1d00ffff == some (0xffff * 2 ^ 208)
#guard decide (powOk (sha256d genesis) (nBitsOf genesis))
-- A harder target than the genesis hash meets (hash ≈ 0x19d6…·2^184): rejected.
#guard !decide (powOk (sha256d genesis) 0x1800ffff)

/-! ## Difficulty retarget (Bitcoin Core `GetNextWorkRequired`, mainnet) -/

/-- `arith_uint256::SetCompact` value (ignoring the validity flags). -/
def compactValue (n : ℕ) : ℕ :=
  let nSize := n / 2 ^ 24
  let nWord := n % 2 ^ 23
  if nSize ≤ 3 then nWord / 256 ^ (3 - nSize) else nWord * 256 ^ (nSize - 3)

/-- `arith_uint256::GetCompact` for a non-negative value. -/
def getCompact (t : ℕ) : ℕ :=
  let size := (Nat.size t + 7) / 8
  let c := if size ≤ 3 then t * 256 ^ (3 - size) else t / 256 ^ (size - 3)
  if c % 2 ^ 24 / 2 ^ 23 = 1 then (c / 256) + 2 ^ 24 * (size + 1) else c + 2 ^ 24 * size

def targetTimespan : ℕ := 1209600

/-- `CalculateNextWorkRequired`: `prevTime` is the last block of the period and `pst` the
first (timestamps as integers; the span may be negative before clamping). -/
def nextWork (prevNBits : ℕ) (prevTime pst : ℤ) : ℕ :=
  let span : ℤ := max 302400 (min 4838400 (prevTime - pst))
  let t := compactValue prevNBits * span.toNat / targetTimespan
  getCompact (min t powLimit)

/-- Timestamp field (header bytes 68..71, little-endian) = header word 17 byte-swapped. -/
def timeOf (hw : ℕ → Word) : ℕ :=
  let w := (hw 17).toNat
  (w / 2 ^ 24) % 256 + 256 * ((w / 2 ^ 16) % 256) + 65536 * ((w / 2 ^ 8) % 256) + 2 ^ 24 * (w % 256)

-- First real retarget (height 32256): span = time(32255) − time(30240) = 1022578.
#guard nextWork 0x1d00ffff 1262152739 1261130161 == 0x1d00d86a
-- Height 2016: span far above 2 weeks · 4 is clamped, the result exceeds powLimit and is capped.
#guard nextWork 0x1d00ffff 1233061996 1231006505 == 0x1d00ffff
#guard getCompact (0xffff * 2 ^ 208) == 0x1d00ffff

/-! ## Minimum block version (Bitcoin Core `ContextualCheckBlockHeader`, "bad-version") -/

/-- `nVersion` as an unsigned 32-bit value: header bytes 0..3, little-endian. -/
def versionOf (hw : ℕ → Word) : ℕ :=
  let w := (hw 0).toNat
  (w / 2 ^ 24) % 256 + 256 * ((w / 2 ^ 16) % 256) + 65536 * ((w / 2 ^ 8) % 256) + 2 ^ 24 * (w % 256)

/-- `nVersion` is a signed `int32_t`. -/
def versionInt (v : ℕ) : ℤ := if v < 2 ^ 31 then v else (v : ℤ) - 2 ^ 32

/-- Mainnet buried deployments: BIP34 (227931), BIP66 (363725), BIP65 (388381). A block at
`height` must have `nVersion ≥ 2, 3, 4` respectively once each is active. -/
def versionOk (height v : ℕ) : Bool :=
  (decide (height < 227931) || decide (2 ≤ versionInt v)) &&
  (decide (height < 363725) || decide (3 ≤ versionInt v)) &&
  (decide (height < 388381) || decide (4 ≤ versionInt v))

#guard versionOk 0 1                    -- genesis
#guard !versionOk 227931 1              -- version 1 rejected once BIP34 is active
#guard versionOk 227930 1
#guard versionOk 363724 2 && !versionOk 363725 2
#guard versionOk 388381 4 && !versionOk 388381 3
#guard versionOk 700000 0x20000000     -- BIP9 version bits
#guard !versionOk 400000 0x80000000    -- negative as int32

/-! ## Chainwork (Bitcoin Core `GetBlockProof`, `nChainWork`) -/

/-- `GetBlockProof`: `(~target / (target + 1)) + 1` over 256-bit integers, or 0 for an invalid
encoding. `~target = 2^256 − 1 − target`. -/
def blockProof (nBits : ℕ) : ℕ :=
  match compactTarget nBits with
  | some t => (2 ^ 256 - 1 - t) / (t + 1) + 1
  | none => 0

/-- Core's formula is `⌊2^256 / (target + 1)⌋` for any 256-bit target. -/
theorem blockProof_eq {n t : ℕ} (h : compactTarget n = some t) (ht : t < 2 ^ 256) :
    blockProof n = 2 ^ 256 / (t + 1) := by
  unfold blockProof; rw [h]
  simp only
  rw [← Nat.add_div_right _ (by omega : 0 < t + 1)]
  congr 1; omega

-- Genesis: work 0x100010001 (Core's chainwork at height 0).
#guard blockProof 0x1d00ffff == 0x100010001
-- Height 32256's target 0x1d00d86a.
#guard blockProof 0x1d00d86a == 2 ^ 256 / (0xd86a * 256 ^ 26 + 1)

/-! ## Median time past (Bitcoin Core `GetMedianTimePast`, `ContextualCheckBlockHeader`)

Core rejects a header whose time is not strictly greater than the median of the timestamps of
its predecessor and that block's ancestors, at most 11 (`nMedianTimeSpan`): "time-too-old".
`prev` lists those timestamps newest first; near genesis it is shorter. Genesis has none.
The `#guard` on real data is mainnet height 101982, whose time is below two of its 11
predecessors' times. -/

/-- `GetMedianTimePast`: sort the (at most 11) timestamps and take index `k / 2`. -/
def medianTimePast (prev : List ℕ) : ℕ :=
  let l := prev.take 11
  (l.mergeSort (fun a b => decide (a ≤ b))).getD (l.length / 2) 0

/-- The header passes the median-time-past rule. -/
def mtpOk (time : ℕ) (prev : List ℕ) : Bool := prev.isEmpty || decide (medianTimePast prev < time)

#guard mtpOk 1294682031 [1294682118, 1294682046, 1294680974, 1294680362, 1294679671, 1294678793,
  1294676428, 1294676299, 1294675358, 1294675210, 1294674490]
#guard mtpOk 6 [1,2,3,4,5,6,7,8,9,10,11] = false
#guard mtpOk 7 [1,2,3,4,5,6,7,8,9,10,11] = true
#guard mtpOk 7 [11,10,9,8,7,6,5,4,3,2,1] = true
#guard mtpOk 6 [11,10,9,8,7,6,5,4,3,2,1] = false
#guard mtpOk 0 [] = true
#guard mtpOk 3 [2, 9] = false
#guard mtpOk 10 [2, 9] = true

end BitcoinConsensus.Bitcoin
