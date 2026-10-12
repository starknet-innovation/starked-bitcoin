/-
SHA-256 compression function, FIPS 180-4 (§4.1.2, §4.2.2, §6.2.2), over
`BitVec 32`. This is the normative specification the AIR is proven against.
-/
import Mathlib

namespace BitcoinConsensus.Sha256

abbrev Word := BitVec 32

/-- FIPS 180-4 §4.2.2. -/
def Kn : List ℕ := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def K (t : ℕ) : Word := BitVec.ofNat 32 (Kn.getD t 0)

def ch (x y z : Word) : Word := (x &&& y) ^^^ (~~~x &&& z)
def maj (x y z : Word) : Word := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)
def bsig0 (x : Word) : Word := x.rotateRight 2 ^^^ x.rotateRight 13 ^^^ x.rotateRight 22
def bsig1 (x : Word) : Word := x.rotateRight 6 ^^^ x.rotateRight 11 ^^^ x.rotateRight 25
def ssig0 (x : Word) : Word := x.rotateRight 7 ^^^ x.rotateRight 18 ^^^ (x >>> 3)
def ssig1 (x : Word) : Word := x.rotateRight 17 ^^^ x.rotateRight 19 ^^^ (x >>> 10)

/-- Message schedule (§6.2.2 step 1); `M t` for `t < 16` are the block words. -/
def schedule (M : ℕ → Word) (t : ℕ) : Word :=
  if h : t < 16 then M t
  else ssig1 (schedule M (t - 2)) + schedule M (t - 7) + ssig0 (schedule M (t - 15)) +
    schedule M (t - 16)
termination_by t
decreasing_by all_goals omega

structure State where
  a : Word
  b : Word
  c : Word
  d : Word
  e : Word
  f : Word
  g : Word
  h : Word
  deriving DecidableEq, Repr

/-- One round (§6.2.2 step 3). -/
def round (s : State) (k w : Word) : State :=
  let t1 := s.h + bsig1 s.e + ch s.e s.f s.g + k + w
  let t2 := bsig0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- Working variables after `t` rounds. -/
def rounds (H : State) (M : ℕ → Word) : ℕ → State
  | 0 => H
  | t + 1 => round (rounds H M t) (K t) (schedule M t)

/-- Intermediate hash value after processing one block (§6.2.2 step 4). -/
def compress (H : State) (M : ℕ → Word) : State :=
  let s := rounds H M 64
  ⟨H.a + s.a, H.b + s.b, H.c + s.c, H.d + s.d, H.e + s.e, H.f + s.f, H.g + s.g, H.h + s.h⟩

def IV : State :=
  ⟨0x6a09e667#32, 0xbb67ae85#32, 0x3c6ef372#32, 0xa54ff53a#32,
   0x510e527f#32, 0x9b05688c#32, 0x1f83d9ab#32, 0x5be0cd19#32⟩

/-- FIPS 180-4 example "abc" (one padded block): sanity check of the spec itself. -/
def abcBlock : ℕ → Word := fun t =>
  if t = 0 then 0x61626380#32 else if t = 15 then 0x18#32 else 0#32

#guard compress IV abcBlock ==
  ⟨0xba7816bf#32, 0x8f01cfea#32, 0x414140de#32, 0x5dae2223#32,
   0xb00361a3#32, 0x96177a9c#32, 0xb410ff61#32, 0xf20015ad#32⟩

end BitcoinConsensus.Sha256
