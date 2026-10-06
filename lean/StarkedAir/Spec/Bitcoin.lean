/-
Bitcoin block-header hashing, over 32-bit words.

A header is 80 bytes; `hw t` is its `t`-th 4-byte word read big-endian (t < 20), i.e. the
words SHA-256 consumes. The block hash is SHA256d of the header (FIPS 180-4 padding for 80
and then 32 bytes). Its 8 big-endian state words are the hash in Bitcoin's internal byte
order. The prev-hash field (bytes 4..35) is therefore header words 1..8.
-/
import StarkedAir.Spec.Sha256

namespace StarkedAir.Spec.Bitcoin

open StarkedAir.Spec.Sha256

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

end StarkedAir.Spec.Bitcoin
