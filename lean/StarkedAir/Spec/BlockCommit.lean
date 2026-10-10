/-
**The block commitment (M3a.6, D-038).** `C = blake2s(blake2s(raw) ++ blake2s(undo))`, where `raw` is the
block's bytes and `undo` the spent-output records (one per input after the coinbase: Core's `TxOutSer`
without the outpoint). M3a commits to `undo` without checking it (D-029).
-/
import StarkedAir.Spec.Blake2s
import StarkedAir.Spec.Block

namespace StarkedAir.Spec.Block

open StarkedAir.Spec.Blake2s (blake2s)

/-- An undo record: Core's `TxOutSer` without the outpoint. -/
def undoRecord (height : ℕ) (coinbase : Bool) (o : TxOut) : Bytes :=
  leBytes 4 (2 * height + (if coinbase then 1 else 0)) ++ leBytes 8 (o.value % 2 ^ 64).toNat ++ serVarBytes o.scriptPubKey

/-- The undo stream: a version byte `0x01`, then the records. -/
def undoStream (records : Bytes) : Bytes := 1 :: records

def blockCommit (raw undo : Bytes) : Bytes := blake2s (blake2s raw ++ blake2s undo)

#guard (blockCommit [] (undoStream [])).length = 32

end StarkedAir.Spec.Block
