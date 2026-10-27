/-
**The coin set's Merkle commitment (D-050): spec.** A record's leaf is `Blake2s-256(key(previous) ‖
encRec(record))`: the previous record's key (its txid's bytes, then `vout` big-endian; 36 zero bytes before
the set's first record), then the record's file bytes. So a leaf proves its record is in the set, and two
consecutive keys bracket every absent key.

A segment's records fill the slots of a heap tree over `2·half` slots (slot `s` is record `s`'s leaf, or the
zero state past the last record): node `j < half` is `hnode` of nodes `2j` and `2j + 1`, node `half ≤ j`
is `hnode` of slots `2(j − half)` and `2(j − half) + 1`. The segment's root is node 1. The set's root folds
its segments' roots with `hnode` in the set tree's shape (`SetTree.SegTree.root`).
-/
import StarkedAir.Spec.SetFile
import StarkedAir.Spec.HeaderTree

namespace StarkedAir.Spec.SetMerkle

open StarkedAir.Spec.SetFile
open StarkedAir.Spec.CoinEpoch (CEv)
open StarkedAir.Spec.Block (Bytes)
open StarkedAir.Spec.HeaderTree (hnode toState)
open StarkedAir.Spec.Sha256 (State)

/-- A record's key: its txid's bytes, then `vout` big-endian (the set's order, `keyLt`). -/
def key (e : CEv) : Bytes := txid e ++ Block.beBytes 4 (vout e)

/-- The key before a record: the previous record's, or 36 zero bytes before the set's first. -/
def prevKey : Option CEv → Bytes
  | none => List.replicate 36 0
  | some p => key p

/-- A leaf message's Blake2s-256, as a state (the eight little-endian digest words). -/
def leafHash (msg : Bytes) : State := toState (Blake2s.hashBlocks Blake2s.h0 0 msg)

/-- The leaves of records `es` following `last`. -/
def leaves : Option CEv → List CEv → List State
  | _, [] => []
  | last, e :: es => leafHash (prevKey last ++ encRec e) :: leaves (some e) es

/-- The zero state: an empty slot. -/
def zero : State := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Slot `s`: leaf `s`, or the zero state. -/
def slot (ls : List State) (s : ℕ) : State := ls.getD s zero

/-- Heap node `j` over `2·half` slots. -/
def node (half : ℕ) (ls : List State) (j : ℕ) : State :=
  if h : 1 ≤ j ∧ j < half then hnode (node half ls (2 * j)) (node half ls (2 * j + 1))
  else hnode (slot ls (2 * (j - half))) (slot ls (2 * (j - half) + 1))
termination_by 2 * half - j

/-- A segment's root: node 1 over its records' leaves (following `last`). -/
def segRoot (half : ℕ) (last : Option CEv) (seg : List CEv) : State := node half (leaves last seg) 1

theorem leaves_length : ∀ (last : Option CEv) (es : List CEv), (leaves last es).length = es.length
  | _, [] => rfl
  | _, _ :: es => by simp [leaves, leaves_length _ es]

end StarkedAir.Spec.SetMerkle
