/-
**Test reader for block bytes (M3a.1).** One row per read: `(pos, byte)` and a boolean `USE`; it
looks up `byte(pos, byte)` with multiplicity `−USE`. With `Block.bytes` as component 0, `read_byte`
gives: every used row reads the block's byte at `pos < LEN`. Exported as `block_reader`.
-/
import StarkedAir.Block.Bytes

namespace StarkedAir.BlockReader

open StarkedAir
open StarkedAir.Sha256 (col boolC)

def reader : Comp where
  air := { name := "block_reader", nMain := 3, pre := [], constraints := [boolC (col 2)] }
  lookups := [⟨Block.REL_BYTE, .neg (col 2), [col 0, col 1]⟩]

end StarkedAir.BlockReader
