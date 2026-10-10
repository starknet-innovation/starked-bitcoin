/-
**Fixed tables (M3a.5, D-035).** One component yields two read-only tables from periodic preprocessed
columns, so it works at any log size `≥ 8`:

* `r8(x)` for `x < 256`: the range table. A value is in `[0, 2^{8k})` when it is a sum of `k` table
  entries times powers of 256. (D-035 planned a 16-bit table; all block components share one trace
  size, and a `2^16`-row table would force every block to `2^16` rows, so this uses bytes.)
* `opc(b, push_n, k1, k2, k4, sig, nzp)` for each byte `b`: the direct push length (`b` when
  `b < 0x4c`); one-hot flags for `PUSHDATA1/2/4` (1, 2 or 4 length bytes); the sigop weight (`sigW`);
  and whether `b` is a non-empty direct push (`1 ≤ b < 0x4c`).

Every row carries value `r mod 256`; the prover puts each value's multiplicity on one row and zero on
the others. There are no constraints: a yielded tuple is always a table row.
-/
import StarkedAir.Block.Bytes

namespace StarkedAir.Block.Tables

open StarkedAir
open StarkedAir.Sha256 (col pre cst)

def REL_R8 : ℕ := 9
def REL_OPC : ℕ := 10

def pushN (b : ℕ) : ℕ := if b < 0x4c then b else 0
def isK (v b : ℕ) : ℕ := if b = v then 1 else 0
def nzp (b : ℕ) : ℕ := if 1 ≤ b ∧ b < 0x4c then 1 else 0
def sigN (b : ℕ) : ℕ := if b = 0xac ∨ b = 0xad then 1 else if b = 0xae ∨ b = 0xaf then 20 else 0

def tab (g : ℕ → ℕ) : PreCol := .periodic ((List.range 256).map g)

/-- Preprocessed (period 256): the value and the opcode table's columns. -/
def preCols : List PreCol :=
  [tab id, tab pushN, tab (isK 0x4c), tab (isK 0x4d), tab (isK 0x4e), tab sigN, tab nzp]

def M8 : ℕ := 0
def MO : ℕ := 1

def tables : Comp where
  air := { name := "block_tables", nMain := 2, pre := preCols, constraints := [] }
  lookups :=
    [ ⟨REL_R8, col M8, [pre 0]⟩,
      ⟨REL_OPC, col MO, (List.range 7).map pre⟩ ]

end StarkedAir.Block.Tables
