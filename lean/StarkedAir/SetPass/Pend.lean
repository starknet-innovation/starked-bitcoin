/-
**Pending bytes (`set_pend`).** The four 64-byte pending tables of the carried hash states, read from
public inputs: Blake2s in and out, SHA-256 in and out. Row `r` yields `(r mod 64, byte)` per table with
a free multiplicity; the byte is `Σₖ [r mod 64 = k] · pub(base + k)`, so a yielded tuple is always the
public byte at its index. No constraints.
-/
import StarkedAir.SetPass.Layout

namespace StarkedAir.SetPass.Pend

open StarkedAir
open StarkedAir.Sha256 (col pre cst)

def per64 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 64).map f)

/-- Preprocessed: the index, then the 64 one-hot selectors. -/
def preCols : List PreCol := per64 id :: (List.range 64).map fun k => per64 fun r => if r = k then 1 else 0
def P_J : ℕ := 0
def P_S (k : ℕ) : ℕ := 1 + k

/-- The public byte at the row's index, of the table at `base`. -/
def pubByte (base : ℕ) : Expr :=
  (List.range 64).foldl (fun acc k => .add acc (.mul (pre (P_S k)) (.pub (H_PEND base k)))) (cst 0)

def tables : List (ℕ × ℕ) := [(REL_PB2I, B2_IN), (REL_PB2O, B2_OUT), (REL_PSHI, SHA_IN), (REL_PSHO, SHA_OUT)]

def lookups : List Lookup := tables.zipIdx.map fun ⟨⟨rel, base⟩, i⟩ => ⟨rel, col i, [pre P_J, pubByte base]⟩

def pend : Comp where
  air := { name := "set_pend", nMain := 4, pre := preCols, constraints := [] }
  lookups := lookups

#guard lookups.all (fun l => Block.Fields.degE l.mult ≤ 2 && l.vals.all (fun v => Block.Fields.degE v ≤ 1))

end StarkedAir.SetPass.Pend
