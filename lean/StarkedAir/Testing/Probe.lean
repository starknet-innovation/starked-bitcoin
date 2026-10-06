/-
Differential-test oracle for the IR semantics.

`probeAir` exercises offsets −3…+5 (with wrap-around), every `PreCol` kind,
and every operator. `oracleJson` evaluates it with `Expr.eval` (the
normative semantics) on a deterministic pseudo-random trace. The Zig
interpreter must reproduce every value (`src/air/interp.zig` test).
-/
import StarkedAir.Export

namespace StarkedAir.Probe

open StarkedAir

def c (i : ℕ) (off : ℤ) : Expr := .col .main i off
def p (i : ℕ) : Expr := .col .pre i 0

def probeAir : Air where
  name := "probe"
  nMain := 3
  pre := [.isFirst, .notLast, .periodic [7, 0, 2147483646, 5, 1], .rowLt 5, .rowGeEnd 3]
  constraints := [
    .sub (c 0 1) (c 1 (-1)),
    .mul (c 2 (-3)) (.add (c 0 5) (.const 3)),
    .neg (.mul (p 0) (c 1 0)),
    .add (.mul (p 1) (c 2 2)) (.mul (p 2) (.sub (c 0 0) (.const 2147483646))),
    .mul (.mul (c 0 (-1)) (c 0 (-1))) (c 1 4),
    .add (.mul (p 3) (.pub 0)) (.mul (p 4) (.sub (c 2 1) (.pub 1)))]

def probePub : List ℕ := [123456789, 2147483000]

/-- Deterministic LCG; values reduced into `[0, P)`. -/
def lcg (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def traceValues (nCols n : ℕ) (seed : ℕ) : List (List ℕ) := Id.run do
  let mut s := seed
  let mut cols : List (List ℕ) := []
  for _ in [0:nCols] do
    let mut col : List ℕ := []
    for _ in [0:n] do
      s := lcg s
      col := col ++ [(s / 2 ^ 32) % P]
    cols := cols ++ [col]
  return cols

def oracleJson (logSize seed : ℕ) : String :=
  let n := 2 ^ logSize
  let cols := traceValues probeAir.nMain n seed
  let main : ℕ → ℕ → F := fun i r => ((cols.getD i []).getD r 0 : F)
  let pub : ℕ → F := fun i => (probePub.getD i 0 : F)
  let evals := (List.range n).map fun r =>
    probeAir.constraints.map fun e => (e.eval n probeAir.pre pub main r).val
  let showList (xs : List ℕ) := "[" ++ ",".intercalate (xs.map toString) ++ "]"
  "{\"log_size\":" ++ toString logSize ++
    ",\"air\":" ++ probeAir.toJson ++
    ",\"pub\":" ++ showList probePub ++
    ",\"main\":[" ++ ",".intercalate (cols.map showList) ++ "]" ++
    ",\"evals\":[" ++ ",".intercalate (evals.map showList) ++ "]}"

end StarkedAir.Probe
