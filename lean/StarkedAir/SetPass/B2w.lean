/-
**Blake2s message words (`set_b2w`).** The stream `P_in ‖ S`: the incoming pending bytes (public), then
the segment's bytes (the byte table), as little-endian words, one row per word, 16 rows per block
(`block_b2msg`'s layout). With `m = nb_out − nb_in`:

* blocks `0 … m` are on, `m ≥ 1`; blocks below `m` are full and yield their words `w(block, k, lo, hi)`;
  block `m` is held back (`HELD`): its active bytes are the outgoing pending bytes (the `pb2o` table)
  and there are `plen_out ≥ 1` of them;
* byte `x` of the stream is active iff `x < plen_in + len` (`64·m + plen_out = plen_in + len`): it is
  pending byte `x` when `x < plen_in` (block 0 only, `plen_in` of them), else segment byte
  `x − plen_in`; inactive bytes are zero.
-/
import StarkedAir.SetPass.Layout

namespace StarkedAir.SetPass.B2w

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)

def ON : ℕ := 0
def BLK : ℕ := 1
def POS : ℕ := 2
def B (j : ℕ) : ℕ := 3 + j
def A (j : ℕ) : ℕ := 7 + j
def N (j : ℕ) : ℕ := 11 + j
def HELD : ℕ := 15
/-- Active bytes so far in the block. -/
def CNT : ℕ := 16
/-- Pending bytes so far in the block. -/
def PCNT : ℕ := 17
/-- The inverse of `BLK − m` off the held block. -/
def HINV : ℕ := 18
/-- `notFirst · ON`. -/
def SM : ℕ := 19
/-- The stream's last row: on, the next off. -/
def END : ℕ := 20
/-- `ON · (1 − HELD)`: the row yields its word. -/
def UW : ℕ := 21
def N_MAIN : ℕ := 22

def per16 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 16).map f)
def preCols : List PreCol :=
  [.isFirst, .notLast, per16 id, per16 (fun k => if k = 0 then 1 else 0), per16 (fun k => if k = 15 then 1 else 0),
   .rowLt 16, .rowLt 15]
def P_FIRST : ℕ := 0
def P_NOTLAST : ℕ := 1
def P_K : ℕ := 2
def P_K0 : ℕ := 3
def P_K15 : ℕ := 4
def P_LT16 : ℕ := 5
def P_LT15 : ℕ := 6

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := p P_FIRST
def notFirst : Expr := om first
def isLast : Expr := om (p P_NOTLAST)
/-- Row 15 (block 0's last row). -/
def row15 : Expr := .sub (p P_LT16) (p P_LT15)

def plenIn : Expr := .pub (H_PLEN B2_IN)
def plenOut : Expr := .pub (H_PLEN B2_OUT)
/-- Blocks compressed in the segment. -/
def m : Expr := .sub (.pub (H_NB B2_OUT)) (.pub (H_NB B2_IN))
def sum4 (f : ℕ → ℕ) : Expr := .add (.add (k (f 0)) (k (f 1))) (.add (k (f 2)) (k (f 3)))

def boolCols : List ℕ := [ON, HELD] ++ (List.range 4).map A ++ (List.range 4).map N

def constraints : List Expr :=
  boolCols.map (fun c => boolC (k c)) ++
  [ -- on rows: a prefix from row 0, block 0 first; the last row is off
    .mul first (om (k ON)), .mul first (k BLK), .mul isLast (k ON),
    .mul notFirst (.mul (k ON) (om (kp ON))),
    .sub (k SM) (.mul notFirst (k ON)),
    .mul (p P_K0) (.sub (k BLK) (.mul (k SM) (.add (kp BLK) one))),
    .mul (om (p P_K0)) (.sub (k BLK) (kp BLK)),
    .sub (k POS) (.add (.mul (cst 64) (k BLK)) (.mul (cst 4) (p P_K))),
    -- the held block is block m (block 0 is not); the stream ends at its last row
    .mul (k HELD) (.sub (k BLK) m),
    .sub (.mul (.sub (k BLK) m) (k HINV)) (om (k HELD)),
    .mul first (k HELD),
    .sub (k END) (.mul (k ON) (om (kn ON))),
    .mul (k END) (om (k HELD)), .mul (k END) (om (p P_K15)),
    .mul (k HELD) (.mul (p P_K15) (kn ON)),
    .sub (k UW) (.mul (k ON) (om (k HELD))),
    -- active bytes: full blocks below m; in the held block a nonempty prefix, counted
    .mul (om (p P_K0)) (.mul (k (A 0)) (om (kp (A 3)))),
    .mul (k HELD) (.mul (p P_K0) (om (k (A 0)))),
    .sub (k CNT) (.add (.mul (om (p P_K0)) (kp CNT)) (sum4 A)),
    .mul (k END) (.sub (k CNT) plenOut),
    .mul first (.sub (.add plenOut (.mul (cst 64) m)) (.add plenIn (.pub PUB_LEN))),
    -- pending bytes: a prefix of block 0, plen_in of them
    .mul (om (p P_K0)) (.mul (k (N 0)) (om (kp (N 3)))),
    .sub (k PCNT) (.add (.mul (om (p P_K0)) (kp PCNT)) (sum4 N)),
    .mul row15 (.sub (k PCNT) plenIn) ] ++
  (List.range 4).map (fun j => .mul (k UW) (om (k (A j)))) ++
  (List.range 4).map (fun j => .mul (k (A j)) (om (k ON))) ++
  (List.range 4).map (fun j => .mul (k (B j)) (om (k (A j)))) ++
  (List.range 3).map (fun j => .mul (k (A (j + 1))) (om (k (A j)))) ++
  (List.range 4).map (fun j => .mul (k (N j)) (k BLK)) ++
  (List.range 4).map (fun j => .mul (k (N j)) (om (k (A j)))) ++
  (List.range 3).map (fun j => .mul (k (N (j + 1))) (om (k (N j))))

def lo : Expr := .add (k (B 0)) (.mul (cst 256) (k (B 1)))
def hi : Expr := .add (k (B 2)) (.mul (cst 256) (k (B 3)))

def lookups : List Lookup :=
  (List.range 4).map (fun j => ⟨REL_PB2I, .neg (k (N j)), [.add (k POS) (cst j), k (B j)]⟩) ++
  (List.range 4).map (fun j => ⟨Block.REL_BYTE, .neg (.sub (k (A j)) (k (N j))), [.sub (.add (k POS) (cst j)) plenIn, k (B j)]⟩) ++
  (List.range 4).map (fun j => ⟨REL_PB2O, .neg (.mul (k HELD) (k (A j))), [.add (.mul (cst 4) (p P_K)) (cst j), k (B j)]⟩) ++
  [ ⟨REL_SB2W, k UW, [k BLK, p P_K, lo, hi]⟩ ]

def b2w : Comp where
  air := { name := "set_b2w", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.B2w
