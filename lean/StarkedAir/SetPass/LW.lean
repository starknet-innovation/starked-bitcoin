/-
**Merkle leaf messages as Blake2s words (`set_lw`, D-050).** Each record `r`'s leaf message is
`key(r − 1) ‖ encRec(r)`: the previous key's 36 bytes, then the record's `49 + len` file bytes; `M = 85 +
len` bytes. One row per 32-bit little-endian word, 16 rows per 64-byte block (`block_b2msg`'s layout),
records one after another from row 0.

* A record starts at a block's row 0 (`NEWR`), right after the previous record's end (`ENDR`: its last
  block's last row), and reads its start and length from `set_rec` (`rec(r, start, len)`). Records count
  from 0; blocks count from 0 within a record.
* Byte `x` of the message is active iff `x < M` (monotone, counted, the count `M` at the end; every
  block but the first starts active); inactive bytes are zero.
* Words 0–8 of block 0 are the previous key's (`pkey(r, w, lo, hi)`); the other active bytes are file
  bytes `start + x − 36`.
* Each row yields `lw(r, block, k, lo, hi)`; each block's row 0 yields `lb(r, block, last, t)`, with `t`
  the counter after the block: `64·(block + 1)`, or `M` for the last block.
-/
import StarkedAir.SetPass.Layout

namespace StarkedAir.SetPass.LW

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)

def ON : ℕ := 0
def RI : ℕ := 1
def BLK : ℕ := 2
def B (j : ℕ) : ℕ := 3 + j
def A (j : ℕ) : ℕ := 7 + j
def CNT : ℕ := 11
def LASTF : ℕ := 12
def T : ℕ := 13
/-- `notFirst · ON · (1 − NEWR)`: the row continues the previous row's record. -/
def SM : ℕ := 14
/-- The record's last row: `K15 · LASTF`. -/
def ENDR : ℕ := 15
def NEWR : ℕ := 16
def START : ℕ := 17
def M : ℕ := 18
/-- The row is in the record's block 0. -/
def F0 : ℕ := 19
/-- `F0 · LT9`: the row's word is the previous key's. -/
def PKU : ℕ := 20
def N_MAIN : ℕ := 21

def per16 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 16).map f)
def preCols : List PreCol :=
  [.isFirst, .notLast, per16 id, per16 (fun k => if k = 0 then 1 else 0), per16 (fun k => if k = 15 then 1 else 0),
   per16 (fun k => if k < 9 then 1 else 0)]
def P_FIRST : ℕ := 0
def P_NOTLAST : ℕ := 1
def P_K : ℕ := 2
def P_K0 : ℕ := 3
def P_K15 : ℕ := 4
def P_LT9 : ℕ := 5

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := p P_FIRST
def notFirst : Expr := om first
def isLast : Expr := om (p P_NOTLAST)
def sumA : Expr := .add (.add (k (A 0)) (k (A 1))) (.add (k (A 2)) (k (A 3)))

def boolCols : List ℕ := [ON, LASTF, NEWR, F0, PKU, A 0, A 1, A 2, A 3]

def constraints : List Expr :=
  boolCols.map (fun c => boolC (k c)) ++
  [ -- on rows: a prefix from row 0, the last row off; a record starts at row 0 and after each record's end
    .mul first (om (k ON)), .mul isLast (k ON), .mul notFirst (.mul (k ON) (om (kp ON))),
    .mul first (om (k NEWR)), .mul (k NEWR) (om (p P_K0)), .mul (k NEWR) (om (k ON)),
    .mul notFirst (.mul (k ON) (.sub (k NEWR) (kp ENDR))),
    .sub (k SM) (.mul notFirst (.mul (k ON) (om (k NEWR)))),
    .sub (k ENDR) (.mul (p P_K15) (k LASTF)),
    .mul (k LASTF) (om (k ON)),
    .mul (k ON) (.mul (om (kn ON)) (om (k ENDR))),
    -- the record index, start and length; blocks within a record
    .mul first (k RI), .mul notFirst (.mul (k NEWR) (.sub (.sub (k RI) (kp RI)) one)),
    .mul (k SM) (.sub (k RI) (kp RI)), .mul (k SM) (.sub (k START) (kp START)), .mul (k SM) (.sub (k M) (kp M)),
    .mul (k NEWR) (k BLK),
    .mul (p P_K0) (.mul (k SM) (.sub (.sub (k BLK) (kp BLK)) one)),
    .mul (om (p P_K0)) (.mul (k SM) (.sub (k BLK) (kp BLK))),
    .sub (k F0) (.add (.mul (p P_K0) (k NEWR)) (.mul (om (p P_K0)) (kp F0))),
    .sub (k PKU) (.mul (k F0) (p P_LT9)),
    -- active bytes: counted from the record's start, monotone, every block starts active
    .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA),
    .mul (k SM) (.mul (k (A 0)) (om (kp (A 3)))),
    .mul (k ON) (.mul (p P_K0) (om (k (A 0)))),
    .mul (om (p P_K0)) (.mul (k SM) (.sub (k LASTF) (kp LASTF))),
    .mul (k ENDR) (.sub (k CNT) (k M)),
    -- the counter after the block
    .sub (k T) (.add (.mul (k LASTF) (k M)) (.mul (om (k LASTF)) (.add (.mul (cst 64) (k BLK)) (cst 64)))) ] ++
  (List.range 4).map (fun j => .mul (k (B j)) (om (k (A j)))) ++
  (List.range 4).map (fun j => .mul (k (A j)) (om (k ON))) ++
  (List.range 3).map (fun j => .mul (k (A (j + 1))) (om (k (A j))))

def lo : Expr := .add (k (B 0)) (.mul (cst 256) (k (B 1)))
def hi : Expr := .add (k (B 2)) (.mul (cst 256) (k (B 3)))

/-- The file position of byte `j` of the row (message byte `64·BLK + 4k + j`, after the 36 key bytes). -/
def filePos (j : ℕ) : Expr :=
  .sub (.add (.add (k START) (.mul (cst 64) (k BLK))) (.add (.mul (cst 4) (p P_K)) (cst j))) (cst 36)

def lookups : List Lookup :=
  [ ⟨REL_PKEY, .neg (k PKU), [k RI, p P_K, lo, hi]⟩,
    ⟨REL_REC, .neg (k NEWR), [k RI, k START, .sub (k M) (cst 85)]⟩ ] ++
  (List.range 4).map (fun j => ⟨Block.REL_BYTE, .neg (.mul (k (A j)) (om (k PKU))), [filePos j, k (B j)]⟩) ++
  [ ⟨REL_LW, k ON, [k RI, k BLK, p P_K, lo, hi]⟩,
    ⟨REL_LB, .mul (k ON) (p P_K0), [k RI, k BLK, k LASTF, k T]⟩ ]

def lw : Comp where
  air := { name := "set_lw", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.LW
