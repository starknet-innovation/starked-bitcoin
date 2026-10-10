/-
**Blake2s message words (M3a.6 `BLK-COMMIT`, D-038 as amended).** The stream the commitment hashes, the
undo bytes (length `pub 8`), as Blake2s message words: one row per 32-bit little-endian word, 16 rows per
64-byte block (the rows' period position is the word index). Bytes from position `len` on are zero
(Blake2s's padding).

* Rows `ON` form a prefix, the stream's blocks; block `BLK` counts from 0 and `POS = 64·BLK + 4·k`.
* `A j` marks byte `j` of the row as in the stream; it is monotone (1s then 0s), its count of 1s is the
  length, and only block 0 may start with a 0 (the empty stream's one block). So `A j = [POS + j < len]`
  and the stream has `max 1 ⌈len / 64⌉` blocks.
* Active bytes are read from the undo table; others are 0.
* Each row yields `b2w(block, k, lo, hi)`; each block's first row yields `b2b(block, last, t)`, with `t`
  the Blake2s counter after the block: `64·(block + 1)`, or the length for the last block.
-/
import StarkedAir.Block.Undo
import StarkedAir.Block.Fields

namespace StarkedAir.Block.B2Msg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)

def REL_B2W : ℕ := 18
def REL_B2B : ℕ := 19

def ON : ℕ := 0
def BLK : ℕ := 1
def POS : ℕ := 2
def B (j : ℕ) : ℕ := 3 + j
def A (j : ℕ) : ℕ := 7 + j
def CNT : ℕ := 11
def LASTF : ℕ := 12
def T : ℕ := 13
/-- `notFirst · ON`: the row continues the previous row's stream. -/
def SM : ℕ := 14
/-- The row ends the stream: the next row is off (never the last row). -/
def END : ℕ := 15
def N_MAIN : ℕ := 16

def per16 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 16).map f)
def preCols : List PreCol :=
  [.isFirst, .notLast, per16 id, per16 (fun k => if k = 0 then 1 else 0), per16 (fun k => if k = 15 then 1 else 0)]
def P_FIRST : ℕ := 0
def P_NOTLAST : ℕ := 1
def P_K : ℕ := 2
def P_K0 : ℕ := 3
def P_K15 : ℕ := 4

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := p P_FIRST
def notFirst : Expr := om first
def isLast : Expr := om (p P_NOTLAST)

/-- The stream's length: `pub 8`. -/
def lenS : Expr := .pub Undo.PUB_LEN
/-- The row's active-byte count. -/
def sumA : Expr := .add (.add (k (A 0)) (k (A 1))) (.add (k (A 2)) (k (A 3)))
def ends : Expr := k END

def boolCols : List ℕ := [ON, LASTF, A 0, A 1, A 2, A 3]

def constraints : List Expr :=
  boolCols.map (fun c => boolC (k c)) ++
  [ -- the first row starts block 0; the last row is off; on rows are a prefix
    .mul first (om (k ON)), .mul first (k BLK),
    .mul isLast (k ON),
    .mul notFirst (.mul (k ON) (om (kp ON))),
    -- blocks and positions
    .sub (k SM) (.mul notFirst (k ON)),
    .mul (p P_K0) (.sub (k BLK) (.mul (k SM) (.add (kp BLK) one))),
    .mul (om (p P_K0)) (.sub (k BLK) (kp BLK)),
    .sub (k POS) (.add (.mul (cst 64) (k BLK)) (.mul (cst 4) (p P_K))),
    -- active bytes: inactive bytes are zero, and the flags are monotone
    .sub (k CNT) (.add (.mul (k SM) (kp CNT)) sumA),
    .mul (k SM) (.mul (k (A 0)) (om (kp (A 3)))),
    .mul (p P_K0) (.mul (om (k (A 0))) (k BLK)),
    -- the end: at a block's last row, with the count equal to the length
    .sub (k END) (.mul (p P_NOTLAST) (.sub (k ON) (kn ON))),
    .mul (om (p P_K15)) ends,
    .mul (p P_K15) (.sub (k LASTF) ends),
    .mul (om (p P_K0)) (.sub (k LASTF) (kp LASTF)),
    .mul ends (.sub (k CNT) lenS),
    -- the counter after the block
    .sub (k T) (.add (.mul (k LASTF) lenS) (.mul (om (k LASTF)) (.add (.mul (cst 64) (k BLK)) (cst 64)))) ] ++
  (List.range 4).map (fun j => .mul (k (B j)) (om (k (A j)))) ++
  (List.range 4).map (fun j => .mul (k (A j)) (om (k ON))) ++
  (List.range 3).map (fun j => .mul (k (A (j + 1))) (om (k (A j))))

def lo : Expr := .add (k (B 0)) (.mul (cst 256) (k (B 1)))
def hi : Expr := .add (k (B 2)) (.mul (cst 256) (k (B 3)))

def lookups : List Lookup :=
  (List.range 4).map (fun j => ⟨Undo.REL_UBYTE, .neg (k (A j)), [.add (k POS) (cst j), k (B j)]⟩) ++
  [ ⟨REL_B2W, k ON, [k BLK, p P_K, lo, hi]⟩,
    ⟨REL_B2B, .mul (k ON) (p P_K0), [k BLK, k LASTF, k T]⟩ ]

def b2msg : Comp where
  air := { name := "block_b2msg", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.B2Msg
