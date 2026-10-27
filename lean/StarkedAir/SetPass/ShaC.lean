/-
**SHA-256 compressions (`set_shac`).** The proven SHA-256 compression AIR (`Gadgets/Sha256.lean`,
constraints unchanged), one compression per 72-row period, with per-period values copied down the
period: block index `BLKI`, `NIL` (unused) and `LASTS` (the segment's last block). With
`m = nb_out − nb_in`:

* used periods are a prefix from period 0; period 0 is block 0 and starts from the public `H_in`; every
  other used period is the next block, chained from the previous period's output;
* message words are the stream's `w(64·BLKI + 4t, lo, hi)`;
* `LASTS` marks block `m − 1`; its output (rows 68–71) is the public `H_out`, and its row 0 yields
  the end token `(m − 1)` that the stream consumes once, so the last block is reached.

`block_sha` differs at the edges: the IV on a message's first block, the second hash, Merkle nodes.
-/
import StarkedAir.SetPass.Layout
import StarkedAir.Block.Sha

namespace StarkedAir.SetPass.ShaC

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC limb)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.Sha (per72)
open StarkedAir.HeaderChain (eqLimbs)

def BLKI : ℕ := 124
def NIL : ℕ := 125
def LASTS : ℕ := 126
def USEW : ℕ := 127
def CHN : ℕ := 128
/-- The inverse of `BLKI − (m − 1)` off the last block. -/
def LINV : ℕ := 129
def N_MAIN : ℕ := 130

/-- Preprocessed: SHA's five, then row 0, init rows, message rows (4..19), the row index, period 0, the
four init rows one-hot, the last row. -/
def preCols : List PreCol :=
  Sha256.preCols ++
  [ per72 (fun q => if q = 0 then 1 else 0),
    per72 (fun q => if q < 4 then 1 else 0),
    per72 (fun q => if 4 ≤ q ∧ q < 20 then 1 else 0),
    per72 (fun q => q),
    .rowLt 72 ] ++
  (List.range 4).map (fun j => per72 (fun q => if q = j then 1 else 0)) ++
  [ per72 (fun q => if q = 71 then 1 else 0) ]
def ROW0 : ℕ := 5
def INIT : ℕ := 6
def MSGROW : ℕ := 7
def ROWIDX : ℕ := 8
def P0 : ℕ := 9
def IQ (j : ℕ) : ℕ := 10 + j
def FIN3 : ℕ := 14

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kq (c : ℕ) : Expr := col c (-72)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e

def mLast : Expr := .sub (.sub (.pub (H_NB SHA_OUT)) (.pub (H_NB SHA_IN))) one

def flagC : List Expr :=
  [NIL, LASTS].map (fun c => boolC (k c)) ++
  [ .sub (k USEW) (om (k NIL)),
    .sub (k CHN) (.mul (k USEW) (om (pre P0))),
    .mul (pre P0) (k NIL),
    .mul (k LASTS) (.sub (k BLKI) mLast),
    .mul (k USEW) (.sub (.mul (.sub (k BLKI) mLast) (k LINV)) (om (k LASTS))),
    .mul (k LASTS) (k NIL) ] ++
  [BLKI, NIL, LASTS].map (fun c => .mul (om (pre ROW0)) (.sub (k c) (kp c)))

def chainC : List Expr :=
  [ .mul (pre P0) (k BLKI),
    .mul (pre ROW0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)),
    .mul (pre ROW0) (.mul (k CHN) (kq NIL)) ]

/-- Init rows: `H_in` in period 0 (row `q` holds words `3 − q` and `7 − q`), else the previous period's
output. -/
def initC : List Expr :=
  let chSel := Expr.mul (pre INIT) (k CHN)
  (List.range 4).flatMap (fun q =>
    let s := Expr.mul (pre P0) (pre (IQ q))
    eqLimbs s Sha256.A 0 (fun h => .pub (H_LIMB SHA_IN (2 * (3 - q) + h))) ++
    eqLimbs s Sha256.E 0 (fun h => .pub (H_LIMB SHA_IN (2 * (7 - q) + h)))) ++
  eqLimbs chSel Sha256.A 0 (fun h => limb Sha256.A h (-4)) ++ eqLimbs chSel Sha256.E 0 (fun h => limb Sha256.E h (-4))

/-- The last block's output is `H_out`: at row 71, word `i < 4` is `a` at offset `−i`, word `4 + i` is
`e` at offset `−i`. -/
def outC : List Expr :=
  (List.range 4).flatMap fun (i : ℕ) =>
    let s := Expr.mul (k LASTS) (pre FIN3)
    let off : ℤ := -((i : ℕ) : ℤ)
    eqLimbs s Sha256.A off (fun h => .pub (H_LIMB SHA_OUT (2 * i + h))) ++
    eqLimbs s Sha256.E off (fun h => .pub (H_LIMB SHA_OUT (2 * (4 + i) + h)))

def constraints : List Expr := Sha256.constraints ++ flagC ++ chainC ++ initC ++ outC

def lookups : List Lookup :=
  [ ⟨REL_SW, .neg (.mul (pre MSGROW) (k USEW)),
      [.add (.mul (cst 64) (k BLKI)) (.sub (.mul (cst 4) (pre ROWIDX)) (cst 16)), limb Sha256.W 0, limb Sha256.W 1]⟩,
    ⟨REL_SHEND, .mul (k LASTS) (pre ROW0), [k BLKI]⟩ ]

def shac : Comp where
  air := { name := "set_shac", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.ShaC
