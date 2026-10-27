/-
**Blake2s compressions (`set_b2c`).** The proven Blake2s compression AIR (`Gadgets/Blake2s.lean`,
constraints unchanged), one compression per 88-row period, with per-period values copied down the
period: block index `BLKI`, `NIL` (unused) and `LASTU` (the segment's last block). With
`m = nb_out − nb_in`:

* used periods are a prefix from period 0; period 0 is block 0 and chains from the public `h_in`; every
  other used period is the next block, chained from the previous period's output;
* the counter is `64 · (nb_in + BLKI + 1)` (`t_lo`, `t_hi` bits; below `2^36`), the final flag 0;
* message words are the walker's `w(BLKI, k, lo, hi)`;
* `LASTU` marks block `m − 1`; its output is the public `h_out`, and its row 0 yields the end token
  `(m − 1)` that the walker consumes once, so the last block is reached.

`block_b2s` differs at the edges only: `h0` and a counter below `2^25` on a stream's first block, a
final flag, the digest by lookup.
-/
import StarkedAir.SetPass.Layout
import StarkedAir.Block.B2s

namespace StarkedAir.SetPass.B2c

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Blake2s (WB ML outW P_INIT P_FIN PERIOD limb)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.B2s (bidx per88)

def BLKI : ℕ := 300
def NIL : ℕ := 301
def LASTU : ℕ := 302
def WLO : ℕ := 303
def WHI : ℕ := 304
def CHN : ℕ := 305
def USEW : ℕ := 306
/-- `USEW` at the word rows (the uses' multiplicity). -/
def MU : ℕ := 307
/-- The inverse of `BLKI − (m − 1)` off the last block. -/
def LINV : ℕ := 308
def N_MAIN : ℕ := 309

/-- The gadget's 50 preprocessed columns, then: period 0, row 0 of a period, rows < 16, the word
index, and one-hot row selectors for rows 0–15. -/
def preCols : List PreCol :=
  Blake2s.preCols ++
  [ .rowLt 88, per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
    per88 (fun r => if r < 16 then r else 0) ] ++
  (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))
def P_P0 : ℕ := 50
def P_R0 : ℕ := 51
def P_LT16 : ℕ := 52
def P_KR : ℕ := 53
def P_RK (j : ℕ) : ℕ := 54 + j

def k (c : ℕ) : Expr := col c
def kq (c : ℕ) : Expr := col c (-88)
def kp (c : ℕ) : Expr := col c (-1)
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e

def mLast : Expr := .sub (.sub (.pub (H_NB B2_OUT)) (.pub (H_NB B2_IN))) one
def bitSum (w : ℕ) (lo len : ℕ) : Expr := Sha256.sumPow (fun i => k (WB w (lo + i))) len

def perConst : List ℕ := [BLKI, NIL, LASTU]

def flagC : List Expr :=
  [NIL, LASTU].map (fun c => boolC (k c)) ++
  [ .sub (k USEW) (om (k NIL)),
    .sub (k CHN) (.mul (k USEW) (om (p P_P0))),
    .sub (k MU) (.mul (k USEW) (p P_LT16)),
    .mul (p P_P0) (k NIL),
    -- the last block: block m − 1, a used period
    .mul (k LASTU) (.sub (k BLKI) mLast),
    .mul (k USEW) (.sub (.mul (.sub (k BLKI) mLast) (k LINV)) (om (k LASTU))),
    .mul (k LASTU) (k NIL) ] ++
  perConst.map (fun c => .mul (om (p P_R0)) (.sub (k c) (kp c)))

/-- Period 0 is block 0; a continuing period is the next block after a used period. -/
def chainC : List Expr :=
  [ .mul (p P_P0) (k BLKI),
    .mul (p P_R0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)),
    .mul (p P_R0) (.mul (k CHN) (kq NIL)) ]

/-- The chaining value: the public `h_in` (limbs) in period 0, else the previous period's output. -/
def initC : List Expr :=
  (List.range 4).flatMap fun j =>
    let s := p (P_INIT j)
    ((List.range 2).flatMap fun h =>
      [ .mul (p P_P0) (.mul s (.sub (limb (outW 0) h) (.pub (H_LIMB B2_IN (2 * j + h))))),
        .mul (p P_P0) (.mul s (.sub (limb (outW 1) h) (.pub (H_LIMB B2_IN (2 * bidx j + h))))) ]) ++
    (List.range 32).flatMap fun b =>
      [ .mul (k CHN) (.mul s (.sub (k (WB (outW 0) b)) (col (WB 0 b) (-4)))),
        .mul (k CHN) (.mul s (.sub (k (WB (outW 1) b)) (col (WB 1 b) (-4)))) ]

/-- The counter `64 · (nb_in + BLKI + 1)` on row 0 (`t_lo` in `W0`, `t_hi` in `W1`), the final flag
(`W2` bit 0) zero. -/
def tfC : List Expr :=
  let g := Expr.mul (p P_R0) (k USEW)
  [ .mul g (.sub (.add (bitSum 0 6 26) (.mul (cst (2 ^ 26)) (bitSum 1 0 4)))
      (.add (.add (.pub (H_NB B2_IN)) (k BLKI)) one)),
    .mul g (k (WB 2 0)) ] ++
  (List.range 6).map (fun i => .mul g (k (WB 0 i))) ++
  (List.range 28).map (fun i => .mul g (k (WB 1 (4 + i))))

/-- Message words picked at rows 0–15 (limbs copied down the period). -/
def wordC : List Expr :=
  [ .mul (p P_LT16) (.sub (k WLO) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 0)))) (cst 0))),
    .mul (p P_LT16) (.sub (k WHI) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 1)))) (cst 0))) ]

/-- The last block's output is `h_out`: final row `j` holds words `j` and `b(4 + j)`. -/
def outC : List Expr :=
  (List.range 4).flatMap fun j =>
    let s := Expr.mul (k LASTU) (p (P_FIN j))
    (List.range 2).flatMap fun h =>
      [ .mul s (.sub (limb 0 h) (.pub (H_LIMB B2_OUT (2 * j + h)))),
        .mul s (.sub (limb 1 h) (.pub (H_LIMB B2_OUT (2 * bidx j + h)))) ]

def constraints : List Expr := Blake2s.constraints ++ flagC ++ chainC ++ initC ++ tfC ++ wordC ++ outC

def lookups : List Lookup :=
  [ ⟨REL_SB2W, .neg (k MU), [k BLKI, p P_KR, k WLO, k WHI]⟩,
    ⟨REL_B2END, .mul (k LASTU) (p P_R0), [k BLKI]⟩ ]

def b2c : Comp where
  air := { name := "set_b2c", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.B2c
