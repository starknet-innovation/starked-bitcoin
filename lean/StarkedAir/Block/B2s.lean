/-
**Block Blake2s (M3a.6 `BLK-COMMIT`, D-038 as amended: `C = blake2s(undo)`).** The proven Blake2s
compression AIR (`Gadgets/Blake2s.lean`, constraints unchanged), one compression per 88-row period, plus
per-period values copied down the period: block index `BLKI`, flags `FST` (the stream's first block: the
chaining value is Blake2s's initial `h0`), `NIL` (unused) and `LASTF` (the stream's last block), and the
counter `T`.

* A used period hashes a stream block: its message words are the walker's (`b2w`), the counter and the
  last flag are the walker's (`b2b`), and a period that continues the previous one (`CHN`) is the next
  block, chained from the previous period's output. Period 0 never continues.
* The last block yields its digest words (`b2d`); rows 0–7 read `b2d(k, pub (9 + 2k), pub (10 + 2k))`, so
  public inputs 9–24 are the digest's limbs.
-/
import StarkedAir.Block.B2Msg
import StarkedAir.Gadgets.Blake2s

namespace StarkedAir.Block.B2s

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Blake2s (WB ML outW P_INIT P_FIN PERIOD limb)
open StarkedAir.Block.Fields (degE)

def REL_B2D : ℕ := 20
/-- The commitment's 16 limbs are public inputs 9–24. -/
def PUB_OUT : ℕ := 9

def BLKI : ℕ := 300
def FST : ℕ := 301
def NIL : ℕ := 302
def LASTF : ℕ := 303
def T : ℕ := 304
def WLO : ℕ := 305
def WHI : ℕ := 306
def CHN : ℕ := 307
/-- `1 − NIL`: the period hashes a stream block. -/
def USEW : ℕ := 308
/-- `USEW · LASTF`: the period yields the digest. -/
def YD : ℕ := 309
/-- The uses' multiplicities, as boolean columns: `USEW·LT16`, `USEW·R0`. -/
def MU0 : ℕ := 310
def MU1 : ℕ := 311
def N_MAIN : ℕ := 312

def per88 (f : ℕ → ℕ) : PreCol := .periodic ((List.range PERIOD).map f)

/-- The gadget's 50 preprocessed columns, then: rows 0–7, row 0 of a period, rows < 16, the word index,
and one-hot row selectors for rows 0–15. -/
def preCols : List PreCol :=
  Blake2s.preCols ++
  [ .rowLt 8, per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
    per88 (fun r => if r < 16 then r else 0) ] ++
  (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))
def P_OUT8 : ℕ := 50
def P_R0 : ℕ := 51
def P_LT16 : ℕ := 52
def P_KR : ℕ := 53
def P_RK (j : ℕ) : ℕ := 54 + j

def k (c : ℕ) : Expr := col c
/-- Column `c` in the previous period. -/
def kq (c : ℕ) : Expr := col c (-88)
def kp (c : ℕ) : Expr := col c (-1)
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e

/-- Init row `k`'s `b` slot is chaining word `bidx k`; final row `k` outputs words `k` and `bidx k`. -/
def bidx (j : ℕ) : ℕ := [5, 6, 7, 4].getD j 0

/-- Blake2s's initial chaining value `h0` (IV with the parameter block). -/
def h0 (i : ℕ) : ℕ := (Spec.Blake2s.h0 i).toNat
def h0Bit (i b : ℕ) : ℕ := if (h0 i).testBit b then 1 else 0

def bitSum (w : ℕ) (m : ℕ) : Expr := Sha256.sumPow (fun i => k (WB w i)) m

def perConst : List ℕ := [BLKI, FST, NIL, LASTF, T]

def flagC : List Expr :=
  [FST, NIL, LASTF, MU0, MU1].map (fun c => boolC (k c)) ++
  [ .mul (k FST) (k NIL),
    .sub (k CHN) (om (.add (k FST) (k NIL))),
    .sub (k USEW) (om (k NIL)),
    .sub (k YD) (.mul (k USEW) (k LASTF)),
    .sub (k MU0) (.mul (k USEW) (p P_LT16)), .sub (k MU1) (.mul (k USEW) (p P_R0)) ] ++
  perConst.map (fun c => .mul (om (p P_R0)) (.sub (k c) (kp c)))

/-- Chaining: a continuing period is the next block after a used period; a first block is block 0;
period 0 does not continue. -/
def chainC : List Expr :=
  [ .mul (p P_R0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)),
    .mul (p P_R0) (.mul (k CHN) (kq NIL)),
    .mul (p P_R0) (.mul (k FST) (k BLKI)),
    .mul (p P_OUT8) (k CHN) ]

/-- The chaining value: `h0` on a first block, else the previous period's output. -/
def initC : List Expr :=
  (List.range 4).flatMap fun j =>
    let s := p (P_INIT j)
    (List.range 32).flatMap fun b =>
      [ .mul (k FST) (.mul s (.sub (k (WB (outW 0) b)) (cst (h0Bit j b)))),
        .mul (k FST) (.mul s (.sub (k (WB (outW 1) b)) (cst (h0Bit (bidx j) b)))),
        .mul (k CHN) (.mul s (.sub (k (WB (outW 0) b)) (col (WB 0 b) (-4)))),
        .mul (k CHN) (.mul s (.sub (k (WB (outW 1) b)) (col (WB 1 b) (-4)))) ]

/-- Counter and final flag on row 0 (`t_lo` in `W0`, `t_hi` in `W1`, `f` in `W2` bit 0). -/
def tfC : List Expr :=
  let g := Expr.mul (p P_R0) (om (k NIL))
  [ .mul g (.sub (bitSum 0 25) (k T)), .mul g (.sub (k (WB 2 0)) (k LASTF)) ] ++
  (List.range 7).map (fun i => .mul g (k (WB 0 (25 + i)))) ++
  (List.range 32).map (fun i => .mul g (k (WB 1 i)))

/-- Message words picked at rows 0–15 (limbs copied down the period). -/
def wordC : List Expr :=
  [ .mul (p P_LT16) (.sub (k WLO) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 0)))) (cst 0))),
    .mul (p P_LT16) (.sub (k WHI) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 1)))) (cst 0))) ]

def constraints : List Expr := Blake2s.constraints ++ flagC ++ chainC ++ initC ++ tfC ++ wordC

/-- Public limb `h` of digest word `kk` at row `kk < 8`: `Σ_j RK_j · pub (9 + 2j + h)`. -/
def pubLimb (h : ℕ) : Expr :=
  (List.range 8).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (.pub (PUB_OUT + 2 * j + h)))) (cst 0)

def lookups : List Lookup :=
  [ ⟨B2Msg.REL_B2W, .neg (k MU0), [k BLKI, p P_KR, k WLO, k WHI]⟩,
    ⟨B2Msg.REL_B2B, .neg (k MU1), [k BLKI, k LASTF, k T]⟩,
    ⟨REL_B2D, .neg (p P_OUT8), [p P_KR, pubLimb 0, pubLimb 1]⟩ ] ++
  (List.range 4).flatMap fun j =>
    [ ⟨REL_B2D, .mul (k YD) (p (P_FIN j)), [cst j, limb 0 0, limb 0 1]⟩,
      ⟨REL_B2D, .mul (k YD) (p (P_FIN j)), [cst (bidx j), limb 1 0, limb 1 1]⟩ ]

def b2s : Comp where
  air := { name := "block_b2s", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.B2s
