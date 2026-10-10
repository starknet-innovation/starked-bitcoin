/-
**Block Blake2s (M3a.6 `BLK-COMMIT`, D-038).** The proven Blake2s compression AIR
(`Gadgets/Blake2s.lean`, constraints unchanged), one compression per 88-row period, plus per-period
values copied down the period: the stream `STR`, block index `BLKI`, and flags `FST` (a stream's
first block: the chaining value is Blake2s's initial `h0`), `NIL` (unused) and `LASTF` (the stream's
last block), and the counter `T`.

* Period 0 (`OUTP`, preprocessed) is the outer hash: `h = h0`, `t = 64`, `f = 1`, message words 0–7
  and 8–15 the two streams' digests (`b2d` uses), and its output limbs are public inputs 9–24.
* Other periods hash stream blocks: message words are the walker's (`b2w`), the counter and the last
  flag are the walker's (`b2b`), and a period that continues the previous one (`CHN`) is the same
  stream's next block, chained from the previous period's output. A stream's last block yields its
  digest words (`b2d`).
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

def STR : ℕ := 300
def BLKI : ℕ := 301
def FST : ℕ := 302
def NIL : ℕ := 303
def LASTF : ℕ := 304
def T : ℕ := 305
def WLO : ℕ := 306
def WHI : ℕ := 307
def CHN : ℕ := 308
/-- `(1 − NIL)(1 − OUTP)`: the period hashes a stream block. -/
def USEW : ℕ := 309
/-- `USEW · LASTF`: the period yields its stream's digest. -/
def YD : ℕ := 310
/-- The counter: 64 for the outer hash, else `T`. -/
def TV : ℕ := 311
/-- The final flag: 1 for the outer hash, else `LASTF`. -/
def FV : ℕ := 312
/-- A main-column copy of `OUTP` (the previous period's is read at offset −88). -/
def OQ : ℕ := 313
/-- The uses' multiplicities, as boolean columns: `USEW·LT16`, `OUTP·LT16`, `USEW·R0`. -/
def MU0 : ℕ := 314
def MU1 : ℕ := 315
def MU2 : ℕ := 316
def N_MAIN : ℕ := 317

def per88 (f : ℕ → ℕ) : PreCol := .periodic ((List.range PERIOD).map f)

/-- The gadget's 50 preprocessed columns, then: the outer period, row 0, rows < 16, the word index,
the digest's stream and word, and one-hot row selectors for rows 0–15. -/
def preCols : List PreCol :=
  Blake2s.preCols ++
  [ .rowLt 88, per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
    per88 (fun r => if r < 16 then r else 0), per88 (fun r => if r < 16 then r / 8 else 0),
    per88 (fun r => if r < 16 then r % 8 else 0) ] ++
  (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))
def P_OUTP : ℕ := 50
def P_R0 : ℕ := 51
def P_LT16 : ℕ := 52
def P_KR : ℕ := 53
def P_DS : ℕ := 54
def P_DK : ℕ := 55
def P_RK (j : ℕ) : ℕ := 56 + j

def k (c : ℕ) : Expr := col c
/-- Column `c` in the previous period. -/
def kq (c : ℕ) : Expr := col c (-88)
def kp (c : ℕ) : Expr := col c (-1)
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def outp : Expr := p P_OUTP

/-- Init row `k`'s `b` slot is chaining word `bidx k`; final row `k` outputs words `k` and `bidx k`. -/
def bidx (j : ℕ) : ℕ := [5, 6, 7, 4].getD j 0

/-- Blake2s's initial chaining value `h0` (IV with the parameter block). -/
def h0 (i : ℕ) : ℕ := (Spec.Blake2s.h0 i).toNat
def h0Bit (i b : ℕ) : ℕ := if (h0 i).testBit b then 1 else 0

def bitSum (w : ℕ) (m : ℕ) : Expr := Sha256.sumPow (fun i => k (WB w i)) m

def perConst : List ℕ := [STR, BLKI, FST, NIL, LASTF, T]

def flagC : List Expr :=
  [FST, NIL, LASTF, MU0, MU1, MU2].map (fun c => boolC (k c)) ++
  [ .mul (k FST) (k NIL), .mul outp (k NIL),
    .sub (k CHN) (.mul (om (.add (k FST) (k NIL))) (om outp)),
    .sub (k USEW) (.mul (om (k NIL)) (om outp)),
    .sub (k YD) (.mul (k USEW) (k LASTF)),
    .sub (k TV) (.add (.mul outp (cst 64)) (.mul (om outp) (k T))),
    .sub (k FV) (.add outp (.mul (om outp) (k LASTF))),
    .sub (k OQ) outp,
    .sub (k MU0) (.mul (k USEW) (p P_LT16)), .sub (k MU1) (.mul outp (p P_LT16)), .sub (k MU2) (.mul (k USEW) (p P_R0)) ] ++
  perConst.map (fun c => .mul (om (p P_R0)) (.sub (k c) (kp c)))

/-- Chaining: a continuing period is the same stream's next block after a stream period; a first
block is block 0. -/
def chainC : List Expr :=
  [ .mul (p P_R0) (.mul (k CHN) (.sub (k STR) (kq STR))),
    .mul (p P_R0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)),
    .mul (p P_R0) (.mul (k CHN) (kq NIL)),
    .mul (p P_R0) (.mul (k CHN) (kq OQ)),
    .mul (p P_R0) (.mul (k FST) (k BLKI)) ]

/-- The chaining value: `h0` on a first block or the outer hash, else the previous period's output. -/
def initC : List Expr :=
  (List.range 4).flatMap fun j =>
    let s := p (P_INIT j)
    (List.range 32).flatMap fun b =>
      [ .mul (.add (k FST) outp) (.mul s (.sub (k (WB (outW 0) b)) (cst (h0Bit j b)))),
        .mul (.add (k FST) outp) (.mul s (.sub (k (WB (outW 1) b)) (cst (h0Bit (bidx j) b)))),
        .mul (k CHN) (.mul s (.sub (k (WB (outW 0) b)) (col (WB 0 b) (-4)))),
        .mul (k CHN) (.mul s (.sub (k (WB (outW 1) b)) (col (WB 1 b) (-4)))) ]

/-- Counter and final flag on row 0 (`t_lo` in `W0`, `t_hi` in `W1`, `f` in `W2` bit 0). -/
def tfC : List Expr :=
  let g := Expr.mul (p P_R0) (om (k NIL))
  [ .mul g (.sub (bitSum 0 25) (k TV)), .mul g (.sub (k (WB 2 0)) (k FV)) ] ++
  (List.range 7).map (fun i => .mul g (k (WB 0 (25 + i)))) ++
  (List.range 32).map (fun i => .mul g (k (WB 1 i)))

/-- Message words picked at rows 0–15 (limbs copied down the period). -/
def wordC : List Expr :=
  [ .mul (p P_LT16) (.sub (k WLO) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 0)))) (cst 0))),
    .mul (p P_LT16) (.sub (k WHI) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 1)))) (cst 0))) ]

/-- The outer hash's output limbs are the public commitment. -/
def outC : List Expr :=
  (List.range 4).flatMap fun j =>
    (List.range 2).flatMap fun h =>
      [ .mul outp (.mul (p (P_FIN j)) (.sub (limb 0 h) (.pub (PUB_OUT + 2 * j + h)))),
        .mul outp (.mul (p (P_FIN j)) (.sub (limb 1 h) (.pub (PUB_OUT + 2 * bidx j + h)))) ]

def constraints : List Expr := Blake2s.constraints ++ flagC ++ chainC ++ initC ++ tfC ++ wordC ++ outC

def lookups : List Lookup :=
  [ ⟨B2Msg.REL_B2W, .neg (k MU0), [k STR, k BLKI, p P_KR, k WLO, k WHI]⟩,
    ⟨REL_B2D, .neg (k MU1), [p P_DS, p P_DK, k WLO, k WHI]⟩,
    ⟨B2Msg.REL_B2B, .neg (k MU2), [k STR, k BLKI, k LASTF, k T]⟩ ] ++
  (List.range 4).flatMap fun j =>
    [ ⟨REL_B2D, .mul (k YD) (p (P_FIN j)), [k STR, cst j, limb 0 0, limb 0 1]⟩,
      ⟨REL_B2D, .mul (k YD) (p (P_FIN j)), [k STR, cst (bidx j), limb 1 0, limb 1 1]⟩ ]

def b2s : Comp where
  air := { name := "block_b2s", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.B2s
