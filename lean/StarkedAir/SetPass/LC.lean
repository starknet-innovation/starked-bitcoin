/-
**Merkle leaf compressions (`set_lc`, D-050).** The proven Blake2s compression AIR (`Gadgets/Blake2s.lean`,
constraints unchanged), one compression per 88-row period: `block_b2s` per record. Per-period values,
copied down the period: record `RI`, block `BLKI`, flags `FST` (the record's first block: the chaining
value is Blake2s's `h0`), `NIL` (unused), `LASTF` (the record's last block) and the counter `T`.

* A used period hashes a block of record `RI`'s leaf message: its words are the walker's
  (`lw(RI, BLKI, k, lo, hi)`), its counter and last flag the walker's (`lb`); a period that continues the
  previous one (`CHN`) is the same record's next block, chained from the previous period's output.
* A record's last block yields its digest words: `leaf(RI, w, lo, hi)` at the final rows (a whole period).
-/
import StarkedAir.SetPass.Layout
import StarkedAir.Block.B2s

namespace StarkedAir.SetPass.LC

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Blake2s (WB ML outW P_INIT P_FIN PERIOD limb)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.B2s (bidx per88 h0Bit)

def BLKI : ℕ := 300
def FST : ℕ := 301
def NIL : ℕ := 302
def LASTF : ℕ := 303
def T : ℕ := 304
def WLO : ℕ := 305
def WHI : ℕ := 306
def CHN : ℕ := 307
def USEW : ℕ := 308
def YD : ℕ := 309
def MU0 : ℕ := 310
def MU1 : ℕ := 311
def RI : ℕ := 312
def N_MAIN : ℕ := 313

/-- `block_b2s`'s preprocessed columns. -/
def preCols : List PreCol := Block.B2s.preCols
def P_OUT8 : ℕ := 50
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

def bitSum (w : ℕ) (m : ℕ) : Expr := Sha256.sumPow (fun i => k (WB w i)) m

def perConst : List ℕ := [BLKI, FST, NIL, LASTF, T, RI]

def flagC : List Expr :=
  [FST, NIL, LASTF, MU0, MU1].map (fun c => boolC (k c)) ++
  [ .mul (k FST) (k NIL),
    .sub (k CHN) (om (.add (k FST) (k NIL))),
    .sub (k USEW) (om (k NIL)),
    .sub (k YD) (.mul (k USEW) (k LASTF)),
    .sub (k MU0) (.mul (k USEW) (p P_LT16)), .sub (k MU1) (.mul (k USEW) (p P_R0)) ] ++
  perConst.map (fun c => .mul (om (p P_R0)) (.sub (k c) (kp c)))

/-- A continuing period is the same record's next block after a used period; a first block is block 0;
period 0 does not continue. -/
def chainC : List Expr :=
  [ .mul (p P_R0) (.mul (k CHN) (.sub (.sub (k BLKI) (kq BLKI)) one)),
    .mul (p P_R0) (.mul (k CHN) (.sub (k RI) (kq RI))),
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

/-- Counter and final flag on row 0 (`t_lo` in `W0` below `2^25`, `t_hi` zero, `f` in `W2` bit 0). -/
def tfC : List Expr :=
  let g := Expr.mul (p P_R0) (om (k NIL))
  [ .mul g (.sub (bitSum 0 25) (k T)), .mul g (.sub (k (WB 2 0)) (k LASTF)) ] ++
  (List.range 7).map (fun i => .mul g (k (WB 0 (25 + i)))) ++
  (List.range 32).map (fun i => .mul g (k (WB 1 i)))

def wordC : List Expr :=
  [ .mul (p P_LT16) (.sub (k WLO) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 0)))) (cst 0))),
    .mul (p P_LT16) (.sub (k WHI) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 1)))) (cst 0))) ]

def constraints : List Expr := Blake2s.constraints ++ flagC ++ chainC ++ initC ++ tfC ++ wordC

def lookups : List Lookup :=
  [ ⟨REL_LW, .neg (k MU0), [k RI, k BLKI, p P_KR, k WLO, k WHI]⟩,
    ⟨REL_LB, .neg (k MU1), [k RI, k BLKI, k LASTF, k T]⟩ ] ++
  (List.range 4).flatMap fun j =>
    [ ⟨REL_LEAF, .mul (k YD) (p (P_FIN j)), [k RI, cst j, limb 0 0, limb 0 1]⟩,
      ⟨REL_LEAF, .mul (k YD) (p (P_FIN j)), [k RI, cst (bidx j), limb 1 0, limb 1 1]⟩ ]

def lc : Comp where
  air := { name := "set_lc", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.LC
