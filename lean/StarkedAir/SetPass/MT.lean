/-
**The segment's Merkle tree (`set_mt`, D-050).** The proven Blake2s compression AIR, one node per 88-row
period: `Blake2s-256(left ‖ right)` of its children's 32-byte digests (one block: `h0`, counter 64,
final). Per period: the node `ID`, flags `NIL` (unused) and `LEAFL` (the node's children are leaf slots),
`USEL`/`USER` (the left/right slot holds a record).

* Node `j < HALF` hashes nodes `2j` and `2j + 1` (`node(·, w, lo, hi)` yields); node `HALF ≤ j` hashes
  slots `2(j − HALF)` and `2(j − HALF) + 1`: a record's leaf (`leaf(s, w, lo, hi)` from `set_lc`) when
  the slot is below the segment's record count `e = i_out − i_in`, else 32 zero bytes. `LEAFL` and the
  slot flags are range-checked (three bytes each way).
* Every node yields its digest words `node(ID, w, lo, hi)` at the final rows (a whole period); row 0
  consumes `node(1, ROOT)`: node 1, the root, is computed and is the public `ROOT`.
* Row 0 checks `e ≤ 2·HALF` (every record has a slot) and `1 ≤ HALF ≤ 2^24` (heap indices stay far below
  `P`).
-/
import StarkedAir.SetPass.Layout
import StarkedAir.Block.B2s

namespace StarkedAir.SetPass.MT

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Blake2s (WB ML outW P_INIT P_FIN PERIOD limb)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.B2s (bidx per88 h0Bit)

def ID : ℕ := 300
def NIL : ℕ := 301
def USEW : ℕ := 302
def LEAFL : ℕ := 303
def USEL : ℕ := 304
def USER : ℕ := 305
def WLO : ℕ := 306
def WHI : ℕ := 307
/-- The child key the row reads: `2·ID + [row ≥ 8] − 2·HALF·LEAFL`. -/
def CK : ℕ := 308
/-- `USEW · LEAFL`, the row's slot flag, the zero-word flag, the uses' multiplicities. -/
def LU : ℕ := 309
def USEROW : ℕ := 310
def ZW : ℕ := 311
def MUN : ℕ := 312
def MUL : ℕ := 313
/-- Three-byte range witnesses: the level, the left and right slots, `2·HALF − e`. -/
def DD (i : ℕ) : ℕ := 314 + i
def UL (i : ℕ) : ℕ := 317 + i
def UR (i : ℕ) : ℕ := 320 + i
def EB (i : ℕ) : ℕ := 323 + i
/-- `HALF − 1`, as three bytes. -/
def HB (i : ℕ) : ℕ := 326 + i
def N_MAIN : ℕ := 329

/-- The gadget's 50 preprocessed columns, then: row 0 of a period, rows < 16, rows < 8, the word index
`r mod 8` on rows < 16, the trace's row 0, and one-hot selectors for rows 0–15. -/
def preCols : List PreCol :=
  Blake2s.preCols ++
  [ per88 (fun r => if r = 0 then 1 else 0), per88 (fun r => if r < 16 then 1 else 0),
    per88 (fun r => if r < 8 then 1 else 0), per88 (fun r => if r < 16 then r % 8 else 0), .isFirst ] ++
  (List.range 16).map (fun j => per88 (fun r => if r = j then 1 else 0))
def P_R0 : ℕ := 50
def P_LT16 : ℕ := 51
def P_LT8 : ℕ := 52
def P_W8 : ℕ := 53
def P_FIRST : ℕ := 54
def P_RK (j : ℕ) : ℕ := 55 + j

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e

def half : Expr := .pub PUB_HALF
/-- The segment's record count. -/
def cnt : Expr := .sub (.pub PUB_I_OUT) (.pub PUB_I_IN)
def b3 (f : ℕ → ℕ) : Expr := .add (.add (k (f 0)) (.mul (cst 256) (k (f 1)))) (.mul (cst 65536) (k (f 2)))
/-- The left slot `2(ID − HALF)`. -/
def slotL : Expr := .mul (cst 2) (.sub (k ID) half)

def bitSum (w : ℕ) (m : ℕ) : Expr := Sha256.sumPow (fun i => k (WB w i)) m

def perConst : List ℕ := [ID, NIL, LEAFL, USEL, USER]

def flagC : List Expr :=
  [NIL, LEAFL, USEL, USER, USEW, LU, MUN, MUL].map (fun c => boolC (k c)) ++
  [ .sub (k USEW) (om (k NIL)),
    .sub (k LU) (.mul (k USEW) (k LEAFL)),
    .sub (k USEROW) (.add (.mul (p P_LT8) (k USEL)) (.mul (om (p P_LT8)) (k USER))),
    .sub (k ZW) (.mul (k LU) (om (k USEROW))),
    .sub (k MUN) (.mul (.mul (k USEW) (p P_LT16)) (om (k LEAFL))),
    .sub (k MUL) (.mul (.mul (k LU) (p P_LT16)) (k USEROW)),
    .sub (k CK) (.sub (.add (.mul (cst 2) (k ID)) (om (p P_LT8))) (.mul (.mul (cst 2) half) (k LEAFL))),
    -- the level: `LEAFL` iff `ID ≥ HALF`
    .mul (k USEW) (.sub (.add (.mul (k LEAFL) (.sub (k ID) half)) (.mul (om (k LEAFL)) (.sub (.sub half one) (k ID))))
      (b3 DD)),
    -- the slots: a flag iff the slot is below the record count
    .mul (k LU) (.sub (.add (.mul (k USEL) (.sub (.sub cnt one) slotL)) (.mul (om (k USEL)) (.sub slotL cnt))) (b3 UL)),
    .mul (k LU) (.sub (.add (.mul (k USER) (.sub (.sub cnt one) (.add slotL one)))
      (.mul (om (k USER)) (.sub (.add slotL one) cnt))) (b3 UR)),
    -- every record has a slot
    .mul (p P_FIRST) (.sub (.sub (.mul (cst 2) half) cnt) (b3 EB)),
    .mul (p P_FIRST) (.sub (.sub half one) (b3 HB)),
    -- an unused slot is 32 zero bytes
    .mul (p P_LT16) (.mul (k ZW) (k WLO)), .mul (p P_LT16) (.mul (k ZW) (k WHI)) ] ++
  perConst.map (fun c => .mul (om (p P_R0)) (.sub (k c) (kp c)))

/-- Every used period starts from `h0`. -/
def initC : List Expr :=
  (List.range 4).flatMap fun j =>
    let s := p (P_INIT j)
    (List.range 32).flatMap fun b =>
      [ .mul (k USEW) (.mul s (.sub (k (WB (outW 0) b)) (cst (h0Bit j b)))),
        .mul (k USEW) (.mul s (.sub (k (WB (outW 1) b)) (cst (h0Bit (bidx j) b)))) ]

/-- Counter 64 and the final flag, on row 0. -/
def tfC : List Expr :=
  let g := Expr.mul (p P_R0) (k USEW)
  [ .mul g (.sub (bitSum 0 25) (cst 64)), .mul g (.sub (k (WB 2 0)) one) ] ++
  (List.range 7).map (fun i => .mul g (k (WB 0 (25 + i)))) ++
  (List.range 32).map (fun i => .mul g (k (WB 1 i)))

def wordC : List Expr :=
  [ .mul (p P_LT16) (.sub (k WLO) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 0)))) (cst 0))),
    .mul (p P_LT16) (.sub (k WHI) ((List.range 16).foldl (fun acc j => .add acc (.mul (p (P_RK j)) (k (ML j 1)))) (cst 0))) ]

def constraints : List Expr := Blake2s.constraints ++ flagC ++ initC ++ tfC ++ wordC

def r8 (e : Expr) (m : Expr) : Lookup := ⟨Block.Tables.REL_R8, .neg m, [e]⟩

def lookups : List Lookup :=
  [ ⟨REL_NODE, .neg (k MUN), [k CK, p P_W8, k WLO, k WHI]⟩,
    ⟨REL_LEAF, .neg (k MUL), [k CK, p P_W8, k WLO, k WHI]⟩ ] ++
  (List.range 4).flatMap (fun j =>
    [ ⟨REL_NODE, .mul (k USEW) (p (P_FIN j)), [k ID, cst j, limb 0 0, limb 0 1]⟩,
      ⟨REL_NODE, .mul (k USEW) (p (P_FIN j)), [k ID, cst (bidx j), limb 1 0, limb 1 1]⟩ ]) ++
  (List.range 8).map (fun w => ⟨REL_NODE, .neg (p P_FIRST), [cst 1, cst w, .pub (PUB_ROOT (2 * w)), .pub (PUB_ROOT (2 * w + 1))]⟩) ++
  (List.range 3).map (fun i => r8 (k (DD i)) (.mul (k USEW) (p P_R0))) ++
  (List.range 3).map (fun i => r8 (k (UL i)) (.mul (k LU) (p P_R0))) ++
  (List.range 3).map (fun i => r8 (k (UR i)) (.mul (k LU) (p P_R0))) ++
  (List.range 3).map (fun i => r8 (k (EB i)) (p P_FIRST)) ++
  (List.range 3).map (fun i => r8 (k (HB i)) (p P_FIRST))

def mt : Comp where
  air := { name := "set_mt", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.MT
