/-
Median-time-past constraints (header chain v4) and the complete header-chain AIR.

Rule (decision D-018): for every header with time `t` and window `T_1..T_11` (the previous
11 times, newest first), at least 6 of the `T_i` are strictly below `t`. The segment starting
at genesis uses a fixed sentinel history (see `docs/airs/header-chain.md` § v4).

Layout (rows relative to the header; slot `i = row − 228`):

| row | contents |
|-----|----------|
| 229..239 | `a` = `T_i` (raw time word), `e` = `d_i` (numeric 32-bit difference), `w` = own time (raw word), col 108 = `b_i = [T_i < t]`, col 109 = lo-limb carry |
| 240 | `a` bits 0..2 = `Σ b_i − 6` |

Window: `T_1` is the predecessor's time copied at row 220 (`e`); `T_i` (`i ≥ 2`) is the
predecessor's `T_{i−1}` (offset −257), or public input `48 + 2(i−2) + h` on the first header.
The last header's `T_1..T_10` are public outputs `68..87`.
-/
import StarkedAir.Gadgets.Retarget

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256

/-- Slot `i` (1..11) selector: `pre (MTP0 + i − 1)` is 1 on row `228 + i`. -/
def MTP0 : ℕ := 40
/-- Count row (240). -/
def MTPC : ℕ := 51

def slotSel (i : ℕ) : Expr := pre (MTP0 + (i - 1))
/-- 1 on rows 229..239. -/
def mtpRegion : Expr := (List.range 11).foldl (fun acc k => .add acc (pre (MTP0 + k))) (cst 0)

/-- `b_i` and the lo-limb carry. -/
def bE : Expr := col 108
def cE : Expr := col 109
/-- 16-bit limb `h` of the numeric difference `d` (bits of `e`). -/
def dLimb (h : ℕ) : Expr := bitsR E (16 * h) 16 0

/-- `b = 1`: `T + 1 + d = t`; `b = 0`: `t + d = T` (lo limb, with carry out `c`). -/
def cmpLo : Expr :=
  .mul mtpRegion (.add
    (.mul bE (.sub (.add (.add (timeLimb A 0 0) (cst 1)) (dLimb 0)) (.add (timeLimb W 0 0) (.mul (cst 65536) cE))))
    (.mul (.sub (cst 1) bE) (.sub (.add (timeLimb W 0 0) (dLimb 0)) (.add (timeLimb A 0 0) (.mul (cst 65536) cE)))))

/-- Hi limb, with carry in `c` and no carry out. -/
def cmpHi : Expr :=
  .mul mtpRegion (.add
    (.mul bE (.sub (.add (.add (timeLimb A 1 0) (dLimb 1)) cE) (timeLimb W 1 0)))
    (.mul (.sub (cst 1) bE) (.sub (.add (.add (timeLimb W 1 0) (dLimb 1)) cE) (timeLimb A 1 0))))

/-- Own time `t` in `w` on every slot row: from header word 17 (row 77), then copied down. -/
def ownTime (h : ℕ) : List Expr :=
  .mul (slotSel 1) (.sub (limb W h) (limb W h (-152))) ::
    (List.range 10).map (fun k => .mul (slotSel (k + 2)) (.sub (limb W h) (limb W h (-1))))

/-- The window `T_1..T_11` in `a`. -/
def window (h : ℕ) : List Expr :=
  .mul (slotSel 1) (.sub (limb A h) (limb E h (-9))) ::
    (List.range 10).flatMap (fun k =>
      [ .mul (.mul (slotSel (k + 2)) notFirst) (.sub (limb A h) (limb A h (-257))),
        .mul (.mul (slotSel (k + 2)) (pre FIRST)) (.sub (limb A h) (.pub (48 + 2 * k + h))) ])

/-- The last header's `T_1..T_10` are public outputs. -/
def windowOut (h : ℕ) : List Expr :=
  (List.range 10).map (fun k => .mul (.mul (slotSel (k + 1)) (pre LAST)) (.sub (limb A h) (.pub (68 + 2 * k + h))))

/-- `Σ_i b_i − 6 = r` with `r` in 3 bits, so at least 6 slots are below `t`. -/
def countC : Expr :=
  .mul (pre MTPC) (.sub (.sub
    ((List.range 11).foldl (fun acc k => .add acc (col 108 (-((11 - k : ℕ) : ℤ)))) (cst 0)) (cst 6))
    (bitsR A 0 3 0))

def mtpCs : List Expr :=
  [0, 1].flatMap (fun h => ownTime h ++ window h ++ windowOut h) ++ [cmpLo, cmpHi, countC]

def constraints : List Expr := baseConstraints ++ powCs ++ stateCs ++ copyCs ++ retargetCs ++ mtpCs

def air : Air := { name := "header_chain_v4", nMain := Sha256.N_MAIN, pre := preCols, constraints }

end StarkedAir.HeaderChain
