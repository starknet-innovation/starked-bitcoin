/-
**Ancestry (D-043 part 3, option A): the previous-block MTP inside the block proof.** The 16th component
of the block system. Its trace is a header chain of 256-row periods laid out exactly as the header-chain
AIR's (`Gadgets/HeaderChain.lean`: SHA256d at rows 0–215, the same preprocessed columns), with the
header chain's SHA, plumbing and prev-hash linkage constraints. When the CSV bit (public input 5) is set:

* period 11's hash is the block hash (public inputs 25–40), so periods 0–10 are the block's 11
  predecessors, oldest first, each committing to the previous one's hash;
* the previous MTP (public inputs 3 and 7, its 16-bit limbs) is compared with each predecessor's time:
  at most 5 of the 11 times are above it and at most 5 below, so it is their median (Core's
  `GetMedianTimePast`);
* the trace has at least 4096 rows (12 periods fit).

Below the CSV height the MTP is unused (the lock-time cutoff is the block's own time) and public inputs 3
and 7 are 0. The timestamps are not public.

Layout per period (rows relative to the period): rows 229 (slot 1) and 230 (slot 2) compare, in the
header chain's `cmpLo`/`cmpHi` form, `a` against `w` (raw time words, `e` the 32-bit difference, column
108 the flag `[a < w]`, 109 the carry). Row 229: `a` = the MTP, `w` = the header's time (row 77); row 230:
`a` = the header's time, `w` = the MTP. Period 0, row 240: the two counts' slack in `a` and `e` bits 0..2.
Column 124 is a copy of the preprocessed `FIRST`.
-/
import StarkedAir.Gadgets.Mtp
import StarkedAir.Lookup

namespace StarkedAir.Block.Anc

open StarkedAir StarkedAir.Sha256 StarkedAir.HeaderChain

def PUB_MLO : ℕ := 3
def PUB_CSV : ℕ := 5
def PUB_MHI : ℕ := 7
def PUB_HASH : ℕ := 25
/-- Number of predecessors; the block header is period `NANC`. -/
def NANC : ℕ := 11

def act : Expr := .pub PUB_CSV
/-- Limb `h` of the MTP. -/
def mpub (h : ℕ) : Expr := .pub (if h = 0 then PUB_MLO else PUB_MHI)

/-- The header chain's prev-hash linkage for every header but the first (`HeaderChain.linkage`'s first
family). -/
def linkNF : List Expr :=
  (List.range 8).flatMap (fun k =>
    eqLimbs (.mul (pre (LINK0 + k)) (.sub (cst 1) (pre FIRST))) W 0 (fun h => limb (linkSrc k).1 h (linkSrc k).2))

/-- Period `NANC`'s hash is the block hash: at period 0's rows `212 + j`, read `NANC` periods down. -/
def hashOut : List Expr :=
  (List.range 4).flatMap (fun j =>
    eqLimbs (.mul (.mul (pre (OUT0 + j)) (pre FIRST)) act) A (256 * NANC) (fun h => .pub (PUB_HASH + 2 * (3 - j) + h)) ++
    eqLimbs (.mul (.mul (pre (OUT0 + j)) (pre FIRST)) act) E (256 * NANC) (fun h => .pub (PUB_HASH + 2 * (7 - j) + h)))

/-- Slots 1 and 2. -/
def cmpSel : Expr := .add (slotSel 1) (slotSel 2)

/-- `b = 1`: `a + 1 + d = w`; `b = 0`: `w + d = a` (lo limb, carry out `c`), as `HeaderChain.cmpLo`. -/
def ancLo : Expr :=
  .mul cmpSel (.add
    (.mul bE (.sub (.add (.add (timeLimb A 0 0) (cst 1)) (dLimb 0)) (.add (timeLimb W 0 0) (.mul (cst 65536) cE))))
    (.mul (.sub (cst 1) bE) (.sub (.add (timeLimb W 0 0) (dLimb 0)) (.add (timeLimb A 0 0) (.mul (cst 65536) cE)))))

/-- Hi limb, carry in `c`, no carry out. -/
def ancHi : Expr :=
  .mul cmpSel (.add
    (.mul bE (.sub (.add (.add (timeLimb A 1 0) (dLimb 1)) cE) (timeLimb W 1 0)))
    (.mul (.sub (cst 1) bE) (.sub (.add (.add (timeLimb W 1 0) (dLimb 1)) cE) (timeLimb A 1 0))))

/-- Slot 1: `a` = MTP, `w` = the header's time; slot 2: `a` = the header's time, `w` = MTP. -/
def operands (h : ℕ) : List Expr :=
  [ .mul (slotSel 1) (.sub (timeLimb A h 0) (mpub h)),
    .mul (slotSel 1) (.sub (limb W h) (limb W h (-152))),
    .mul (slotSel 2) (.sub (limb A h) (limb W h (-153))),
    .mul (slotSel 2) (.sub (timeLimb W h 0) (mpub h)) ]

/-- Flag of slot `s` (229 or 230) of period `k`, read from period 0's row 240. -/
def flagAt (s k : ℕ) : Expr := col 108 ((256 * k : ℕ) + (s : ℤ) - 240)

def countSum (s : ℕ) : Expr := (List.range NANC).foldl (fun acc k => .add acc (flagAt s k)) (cst 0)

/-- At period 0's row 240: `Σ_k [MTP < t_k] + r₁ = 5` and `Σ_k [t_k < MTP] + r₂ = 5`, `r` in 3 bits. -/
def counts : List Expr :=
  [ .mul (.mul (.mul (pre MTPC) (pre FIRST)) act) (.sub (.add (countSum 229) (bitsR A 0 3 0)) (cst 5)),
    .mul (.mul (.mul (pre MTPC) (pre FIRST)) act) (.sub (.add (countSum 230) (bitsR E 0 3 0)) (cst 5)) ]

/-- Column 124 copies `FIRST` (the prover reads preprocessed columns at offset 0 only). -/
def FCOPY : ℕ := Sha256.N_MAIN

/-- The CSV bit is boolean; without it the MTP limbs are 0; with it the trace has more than 2048 rows
(`FIRST` read 2048 rows down is 1 exactly when the trace has at most 2048 rows). -/
def gates : List Expr :=
  [ .mul act (.sub act (cst 1)),
    .mul (.sub (cst 1) act) (.pub PUB_MLO),
    .mul (.sub (cst 1) act) (.pub PUB_MHI),
    .sub (col FCOPY) (pre FIRST),
    .mul (.mul act (pre FIRST)) (col FCOPY 2048) ]

def ancCs : List Expr := hashOut ++ ([0, 1].flatMap operands) ++ [ancLo, ancHi] ++ counts ++ gates

def constraints : List Expr := Sha256.constraints ++ plumbing ++ linkNF ++ ancCs

def anc : Comp where
  air := { name := "block_anc", nMain := Sha256.N_MAIN + 1, pre := HeaderChain.preCols, constraints := constraints }
  lookups := []

end StarkedAir.Block.Anc
