/-
Bitcoin header-chain AIR (v1: SHA256d + linkage).

One header per 256-row period:

| rows     | role |
|----------|------|
| 0–71     | compression 0: IV, header bytes 0..63 |
| 72–143   | compression 1: output of 0, header bytes 64..79 + padding |
| 144–215  | compression 2: IV, digest of 1 + padding → block hash (rows 212–215) |
| 216–255  | reserved (proof-of-work and difficulty checks, later) |

The columns are those of `Sha256.air` (its constraints are included verbatim), plus
plumbing constraints over limbs:
* `IV`: the init rows of compressions 0 and 2 hold the SHA-256 IV.
* `CHAIN`: the init rows of compression 1 equal the finalize rows of compression 0.
* `WCONST`: the padding words of compressions 1 and 2.
* `MSG_k`: word `k < 8` of compression 2's message is digest word `k` of compression 1.
* `LINK_k`: header words 1..8 (prev hash) equal the previous header's hash words, except for
  the first header, where they equal public inputs 0..15 (8 words × lo/hi).
* `OUT_j`: the last header's hash equals public inputs 16..31.

Bitcoin's prev-hash field (header bytes 4..35) is the previous SHA256d digest in internal byte
order, which is exactly digest words H0..H7 read big-endian, i.e. header words 1..8.
-/
import StarkedAir.Gadgets.Sha256

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256

def PERIOD : ℕ := 256

/-! ### Preprocessed columns (0..4 are SHA's selectors, laid out on three blocks) -/

def IS_IV : ℕ := 5
def IVA_LO : ℕ := 6
def IVE_LO : ℕ := 8
def IS_CHAIN : ℕ := 10
def IS_WCONST : ℕ := 11
def WC_LO : ℕ := 12
def MSG0 : ℕ := 14
def LINK0 : ℕ := 22
def FIRST : ℕ := 30
def LAST : ℕ := 31
def OUT0 : ℕ := 32

def ivWords : List ℕ :=
  [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Padding words: compression 1 words 4..15 (rows 80..91), compression 2 words 8..15
(rows 156..163). -/
def padWord (q : ℕ) : ℕ :=
  if q = 80 then 0x80000000 else if q = 91 then 640
  else if q = 156 then 0x80000000 else if q = 163 then 256 else 0

def isPadRow (q : ℕ) : Bool := (80 ≤ q && q < 92) || (156 ≤ q && q < 164)

/-- SHA selector `i` (< 5) over a header period: SHA's block pattern on rows < 216. -/
def shaSel (i q : ℕ) : ℕ :=
  if q < 216 then (Sha256.preCols.getD i (.periodic [0])).eval 72 (q % 72) |>.val else 0

def periodic256 (f : ℕ → ℕ) : PreCol := .periodic ((List.range PERIOD).map f)
def oneRow (row : ℕ) : PreCol := periodic256 (fun q => if q = row then 1 else 0)

def preCols : List PreCol :=
  (List.range 5).map (fun i => periodic256 (shaSel i)) ++
  [ periodic256 (fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then 1 else 0),          -- 5 IS_IV
    periodic256 (fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (3 - q % 4) 0 % 2 ^ 16 else 0),
    periodic256 (fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (3 - q % 4) 0 / 2 ^ 16 else 0),
    periodic256 (fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (7 - q % 4) 0 % 2 ^ 16 else 0),
    periodic256 (fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (7 - q % 4) 0 / 2 ^ 16 else 0),
    periodic256 (fun q => if 72 ≤ q ∧ q < 76 then 1 else 0),                          -- 10 IS_CHAIN
    periodic256 (fun q => if isPadRow q then 1 else 0),                               -- 11 IS_WCONST
    periodic256 (fun q => padWord q % 2 ^ 16),                                        -- 12 WC_LO
    periodic256 (fun q => padWord q / 2 ^ 16) ] ++                                    -- 13 WC_HI
  (List.range 8).map (fun k => oneRow (148 + k)) ++                                  -- 14..21 MSG_k
  (List.range 8).map (fun k => oneRow (5 + k)) ++                                    -- 22..29 LINK_k
  [ .rowLt PERIOD, .rowGeEnd PERIOD ] ++                                              -- 30, 31
  (List.range 4).map (fun j => oneRow (212 + j))                                     -- 32..35 OUT_j

/-! ### Constraints -/

/-- `sel · (limb X h @ offX − rhs)` for both halves, where `rhs h` is the right-hand side. -/
def eqLimbs (sel : Expr) (X : ℕ) (offX : ℤ) (rhs : ℕ → Expr) : List Expr :=
  [0, 1].map fun h => .mul sel (.sub (limb X h offX) (rhs h))

/-- Message word `k` of compression 2 comes from digest word `k` of compression 1:
words 0..3 are `a` at rows 143..140, words 4..7 are `e` at rows 143..140. -/
def msgSrc (k : ℕ) : ℕ × ℤ :=
  if k < 4 then (A, -((5 + 2 * k : ℕ) : ℤ)) else (E, -((9 + 2 * (k - 4) : ℕ) : ℤ))

/-- Header word `k + 1` (prev-hash word `k`) of the next header comes from hash word `k`:
words 0..3 are `a` at rows 215..212, words 4..7 are `e` at rows 215..212, one period up. -/
def linkSrc (k : ℕ) : ℕ × ℤ :=
  if k < 4 then (A, -((46 + 2 * k : ℕ) : ℤ)) else (E, -((50 + 2 * (k - 4) : ℕ) : ℤ))

def plumbing : List Expr :=
  eqLimbs (pre IS_IV) A 0 (fun h => pre (IVA_LO + h)) ++
  eqLimbs (pre IS_IV) E 0 (fun h => pre (IVE_LO + h)) ++
  eqLimbs (pre IS_CHAIN) A 0 (fun h => limb A h (-4)) ++
  eqLimbs (pre IS_CHAIN) E 0 (fun h => limb E h (-4)) ++
  eqLimbs (pre IS_WCONST) W 0 (fun h => pre (WC_LO + h)) ++
  (List.range 8).flatMap (fun k =>
    eqLimbs (pre (MSG0 + k)) W 0 (fun h => limb (msgSrc k).1 h (msgSrc k).2))

def linkage : List Expr :=
  (List.range 8).flatMap (fun k =>
    eqLimbs (.mul (pre (LINK0 + k)) (.sub (cst 1) (pre FIRST))) W 0
      (fun h => limb (linkSrc k).1 h (linkSrc k).2) ++
    eqLimbs (.mul (pre (LINK0 + k)) (pre FIRST)) W 0 (fun h => .pub (2 * k + h)))

/-- Row `212 + j` holds hash words `3 − j` (in `a`) and `7 − j` (in `e`). -/
def outputs : List Expr :=
  (List.range 4).flatMap (fun j =>
    eqLimbs (.mul (pre (OUT0 + j)) (pre LAST)) A 0 (fun h => .pub (16 + 2 * (3 - j) + h)) ++
    eqLimbs (.mul (pre (OUT0 + j)) (pre LAST)) E 0 (fun h => .pub (16 + 2 * (7 - j) + h)))

def constraints : List Expr := Sha256.constraints ++ plumbing ++ linkage ++ outputs

def air : Air := { name := "header_chain_v1", nMain := Sha256.N_MAIN, pre := preCols, constraints }

end StarkedAir.HeaderChain
