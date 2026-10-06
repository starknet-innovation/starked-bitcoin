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
def POW : ℕ := 36
def STATE : ℕ := 37

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
  (List.range 4).map (fun j => oneRow (212 + j)) ++                                  -- 32..35 OUT_j
  [ oneRow 216,                                                                       -- 36 POW
    oneRow 218,                                                                       -- 37 STATE
    oneRow 220,                                                                       -- 38 PREV (retarget copies)
    oneRow 221 ]                                                                      -- 39 RT (retarget)

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

/-- SHA256d, linkage and endpoint constraints (v1). -/
def baseConstraints : List Expr := Sha256.constraints ++ plumbing ++ linkage ++ outputs

/-! ### Proof of work (row 216 of each header; scratch in rows 216–217)

Row 216 reuses bit columns as scratch: `A` bits 0..26 are a one-hot `s = nSize − 3`;
`E` bits 0..23 are `D`; `W` bit 0 is `lt`; `W` bits 1..23 are `mant − 1`. Row 217's `A` bits
0..12 hold `L`, the sum of the hash bytes below the mantissa position. The hash is read from
rows 212..215 and `nBits` from header word 18 (row 78). -/

/-- Bit `k` of hash byte `i` (internal byte order): word `i/4`, bits `8·(3 − i%4) + k`.
Words 0..3 are `a` at rows 215..212, words 4..7 are `e` at rows 215..212. -/
def hashBit (i k : ℕ) : Expr :=
  let w := i / 4
  let b := 8 * (3 - i % 4) + k
  if w < 4 then col (A + b) (-((1 + w : ℕ) : ℤ)) else col (E + b) (-((1 + (w - 4) : ℕ) : ℤ))

def hashByteE (i : ℕ) : Expr := sumPow (hashBit i) 8

/-- Bit `k` of header word 18 (nBits, byte-swapped), 138 rows up. -/
def nbBit (k : ℕ) : Expr := col (W + k) (-138)

/-- `nSize`: header byte 75 = word-18 bits 0..7. -/
def expE : Expr := sumPow nbBit 8

/-- `nWord = nBits & 0x7fffff`: bytes 72, 73 and the low 7 bits of byte 74. -/
def mantBit (t : ℕ) : Expr := if t < 8 then nbBit (24 + t) else if t < 16 then nbBit (8 + t) else nbBit (t - 8)

def mantE : Expr := sumPow mantBit 23

/-- Σ_{i ∈ [s, 32)} byte_i. -/
def suffixE (s : ℕ) : Expr := ((List.range 32).filter (s ≤ ·)).foldl (fun acc i => .add acc (hashByteE i)) (cst 0)

/-- Σ_{i < s} byte_i. -/
def prefixE (s : ℕ) : Expr := (List.range s).foldl (fun acc i => .add acc (hashByteE i)) (cst 0)

def midE (s : ℕ) : Expr :=
  .add (.add (hashByteE s) (.mul (cst 256) (hashByteE (s + 1)))) (.mul (cst 65536) (hashByteE (s + 2)))

def ohE (s : ℕ) : Expr := col (A + s)

/-- `Σ_{s ≤ 26} oh_s · f s`. -/
def selectE (f : ℕ → Expr) : Expr :=
  (List.range 27).foldl (fun acc s => .add acc (.mul (ohE s) (f s))) (cst 0)

def dE : Expr := sumPow (fun k => col (E + k)) 24
def ltE : Expr := col W
def m1E : Expr := sumPow (fun k => col (W + 1 + k)) 23
def lE : Expr := sumPow (fun k => col (A + k) 1) 13

def powCs : List Expr :=
  let sel := pre POW
  [ .mul sel (.sub (selectE (fun _ => cst 1)) (cst 1)),                          -- exactly one s
    .mul sel (.sub (.sub expE (cst 3)) (selectE (fun s => cst s))),               -- s = nSize − 3
    .mul sel (nbBit 15),                                                          -- not negative
    .mul sel (selectE (fun s => suffixE (s + 3))),                                -- high bytes zero
    .mul sel (.sub (.sub (.sub mantE (selectE midE)) ltE) dE),                    -- mant = mid + lt + D
    .mul sel (.mul (.sub (cst 1) ltE) dE),                                        -- ¬lt → D = 0
    .mul sel (.sub lE (selectE prefixE)),                                         -- L = low-byte sum
    .mul sel (.mul (.sub (cst 1) ltE) lE),                                        -- ¬lt → low bytes zero
    .mul sel (.sub (.sub mantE (cst 1)) m1E),                                     -- mant ≥ 1
    .mul sel (.mul (ohE 26) (sumPow (fun t => nbBit (8 + t)) 7)) ]                -- powLimit

/-! ### Chain state (row 218 of each header; scratch in rows 218–219)

Row 218: `A` = height (30 bits; bits 30, 31 zero), `E` = period-start time `pst` (raw header
word-17 form), `W` bit 0 = boundary flag, bits 1..11 = `rem = height mod 2016`,
bits 12..22 = `rem − 1` (when not a boundary), bit 23 = `g = ¬first ∧ ¬boundary`,
bit 24 = `g2 = first ∧ ¬boundary`; carry column `CA_LO` bit 0 = carry of the height
increment. Row 219: `A` bits 0..19 = `q = height / 2016`; `E` bits 0..10 = `2015 − rem`.

Public inputs 32..37: the segment's first height and its predecessor's nBits and pst
(lo/hi limbs). Outputs 38..43: the last header's height, nBits and pst. -/

def bitsAt (base k : ℕ) (off : ℤ := 0) : Expr := sumPow (fun i => col (base + i) off) k
def heightE : Expr := bitsAt A 30
def flagE : Expr := col W
def remE : Expr := bitsAt (W + 1) 11
def remM1E : Expr := bitsAt (W + 12) 11
def gE : Expr := col (W + 23)
def g2E : Expr := col (W + 24)
def qE : Expr := bitsAt A 20 1
def remCompE : Expr := bitsAt E 11 1
def hCarryE : Expr := col CA_LO

def stateSel : Expr := pre STATE
def notFirst : Expr := .sub (cst 1) (pre FIRST)

def stateBase : List Expr :=
  let sel := stateSel
  let first := pre FIRST
  let one := cst 1
  [ -- height: < 2^30, increments from the previous header, or is public for the first one.
    .mul sel (col (A + 30)), .mul sel (col (A + 31)),
    .mul (.mul sel notFirst)
      (.sub (.add (limb A 0 (-256)) one) (.add (limb A 0) (.mul (cst 65536) hCarryE))),
    .mul (.mul sel notFirst) (.sub (.add (limb A 1 (-256)) hCarryE) (limb A 1)),
    .mul (.mul sel first) (.sub (limb A 0) (.pub 32)),
    .mul (.mul sel first) (.sub (limb A 1) (.pub 33)),
    -- height = 2016·q + rem, rem ≤ 2015, flag ↔ rem = 0.
    .mul sel (.sub heightE (.add (.mul (cst 2016) qE) remE)),
    .mul sel (.sub (cst 2015) (.add remE remCompE)),
    .mul (.mul sel flagE) remE,
    .mul (.mul sel (.sub one flagE)) (.sub (.sub remE one) remM1E),
    -- g = ¬first ∧ ¬flag, g2 = first ∧ ¬flag.
    .mul sel (.sub gE (.mul notFirst (.sub one flagE))),
    .mul sel (.sub g2E (.mul first (.sub one flagE))) ]

/-- nBits (word 18, row 78) is constant within a period. -/
def nbitsLink (h : ℕ) : Expr := .mul (.mul stateSel gE) (.sub (limb W h (-140)) (limb W h (-396)))
def nbitsFirst (h : ℕ) : Expr := .mul (.mul stateSel g2E) (.sub (limb W h (-140)) (.pub (34 + h)))
/-- pst resets to the header's own time (word 17, row 77) at a boundary, else carries over. -/
def pstReset (h : ℕ) : Expr := .mul (.mul stateSel flagE) (.sub (limb E h) (limb W h (-141)))
def pstCarry (h : ℕ) : Expr := .mul (.mul stateSel gE) (.sub (limb E h) (limb E h (-256)))
def pstFirst (h : ℕ) : Expr := .mul (.mul stateSel g2E) (.sub (limb E h) (.pub (36 + h)))
/-- Outputs of the last header: height, nBits, pst. -/
def outHeight (h : ℕ) : Expr := .mul (.mul stateSel (pre LAST)) (.sub (limb A h) (.pub (38 + h)))
def outNBits (h : ℕ) : Expr := .mul (.mul stateSel (pre LAST)) (.sub (limb W h (-140)) (.pub (40 + h)))
def outPst (h : ℕ) : Expr := .mul (.mul stateSel (pre LAST)) (.sub (limb E h) (.pub (42 + h)))

def stateFam (h : ℕ) : List Expr :=
  [nbitsLink h, nbitsFirst h, pstReset h, pstCarry h, pstFirst h, outHeight h, outNBits h, outPst h]

def stateCs : List Expr := stateBase ++ [0, 1].flatMap stateFam

-- The full constraint list and `air` are assembled in `Gadgets/Retarget.lean`.

end StarkedAir.HeaderChain
