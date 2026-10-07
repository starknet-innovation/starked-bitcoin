/-
Chainwork constraints (header chain v5).

Per header, with target `T = mant · 256^s` from the proof-of-work row (216) and header word 18:
`q = ⌊2^256 / (T + 1)⌋` (Core `GetBlockProof`), enforced exactly by
`R = q · mant`, `R · 256^s + q + ρ = 2^256` and `ρ + σ = T` (so `0 ≤ ρ ≤ T`), and the running
chainwork `W_j = W_{j−1} + q_j`. Requires `s ≥ 16` (decision D-021), so `q, R < 2^128`.

All values are little-endian byte strings held in bit columns. Constraints sit at row 248
(selector `WORK`) and read rows 241..253 at offsets −7..+5:

| row | a | e | w |
|-----|---|---|---|
| 241 | q 0..3 | q 4..7 | q 8..11 |
| 242 | q 12..15 | R 0..3 | R 4..7 |
| 243 | R 8..11 | R 12..15 | ρ 0..3 |
| 244 | ρ 4..7 | ρ 8..11 | ρ 12..15 |
| 245 | ρ 16..19 | ρ 20..23 | ρ 24..27 |
| 246 | σ 0..3 | σ 4..7 | σ 8..11 |
| 247 | σ 12..15 | σ 16..19 | σ 20..23 |
| 248 | σ 24..27 | W 0..3 | W 4..7 |
| 249 | W 8..11 | W 12..15 | W 16..19 |
| 250 | product carries 0..2 (10 bits each) | 3..5 | 6..8 |
| 251 | 9..11 | 12..14 | 15..16 |
| 252 | main carries 0..15 (2 bits each) | 16..31 | 32..40 |
| 253 | `ρ + σ` carries 0..27 (1 bit) | W carries 0..8 (1 bit) | — |

Public inputs 88..97: chainwork before the segment (10 × 16-bit limbs); 98..107: after it.
-/
import StarkedAir.Gadgets.Mtp

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256

def WORK : ℕ := 52

/-- Offset from the anchor row 248 to `row`, shifted by `sh` (−256 = previous header). -/
def workOff (row : ℕ) (sh : ℤ) : ℤ := (row : ℤ) - 248 + sh

/-- Field `i` (`w` bits, `per` fields per word) of the number laid out over word `slots`. -/
def fieldOf (slots : List (ℕ × ℕ)) (w per : ℕ) (sh : ℤ) (i : ℕ) : Expr :=
  match slots[i / per]? with
  | some (row, X) => bitsR X (w * (i % per)) w (workOff row sh)
  | none => cst 0

def qSlots : List (ℕ × ℕ) := [(241, A), (241, E), (241, W), (242, A)]
def rSlots : List (ℕ × ℕ) := [(242, E), (242, W), (243, A), (243, E)]
def rhoSlots : List (ℕ × ℕ) := [(243, W), (244, A), (244, E), (244, W), (245, A), (245, E), (245, W)]
def sigSlots : List (ℕ × ℕ) := [(246, A), (246, E), (246, W), (247, A), (247, E), (247, W), (248, A)]
def wSlots : List (ℕ × ℕ) := [(248, E), (248, W), (249, A), (249, E), (249, W)]
def pcSlots : List (ℕ × ℕ) := [(250, A), (250, E), (250, W), (251, A), (251, E), (251, W)]
def mcSlots : List (ℕ × ℕ) := [(252, A), (252, E), (252, W)]

def qB (i : ℕ) : Expr := fieldOf qSlots 8 4 0 i
def rB (i : ℕ) : Expr := fieldOf rSlots 8 4 0 i
def rhoB (i : ℕ) : Expr := fieldOf rhoSlots 8 4 0 i
def sigB (i : ℕ) : Expr := fieldOf sigSlots 8 4 0 i
def wB (sh : ℤ) (i : ℕ) : Expr := fieldOf wSlots 8 4 sh i
def pcE (k : ℕ) : Expr := fieldOf pcSlots 10 3 0 k
def mcE' (k : ℕ) : Expr := fieldOf mcSlots 2 16 0 k
def ecE (k : ℕ) : Expr := fieldOf [(253, A)] 1 32 0 k
def wcE (k : ℕ) : Expr := fieldOf [(253, E)] 1 32 0 k

/-- Exponent one-hot bit `s` (row 216). -/
def ohS (s : ℕ) : Expr := col (A + s) (-32)
/-- Mantissa bytes of header word 18 (row 78). -/
def mB (j : ℕ) : Expr :=
  if j < 2 then beByte W j (-170) else if j = 2 then bitsR W 8 7 (-170) else cst 0

/-- `Σ_{i < n} f i` as an expression. -/
def sumE (n : ℕ) (f : ℕ → Expr) : Expr := (List.range n).foldl (fun acc i => .add acc (f i)) (cst 0)

def workSel : Expr := pre WORK

/-- `s ≥ 16`. -/
def sMin : Expr := .mul workSel (sumE 16 ohS)

/-- `R = q · mant`, column `k` (0..17). -/
def prodCol (k : ℕ) : Expr :=
  .mul workSel (.sub (.add (sumE 16 fun i => if i ≤ k ∧ k - i < 3 then .mul (qB i) (mB (k - i)) else cst 0)
      (if k = 0 then cst 0 else pcE (k - 1)))
    (.add (rB k) (if k < 17 then .mul (cst 256) (pcE k) else cst 0)))

/-- `R · 256^s + q + ρ = 2^256`, column `k` (0..41). -/
def mainCol (k : ℕ) : Expr :=
  .mul workSel (.sub (.add (.add (.add (sumE 27 fun s => if 16 ≤ s ∧ s ≤ k ∧ k - s < 16 then .mul (ohS s) (rB (k - s)) else cst 0)
      (qB k)) (rhoB k)) (if k = 0 then cst 0 else mcE' (k - 1)))
    (.add (if k = 32 then cst 1 else cst 0) (if k < 41 then .mul (cst 256) (mcE' k) else cst 0)))

/-- `ρ + σ = T = mant · 256^s`, column `k` (0..28). -/
def rsCol (k : ℕ) : Expr :=
  .mul workSel (.sub (.add (.add (rhoB k) (sigB k)) (if k = 0 then cst 0 else ecE (k - 1)))
    (.add (sumE 27 fun s => if 16 ≤ s ∧ s ≤ k ∧ k - s < 3 then .mul (ohS s) (mB (k - s)) else cst 0)
      (if k < 28 then .mul (cst 256) (ecE k) else cst 0)))

/-- 16-bit limbs of `q` and of the chainwork (`sh = −256`: the previous header's). -/
def qL (l : ℕ) : Expr := .add (qB (2 * l)) (.mul (cst 256) (qB (2 * l + 1)))
def wL (sh : ℤ) (l : ℕ) : Expr := .add (wB sh (2 * l)) (.mul (cst 256) (wB sh (2 * l + 1)))

/-- `W_j = W_{j−1} + q_j`, limb `l` (0..9); `prevW` is the previous chainwork limb. -/
def workAdd (sel prevW : Expr) (l : ℕ) : Expr :=
  .mul sel (.sub (.add (.add prevW (qL l)) (if l = 0 then cst 0 else wcE (l - 1)))
    (.add (wL 0 l) (if l < 9 then .mul (cst 65536) (wcE l) else cst 0)))

def workFam (l : ℕ) : List Expr :=
  [ workAdd (.mul workSel notFirst) (wL (-256) l) l,
    workAdd (.mul workSel (pre FIRST)) (.pub (88 + l)) l,
    .mul (.mul workSel (pre LAST)) (.sub (wL 0 l) (.pub (98 + l))) ]

def workCs : List Expr :=
  sMin :: (List.range 18).map prodCol ++ (List.range 42).map mainCol ++ (List.range 29).map rsCol ++
    (List.range 10).flatMap workFam

end StarkedAir.HeaderChain
