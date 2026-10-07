/-
Difficulty retarget constraints (header chain v3b): at a header whose height is a positive
multiple of 2016, its nBits must equal Bitcoin Core's `GetNextWorkRequired` (mainnet).

Layout (rows relative to the header; all values in bit columns):

| row | contents |
|-----|----------|
| 220 | `a` = previous header's nBits word, `e` = previous header's time word, `w` = previous pst word (copies; public for the first header) |
| 221 | `a` bits 0..26 = previous exponent one-hot; `e` bits 0..22 = clamped span; `w` bits: 0 `rt`, 1 `nz`, 2 `lo`, 3 `mid`, 4 `hi`, 5 `d₋₁`, 6 `d₀`, 7 `d₊₁`, 8 `cap`, 9 `kp`, 10 `kn` |
| 222 | `a` bits 0..22 = `span − 302400`; `e` bits 0..22 = `4838400 − span`; `w` = slack `v` (bits 0..31), carry col 108 = `v` bit 32, col 114 = time carry |
| 223 | `P0 = mant_prev · span`: bytes 0..3 in `a`, 4..5 in `e` bits 0..15 |
| 224 | product carries (10 bits each): `a` = 0,1,2; `e` = 3,4 |
| 225 | remainder `ρ` bytes 0..3 in `a`, byte 4 in `e` bits 0..7; `σ = div − 1 − ρ` bytes 0..3 in `w` |
| 226 | `σ` byte 4 in `a` bits 0..7; division carries 0..3 in `e` (8 bits each), 4..7 in `w` |
| 227 | `a` bits 0..9: σ carries (2 bits each); `e` bits 0..22: `mant' − 0x8000`; `w` bits 0..19: `q − 1` |
| 228 | cap slack `τ` bytes 0..3 in `a`, 4..5 in `e` bits 0..15; cap carries (4 bits each) in `w` bits 0..23 |

Every constraint has degree ≤ 3. The only product of two variable values (`mant_prev ·
span`) is enforced on every header (not gated), so the gating factors stay within degree 3.
-/
import StarkedAir.Gadgets.HeaderChain

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256

def PREV : ℕ := 38
def RT : ℕ := 39


/-! ### Expression helpers (all at the retarget row 221; `o` = row offset) -/

/-- `k` bits of column `base + lo …` at row offset `o`. -/
def bitsR (base lo k : ℕ) (o : ℤ) : Expr := sumPow (fun i => col (base + lo + i) o) k
def bitR (base i : ℕ) (o : ℤ) : Expr := col (base + i) o

/-- Byte `i` (0 = most significant) of the 32-bit word in columns `base…`, at offset `o`.
For the nBits and time fields this is little-endian numeric byte `i`. -/
def beByte (base i : ℕ) (o : ℤ) : Expr := bitsR base (8 * (3 - i)) 8 o

def wctl (i : ℕ) : Expr := bitR W i 0
def rtE : Expr := wctl 0
def nzE : Expr := wctl 1
def loE : Expr := wctl 2
def midE' : Expr := wctl 3
def hiE : Expr := wctl 4
def dE' (k : ℕ) : Expr := wctl (5 + k)       -- k = 0: d = −1, 1: d = 0, 2: d = +1
def capE : Expr := wctl 8
def kpE : Expr := wctl 9
def knE : Expr := wctl 10

def ohP (s : ℕ) : Expr := bitR A s 0
def spanE : Expr := bitsR E 0 23 0
def spanLo : Expr := bitsR E 0 16 0
def spanHi : Expr := bitsR E 16 7 0

/-- Previous nBits (row 220): exponent and mantissa bytes. -/
def prevExp : Expr := beByte A 3 (-1)
def prevMant (i : ℕ) : Expr := if i < 2 then beByte A i (-1) else bitsR A 8 7 (-1)
/-- Own nBits (header word 18, row 78 = offset −143): mantissa bytes. -/
def ownMant (i : ℕ) : Expr := if i < 2 then beByte W i (-143) else bitsR W 8 7 (-143)
def ownMantE : Expr := .add (.add (ownMant 0) (.mul (cst 256) (ownMant 1))) (.mul (cst 65536) (ownMant 2))
/-- Span bytes. -/
def spanByte (i : ℕ) : Expr := if i < 2 then bitsR E (8 * i) 8 0 else bitsR E 16 7 0

/-- Numeric 16-bit limbs of a little-endian time field held as a raw word. -/
def timeLimb (base h : ℕ) (o : ℤ) : Expr :=
  .add (beByte base (2 * h) o) (.mul (cst 256) (beByte base (2 * h + 1) o))

def p0Byte (k : ℕ) : Expr := if k < 4 then bitsR A (8 * k) 8 2 else if k < 6 then bitsR E (8 * (k - 4)) 8 2 else cst 0
def mcE (k : ℕ) : Expr := if k < 3 then bitsR A (10 * k) 10 3 else bitsR E (10 * (k - 3)) 10 3
def rhoByte (k : ℕ) : Expr := if k < 4 then bitsR A (8 * k) 8 4 else if k = 4 then bitsR E 0 8 4 else cst 0
def sigByte (k : ℕ) : Expr := if k < 4 then bitsR W (8 * k) 8 4 else if k = 4 then bitsR A 0 8 5 else cst 0
def dcE (k : ℕ) : Expr := if k < 4 then bitsR E (8 * k) 8 5 else bitsR W (8 * (k - 4)) 8 5
def scE (k : ℕ) : Expr := bitsR A (2 * k) 2 6
def tauByte (k : ℕ) : Expr := if k < 4 then bitsR A (8 * k) 8 7 else if k < 6 then bitsR E (8 * (k - 4)) 8 7 else cst 0
def ccE (k : ℕ) : Expr := bitsR W (4 * k) 4 7

/-- Little-endian bytes of the divisors `1209600 · 256^(1+d)` and of `divisor − 1`. -/
def divBytes : ℕ → List ℕ
  | 0 => [0x00, 0x75, 0x12]
  | 1 => [0x00, 0x00, 0x75, 0x12]
  | _ => [0x00, 0x00, 0x00, 0x75, 0x12]
def divM1Bytes : ℕ → List ℕ
  | 0 => [0xff, 0x74, 0x12]
  | 1 => [0xff, 0xff, 0x74, 0x12]
  | _ => [0xff, 0xff, 0xff, 0x74, 0x12]

/-- `Σ_d d-flag · c_d`. -/
def byD (f : ℕ → Expr) : Expr := .add (.add (.mul (dE' 0) (f 0)) (.mul (dE' 1) (f 1))) (.mul (dE' 2) (f 2))
def dAny : Expr := .add (.add (dE' 0) (dE' 1)) (dE' 2)

/-- Cap thresholds `1209600 · 256^(28 − s)` for `s = 25, 26`. -/
def capThr25 : List ℕ := [0, 0, 0, 0, 0x75, 0x12]
def capThr26 : List ℕ := [0, 0, 0, 0x75, 0x12]

def sumCol (k : ℕ) (f : ℕ → ℕ → Expr) (ni nj : ℕ) : Expr :=
  ((List.range ni).flatMap fun i => (List.range nj).filterMap fun j => if i + j = k then some (f i j) else none).foldl
    .add (cst 0)

/-! ### Constraints -/

def copySelNF : Expr := .mul (pre PREV) (.sub (cst 1) (pre FIRST))
def copySelF : Expr := .mul (pre PREV) (pre FIRST)

/-- Copies of the predecessor's nBits, time and pst at row 220 (and the last header's time
as output). -/
def copyFam (h : ℕ) : List Expr :=
  [ .mul copySelNF (.sub (limb A h) (limb W h (-398))), .mul copySelF (.sub (limb A h) (.pub (34 + h))),
    .mul copySelNF (.sub (limb E h) (limb W h (-399))), .mul copySelF (.sub (limb E h) (.pub (44 + h))),
    .mul copySelNF (.sub (limb W h) (limb E h (-258))), .mul copySelF (.sub (limb W h) (.pub (36 + h))),
    .mul (.mul (pre PREV) (pre LAST)) (.sub (limb W h (-143)) (.pub (46 + h))) ]

def copyCs : List Expr := [0, 1].flatMap copyFam

def rtSel : Expr := pre RT
def flagAt : Expr := col W (-3)
def qAt : Expr := sumPow (fun i => col (A + i) (-2)) 20
def ohSum : Expr := (List.range 27).foldl (fun acc s => .add acc (ohP s)) (cst 0)
def ohWeighted : Expr := (List.range 27).foldl (fun acc s => .add acc (.mul (cst s) (ohP s))) (cst 0)
def ownOhWeighted : Expr := (List.range 27).foldl (fun acc s => .add acc (.mul (cst s) (col (A + s) (-5)))) (cst 0)

def rtBase : List Expr :=
  let sel := rtSel
  let one := cst 1
  [ -- rt = boundary ∧ height > 0;  nz ↔ q ≥ 1.
    .mul sel (.sub rtE (.mul flagAt nzE)),
    .mul (.mul sel nzE) (.sub (.sub qAt one) (bitsR W 0 20 6)),
    .mul (.mul sel (.sub one nzE)) qAt,
    -- previous exponent one-hot (only when rt).
    .mul sel (.sub ohSum rtE),
    .mul sel (.sub (.mul rtE (.sub prevExp (cst 3))) ohWeighted),
    -- clamp branch flags.
    .mul sel (.sub (.add (.add loE midE') hiE) rtE),
    -- mid: prevTime = pst + span exactly, span ∈ [302400, 4838400].
    .mul (.mul sel midE') (.sub (.add (timeLimb W 0 (-1)) spanLo)
      (.add (timeLimb E 0 (-1)) (.mul (cst 65536) (col CE_LO 1)))),
    .mul (.mul sel midE') (.sub (.add (.add (timeLimb W 1 (-1)) spanHi) (col CE_LO 1)) (timeLimb E 1 (-1))),
    .mul (.mul sel midE') (.sub (.sub spanE (cst 302400)) (bitsR A 0 23 1)),
    .mul (.mul sel midE') (.sub (.sub (cst 4838400) spanE) (bitsR E 0 23 1)),
    -- lo: span = 302400 and pst + 302399 = prevTime + v (v ≥ 0).
    .mul (.mul sel loE) (.sub spanE (cst 302400)),
    .mul (.mul sel loE) (.sub (.add (.add (timeLimb W 0 (-1)) (cst (302399 % 65536))) (.mul (cst 65536) knE))
      (.add (.add (timeLimb E 0 (-1)) (bitsR W 0 16 1)) (.mul (cst 65536) kpE))),
    .mul (.mul sel loE) (.sub (.add (.add (timeLimb W 1 (-1)) (cst (302399 / 65536))) kpE)
      (.add (.add (.add (timeLimb E 1 (-1)) (bitsR W 16 16 1)) (.mul (cst 65536) (col CA_LO 1))) knE)),
    -- hi: span = 4838400 and prevTime = pst + 4838401 + v (v ≥ 0).
    .mul (.mul sel hiE) (.sub spanE (cst 4838400)),
    .mul (.mul sel hiE) (.sub (.add (.add (.add (timeLimb W 0 (-1)) (cst (4838401 % 65536))) (bitsR W 0 16 1))
        (.mul (cst 65536) knE))
      (.add (timeLimb E 0 (-1)) (.mul (cst 65536) kpE))),
    .mul (.mul sel hiE) (.sub (.add (.add (.add (.add (timeLimb W 1 (-1)) (cst (4838401 / 65536))) (bitsR W 16 16 1))
        (.mul (cst 65536) (col CA_LO 1))) kpE) (.add (timeLimb E 1 (-1)) knE)) ]

/-- P0 = mant_prev · span, byte-wise (ungated by rt): column k. -/
def p0Col (k : ℕ) : Expr :=
  .mul rtSel (.sub (.add (sumCol k (fun i j => .mul (prevMant i) (spanByte j)) 3 3)
      (if k = 0 then cst 0 else mcE (k - 1)))
    (.add (p0Byte k) (if k < 5 then .mul (cst 256) (mcE k) else cst 0)))

def dHead : List Expr :=
  [ -- division branch flags: exactly one when rt ∧ ¬cap; cap only when rt.
    .mul rtSel (.sub (.add dAny capE) rtE),
    -- s' − s_prev = d.
    .mul (.mul rtSel dAny) (.sub (.sub ownOhWeighted ohWeighted) (.sub (dE' 2) (dE' 0))),
    -- canonical mantissa: mant' ≥ 0x8000.
    .mul (.mul rtSel dAny) (.sub (.sub ownMantE (cst 0x8000)) (bitsR E 0 23 6)) ]

/-- divisor · mant' + ρ = 256 · P0, column k (k = 0..7). -/
def divCol (k : ℕ) : Expr :=
  .mul rtSel (.sub (.add (.add (byD fun d => sumCol k (fun i j => .mul (cst ((divBytes d).getD i 0)) (ownMant j)) 5 3)
        (.mul dAny (rhoByte k))) (.mul dAny (if k = 0 then cst 0 else dcE (k - 1))))
    (.mul dAny (.add (if k = 0 then cst 0 else p0Byte (k - 1)) (if k < 7 then .mul (cst 256) (dcE k) else cst 0))))

/-- ρ + σ = divisor − 1, column k (k = 0..4). -/
def remCol (k : ℕ) : Expr :=
  .mul rtSel (.sub (.add (.mul dAny (.add (rhoByte k) (sigByte k))) (.mul dAny (if k = 0 then cst 0 else scE (k - 1))))
    (.add (byD fun d => cst ((divM1Bytes d).getD k 0)) (.mul dAny (if k < 4 then .mul (cst 256) (scE k) else cst 0))))

def capHead : List Expr :=
  [ -- cap: s_prev ∈ {25, 26}, own nBits = 0x1d00ffff (raw word 0xffff001d).
    .mul (.mul rtSel capE) (.sub (.add (ohP 25) (ohP 26)) (cst 1)),
    .mul (.mul rtSel capE) (.sub (limb W 0 (-143)) (cst 0x001d)),
    .mul (.mul rtSel capE) (.sub (limb W 1 (-143)) (cst 0xffff)) ]

/-- cap: P0 = threshold(s_prev) + τ, column k (k = 0..5). -/
def capCol (k : ℕ) : Expr :=
  .mul (.mul rtSel capE) (.sub (.add (.add (.add (.mul (ohP 25) (cst (capThr25.getD k 0))) (.mul (ohP 26) (cst (capThr26.getD k 0))))
      (tauByte k)) (if k = 0 then cst 0 else ccE (k - 1)))
    (.add (p0Byte k) (if k < 5 then .mul (cst 256) (ccE k) else cst 0)))

def retargetCs : List Expr :=
  rtBase ++ (List.range 6).map p0Col ++ dHead ++ (List.range 8).map divCol ++ (List.range 5).map remCol ++
    capHead ++ (List.range 6).map capCol

end StarkedAir.HeaderChain
