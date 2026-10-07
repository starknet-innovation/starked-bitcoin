/-
SHA-256 compression AIR (layout v1). See `docs/airs/sha256.md`.

One compression occupies a 72-row period:

| rows   | role |
|--------|------|
| 0–3    | init: `a` holds input (d,c,b,a), `e` holds input (h,g,f,e) |
| 4–67   | round t = row − 4: `a`, `e` hold the new working values; `w` holds W[t] |
| 68–71  | finalize: `a`/`e` hold input + final (mod 2³²), same order as init |

Only `a` and `e` are stored; b,c,d = a@−1,−2,−3 and f,g,h = e@−1,−2,−3.
Every constraint has degree ≤ 3. Bitwise functions are polynomials over
boolean columns (no lookups). Additions run over 16-bit limbs with carry bits.

Main columns (124):
  a[32] 0..31 · e[32] 32..63 · w[32] 64..95
  Σ0 lo/hi 96,97 · Σ1 98,99 · Ch 100,101 · Maj 102,103 · σ0 104,105 · σ1 106,107
  carries: ca_lo[3] 108..110 · ca_hi[3] 111..113 · ce_lo[3] 114..116 ·
           ce_hi[3] 117..119 · cw_lo[2] 120,121 · cw_hi[2] 122,123
Preprocessed: is_round, is_sched, is_final, k_lo, k_hi (period 72).
-/
import StarkedAir.IR
import StarkedAir.Spec.Sha256

namespace StarkedAir.Sha256

open StarkedAir

/-! ### Constants -/

/-- Round constants, from the normative spec. -/
def K : List ℕ := Spec.Sha256.Kn

def PERIOD : ℕ := 72

/-! ### Column layout -/

def A : ℕ := 0
def E : ℕ := 32
def W : ℕ := 64
def S0 : ℕ := 96
def S1 : ℕ := 98
def CH : ℕ := 100
def MJ : ℕ := 102
def s0 : ℕ := 104
def s1 : ℕ := 106
def CA_LO : ℕ := 108
def CA_HI : ℕ := 111
def CE_LO : ℕ := 114
def CE_HI : ℕ := 117
def CW_LO : ℕ := 120
def CW_HI : ℕ := 122
def N_MAIN : ℕ := 124

def IS_ROUND : ℕ := 0
def IS_SCHED : ℕ := 1
def IS_FINAL : ℕ := 2
def K_LO : ℕ := 3
def K_HI : ℕ := 4

def preCols : List PreCol :=
  let rows := List.range PERIOD
  let ind (p : ℕ → Bool) : PreCol := .periodic (rows.map fun r => if p r then 1 else 0)
  let k (f : ℕ → ℕ) : PreCol :=
    .periodic (rows.map fun r => if 4 ≤ r ∧ r < 68 then f (K.getD (r - 4) 0) else 0)
  [ind (fun r => 4 ≤ r && r < 68), ind (fun r => 20 ≤ r && r < 68), ind (fun r => 68 ≤ r),
   k (· % 2 ^ 16), k (· / 2 ^ 16)]

/-! ### Expression helpers -/

def col (i : ℕ) (off : ℤ := 0) : Expr := .col .main i off
def pre (i : ℕ) : Expr := .col .pre i 0
def cst (v : ℕ) : Expr := .const v

/-- `Σ_{j<k} 2^j · f j`, as left-nested additions starting from `0`. -/
def sumPow (f : ℕ → Expr) : ℕ → Expr
  | 0 => cst 0
  | k + 1 => .add (sumPow f k) (.mul (cst (2 ^ k)) (f k))

/-- `Σ_{j<16} 2^j · f (16·half + j)`. -/
def limbOf (f : ℕ → Expr) (half : ℕ) : Expr := sumPow (fun j => f (16 * half + j)) 16

/-- 16-bit limb `half` of the word whose bit `i` is column `base + i` at `off`. -/
def limb (base half : ℕ) (off : ℤ := 0) : Expr := limbOf (fun i => col (base + i) off) half

def xor2 (x y : Expr) : Expr := .sub (.add x y) (.mul (cst 2) (.mul x y))
def xor3 (x y z : Expr) : Expr :=
  .add (.sub (.add (.add x y) z) (.mul (cst 2) (.add (.add (.mul x y) (.mul y z)) (.mul z x))))
    (.mul (cst 4) (.mul (.mul x y) z))
def chE (x y z : Expr) : Expr := .sub (.add (.mul x y) z) (.mul x z)
def majE (x y z : Expr) : Expr :=
  .sub (.add (.add (.mul x y) (.mul y z)) (.mul z x)) (.mul (cst 2) (.mul (.mul x y) z))

/-- Bit `i` of ROTR^r1 ⊕ ROTR^r2 ⊕ ROTR^r3 of the word at `base`, `off`. -/
def bigSigmaBit (base : ℕ) (off : ℤ) (r1 r2 r3 i : ℕ) : Expr :=
  xor3 (col (base + (i + r1) % 32) off) (col (base + (i + r2) % 32) off)
    (col (base + (i + r3) % 32) off)

/-- Bit `i` of ROTR^r1 ⊕ ROTR^r2 ⊕ SHR^s of the word at `base`, `off`. -/
def smallSigmaBit (base : ℕ) (off : ℤ) (r1 r2 s i : ℕ) : Expr :=
  let x := col (base + (i + r1) % 32) off
  let y := col (base + (i + r2) % 32) off
  if i + s < 32 then xor3 x y (col (base + i + s) off) else xor2 x y

def bitsOf (base n : ℕ) : Expr := sumPow (fun j => col (base + j)) n

def boolC (e : Expr) : Expr := .mul e (.sub e (cst 1))

/-- `limbCol − Σ 2^j f(16·half + j)`, for both halves. -/
def defineLimbs (dst : ℕ) (f : ℕ → Expr) : List Expr :=
  [.sub (col dst) (limbOf f 0), .sub (col (dst + 1)) (limbOf f 1)]

/-- `sel · (Σ terms − result − 2^16·carry)`. -/
def addC (sel : Expr) (terms : List Expr) (result carry : Expr) : Expr :=
  .mul sel (.sub (.sub (terms.foldl .add (cst 0)) result) (.mul (cst 65536) carry))

/-! ### Constraints -/

def booleans : List Expr :=
  (List.range N_MAIN).filter (fun i => decide (i < 96 ∨ CA_LO ≤ i)) |>.map (boolC ∘ col)

def bitwise : List Expr :=
  defineLimbs S0 (bigSigmaBit A (-1) 2 13 22) ++
  defineLimbs S1 (bigSigmaBit E (-1) 6 11 25) ++
  defineLimbs CH (fun i => chE (col (E + i) (-1)) (col (E + i) (-2)) (col (E + i) (-3))) ++
  defineLimbs MJ (fun i => majE (col (A + i) (-1)) (col (A + i) (-2)) (col (A + i) (-3))) ++
  defineLimbs s0 (smallSigmaBit W (-15) 7 18 3) ++
  defineLimbs s1 (smallSigmaBit W (-2) 17 19 10)

def roundAdds : List Expr :=
  let r := pre IS_ROUND
  let k (h : ℕ) := pre (K_LO + h)
  let t1 (h : ℕ) := [limb E h (-4), col (S1 + h), col (CH + h), k h, limb W h]
  [ addC r (t1 0 ++ [col S0, col MJ]) (limb A 0) (bitsOf CA_LO 3),
    addC r (t1 1 ++ [col (S0 + 1), col (MJ + 1), bitsOf CA_LO 3]) (limb A 1) (bitsOf CA_HI 3),
    addC r (limb A 0 (-4) :: t1 0) (limb E 0) (bitsOf CE_LO 3),
    addC r (limb A 1 (-4) :: t1 1 ++ [bitsOf CE_LO 3]) (limb E 1) (bitsOf CE_HI 3) ]

def scheduleAdds : List Expr :=
  let s := pre IS_SCHED
  [ addC s [col s1, limb W 0 (-7), col s0, limb W 0 (-16)] (limb W 0) (bitsOf CW_LO 2),
    addC s [col (s1 + 1), limb W 1 (-7), col (s0 + 1), limb W 1 (-16), bitsOf CW_LO 2]
      (limb W 1) (bitsOf CW_HI 2) ]

def finalAdds : List Expr :=
  let f := pre IS_FINAL
  [ addC f [limb A 0 (-4), limb A 0 (-68)] (limb A 0) (bitsOf CA_LO 3),
    addC f [limb A 1 (-4), limb A 1 (-68), bitsOf CA_LO 3] (limb A 1) (bitsOf CA_HI 3),
    addC f [limb E 0 (-4), limb E 0 (-68)] (limb E 0) (bitsOf CE_LO 3),
    addC f [limb E 1 (-4), limb E 1 (-68), bitsOf CE_LO 3] (limb E 1) (bitsOf CE_HI 3) ]

def constraints : List Expr := booleans ++ bitwise ++ roundAdds ++ scheduleAdds ++ finalAdds

def air : Air := { name := "sha256_compress", nMain := N_MAIN, pre := preCols, constraints }

end StarkedAir.Sha256
