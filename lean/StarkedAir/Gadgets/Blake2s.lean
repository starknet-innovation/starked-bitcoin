/-
**Blake2s compression AIR** (roadmap BLAKE2S; spec `Spec/Blake2s.lean`, RFC 7693).

One compression occupies an 88-row period:

| rows  | role |
|-------|------|
| 0–3   | init: row `k` holds the state slots of diagonal G `4+k` (`v` before round 0); row 0 also holds `t_lo`, `t_hi`, `f` |
| 4–83  | G step `j = row − 4` (round `j / 8`, G `j % 8`): one G function per row |
| 84–87 | final: row `k` holds output words `k` (W0) and `b(4+k)` (W1), via W2, W3 |

Every row has eight 32-bit words as bit columns, `W0 … W7`. In a G row they are
`a₁, d₁, c₁, b₁` (after the first half of G) and `a₂, d₂, c₂, b₂` (the outputs); the output of
role `a, b, c, d` is `W4, W7, W6, W5`. A G row reads its inputs from the outputs of the rows that
last wrote those state slots, always in the same role, at an offset that depends only on the G
position (`srcOff`). Init rows lay out the initial state the same way, as if written by the
previous round's diagonal step. Message words are 16-bit limbs (`M`), copied down the period and
picked per row by preprocessed one-hot selectors (`XSEL`, `YSEL`, from `σ`). Additions run over
16-bit limbs with carry bits; xor and rotations are polynomials over bits. Degree ≤ 3, no lookups.

Main columns (300): W0..W7 bits 0..255 · M (16 words × lo/hi) 256..287 · carries 288..299.
Preprocessed (50): INIT₀₋₃, G₀₋₇, FIN₀₋₃, COPY, XSEL₀₋₁₅, YSEL₀₋₁₅, IS_G.
-/
import StarkedAir.Gadgets.Sha256
import StarkedAir.Spec.Blake2s

namespace StarkedAir.Blake2s

open StarkedAir

def PERIOD : ℕ := 88

/-! ### Column layout -/

/-- Bit `i` of word slot `w`. -/
abbrev WB (w i : ℕ) : ℕ := 32 * w + i
def MSG : ℕ := 256
/-- Limb `h` of message word `k`. -/
def ML (k h : ℕ) : ℕ := MSG + 2 * k + h
def CA1_LO : ℕ := 288  -- 2 bits
def CA1_HI : ℕ := 290  -- 2 bits
def CC1_LO : ℕ := 292
def CC1_HI : ℕ := 293
def CA2_LO : ℕ := 294  -- 2 bits
def CA2_HI : ℕ := 296  -- 2 bits
def CC2_LO : ℕ := 298
def CC2_HI : ℕ := 299
def N_MAIN : ℕ := 300

/-- Output word slot of role `0 = a, 1 = b, 2 = c, 3 = d`. -/
def outW : ℕ → ℕ
  | 0 => 4 | 1 => 7 | 2 => 6 | _ => 5

def P_INIT (k : ℕ) : ℕ := k
def P_G (g : ℕ) : ℕ := 4 + g
def P_FIN (k : ℕ) : ℕ := 12 + k
def P_COPY : ℕ := 16
def P_XSEL (k : ℕ) : ℕ := 17 + k
def P_YSEL (k : ℕ) : ℕ := 33 + k
def P_ISG : ℕ := 49

/-- Distance back to the writer of input `role` (0 = a … 3 = d) for G position `g`
(columns 0–3, diagonals 4–7). -/
def src : ℕ → ℕ → ℕ
  | 0, 0 => 4 | 0, 1 => 1 | 0, 2 => 2 | 0, _ => 3
  | 1, 0 => 4 | 1, 1 => 5 | 1, 2 => 2 | 1, _ => 3
  | 2, 0 => 4 | 2, 1 => 5 | 2, 2 => 6 | 2, _ => 3
  | 3, 0 => 4 | 3, 1 => 5 | 3, 2 => 6 | 3, _ => 7
  | 4, 0 => 4 | 4, 1 => 3 | 4, 2 => 2 | 4, _ => 1
  | 5, 0 => 4 | 5, 1 => 3 | 5, 2 => 2 | 5, _ => 5
  | 6, 0 => 4 | 6, 1 => 3 | 6, 2 => 6 | 6, _ => 5
  | _, 0 => 4 | _, 1 => 7 | _, 2 => 6 | _, _ => 5

def srcOff (g role : ℕ) : ℤ := -((src g role : ℕ) : ℤ)

/-- In final row `k`, the offset of the last diagonal row holding `v[k+8]` (role c) and
`v[b(4+k)+8]` (role d): diagonal `(k+2) mod 4`. -/
def finOff (k : ℕ) : ℤ := if k < 2 then -2 else -6

/-- Preprocessed column `i` is `1` at period row `r` iff `preQ i r`. -/
def preQ (i r : ℕ) : Bool :=
  let isG := 4 ≤ r && r < 84
  let gOf := (r - 4) % 8
  let rOf := (r - 4) / 8
  if i < 4 then r == i
  else if i < 12 then isG && gOf == i - 4
  else if i < 16 then r == 84 + (i - 12)
  else if i = 16 then 1 ≤ r
  else if i < 33 then isG && Spec.Blake2s.sigma rOf (2 * gOf) == i - 17
  else if i < 49 then isG && Spec.Blake2s.sigma rOf (2 * gOf + 1) == i - 33
  else isG

def preCols : List PreCol :=
  (List.range 50).map fun i => .periodic ((List.range PERIOD).map fun r => if preQ i r then 1 else 0)

/-! ### Expression helpers (shared with the SHA-256 AIR, so its evaluation lemmas apply) -/

export StarkedAir.Sha256 (col pre cst sumPow xor2 boolC bitsOf addC)

/-- Limb `h` (16 bits) of word slot `w` at offset `off`. -/
abbrev limb (w h : ℕ) (off : ℤ := 0) : Expr := StarkedAir.Sha256.limb (32 * w) h off

/-- `x ⊕ c` for a constant bit `c`. -/
def xorC (x : Expr) (c : Bool) : Expr := if c then .sub (cst 1) x else x

/-- Message limb `h` of the word picked by the selector family `base` (XSEL or YSEL). -/
def msgLimb (base h : ℕ) : Expr :=
  (List.range 16).foldl (fun acc k => .add acc (.mul (pre (base + k)) (col (ML k h)))) (cst 0)

/-- Bit `i` of `ROTR^r (x ⊕ y)`, from bit columns of word slots at offsets. -/
def rotXor (wx : ℕ) (ox : ℤ) (wy : ℕ) (oy : ℤ) (r i : ℕ) : Expr :=
  xor2 (col (WB wx ((i + r) % 32)) ox) (col (WB wy ((i + r) % 32)) oy)

/-- `sel · (bit − value)` for all 32 bits. -/
def bitsEq (sel : Expr) (w : ℕ) (val : ℕ → Expr) : List Expr :=
  (List.range 32).map fun i => .mul sel (.sub (col (WB w i)) (val i))

def ivBit (k i : ℕ) : Bool := (Spec.Blake2s.IVn.getD k 0).testBit i

/-! ### Constraints -/

def booleans : List Expr :=
  ((List.range 256) ++ (List.range 12).map (CA1_LO + ·)).map (boolC ∘ col)

/-- First half of G position `g`: `a₁ = a + b + x`, `d₁ = (d ⊕ a₁) ⋙ 16`, `c₁ = c + d₁`,
`b₁ = (b ⊕ c₁) ⋙ 12`, inputs read at `srcOff g`. -/
def gFirst (g : ℕ) : List Expr :=
  let s := pre (P_G g)
  let o := srcOff g
  [ addC s [limb (outW 0) 0 (o 0), limb (outW 1) 0 (o 1), msgLimb (P_XSEL 0) 0] (limb 0 0) (bitsOf CA1_LO 2),
    addC s [limb (outW 0) 1 (o 0), limb (outW 1) 1 (o 1), msgLimb (P_XSEL 0) 1, bitsOf CA1_LO 2] (limb 0 1) (bitsOf CA1_HI 2),
    addC s [limb (outW 2) 0 (o 2), limb 1 0] (limb 2 0) (col CC1_LO),
    addC s [limb (outW 2) 1 (o 2), limb 1 1, col CC1_LO] (limb 2 1) (col CC1_HI) ] ++
  bitsEq s 1 (rotXor (outW 3) (o 3) 0 0 16) ++
  bitsEq s 3 (rotXor (outW 1) (o 1) 2 0 12)

/-- Second half (same for every G): `a₂ = a₁ + b₁ + y`, `d₂ = (d₁ ⊕ a₂) ⋙ 8`, `c₂ = c₁ + d₂`,
`b₂ = (b₁ ⊕ c₂) ⋙ 7`. -/
def gSecond : List Expr :=
  let s := pre P_ISG
  [ addC s [limb 0 0, limb 3 0, msgLimb (P_YSEL 0) 0] (limb 4 0) (bitsOf CA2_LO 2),
    addC s [limb 0 1, limb 3 1, msgLimb (P_YSEL 0) 1, bitsOf CA2_LO 2] (limb 4 1) (bitsOf CA2_HI 2),
    addC s [limb 2 0, limb 5 0] (limb 6 0) (col CC2_LO),
    addC s [limb 2 1, limb 5 1, col CC2_LO] (limb 6 1) (col CC2_HI) ] ++
  bitsEq s 5 (rotXor 1 0 4 0 8) ++
  bitsEq s 7 (rotXor 3 0 6 0 7)

/-- Init rows: `c` and `d` of row `k` are IV words, mixed with `t_lo`, `t_hi`, `f` (row 0's
`W0`, `W1`, `W2` bit 0); `f`'s other bits are zero. Row k: c = v[(10,11,8,9)ₖ], d = v[(15,12,13,14)ₖ]. -/
def init : List Expr :=
  let cIV : ℕ → ℕ := fun k => [2, 3, 0, 1].getD k 0
  ((List.range 4).flatMap fun k =>
    bitsEq (pre (P_INIT k)) (outW 2) (fun i => cst (ivBit (cIV k) i).toNat) ++
    bitsEq (pre (P_INIT k)) (outW 3) (fun i =>
      if k = 0 then cst (ivBit 7 i).toNat
      else if k = 1 then xorC (col (WB 0 i) (-1)) (ivBit 4 i)
      else if k = 2 then xorC (col (WB 1 i) (-2)) (ivBit 5 i)
      else xorC (col (WB 2 0) (-3)) (ivBit 6 i))) ++
  ((List.range 31).map fun i => .mul (pre (P_INIT 0)) (col (WB 2 (i + 1))))

/-- Final row `k`: `W2 = h[k] ⊕ v[k]`, `W0 = W2 ⊕ v[k+8]`; `W3 = h[b] ⊕ v[b]`, `W1 = W3 ⊕ v[b+8]`
(`b = b(4+k)`), two xors at a time to stay within degree 3. -/
def final : List Expr :=
  (List.range 4).flatMap fun k =>
    let s := pre (P_FIN k)
    bitsEq s 2 (fun i => xor2 (col (WB (outW 0) i) (-84)) (col (WB (outW 0) i) (-4))) ++
    bitsEq s 0 (fun i => xor2 (col (WB 2 i)) (col (WB (outW 2) i) (finOff k))) ++
    bitsEq s 3 (fun i => xor2 (col (WB (outW 1) i) (-84)) (col (WB (outW 1) i) (-4))) ++
    bitsEq s 1 (fun i => xor2 (col (WB 3 i)) (col (WB (outW 3) i) (finOff k)))

/-- Message limbs are constant over the period. -/
def copy : List Expr :=
  (List.range 32).map fun j => .mul (pre P_COPY) (.sub (col (MSG + j)) (col (MSG + j) (-1)))

def constraints : List Expr :=
  booleans ++ (List.range 8).flatMap gFirst ++ gSecond ++ init ++ final ++ copy

def air : Air := { name := "blake2s_compress", nMain := N_MAIN, pre := preCols, constraints }

end StarkedAir.Blake2s
