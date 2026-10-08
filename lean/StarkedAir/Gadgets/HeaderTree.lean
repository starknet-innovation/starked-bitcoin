/-
**Header commitment tree components (HC-HASHTREE, D-033).** Two components of one system:

* `headers`: the header-chain AIR (`HeaderChain.air`, constraints unchanged) with one extra main
  column (a multiplicity) and one lookup: at row 215 of header `j` it yields
  `node(0, height − h₀, hash)`, the leaf at its position relative to the segment start.
* `tree`: the Blake2s compression AIR (constraints included unchanged) plus a node level and
  position copied down each period (the level range-checked and nonzero), the constant inputs
  (`h₀`, `t = 64`, final), and three lookups: at row 0 it uses `node(ℓ−1, 2p, left)` and
  `node(ℓ−1, 2p+1, right)` (its message), at row 87 it yields `node(ℓ, p, output)`.

The verifier contributes the public entry `node(K, 0, T)` (multiplicity −1): the segment's
`2^K` leaves hash to the public root `T`. Tuples carry words as 16-bit limbs.
-/
import StarkedAir.Gadgets.Version
import StarkedAir.Gadgets.Blake2s
import StarkedAir.Lookup
import StarkedAir.Spec.HeaderTree

namespace StarkedAir.HeaderTree

open StarkedAir

def REL_NODE : ℕ := 2

/-! ### The tree component -/

def LVL : ℕ := 300
def LVLB (i : ℕ) : ℕ := 301 + i
def LVL_INV : ℕ := 306
def POS : ℕ := 307
def TMULT : ℕ := 308
def N_MAIN : ℕ := 309

open StarkedAir.Sha256 (col pre cst sumPow boolC)
open StarkedAir.Blake2s (limb ML outW P_INIT P_FIN P_COPY)

/-- Word `k` of the parameter-block chaining value `h₀`, as a natural. -/
def h0Nat (k : ℕ) : ℕ := (Spec.Blake2s.h0 k).toNat

/-- `sel · (bit i of word slot w − c i)` for all 32 bits. -/
def bitsConst (sel : Expr) (w : ℕ) (c : ℕ → Bool) : List Expr :=
  (List.range 32).map fun i => .mul sel (.sub (col (32 * w + i)) (cst (c i).toNat))

def bOf (k : ℕ) : ℕ := [5, 6, 7, 4].getD k 0

/-- Constant compression inputs: `h = h₀` (init row `k` holds `h[k]` as `a` and `h[b(4+k)]` as
`b`), `t = 64` (row 0 `W0`, `W1`), final (row 0 `W2` bit 0). -/
def constIn : List Expr :=
  ((List.range 4).flatMap fun k =>
    bitsConst (pre (P_INIT k)) (outW 0) (fun i => (h0Nat k).testBit i) ++
    bitsConst (pre (P_INIT k)) (outW 1) (fun i => (h0Nat (bOf k)).testBit i)) ++
  bitsConst (pre (P_INIT 0)) 0 (fun i => (64 : ℕ).testBit i) ++
  bitsConst (pre (P_INIT 0)) 1 (fun _ => false) ++
  [.mul (pre (P_INIT 0)) (.sub (col (32 * 2)) (cst 1))]

def levelCs : List Expr :=
  [ .mul (pre P_COPY) (.sub (col LVL) (col LVL (-1))),
    .mul (pre P_COPY) (.sub (col POS) (col POS (-1))),
    .sub (col LVL) (sumPow (fun i => col (LVLB i)) 5),
    .sub (.mul (col LVL) (col LVL_INV)) (cst 1) ] ++
  (List.range 5).map fun i => boolC (col (LVLB i))

def treeConstraints : List Expr := Blake2s.constraints ++ constIn ++ levelCs

/-- Message limbs of words `8·half … 8·half + 7`, lo/hi interleaved. -/
def msgLimbs (half : ℕ) : List Expr :=
  (List.range 16).map fun j => col (ML (8 * half + j / 2) (j % 2))

/-- Output limbs read from final row 87: word `i` is `W0` of row `84+i` (`i < 4`), else `W1`
of row `84 + (i+3) mod 4`. -/
def outLimbs : List Expr :=
  (List.range 16).map fun j =>
    let i : ℕ := j / 2
    if i < 4 then limb 0 (j % 2) ((84 + i : ℕ) - (87 : ℤ)) else limb 1 (j % 2) ((84 + (i + 3) % 4 : ℕ) - (87 : ℤ))

def treeLookups : List Lookup :=
  [ ⟨REL_NODE, .neg (pre (P_INIT 0)), .sub (col LVL) (cst 1) :: .mul (cst 2) (col POS) :: msgLimbs 0⟩,
    ⟨REL_NODE, .neg (pre (P_INIT 0)), .sub (col LVL) (cst 1) :: .add (.mul (cst 2) (col POS)) (cst 1) :: msgLimbs 1⟩,
    ⟨REL_NODE, .mul (pre (P_FIN 3)) (col TMULT), col LVL :: col POS :: outLimbs⟩ ]

def tree : Comp where
  air := { name := "blake2s_tree", nMain := N_MAIN, pre := Blake2s.preCols, constraints := treeConstraints }
  lookups := treeLookups

/-! ### The header component -/

def HMULT : ℕ := Sha256.N_MAIN

/-- Hash word `k` of the header whose output row is the current one (row 215): `A` at `−k` for
`k < 4`, else `E` at `−(k−4)` (Sha256Sound's `stAt`). -/
def hashLimbs : List Expr :=
  (List.range 16).map fun j =>
    let k : ℕ := j / 2
    if k < 4 then Sha256.limb Sha256.A (j % 2) (-(k : ℤ)) else Sha256.limb Sha256.E (j % 2) (-((k - 4 : ℕ) : ℤ))

/-- The leaf position: the height (row 218, `A` bits 0..29) minus the segment's first height
(public inputs 32, 33). -/
def relHeight : Expr :=
  .sub (HeaderChain.bitsAt Sha256.A 30 3) (.add (.pub 32) (.mul (cst 65536) (.pub 33)))

def headers : Comp where
  air := { HeaderChain.air with name := "header_chain_v7", nMain := Sha256.N_MAIN + 1 }
  lookups := [⟨REL_NODE, .mul (pre (HeaderChain.OUT0 + 3)) (col HMULT), cst 0 :: relHeight :: hashLimbs⟩]

end StarkedAir.HeaderTree
