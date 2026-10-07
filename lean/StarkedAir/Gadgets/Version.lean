/-
Minimum block version (header chain v6) and the complete header-chain AIR.

Bitcoin Core `ContextualCheckBlockHeader` ("bad-version"): on mainnet a block at height `h` must
have `nVersion ≥ 2` once `h ≥ 227931` (BIP34), `≥ 3` once `h ≥ 363725` (BIP66) and `≥ 4` once
`h ≥ 388381` (BIP65); `nVersion` is a signed int32 (header bytes 0..3, little-endian).

Layout (rows of each header; constraints at row 254, selector `VER`):

| row | contents |
|-----|----------|
| 254 | `a`/`e`/`w` bits 0..29 = `d_1`/`d_2`/`d_3`; cols 108..110 = flags `f_k = [h ≥ T_k]` |
| 255 | `a` = `e = v − m` (numeric, 32 bits), col 108 = lo-limb carry |

`f_k = 1`: `h = T_k + d_k`; `f_k = 0`: `h + 1 + d_k = T_k` (so the flags are exact).
When `f_1 = 1`: `v = m + e` exactly over two 16-bit limbs with `m = 1 + f_1 + f_2 + f_3`, and
the int32 sign bit of `v` is 0.
-/
import StarkedAir.Gadgets.Work

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256

def VER : ℕ := 53

def verSel : Expr := pre VER
/-- Height (row 218), 30 bits. -/
def verHeight : Expr := bitsR A 0 30 (-36)
/-- Activation thresholds and the column groups holding `d_k`. -/
def verT (k : ℕ) : ℕ := if k = 0 then 227931 else if k = 1 then 363725 else 388381
def verD (k : ℕ) : Expr := bitsR (if k = 0 then A else if k = 1 then E else W) 0 30 0
def verF (k : ℕ) : Expr := col (108 + k)

/-- `f_k` is exactly `[h ≥ T_k]`. -/
def verFlag (k : ℕ) : Expr :=
  .mul verSel (.add (.mul (verF k) (.sub (.sub verHeight (cst (verT k))) (verD k)))
    (.mul (.sub (cst 1) (verF k)) (.sub (.sub (cst (verT k - 1)) verHeight) (verD k))))

/-- Required minimum when `f_1 = 1`. -/
def verMin : Expr := .add (.add (.add (cst 1) (verF 0)) (verF 1)) (verF 2)
/-- `e = v − m` (row 255) and its carry. -/
def verE (h : ℕ) : Expr := bitsR A (16 * h) 16 1
def verC : Expr := col 108 1

def verLo : Expr :=
  .mul (.mul verSel (verF 0)) (.sub (.add verMin (verE 0)) (.add (timeLimb W 0 (-250)) (.mul (cst 65536) verC)))
def verHi : Expr :=
  .mul (.mul verSel (verF 0)) (.sub (.add (verE 1) verC) (timeLimb W 1 (-250)))
/-- Sign bit of `nVersion` (numeric bit 31 = raw bit 7 of header word 0). -/
def verSign : Expr := .mul (.mul verSel (verF 0)) (col (W + 7) (-250))

def versionCs : List Expr := (List.range 3).map verFlag ++ [verLo, verHi, verSign]

def constraints : List Expr :=
  baseConstraints ++ powCs ++ stateCs ++ copyCs ++ retargetCs ++ mtpCs ++ workCs ++ versionCs

def air : Air := { name := "header_chain_v6", nMain := Sha256.N_MAIN, pre := preCols, constraints }

end StarkedAir.HeaderChain
