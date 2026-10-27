/-
**Records (`set_rec`).** One row per record of the segment, in file order; rows are a prefix (at least
one). A record is `txid(32) ‖ vout(4) ‖ height(4) ‖ cb(1) ‖ txi(4) ‖ len(4) ‖ ser(len)` at segment
position `START` (`Spec/SetFile.encRec`):

* the first record starts at 0, each next one after the previous one's `49 + len` bytes, and the last
  one ends at the segment length (`pub 0`); `START < 2^24`;
* the 49 head bytes and `ser`'s first 8 (the amount) are read from the byte table;
* `cb ≤ 1`, `height < 2^24`, `8 ≤ len < 2^24`; the code bytes `2·height + cb` (carries);
* the key (txid bytes, then `vout` big-endian) is above the previous record's, the first record's above
  the public incoming key when there is one (one differing byte, equal before it);
* the coin tuple (`block_coin`'s 26 terms, the fingerprint from `block_fpwalk`) and the fraction
  `1/(z − φ)`, accumulated from the public incoming sum;
* the amount (12 bytes with carries), the highest height, the record count, from the public incoming
  values; the last row's are the outgoing ones, and its key the outgoing last key.

It yields `rec(r, START, len)` and the code bytes `code(r, i, byte)` for the `TxOutSer` stream, and the
`ser` segment `(0, r, START + 49, len)`, whose fingerprint it reads back.
-/
import StarkedAir.SetPass.Layout

namespace StarkedAir.SetPass.Rec

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

def ON : ℕ := 0
/-- The last record: on, and the next row off. -/
def LST : ℕ := 1
def IDX : ℕ := 2
def START : ℕ := 3
def HB (j : ℕ) : ℕ := 4 + j
def AB (j : ℕ) : ℕ := 53 + j
def LENC : ℕ := 61
/-- Code bytes and their carries `K 1 … K 3` (`K 0` is `cb`). -/
def C (i : ℕ) : ℕ := 62 + i
def K (i : ℕ) : ℕ := 65 + i
/-- `len − 8` and `START`, as three bytes each. -/
def D (i : ℕ) : ℕ := 69 + i
def SB (i : ℕ) : ℕ := 72 + i
def FC : ℕ := 75
def ACC : ℕ := 79
/-- The amount so far (12 bytes) and its carries `AC 1 … AC 11`. -/
def AM (j : ℕ) : ℕ := 83 + j
def AC (j : ℕ) : ℕ := 94 + j
/-- The previous maximum height, the maximum, whether the height exceeds it, the difference bytes. -/
def PMX : ℕ := 106
def MX : ℕ := 107
def GT : ℕ := 108
def MD (i : ℕ) : ℕ := 109 + i
/-- The key comparison: the differing position (one-hot), the previous key, `key − prev − 1` there. -/
def DIFF (j : ℕ) : ℕ := 112 + j
def PREV (j : ℕ) : ℕ := 148 + j
def DELTA : ℕ := 184
def FH : ℕ := 185
def N_MAIN : ℕ := 189

def preCols : List PreCol := [.isFirst, .notLast]

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := pre 0
def notFirst : Expr := om first
def isLast : Expr := om (pre 1)
def pair (a b : Expr) : Expr := .add a (.mul (cst 256) b)
def b3 (f : ℕ → ℕ) : Expr := .add (pair (k (f 0)) (k (f 1))) (.mul (cst 65536) (k (f 2)))
def hb (j : ℕ) : Expr := k (HB j)

/-- Key byte `j`: the txid's bytes, then `vout`'s from the most significant. -/
def keyCol (j : ℕ) : ℕ := if j < 32 then HB j else HB (35 - (j - 32))
def height : Expr := .add (pair (hb 36) (hb 37)) (.mul (cst 65536) (hb 38))
def txi : Expr := .add (.add (pair (hb 41) (hb 42)) (.mul (cst 65536) (hb 43))) (.mul (cst 16777216) (hb 44))
def lenOf : Expr := .add (pair (hb 45) (hb 46)) (.mul (cst 65536) (hb 47))
/-- Comparing with a previous key: every row but the first, which compares when there is an incoming key. -/
def cmp : Expr := .add (.sub (k ON) first) (.mul first (.pub PUB_HASLAST))

/-- Txid limb `i`, as `block_coin`'s: word `w` is big-endian bytes `4w … 4w + 3`; limb `2w` its low half. -/
def txidLimb (i : ℕ) : Expr :=
  let w := i / 2
  if i % 2 = 0 then pair (hb (4 * w + 3)) (hb (4 * w + 2)) else pair (hb (4 * w + 1)) (hb (4 * w))

/-- The coin tuple (`block_coin`'s layout, 26 terms). -/
def tuple : List Expr :=
  (List.range 16).map txidLimb ++
  [pair (hb 32) (hb 33), pair (hb 34) (hb 35), pair (k (C 0)) (k (C 1)), pair (k (C 2)) (k (C 3)),
    k FH, k (FH + 1), k (FH + 2), k (FH + 3), k LENC, txi]

#guard tuple.length = Block.Coin.W

def phi : QE :=
  (List.range Block.Coin.W).foldl (fun acc j => acc.add ((pubQ (PUB_ALPHA j)).mul (base (tuple.getD j (cst 0))))) (base (cst 0))

def localC : List Expr :=
  [ON, LST, GT].map (fun c => boolC (k c)) ++
  [K 1, K 2, K 3].map (fun c => boolC (k c)) ++
  (List.range 11).map (fun j => boolC (k (AC (j + 1)))) ++
  (List.range 36).map (fun j => boolC (k (DIFF j))) ++
  [ -- rows: a nonempty prefix; the last record
    .mul first (om (k ON)), .mul notFirst (.mul (k ON) (om (kp ON))), .mul isLast (k ON),
    .sub (k LST) (.mul (k ON) (om (kn ON))),
    -- the index and the count
    .mul first (k IDX), .mul notFirst (.mul (k ON) (.sub (.sub (k IDX) (kp IDX)) one)),
    .mul (k LST) (.sub (.add (k IDX) one) (.sub (.pub PUB_I_OUT) (.pub PUB_I_IN))),
    -- positions
    .mul first (k START),
    .mul notFirst (.mul (k ON) (.sub (k START) (.add (.add (kp START) (cst 49)) (kp LENC)))),
    .mul (k LST) (.sub (.add (.add (k START) (cst 49)) (k LENC)) (.pub PUB_LEN)),
    .mul (k ON) (.sub (k START) (b3 SB)),
    -- the fields
    .sub (k LENC) lenOf, .mul (k ON) (hb 48), .mul (k ON) (.sub (.sub (k LENC) (cst 8)) (b3 D)),
    .mul (k ON) (boolC (hb 40)), .mul (k ON) (hb 39),
    .sub (k (C 0)) (.sub (.add (.mul (cst 2) (hb 36)) (hb 40)) (.mul (cst 256) (k (K 1)))),
    .sub (k (C 1)) (.sub (.add (.mul (cst 2) (hb 37)) (k (K 1))) (.mul (cst 256) (k (K 2)))),
    .sub (k (C 2)) (.sub (.add (.mul (cst 2) (hb 38)) (k (K 2))) (.mul (cst 256) (k (K 3)))),
    .sub (k (C 3)) (.add (.mul (cst 2) (hb 39)) (k (K 3))),
    -- the highest height
    .sub (k PMX) (.add (.mul notFirst (kp MX)) (.mul first (.pub PUB_MAXH_IN))),
    .sub (k MX) (.add (k PMX) (.mul (k GT) (.sub height (k PMX)))),
    .mul (k GT) (om (k ON)),
    .mul (k ON) (.sub (b3 MD) (.add (.mul (k GT) (.sub (.sub height (k PMX)) one))
      (.mul (om (k GT)) (.sub (k PMX) height)))),
    .mul isLast (.sub (k MX) (.pub PUB_MAXH_OUT)),
    -- the key: one differing byte when comparing, equal before it, greater there
    .sub ((List.range 36).foldl (fun acc j => .add acc (k (DIFF j))) (cst 0)) cmp,
    .sub (k DELTA) (.sub ((List.range 36).foldl (fun acc j =>
      .add acc (.mul (k (DIFF j)) (.sub (k (keyCol j)) (k (PREV j))))) (cst 0)) cmp) ] ++
  (List.range 36).map (fun j => .sub (k (PREV j)) (.add (.mul notFirst (kp (keyCol j))) (.mul first (.pub (PUB_LAST_IN j))))) ++
  (List.range 36).map (fun j =>
    let before := (List.range j).foldl (fun acc i => .sub acc (k (DIFF i))) cmp
    .mul (.sub before (k (DIFF j))) (.sub (k (keyCol j)) (k (PREV j)))) ++
  (List.range 36).map (fun j => .mul (k LST) (.sub (k (keyCol j)) (.pub (PUB_LAST_OUT j)))) ++
  -- the amount: 12 bytes, carries in from the previous byte, none into byte 0 or out of byte 11
  (List.range 12).map (fun j =>
    let prev := Expr.add (.mul notFirst (kp (AM j))) (.mul first (.pub (PUB_AMT_IN j)))
    let add := if j < 8 then Expr.mul (k ON) (k (AB j)) else cst 0
    let cin := if j = 0 then cst 0 else k (AC j)
    let cout := if j = 11 then cst 0 else Expr.mul (cst 256) (k (AC (j + 1)))
    .sub (k (AM j)) (.sub (.add (.add prev add) cin) cout)) ++
  (List.range 12).map (fun j => .mul isLast (.sub (k (AM j)) (.pub (PUB_AMT_OUT j))))

/-- The running sum (`ExtSum`'s constraints): multiplicity `ON`, from the public incoming sum. -/
def fracC : List Expr := (((pubQ PUB_Z).sub phi).mul (colQ FC) |>.sub (base (k ON))).coords
def zeroC : List Expr := (colQ FC).coords.map fun e => .mul (om (k ON)) e
def accC : List Expr :=
  ((colQ ACC).sub ((((base notFirst).mul (colQ ACC (-1))).add ((base first).mul (pubQ PUB_SUM_IN))).add (colQ FC))).coords
def lastC : List Expr := ((base isLast).mul ((colQ ACC).sub (pubQ PUB_SUM_OUT))).coords

def constraints : List Expr := localC ++ fracC ++ zeroC ++ accC ++ lastC

def r8 (e : Expr) (m : Expr) : Lookup := ⟨Block.Tables.REL_R8, .neg m, [e]⟩

def lookups : List Lookup :=
  (List.range 49).map (fun j => ⟨Block.REL_BYTE, .neg (k ON), [.add (k START) (cst j), hb j]⟩) ++
  (List.range 8).map (fun j => ⟨Block.REL_BYTE, .neg (k ON), [.add (k START) (cst (49 + j)), k (AB j)]⟩) ++
  [ ⟨REL_REC, k ON, [k IDX, k START, k LENC]⟩ ] ++
  (List.range 4).map (fun i => ⟨REL_CODE, k ON, [k IDX, cst i, k (C i)]⟩) ++
  [ ⟨Block.FpWalk.REL_SEG, k ON, [cst 0, k IDX, .add (k START) (cst 49), k LENC]⟩,
    ⟨Block.FpWalk.REL_FP, .neg (k ON), [cst 0, k IDX, k LENC, k FH, k (FH + 1), k (FH + 2), k (FH + 3)]⟩ ] ++
  (List.range 3).map (fun i => r8 (k (C i)) (k ON)) ++
  (List.range 3).map (fun i => r8 (k (D i)) (k ON)) ++
  (List.range 3).map (fun i => r8 (k (SB i)) (k ON)) ++
  (List.range 3).map (fun i => r8 (k (MD i)) (k ON)) ++
  (List.range 12).map (fun j => r8 (k (AM j)) one) ++
  [r8 (k DELTA) cmp]

def rec : Comp where
  air := { name := "set_rec", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.Rec
