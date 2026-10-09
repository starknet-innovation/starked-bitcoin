/-
**Block fields (M3a.2 `BLK-FIELDS`, AIR layer).** One row per token (`Spec/BlockTokens.lean`).
Row `r` covers bytes `[START, START + LEN)`; rows tile the block from 0 to `LEN_pub` (`pub 0`, as in
`Block.bytes`), then padding. The row's CompactSize (if any) is read from the byte table at
`START + OFF` and decoded canonically; a segwit transaction head reads its marker `00` and flag
`01`. Counters and two is-zero helpers choose each row's kind from the previous row, following
the token grammar. Opaque fields (header, hashes, scripts, items, fixed-size fields) are not read
here.
-/
import StarkedAir.Block.Bytes

/-! Degrees: constraints at most 3, lookup multiplicities at most 2, tuple entries 1 (`#guard`s below). -/

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow)

/-! ### Columns -/

def K_BLK : ℕ := 0
def K_TXH : ℕ := 1
def K_IN : ℕ := 2
def K_NOUT : ℕ := 3
def K_OUT : ℕ := 4
def K_WCNT : ℕ := 5
def K_WITEM : ℕ := 6
def K_LOCK : ℕ := 7
def K_PAD : ℕ := 8
def START : ℕ := 9
def LEN : ℕ := 10
def VAL : ℕ := 11
def SEG : ℕ := 12
def OFF : ℕ := 13
def CP1 : ℕ := 14
def CP3 : ℕ := 15
def CP5 : ℕ := 16
/-- CompactSize bytes: `17 … 21`. -/
def CB (j : ℕ) : ℕ := 17 + j
/-- Range-check bits: slot A `22 …`, slot B `47 …`, `START`'s bits `72 …` (25 each). -/
def RA (j : ℕ) : ℕ := 22 + j
def RB (j : ℕ) : ℕ := 47 + j
def RS (j : ℕ) : ℕ := 72 + j
def TXL : ℕ := 97
def INL : ℕ := 98
def NIN : ℕ := 99
def OUTL : ℕ := 100
def WINL : ℕ := 101
def ITEML : ℕ := 102
def HASW : ℕ := 103
def Z1 : ℕ := 104
def INV1 : ℕ := 105
def Z2 : ℕ := 106
def INV2 : ℕ := 107
def EOC : ℕ := 108
def ESC : ℕ := 109
/-- The decision expressions, stored (keeps the is-zero tests at degree 3). -/
def E1C : ℕ := 110
def E2C : ℕ := 111
/-- Two bits bounding the 5-byte form's top byte by 3 (canonical values have it at most 2), so the
decoded sum stays below `2^26` and never wraps modulo `P`. -/
def C4B0 : ℕ := 112
def C4B1 : ℕ := 113
/-- Per-transaction values carried down its rows (M3a.3): its start, the witness section's start (the
row after the outputs), its index; and the multiplicity of its `tx` tuple. -/
def TXA : ℕ := 114
def WST : ℕ := 115
def TXI : ℕ := 116
def TXM : ℕ := 117
def N_MAIN : ℕ := 118

/-- `tx(i, a, seg, w, l)`: transaction `i` starts at `a`, its witness section at `w`, its locktime at `l`. -/
def REL_TX : ℕ := 4

def kinds : List ℕ := [K_BLK, K_TXH, K_IN, K_NOUT, K_OUT, K_WCNT, K_WITEM, K_LOCK, K_PAD]

/-- `isFirst`, `notLast`. -/
def preCols : List PreCol := [.isFirst, .notLast]

def LENPUB : Expr := .pub 0
def first : Expr := pre 0
def notFirst : Expr := .sub (cst 1) (pre 0)
def isLast : Expr := .sub (cst 1) (pre 1)

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def oneMinus (e : Expr) : Expr := .sub one e

/-- CompactSize prefix length. -/
def pref : Expr := .add (k CP1) (.add (.mul (cst 3) (k CP3)) (.mul (cst 5) (k CP5)))
/-- Rows with a CompactSize: all but locktime and padding. -/
def hasC : Expr := oneMinus (.add (k K_LOCK) (k K_PAD))

/-- The row length by kind. -/
def lenE : Expr :=
  .add (.mul (k K_BLK) (.add (cst 80) pref)) <|
  .add (.mul (k K_TXH) (.add (.add (cst 4) (.mul (cst 2) (k SEG))) pref)) <|
  .add (.mul (k K_IN) (.add (.add (cst 40) pref) (k VAL))) <|
  .add (.mul (k K_NOUT) pref) <|
  .add (.mul (k K_OUT) (.add (.add (cst 8) pref) (k VAL))) <|
  .add (.mul (k K_WCNT) pref) <|
  .add (.mul (k K_WITEM) (.add pref (k VAL))) <|
  .mul (k K_LOCK) (cst 4)

/-- The CompactSize's offset within the row. -/
def offE : Expr :=
  .add (.mul (k K_BLK) (cst 80)) <|
  .add (.mul (k K_TXH) (.add (cst 4) (.mul (cst 2) (k SEG)))) <|
  .add (.mul (k K_IN) (cst 36)) (.mul (k K_OUT) (cst 8))

/-- The value of the CompactSize's bytes, by form. -/
def valE : Expr :=
  .add (.mul (k CP1) (k (CB 0))) <|
  .add (.mul (k CP3) (.add (k (CB 1)) (.mul (cst 256) (k (CB 2))))) <|
  .mul (k CP5) (.add (k (CB 1)) (.add (.mul (cst 256) (k (CB 2)))
    (.add (.mul (cst 65536) (k (CB 3))) (.mul (cst 16777216) (k (CB 4))))))

def MAXS : ℕ := 0x02000000

/-- Decision expressions for the two is-zero helpers. -/
def e1 : Expr :=
  .add (.mul (k K_BLK) (k VAL)) <| .add (.mul (k K_TXH) (k VAL)) <| .add (.mul (k K_IN) (.sub (k INL) one)) <|
  .add (.mul (k K_NOUT) (k VAL)) <| .add (.mul (k K_OUT) (.sub (k OUTL) one)) <|
  .add (.mul (k K_WCNT) (k VAL)) <| .add (.mul (k K_WITEM) (.sub (k ITEML) one)) <| .mul (k K_LOCK) (k TXL)

def e2 : Expr := .add (.mul (.add (k K_WCNT) (k K_WITEM)) (.sub (k WINL) one)) (.mul (k K_LOCK) (k HASW))

def isZero (z inv : ℕ) (e : Expr) : List Expr :=
  [boolC (k z), .mul (k z) e, .mul (oneMinus (k z)) (.sub (.mul e (k inv)) one)]

/-- `x` (an expression) equals `next` kind `c` at this row, from the previous row. -/
def trans (c : ℕ) (from_ : Expr) : Expr := .sub (k c) from_

/-- Kinds: one-hot; the block row is row 0; the last row pads. -/
def kindC : List Expr :=
  kinds.map (fun c => boolC (k c)) ++
  [ .sub (kinds.foldr (fun c acc => .add (k c) acc) (cst 0)) one,
    .sub (k K_BLK) first,
    .mul isLast (oneMinus (k K_PAD)) ]

/-- Transitions (row 0's predecessor is the last row, a padding row: only `K_BLK` follows it). -/
def transC : List Expr :=
  [ trans K_TXH (.add (kp K_BLK) (.mul (kp K_LOCK) (oneMinus (kp Z1)))),
    trans K_IN (.add (kp K_TXH) (.mul (kp K_IN) (oneMinus (kp Z1)))),
    trans K_NOUT (.mul (kp K_IN) (kp Z1)),
    trans K_OUT (.mul (.add (kp K_NOUT) (kp K_OUT)) (oneMinus (kp Z1))),
    trans K_WCNT (.add (.mul (kp EOC) (kp SEG)) (.mul (kp ESC) (oneMinus (kp Z2)))),
    trans K_WITEM (.mul (.add (kp K_WCNT) (kp K_WITEM)) (oneMinus (kp Z1))),
    trans K_LOCK (.add (.mul (kp EOC) (oneMinus (kp SEG))) (.mul (kp ESC) (kp Z2))),
    trans K_PAD (.add (.mul (kp K_LOCK) (kp Z1)) (.mul (kp K_PAD) notFirst)),
    .sub (k EOC) (.mul (.add (k K_NOUT) (k K_OUT)) (k Z1)),
    .sub (k ESC) (.mul (.add (k K_WCNT) (k K_WITEM)) (k Z1)) ]

def tileC : List Expr :=
  [ .mul first (k START),
    .mul notFirst (.sub (k START) (.add (kp START) (kp LEN))),
    .mul (k K_PAD) (.sub (k START) LENPUB),
    .sub (k LEN) lenE,
    .sub (k START) (sumPow (fun j => k (RS j)) 25) ]

def compactC : List Expr :=
  [ .sub (k OFF) offE,
    .sub (.add (k CP1) (.add (k CP3) (k CP5))) hasC,
    .sub (k VAL) valE,
    .sub (k (CB 0)) (.add (.mul (k CP1) (k VAL)) (.add (.mul (cst 253) (k CP3)) (.mul (cst 254) (k CP5)))),
    .sub (sumPow (fun j => k (RA j)) 25)
      (.add (.mul (k CP1) (.sub (cst 252) (k VAL))) (.add (.mul (k CP3) (.sub (k VAL) (cst 253)))
        (.mul (k CP5) (.sub (k VAL) (cst 65536))))),
    .sub (sumPow (fun j => k (RB j)) 25) (.mul (k CP5) (.sub (cst MAXS) (k VAL))),
    .mul (k CP5) (.sub (k (CB 4)) (.add (k C4B0) (.mul (cst 2) (k C4B1)))) ]

/-- Segwit: constant within a transaction; at least one non-empty witness stack. -/
def segC : List Expr :=
  [ boolC (k SEG),
    .mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k SEG) (kp SEG))),
    .mul (k K_TXH) (k HASW),
    .mul (oneMinus (k K_TXH)) (.sub (k HASW) (.add (kp HASW) (.mul (kp K_WCNT) (oneMinus (kp Z1))))),
    .mul (k K_LOCK) (.mul (k SEG) (k Z2)) ]

def countC : List Expr :=
  [ .mul (k K_BLK) (.add (.sub (k TXL) (k VAL)) one),
    .mul notFirst (.add (.sub (k TXL) (kp TXL)) (kp K_LOCK)),
    .mul (k K_TXH) (.sub (k INL) (k VAL)),
    .mul (oneMinus (k K_TXH)) (.mul notFirst (.add (.sub (k INL) (kp INL)) (kp K_IN))),
    .mul (k K_TXH) (.sub (k NIN) (k VAL)),
    .mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k NIN) (kp NIN))),
    .mul (k K_NOUT) (.sub (k OUTL) (k VAL)),
    .mul (oneMinus (k K_NOUT)) (.mul notFirst (.add (.sub (k OUTL) (kp OUTL)) (kp K_OUT))),
    .mul (kp EOC) (.sub (k WINL) (k NIN)),
    .mul (oneMinus (kp EOC)) (.add (.sub (k WINL) (kp WINL)) (kp ESC)),
    .mul (k K_WCNT) (.sub (k ITEML) (k VAL)),
    .mul (oneMinus (k K_WCNT)) (.mul notFirst (.add (.sub (k ITEML) (kp ITEML)) (kp K_WITEM))),
    -- The block and every transaction are non-empty.
    .mul (k K_BLK) (k Z1),
    .mul (k K_TXH) (k Z1) ]

def zeroC : List Expr :=
  [.sub (k E1C) e1, .sub (k E2C) e2] ++ isZero Z1 INV1 (k E1C) ++ isZero Z2 INV2 (k E2C)

def bitC : List Expr :=
  [CP1, CP3, CP5, C4B0, C4B1].map (fun c => boolC (k c)) ++
  (List.range 25).flatMap (fun j => [boolC (k (RA j)), boolC (k (RB j)), boolC (k (RS j))])

/-- Per-transaction values (M3a.3). -/
def txC : List Expr :=
  [ .mul (k K_TXH) (.sub (k TXA) (k START)),
    .mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k TXA) (kp TXA))),
    .mul (kp EOC) (.sub (k WST) (k START)),
    .mul (oneMinus (kp EOC)) (.mul notFirst (.sub (k WST) (kp WST))),
    .mul (k K_BLK) (k TXI),
    .mul notFirst (.sub (k TXI) (.add (kp TXI) (kp K_LOCK))) ]

/-- M3a.4: the block token's transaction count is public input 1 (the Merkle tree's leaf count). -/
def pubC : List Expr := [.mul first (.sub (k VAL) (.pub 1))]

def constraints : List Expr := kindC ++ transC ++ tileC ++ compactC ++ segC ++ countC ++ zeroC ++ bitC ++ txC ++ pubC

/-- Byte reads: the CompactSize's bytes, and a segwit head's marker and flag. -/
def lookups : List Lookup :=
  [ ⟨REL_BYTE, .neg hasC, [.add (k START) (k OFF), k (CB 0)]⟩,
    ⟨REL_BYTE, .neg (.add (k CP3) (k CP5)), [.add (.add (k START) (k OFF)) (cst 1), k (CB 1)]⟩,
    ⟨REL_BYTE, .neg (.add (k CP3) (k CP5)), [.add (.add (k START) (k OFF)) (cst 2), k (CB 2)]⟩,
    ⟨REL_BYTE, .neg (k CP5), [.add (.add (k START) (k OFF)) (cst 3), k (CB 3)]⟩,
    ⟨REL_BYTE, .neg (k CP5), [.add (.add (k START) (k OFF)) (cst 4), k (CB 4)]⟩,
    ⟨REL_BYTE, .neg (.mul (k K_TXH) (k SEG)), [.add (k START) (cst 4), cst 0]⟩,
    ⟨REL_BYTE, .neg (.mul (k K_TXH) (k SEG)), [.add (k START) (cst 5), cst 1]⟩,
    ⟨REL_TX, .mul (k K_LOCK) (k TXM), [k TXI, k TXA, k SEG, k WST, k START]⟩ ]

def fields : Comp where
  air := { name := "block_fields", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

/-- Polynomial degree of an expression. -/
def degE : Expr → ℕ
  | .col .. => 1
  | .const _ => 0
  | .pub _ => 0
  | .add a b | .sub a b => max (degE a) (degE b)
  | .mul a b => degE a + degE b
  | .neg a => degE a

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Fields
