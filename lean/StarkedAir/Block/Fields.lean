/-
**Block fields (M3a.2 `BLK-FIELDS`, AIR layer).** One row per token (`Spec/BlockTokens.lean`).
Row `r` covers bytes `[START, START + LEN)`; rows tile the block from 0 to `LEN_pub` (`pub 0`, as in
`Block.bytes`), then padding. The row's CompactSize (if any) is read from the byte table at
`START + OFF` and decoded canonically; a segwit transaction head reads its marker `00` and flag
`01`. Counters and two is-zero helpers choose each row's kind from the previous row, following
the token grammar. Opaque fields (header, hashes, scripts, items, fixed-size fields) are not read
here.
-/
import StarkedAir.Block.Tables

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

/-! ### Per-transaction checks (M3a.5b, D-035)

Columns from `118` on. Byte slots `BY 0 … 7` read the block at `BASEC + j`: an output's 8 value bytes, a
lock time's 4 bytes, an input's 4 sequence bytes (`BASEC = START + LEN − 4` on input rows). Range slots
`RG 0 … 12` are looked up in the byte table `r8` on every row (unused slots hold 0); each kind of row
gives them its own meaning. Public inputs: `pub 2` the height, `pub 6` the segwit bit. -/

def FZ : ℕ := 118
def FL : ℕ := 119
def FS : ℕ := 120
def TY : ℕ := 121
def BASEC : ℕ := 122
def BY (j : ℕ) : ℕ := 123 + j
def AQ : ℕ := 131
def BQ : ℕ := 132
def INVQ : ℕ := 133
def EXPQ : ℕ := 134
def QH : ℕ := 135
def QB (j : ℕ) : ℕ := 136 + j
def OH (j : ℕ) : ℕ := 141 + j
def ZT : ℕ := 147
def INVT : ℕ := 148
def GIN : ℕ := 149
def INVN : ℕ := 150
def TLO : ℕ := 151
def THI : ℕ := 152
def CAR : ℕ := 153
def BOR : ℕ := 154
def RG (j : ℕ) : ℕ := 155 + j
def B2 : ℕ := 168
def BRW : ℕ := 169
def GL0 : ℕ := 170
def GL1 : ℕ := 171
def GZ : ℕ := 172
def GS : ℕ := 173
def CLO : ℕ := 174
def CHI : ℕ := 175
def WB : ℕ := 176
def NS : ℕ := 177
def SSC : ℕ := 178
def ZV : ℕ := 179
def INVV : ℕ := 180
def G0 : ℕ := 181
def ISC : ℕ := 182
def AFT : ℕ := 183
def HASC : ℕ := 184
def REQC : ℕ := 185
def REQ : ℕ := 186
def MML : ℕ := 187
def MMB : ℕ := 188
def DW : ℕ := 189
def N_MAIN' : ℕ := 190

/-- `script(start, len)`: a non-empty script (sigop walker). -/
def REL_SCRIPT : ℕ := 11
/-- `totals(W, NSEG, HASC)`: witness bytes, segwit transactions, whether a commitment output is claimed. -/
def REL_TOT : ℕ := 12
/-- `ctx(cutoffLo, cutoffHi)`: the finality cutoff's 16-bit limbs. -/
def REL_CTX : ℕ := 13
/-- `commit(start, len)`: the coinbase output taken as the witness commitment. -/
def REL_COMMIT : ℕ := 14

/-- `MAX_MONEY = MAXHI · 2^24 + MAXLO`. -/
def MAXLO : ℕ := 475136
def MAXHI : ℕ := 125169754
/-- The witness-commitment pattern `6a24aa21a9ed`. -/
def pat : List ℕ := [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed]

def by4 (j : ℕ) : Expr := k (BY j)
def rg (j : ℕ) : Expr := k (RG j)
def c (v : ℕ) : Expr := cst v
/-- `a + 256·b`, `a + 256·b + 65536·c`, … -/
def le2 (a b : Expr) : Expr := .add a (.mul (c 256) b)
def le3 (a b d : Expr) : Expr := .add (le2 a b) (.mul (c 65536) d)
def le4 (a b d e : Expr) : Expr := .add (le3 a b d) (.mul (c 16777216) e)
/-- An output's value limbs: bytes 0–2 and 3–6 (byte 7 is 0). -/
def vlo : Expr := le3 (by4 0) (by4 1) (by4 2)
def vhi : Expr := le4 (by4 3) (by4 4) (by4 5) (by4 6)
/-- A lock time's (or sequence's) 16-bit limbs. -/
def lo16 : Expr := le2 (by4 0) (by4 1)
def hi16 : Expr := le2 (by4 2) (by4 3)
def qE : Expr := .add (.mul (c 32) (k QH)) (sumPow (fun j => k (QB j)) 5)
def ohSum (f : ℕ → ℕ) : Expr := (List.range 6).foldr (fun j acc => .add (.mul (c (f j)) (k (OH j))) acc) (c 0)
def same (x : ℕ) : Expr := .mul notFirst (.sub (k x) (kp x))

def modeC : List Expr :=
  [FZ, FL, FS, TY].map (fun x => boolC (k x)) ++
  [ .sub (.add (k FZ) (.add (k FL) (k FS))) one ] ++
  [FZ, FL, FS, TY].map (fun x => .mul (oneMinus (k K_TXH)) (same x))

def valueC : List Expr :=
  [ .sub (k BASEC) (.add (k START) (.mul (k K_IN) (.sub (k LEN) (c 4)))),
    .mul (k K_OUT) (by4 7),
    .mul (k K_OUT) (.sub (rg 0) (.sub (c 7) (by4 6))),
    .mul (k K_OUT) (.sub (k TLO) (le3 (rg 1) (rg 2) (rg 3))),
    .mul (k K_OUT) (.sub (le3 (rg 4) (rg 5) (rg 6)) (.add (.sub (c MAXLO) (k TLO)) (.mul (c 16777216) (k BOR)))),
    .mul (k K_OUT) (.sub (le4 (rg 7) (rg 8) (rg 9) (rg 10)) (.sub (.sub (c MAXHI) (k THI)) (k BOR))),
    .mul (k K_OUT) (.sub (rg 11) (.sub (c 7) (rg 10))),
    boolC (k BOR), boolC (k CAR), .mul (oneMinus (k K_OUT)) (k CAR),
    .mul notFirst (.add (.sub (.sub (k TLO) (.mul (oneMinus (k K_TXH)) (kp TLO))) (.mul (k K_OUT) vlo))
      (.mul (c 16777216) (k CAR))),
    .mul notFirst (.sub (.sub (.sub (k THI) (.mul (oneMinus (k K_TXH)) (kp THI))) (.mul (k K_OUT) vhi)) (k CAR)),
    .mul (k K_NOUT) (.sub (.mul (k VAL) (k INVN)) one) ]

def prevoutC : List Expr :=
  [ boolC (k ZT), .mul (k ZT) (k TXI), .mul (oneMinus (k ZT)) (.sub (.mul (k TXI) (k INVT)) one),
    .sub (k GIN) (.mul (k K_IN) (oneMinus (k ZT))),
    boolC (k QH) ] ++ (List.range 5).map (fun j => boolC (k (QB j))) ++
  [ .mul (k QH) (.add (k (QB 2)) (.add (k (QB 3)) (k (QB 4)))) ] ++
  (List.range 6).map (fun j => boolC (k (OH j))) ++
  [ .mul (k MMB) (.sub (ohSum (fun _ => 1)) one),
    .sub (k AQ) (.add (.mul (k GIN) (.add (k START) qE)) (.mul (k MMB) (.add (k SSC) (ohSum id)))),
    .sub (k EXPQ) (.add (.mul (k GIN) (.mul (c 255) (k QH))) (.mul (k MMB) (ohSum (fun j => pat.getD j 0)))),
    .mul (.add (k GIN) (k MMB)) (.sub (.mul (.sub (k BQ) (k EXPQ)) (k INVQ)) one) ]

def finalC : List Expr :=
  [ .sub (k GZ) (.mul (k K_LOCK) (k FZ)),
    .sub (k GS) (.mul (k K_IN) (k FS)),
    .sub (k GL0) (.mul (k K_LOCK) (.mul (k FL) (oneMinus (k TY)))),
    .sub (k GL1) (.mul (k K_LOCK) (.mul (k FL) (k TY))),
    .mul (k GZ) (.add (by4 0) (.add (by4 1) (.add (by4 2) (by4 3)))) ] ++
  (List.range 4).map (fun j => .mul (k GS) (.sub (by4 j) (c 255))) ++
  [ .mul (k GL0) (by4 3),
    .mul (k GL0) (.sub (rg 0) (.sub (c 127) (by4 2))),
    .mul (k GL0) (.sub (le3 (rg 1) (rg 2) (rg 3)) (.sub (.sub (.pub 2) one) (le3 (by4 0) (by4 1) (by4 2)))),
    .mul (k GL1) (.sub (le2 (rg 4) (rg 5)) (.add (.sub lo16 (c 0x6500)) (.mul (c 65536) (k B2)))),
    .mul (k GL1) (.sub (le2 (rg 6) (rg 7)) (.sub (.sub hi16 (c 0x1DCD)) (k B2))),
    .mul (k GL1) (.sub (le2 (rg 8) (rg 9)) (.add (.sub (.sub (k CLO) lo16) one) (.mul (c 65536) (k BRW)))),
    .mul (k GL1) (.sub (le2 (rg 10) (rg 11)) (.sub (.sub (k CHI) hi16) (k BRW))),
    boolC (k B2), boolC (k BRW), same CLO, same CHI ]

def totalsC : List Expr :=
  [ .sub (k DW) (.add (.mul (c 2) (.mul (k K_TXH) (k SEG))) (.mul (.add (k K_WCNT) (k K_WITEM)) (k LEN))),
    .mul first (k WB), .mul notFirst (.sub (.sub (k WB) (kp WB)) (k DW)),
    .mul first (k NS), .mul notFirst (.sub (.sub (k NS) (kp NS)) (.mul (k K_TXH) (k SEG))),
    .sub (k SSC) (.add (.add (k START) (k OFF)) pref),
    boolC (k ZV), .mul (k ZV) (k VAL), .mul (oneMinus (k ZV)) (.sub (.mul (k VAL) (k INVV)) one) ]

def commitC : List Expr :=
  [ .sub (k G0) (.mul (k K_OUT) (.mul (k ZT) (.pub 6))),
    boolC (k ISC), .mul (k ISC) (oneMinus (k G0)),
    .mul first (k AFT), .mul notFirst (.sub (.sub (k AFT) (kp AFT)) (kp ISC)), .mul (k ISC) (k AFT),
    boolC (k HASC), same HASC, .mul isLast (.sub (k HASC) (k AFT)),
    .sub (k REQC) (.mul (k G0) (oneMinus (k ISC))),
    .sub (k REQ) (.mul (k REQC) (.add (oneMinus (k HASC)) (k AFT))),
    boolC (k MML), boolC (k MMB), .sub (.add (k MML) (k MMB)) (k REQ),
    .mul (k MML) (.sub (rg 12) (.sub (c 37) (k VAL))) ]

def chkC : List Expr := modeC ++ valueC ++ prevoutC ++ finalC ++ totalsC ++ commitC

def constraints : List Expr := kindC ++ transC ++ tileC ++ compactC ++ segC ++ countC ++ zeroC ++ bitC ++ txC ++ pubC ++ chkC

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

/-- M3a.5b: byte slots, the auxiliary read, range slots, and the tuples for the other components. -/
def chkLookups : List Lookup :=
  (List.range 8).map (fun j =>
    ⟨REL_BYTE, .neg (if j < 4 then .add (k K_OUT) (.add (k K_LOCK) (k K_IN)) else k K_OUT),
      [.add (k BASEC) (c j), by4 j]⟩) ++
  [ ⟨REL_BYTE, .neg (.add (k GIN) (k MMB)), [k AQ, k BQ]⟩ ] ++
  (List.range 13).map (fun j => ⟨Tables.REL_R8, .neg one, [rg j]⟩) ++
  [ ⟨REL_SCRIPT, .mul (.add (k K_IN) (k K_OUT)) (oneMinus (k ZV)), [k SSC, k VAL]⟩,
    ⟨REL_TOT, isLast, [k WB, k NS, k HASC]⟩,
    ⟨REL_CTX, .neg first, [k CLO, k CHI]⟩,
    ⟨REL_COMMIT, k ISC, [k SSC, k VAL]⟩,
    -- M3b: output and input tokens for the coin events (`Block/Coin.lean`)
    ⟨24, k K_OUT, [k TXI, k START, k LEN, k SSC, k VAL]⟩,
    ⟨25, k K_IN, [k TXI, k START]⟩ ]

def fields : Comp where
  air := { name := "block_fields", nMain := N_MAIN', pre := preCols, constraints := constraints }
  lookups := lookups ++ chkLookups

/-- Polynomial degree of an expression. -/
def degE : Expr → ℕ
  | .col .. => 1
  | .const _ => 0
  | .pub _ => 0
  | .add a b | .sub a b => max (degE a) (degE b)
  | .mul a b => degE a + degE b
  | .neg a => degE a

#guard constraints.all (fun c => degE c ≤ 3)
#guard (lookups ++ chkLookups).all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Fields
