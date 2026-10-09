/-
**Hash messages (M3a.3 `BLK-SHA`, message component).** One row per byte of a padded SHA-256
message. Messages: the header (id 0, bytes `[0, 80)`), and per transaction `i` its txid message
(id `1 + 2i`) and wtxid message (id `2 + 2i`), from the fields' tuple `tx(i, a, seg, w, l)`:

* whole messages (wtxid, legacy txid, header): bytes `[a, l + 4)`;
* split messages (segwit txid): `[a, a + 4) ++ [a + 6, w) ++ [l, l + 4)` (pieces 0, 1, 2).

Data bytes come from the byte table. Then the SHA padding: `80`, zeros up to byte 56 of a block, and
the 8-byte big-endian bit length. Messages start at rows `≡ 0 (mod 64)`, so a row's position in its
block is the preprocessed `row mod 64`. Every 4th row yields the word ending there,
`msgw(id, byte index, lo, hi)`, and a message's last row yields its padded length `mlen(id, len)`.
-/
import StarkedAir.Block.Fields

namespace StarkedAir.Block.Msg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC sumPow)
open StarkedAir.Block.Fields (REL_TX degE)

def REL_MSGW : ℕ := 5
def REL_MLEN : ℕ := 6

/-! ### Columns -/

def D : ℕ := 0
def P80 : ℕ := 1
def ZR : ℕ := 2
def LN : ℕ := 3
def NIL : ℕ := 4
def FIRSTM : ℕ := 5
def PC0 : ℕ := 6
def PC1 : ℕ := 7
def PC2 : ℕ := 8
def MT : ℕ := 9
def HDR : ℕ := 10
def WTX : ℕ := 11
def SEG : ℕ := 12
def TI : ℕ := 13
def TA : ℕ := 14
def TW : ℕ := 15
def TL : ℕ := 16
def MID : ℕ := 17
def IDX : ℕ := 18
def POS : ℕ := 19
def BYTE : ℕ := 20
def BIT0 : ℕ := 21
def EZ : ℕ := 29
def Z : ℕ := 30
def INV : ℕ := 31
def CONT : ℕ := 32
def SW : ℕ := 33
def ENDD : ℕ := 34
def DLC : ℕ := 35
def WM : ℕ := 36
def MM : ℕ := 37
def N_MAIN : ℕ := 38

/-- Preprocessed: `isFirst`, `notLast`, then indicators of `row mod 64`: `= 0`, `≡ 3 (mod 4)`,
`= 55`, `= 63`, `∈ [56, 60)`, `= 56`. -/
def per64 (p : ℕ → Bool) : PreCol := .periodic ((List.range 64).map fun q => if p q then 1 else 0)
def preCols : List PreCol :=
  [.isFirst, .notLast, per64 (· = 0), per64 (· % 4 = 3), per64 (· = 55), per64 (· = 63),
   per64 (fun q => 56 ≤ q && q < 60), per64 (· = 56)]

def FIRST : ℕ := 0
def NOTLAST : ℕ := 1
def IS0 : ℕ := 2
def IS3 : ℕ := 3
def IS55 : ℕ := 4
def IS63 : ℕ := 5
def LZ : ℕ := 6
/-- `row mod 64 = 56`: the previous row is at 55 (preprocessed columns are read at offset 0 only;
likewise "the previous row is at 63" is `IS0`). -/
def IS56 : ℕ := 7

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def notFirst : Expr := om (pre FIRST)

/-- The value the is-zero test checks: the end of piece 0 (index 3) or 1 (position `w − 1`) of a
split message, else the end of the data (position `l + 3`). -/
def ezE : Expr :=
  .add (.mul (k MT) (.add (.mul (k PC0) (.sub (k IDX) (cst 3)))
    (.add (.mul (k PC1) (.add (.sub (k POS) (k TW)) one)) (.mul (k PC2) (.sub (k POS) (.add (k TL) (cst 3)))))))
    (.mul (om (k MT)) (.sub (k POS) (.add (k TL) (cst 3))))

def kinds : List ℕ := [D, P80, ZR, LN, NIL]

def kindC : List Expr :=
  ([D, P80, ZR, LN, NIL, FIRSTM, PC0, PC1, PC2, HDR, WTX, SEG, Z] ++ (List.range 8).map (BIT0 + ·)).map
    (fun c => boolC (k c)) ++
  [ .sub (kinds.foldr (fun c acc => .add (k c) acc) (cst 0)) one,
    .mul (k FIRSTM) (om (k D)),
    .mul (k FIRSTM) (om (pre IS0)),
    .mul (om (pre NOTLAST)) (om (k NIL)) ]

def transC : List Expr :=
  [ .sub (k CONT) (.mul (k D) (om (k Z))),
    .sub (k SW) (.mul (k Z) (.mul (k MT) (.add (k PC0) (k PC1)))),
    .sub (k ENDD) (.sub (.mul (k D) (k Z)) (k SW)),
    .sub (.sub (k D) (k FIRSTM)) (.add (kp CONT) (kp SW)),
    .sub (k P80) (kp ENDD),
    .sub (k ZR) (.mul (.add (kp P80) (kp ZR)) (om (pre IS56))),
    .sub (k LN) (.add (.mul (.add (kp P80) (kp ZR)) (pre IS56)) (.mul (kp LN) (om (pre IS0)))),
    .sub (.add (k NIL) (k FIRSTM)) (.add (.mul (kp LN) (pre IS0)) (kp NIL)),
    .sub (.add (k PC0) (.add (k PC1) (k PC2))) (k D),
    .sub (.sub (k PC0) (k FIRSTM)) (.mul (kp CONT) (kp PC0)),
    .sub (k PC1) (.add (.mul (kp CONT) (kp PC1)) (.mul (kp SW) (kp PC0))),
    .sub (k PC2) (.add (.mul (kp CONT) (kp PC2)) (.mul (kp SW) (kp PC1))) ]

def msgC : List Expr :=
  [ .sub (k MT) (.mul (.sub (om (k WTX)) (k HDR)) (k SEG)),
    .mul (k HDR) (k TA),
    .mul (k HDR) (.sub (k TL) (cst 76)),
    .mul (k WTX) (k HDR),
    .sub (k MID) (.mul (om (k HDR)) (.add (.add one (.mul (cst 2) (k TI))) (k WTX))),
    .mul (k D) (.sub (k POS) (.add (.add (.add (k TA) (k IDX)) (.mul (cst 2) (k PC1)))
      (.mul (k PC2) (.add (.sub (k TL) (k TW)) (cst 2))))),
    .sub (k EZ) ezE,
    .mul (k Z) (k EZ),
    .mul (om (k Z)) (.sub (.mul (k EZ) (k INV)) one),
    .mul (k FIRSTM) (k IDX),
    .mul (om (k FIRSTM)) (.mul notFirst (.sub (.sub (k IDX) (kp IDX)) one)) ] ++
  [HDR, WTX, SEG, TI, TA, TW, TL].map (fun c => .mul (om (k FIRSTM)) (.mul notFirst (.sub (k c) (kp c))))

def byteE (off : ℤ) : Expr := col BYTE off

def padC : List Expr :=
  [ .sub (k BYTE) (sumPow (fun j => k (BIT0 + j)) 8),
    .mul (k P80) (.sub (k BYTE) (cst 128)),
    .mul (k ZR) (k BYTE),
    .mul (k LN) (.mul (pre LZ) (k BYTE)),
    .mul (pre IS63) (.mul (k LN) (.sub (.add (.add (.add (.mul (cst 16777216) (byteE (-3)))
      (.mul (cst 65536) (byteE (-2)))) (.mul (cst 256) (byteE (-1)))) (k BYTE)) (.mul (cst 8) (k DLC)))),
    .mul (k P80) (.sub (k DLC) (k IDX)),
    .mul (om (k P80)) (.mul notFirst (.sub (k DLC) (kp DLC))),
    .mul (k WM) (k NIL),
    .mul (k MM) (om (pre IS63)),
    .mul (k MM) (om (k LN)) ]

def constraints : List Expr := kindC ++ transC ++ msgC ++ padC

def lookups : List Lookup :=
  [ ⟨StarkedAir.Block.REL_BYTE, .neg (k D), [k POS, k BYTE]⟩,
    ⟨REL_TX, .neg (.mul (k FIRSTM) (om (k HDR))), [k TI, k TA, k SEG, k TW, k TL]⟩,
    ⟨REL_MSGW, .mul (pre IS3) (k WM),
      [k MID, .sub (k IDX) (cst 3), .add (.mul (cst 256) (byteE (-1))) (k BYTE),
       .add (.mul (cst 256) (byteE (-3))) (byteE (-2))]⟩,
    ⟨REL_MLEN, .mul (k LN) (k MM), [k MID, .add (k IDX) one]⟩ ]

def msg : Comp where
  air := { name := "block_msg", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Msg
