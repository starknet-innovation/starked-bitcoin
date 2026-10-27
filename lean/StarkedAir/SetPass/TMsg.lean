/-
**The `TxOutSer` stream (`set_tmsg`).** SHA-256's message, one byte per row from row 0 (the row is the
stream position `Y`): the incoming pending bytes (public), then per record its `TxOutSer`:
`txid ‖ vout` (36 file bytes from the record's start), the 4 code bytes (`set_rec`'s), `ser` (file bytes
from the record's start + 49). Records come from `rec(r, start, len)`, in order from 0; a record's rows
are its parts in order (`P0`: 36 rows, `PC`: 4, `PS`: `len`), counted by `O`, and it ends at
`O = 39 + len`; the stream ends at a record's end.

The whole blocks (`m = nb_out − nb_in ≥ 1` of them) yield big-endian words `w(y − 3, lo, hi)` at rows
`y ≡ 3 (mod 4)`; the rest (`TAIL`, fewer than 64 rows from a multiple of 64) are the outgoing pending
bytes (the `psho` table). The last record walked is the segment's last (`i_out − i_in − 1`), and row 0
consumes `set_shac`'s end token.
-/
import StarkedAir.SetPass.Layout

namespace StarkedAir.SetPass.TMsg

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)

def ON : ℕ := 0
def Y : ℕ := 1
def B : ℕ := 2
/-- Row kinds: an incoming pending byte, a record's outpoint, code or `ser` byte. -/
def PND : ℕ := 3
def P0 : ℕ := 4
def PC : ℕ := 5
def PS : ℕ := 6
/-- A record's first row, the first record's first row, a record's last row. -/
def NEW : ℕ := 7
def FR : ℕ := 8
def ENDR : ℕ := 9
def R : ℕ := 10
def O : ℕ := 11
def RST : ℕ := 12
def RLEN : ℕ := 13
def TAIL : ℕ := 14
/-- `ON · (1 − TAIL)`, and the stream's last row (on, the next off). -/
def NT : ℕ := 15
def ENDS : ℕ := 16
/-- The block index `⌊Y / 64⌋`. -/
def SB : ℕ := 17
def N_MAIN : ℕ := 18

def per4 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 4).map f)
def per64 (f : ℕ → ℕ) : PreCol := .periodic ((List.range 64).map f)
def preCols : List PreCol :=
  [.isFirst, .notLast, per4 (fun r => if r = 3 then 1 else 0), per64 (fun r => if r = 0 then 1 else 0),
   per64 (fun r => if r = 63 then 1 else 0), per64 id]
def P_FIRST : ℕ := 0
def P_NOTLAST : ℕ := 1
def P_IS3 : ℕ := 2
def P_B0 : ℕ := 3
def P_B63 : ℕ := 4
def P_K64 : ℕ := 5

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := p P_FIRST
def notFirst : Expr := om first
def isLast : Expr := om (p P_NOTLAST)

def rec : Expr := .add (.add (k P0) (k PC)) (k PS)
/-- Continuing record rows: record rows that are not a record's first. -/
def cont : Expr := .sub rec (k NEW)
def qlenIn : Expr := .pub (H_PLEN SHA_IN)

def constraints : List Expr :=
  [ON, PND, P0, PC, PS, NEW, ENDR, TAIL].map (fun c => boolC (k c)) ++
  [ -- rows: a nonempty prefix, each of one kind; the position is the row
    .sub (k ON) (.add (k PND) rec),
    .mul first (om (k ON)), .mul isLast (k ON), .mul notFirst (.mul (k ON) (om (kp ON))),
    .mul first (k Y), .mul notFirst (.sub (.sub (k Y) (kp Y)) one),
    -- pending rows: a prefix of qlen_in rows
    .mul notFirst (.mul (k PND) (om (kp PND))),
    .mul first (.mul (om (k PND)) qlenIn),
    .mul notFirst (.mul (.sub (kp PND) (k PND)) (.sub (k Y) qlenIn)),
    -- records: the first starts after the pending rows, each next one after a record's end
    .sub (k FR) (.add (.mul first (om (k PND))) (.mul notFirst (.mul (kp PND) (om (k PND))))),
    .sub (k NEW) (.add (k FR) (.mul notFirst (.mul (kp ENDR) (k ON)))),
    .mul (k NEW) (om (k P0)), .mul (k NEW) (k O), .mul (k FR) (k R),
    .mul (.sub (k NEW) (k FR)) (.sub (.sub (k R) (kp R)) one),
    .mul cont (.sub (k R) (kp R)), .mul cont (.sub (k RST) (kp RST)), .mul cont (.sub (k RLEN) (kp RLEN)),
    .mul cont (.sub (.sub (k O) (kp O)) one),
    -- parts: 36 outpoint rows, 4 code rows, then ser rows to the record's end
    .mul (k P0) (om (.add (kn P0) (kn PC))),
    .mul (k P0) (.mul (kn PC) (.sub (k O) (cst 35))),
    .mul (k PC) (om (.add (kn PC) (kn PS))),
    .mul (k PC) (.mul (kn PS) (.sub (k O) (cst 39))),
    .mul (k PS) (.mul (om (k ENDR)) (om (kn PS))),
    .mul (k ENDR) (om (k PS)),
    .mul (k ENDR) (.sub (k O) (.add (cst 39) (k RLEN))),
    .sub (k ENDS) (.mul (k ON) (om (kn ON))),
    .mul (k ENDS) (om (k ENDR)),
    -- the tail: from a multiple of 64 to the end, under 64 rows; whole blocks before it
    .mul (k TAIL) (om (k ON)), .mul first (k TAIL),
    .mul (k ON) (.mul (kp TAIL) (om (k TAIL))),
    .mul (k TAIL) (.mul (om (kp TAIL)) (om (p P_B0))),
    .mul (k TAIL) (p P_B63),
    .sub (k NT) (.mul (k ON) (om (k TAIL))),
    .mul (k NT) (.mul (om (p P_B63)) (om (kn ON))),
    .mul first (k SB), .mul notFirst (.sub (.sub (k SB) (kp SB)) (p P_B0)),
    -- the outgoing state: pending length and block count
    .mul (k ENDS) (.sub (.pub (H_PLEN SHA_OUT)) (.mul (k TAIL) (.add (p P_K64) one))),
    .mul (k ENDS) (.sub (.sub (.pub (H_NB SHA_OUT)) (.pub (H_NB SHA_IN))) (.sub (.add (k SB) one) (k TAIL))),
    -- every record: the last one walked is the segment's last
    .mul (k ENDS) (.sub (.add (k R) one) (.sub (.pub PUB_I_OUT) (.pub PUB_I_IN))) ]

/-- The big-endian word ending at the row: bytes at offsets `−3 … 0`. -/
def hiW : Expr := .add (.mul (cst 256) (col B (-3))) (col B (-2))
def loW : Expr := .add (.mul (cst 256) (col B (-1))) (k B)

def lookups : List Lookup :=
  [ ⟨REL_PSHI, .neg (k PND), [k Y, k B]⟩,
    ⟨Block.REL_BYTE, .neg (k P0), [.add (k RST) (k O), k B]⟩,
    ⟨REL_CODE, .neg (k PC), [k R, .sub (k O) (cst 36), k B]⟩,
    ⟨Block.REL_BYTE, .neg (k PS), [.add (.add (k RST) (k O)) (cst 9), k B]⟩,
    ⟨REL_REC, .neg (k NEW), [k R, k RST, k RLEN]⟩,
    ⟨REL_PSHO, .neg (k TAIL), [p P_K64, k B]⟩,
    ⟨REL_SW, .mul (k NT) (p P_IS3), [.sub (k Y) (cst 3), loW, hiW]⟩,
    ⟨REL_SHEND, .neg first, [.sub (.sub (.pub (H_NB SHA_OUT)) (.pub (H_NB SHA_IN))) one]⟩ ]

def tmsg : Comp where
  air := { name := "set_tmsg", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.SetPass.TMsg
