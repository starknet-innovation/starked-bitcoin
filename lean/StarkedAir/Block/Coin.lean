/-
**Coin events (M3b, D-040).** One row per input and output token of the block, in position order. Each
row is one of three kinds:
- **an output (`KO`)** creates `+1/(z − φ)`, unless the output is unspendable (first script byte `0x6a`,
  or a script over 10,000 bytes) or BIP30-lost;
- **a non-coinbase input (`KI`)** spends `−1/(z − φ)`;
- **the coinbase input (`CBI`)** is only consumed.

The tuple `φ = Σₖ αₖ tₖ` covers:
- the txid's 16 limbs and the output index (2 limbs);
- `code = 2·height + coinbase` (2 limbs);
- the `serTxOut` fingerprint (4 coordinates, `block_fpwalk`) and its length;
- the creation transaction index.

The running sum against the public `(α, z)` is `ExtSum`'s; the block's partial sum and its input count are
public.

* Rows are a prefix with strictly increasing token starts (range-checked), so they are the block's tokens
  in order. The output index counts the outputs after a transaction's inputs, and the record index `J`
  counts the non-coinbase inputs before the row.
* Outputs: the txid is SHA's digest of message `1 + 2·tx`, and the code comes from `pub 2` and `tx = 0`.
  The output's bytes are offered as the segment `(0, start)`, whose fingerprint comes back.
* Inputs: the txid and index limbs come from the 36 prevout bytes; the code and amount from undo
  record `J` (`block_urec`), and the fingerprint from segment `(1, J)`. The claimed creation
  `(height, tx)` is lexicographically earlier than `(pub 2, tx)`, and a coinbase coin is at least 100
  blocks old.
-/
import StarkedAir.Block.URec
import StarkedAir.Block.Ctx

namespace StarkedAir.Block.Coin

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

/-- `out(tx, start, len, script start, script length)` and `in(tx, start)`, yielded by the fields. -/
def REL_OUTT : ℕ := 24
def REL_INT : ℕ := 25

-- kinds and token
def KO : ℕ := 0
def KI : ℕ := 1
def CBI : ℕ := 2
def TXI : ℕ := 3
def START : ℕ := 4
def LEN : ℕ := 5
def SSC : ℕ := 6
def SVAL : ℕ := 7
/-- `START − START_prev − 1`, as three bytes. -/
def D (i : ℕ) : ℕ := 8 + i
def VOUT : ℕ := 11
def VLO : ℕ := 12
def VHI : ℕ := 13
def VB (i : ℕ) : ℕ := 14 + i
def J : ℕ := 16
def ZI : ℕ := 17
def CBO : ℕ := 18
/-- Prevout bytes `PB 0 … PB 35`. -/
def PB (i : ℕ) : ℕ := 19 + i
/-- Txid limbs `TL 0 … TL 15`. -/
def TLB (i : ℕ) : ℕ := 55 + i
def CLO : ℕ := 71
def CHI : ℕ := 72
def CB (i : ℕ) : ℕ := 73 + i
/-- The undo record's amount limbs. -/
def VAMT (i : ℕ) : ℕ := 75 + i
def HC : ℕ := 79
def CBC : ℕ := 80
def HB (i : ℕ) : ℕ := 81 + i
def CTX : ℕ := 84
def ORD : ℕ := 85
def OB (i : ℕ) : ℕ := 86 + i
def MB (i : ℕ) : ℕ := 89 + i
def FH : ℕ := 92
def SLEN : ℕ := 96
def SB : ℕ := 97
def ZS : ℕ := 98
def SINV : ℕ := 99
def U6A : ℕ := 100
def INVB : ℕ := 101
def BIG : ℕ := 102
def GB (i : ℕ) : ℕ := 103 + i
def UNSP : ℕ := 106
def U6Z : ℕ := 107
def MM : ℕ := 108
def FC : ℕ := 109
def ACC : ℕ := 113
/-- The fingerprint segment's id: the start for an output, the record index for an input. -/
def SIDC : ℕ := 117
-- amounts (24-bit low and high limbs)
def VL : ℕ := 118
def VH : ℕ := 119
def INL : ℕ := 120
def INH : ℕ := 121
def OUL : ℕ := 122
def OUH : ℕ := 123
def CY : ℕ := 124
def FEL : ℕ := 125
def FEH : ℕ := 126
def FCY : ℕ := 127
def CBL : ℕ := 128
def CBH : ℕ := 129
/-- The transaction's last output row. -/
def TEND : ℕ := 130
/-- Comparator 1 (`A − B ≥ 0`): low bytes, high bytes, borrow. -/
def Q1 (i : ℕ) : ℕ := 131 + i
def H1 (i : ℕ) : ℕ := 134 + i
def BR1 : ℕ := 138
def NB (i : ℕ) : ℕ := 139 + i
def FB (i : ℕ) : ℕ := 142 + i
/-- Comparator 2 (the block's coinbase): low bytes, high bytes, the low limb's carry `KP − KN`. -/
def Q2 (i : ℕ) : ℕ := 145 + i
def H2 (i : ℕ) : ℕ := 148 + i
def KP : ℕ := 152
def KN : ℕ := 153
/-- The range checks' multiplicities, as boolean columns: `KI + KO`, `KI + tf`, the last on row. -/
def MNB : ℕ := 154
def MC1 : ℕ := 155
def MLO : ℕ := 156
/-- `7 − H1 3` and `7 − H2 3`, range-checked: the comparators' high limbs stay below `2^27 < P`, so their
equations cannot wrap modulo `P` (as in the fields' value check). -/
def H1C : ℕ := 157
def H2C : ℕ := 158
/-- Comparator 3 (the block's accumulated fees within `MAX_MONEY`, Core's
`bad-txns-accumulated-fee-outofrange`): low bytes, high bytes, borrow, the high limb's top-byte bound. -/
def Q3 (i : ℕ) : ℕ := 159 + i
def H3 (i : ℕ) : ℕ := 162 + i
def BR3 : ℕ := 166
def H3C : ℕ := 167
def N_MAIN : ℕ := 168

-- public inputs (after the block's 41 and the fingerprint's `γ` at 41–44); `VAMT` is unused (amounts are
-- `VL`, `VH`)
def PUB_Z : ℕ := 45
def W : ℕ := 26
def PUB_ALPHA (j : ℕ) : ℕ := 49 + 4 * j
def PUB_S : ℕ := 153
def PUB_NIN : ℕ := 157
def PUB_LOST : ℕ := 158
/-- The block subsidy, as 24-bit low and high limbs. -/
def PUB_SUBL : ℕ := 159
def PUB_SUBH : ℕ := 160
def N_PUB : ℕ := 161

def preCols : List PreCol := [.isFirst, .notLast]
def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := pre 0
def notFirst : Expr := om first
def notLast : Expr := pre 1
def isLast : Expr := om notLast
def on : Expr := .add (.add (k KO) (k KI)) (k CBI)
def onp : Expr := .add (.add (kp KO) (kp KI)) (kp CBI)
def onn : Expr := .add (.add (kn KO) (kn KI)) (kn CBI)
def b3 (f : ℕ → ℕ) : Expr := .add (.add (k (f 0)) (.mul (cst 256) (k (f 1)))) (.mul (cst 65536) (k (f 2)))
def pair (a b : ℕ) : Expr := .add (k a) (.mul (cst 256) (k b))
def height : Expr := .pub 2

/-- The tuple, `w = 26` entries. -/
def tuple : List Expr :=
  (List.range 16).map (fun i => k (TLB i)) ++
  [k VLO, k VHI, k CLO, k CHI, k FH, k (FH + 1), k (FH + 2), k (FH + 3), k SLEN, k CTX]

#guard tuple.length = W

def phi : QE :=
  (List.range W).foldl (fun acc j => acc.add ((pubQ (PUB_ALPHA j)).mul (base (tuple.getD j (cst 0))))) (base (cst 0))

/-- The txid limbs from the prevout bytes: word `w` is big-endian bytes `4w … 4w + 3`; limb `2w` its low
half, `2w + 1` its high half. -/
def prevLimb (i : ℕ) : Expr :=
  let w := i / 2
  if i % 2 = 0 then pair (PB (4 * w + 3)) (PB (4 * w + 2)) else pair (PB (4 * w + 1)) (PB (4 * w))

def lastOn : Expr := .mul notLast (.sub on onn)
def b4 (f : ℕ → ℕ) : Expr := .add (b3 f) (.mul (cst 16777216) (k (f 3)))
def two24 : Expr := cst 16777216
/-- A transaction's last output, not the coinbase's: the fee check. -/
def tf : Expr := .mul (k TEND) (om (k CBO))

/-- Amounts: running input and output sums per transaction, the fees, the coinbase's outputs; inputs within
`MAX_MONEY` and at least the outputs; the coinbase within subsidy plus fees. -/
def amountC : List Expr :=
  [ boolC (k CY), boolC (k FCY), boolC (k BR1), boolC (k KP), boolC (k KN), .mul (k KP) (k KN),
    boolC (k MNB), boolC (k MC1), boolC (k MLO),
    .sub (k MNB) (.add (k KI) (k KO)), .sub (k MC1) (.add (k KI) tf), .sub (k MLO) lastOn,
    -- inputs: a running sum (fresh after outputs or at the start), normalized, within MAX_MONEY
    .mul (k KI) (.sub (.add (k INL) (.mul two24 (k CY))) (.add (.mul (kp KI) (kp INL)) (k VL))),
    .mul (k KI) (.sub (k INH) (.add (.add (.mul (kp KI) (kp INH)) (k VH)) (k CY))),
    .mul (k KI) (.sub (k INL) (b3 NB)),
    .mul (k KI) (.sub (b3 Q1) (.add (.sub (cst Fields.MAXLO) (k INL)) (.mul two24 (k BR1)))),
    .mul (k KI) (.sub (b4 H1) (.sub (.sub (cst Fields.MAXHI) (k INH)) (k BR1))),
    -- outputs: the inputs' sum carried, a running output sum, normalized
    .mul (k KO) (.sub (k INL) (kp INL)), .mul (k KO) (.sub (k INH) (kp INH)),
    .mul (k KO) (.sub (.add (k OUL) (.mul two24 (k CY))) (.add (.mul (kp KO) (kp OUL)) (k VL))),
    .mul (k KO) (.sub (k OUH) (.add (.add (.mul (kp KO) (kp OUH)) (k VH)) (k CY))),
    .mul (k KO) (.sub (k OUL) (b3 NB)),
    -- the transaction's end: inputs at least outputs (the fee)
    .sub (k TEND) (.mul (k KO) (om (kn KO))),
    .mul tf (.sub (b3 Q1) (.add (.sub (k INL) (k OUL)) (.mul two24 (k BR1)))),
    .mul tf (.sub (b4 H1) (.sub (.sub (k INH) (k OUH)) (k BR1))),
    -- the fees: summed over the block, normalized
    .sub (.add (k FEL) (.mul two24 (k FCY))) (.add (.mul notFirst (kp FEL)) (.mul tf (b3 Q1))),
    .sub (k FEH) (.add (.add (.mul notFirst (kp FEH)) (.mul tf (b4 H1))) (k FCY)),
    .sub (k FEL) (b3 FB),
    -- the coinbase's outputs (its last output row)
    .sub (k CBL) (.add (.mul notFirst (kp CBL)) (.mul (.mul (k TEND) (k CBO)) (k OUL))),
    .sub (k CBH) (.add (.mul notFirst (kp CBH)) (.mul (.mul (k TEND) (k CBO)) (k OUH))),
    -- the block: coinbase outputs at most subsidy plus fees
    .mul lastOn (.sub (b3 Q2) (.add (.sub (.add (.pub PUB_SUBL) (k FEL)) (k CBL))
      (.mul two24 (.sub (k KN) (k KP))))),
    .mul lastOn (.sub (b4 H2) (.add (.sub (.add (.pub PUB_SUBH) (k FEH)) (k CBH)) (.sub (k KP) (k KN)))),
    -- the comparators' top bytes are at most 7
    .sub (k H1C) (.sub (cst 7) (k (H1 3))), .sub (k H2C) (.sub (cst 7) (k (H2 3))),
    -- the accumulated fees within MAX_MONEY, after each non-coinbase transaction
    boolC (k BR3),
    .mul tf (.sub (b3 Q3) (.add (.sub (cst Fields.MAXLO) (k FEL)) (.mul two24 (k BR3)))),
    .mul tf (.sub (b4 H3) (.sub (.sub (cst Fields.MAXHI) (k FEH)) (k BR3))),
    .sub (k H3C) (.sub (cst 7) (k (H3 3))) ]

def localC : List Expr :=
  [KO, KI, CBI, CBC, ORD, U6A, BIG, ZS].map (fun c => boolC (k c)) ++
  [ boolC on,
    -- rows: a prefix, in increasing position
    .mul notFirst (.mul on (om onp)), .mul isLast on,
    .mul notFirst (.mul on (.sub (.sub (.sub (k START) (kp START)) one) (b3 D))),
    -- the transaction is the coinbase: `CBO = [TXI = 0]`
    .sub (k CBO) (om (.mul (k TXI) (k ZI))), .mul (k CBO) (k TXI),
    .mul (k CBI) (om (k CBO)), .mul (k KI) (k CBO),
    -- the record index and the output index
    .mul first (k J), .mul notFirst (.sub (k J) (.add (kp J) (kp KI))),
    .mul (k KO) (.sub (k VOUT) (.mul (kp KO) (.add (kp VOUT) one))),
    .mul (k KO) (.sub (.add (k VLO) (.mul (cst 65536) (k VHI))) (k VOUT)),
    .mul (k KO) (.sub (k VLO) (pair (VB 0) (VB 1))),
    .mul (k KI) (.sub (k VLO) (pair (PB 32) (PB 33))), .mul (k KI) (.sub (k VHI) (pair (PB 34) (PB 35))),
    -- txid limbs of an input
    .mul (k KO) (.sub (.add (k CLO) (.mul (cst 65536) (k CHI))) (.add (.mul (cst 2) height) (k CBO))),
    .mul (k KO) (.sub (k CLO) (pair (CB 0) (CB 1))),
    .mul (k KO) (.sub (k CTX) (k TXI)), .mul (k KO) (.sub (k SLEN) (k LEN)),
    -- the claim: code = 2·HC + CBC, order and maturity
    .mul (k KI) (.sub (.add (k CLO) (.mul (cst 65536) (k CHI))) (.add (.mul (cst 2) (k HC)) (k CBC))),
    .mul (k KI) (.sub (k HC) (b3 HB)),
    .mul (k KI) (.mul (om (k ORD)) (.sub (k HC) height)),
    .mul (k KI) (.sub (b3 OB) (.add (.mul (k ORD) (.sub (.sub height one) (k HC)))
      (.mul (om (k ORD)) (.sub (.sub (k TXI) one) (k CTX))))),
    .mul (k KI) (.mul (k CBC) (.sub (.sub (.sub height (k HC)) (cst 100)) (b3 MB))),
    -- unspendable: an `OP_RETURN` first byte (nonempty script) or more than 10,000 bytes
    .sub (k ZS) (om (.mul (k SVAL) (k SINV))), .mul (k ZS) (k SVAL),
    .sub (om (k U6A)) (.mul (.sub (k SB) (cst 0x6a)) (k INVB)), .mul (k U6A) (.sub (k SB) (cst 0x6a)),
    .sub (k U6Z) (.mul (k U6A) (om (k ZS))),
    .mul (k KO) (.sub (b3 GB) (.add (.mul (k BIG) (.sub (k SVAL) (cst 10001))) (.mul (om (k BIG)) (.sub (cst 10000) (k SVAL))))),
    .sub (k UNSP) (.sub (.add (k U6Z) (k BIG)) (.mul (k U6Z) (k BIG))),
    -- the multiplicity
    .sub (k MM) (.sub (.mul (k KO) (.mul (om (k UNSP)) (om (.mul (k CBO) (.pub PUB_LOST))))) (k KI)),
    -- the input count
    .mul lastOn (.sub (.add (k J) (k KI)) (.pub PUB_NIN)),
    .mul first (.mul (om on) (.pub PUB_NIN)),
    .sub (k SIDC) (.add (.mul (k KO) (k START)) (.mul (k KI) (k J))) ] ++
  (List.range 16).map (fun i => .mul (k KI) (.sub (k (TLB i)) (prevLimb i)))

/-- The running sum (`ExtSum`'s constraints, on this layout). -/
def mE : Expr := k MM
def fracC : List Expr := (((pubQ PUB_Z).sub phi).mul (colQ FC) |>.sub (base mE)).coords
def zeroC : List Expr := (colQ FC).coords.map fun e => .mul (.sub one (.mul mE mE)) e
def accC : List Expr := ((colQ ACC).sub (((base notFirst).mul (colQ ACC (-1))).add (colQ FC))).coords
def lastC : List Expr := ((base isLast).mul ((colQ ACC).sub (pubQ PUB_S))).coords

def constraints : List Expr := localC ++ fracC ++ zeroC ++ accC ++ lastC ++ amountC

def r8 (e : Expr) (m : Expr) : Lookup := ⟨Tables.REL_R8, .neg m, [e]⟩

def lookups : List Lookup :=
  [ ⟨REL_OUTT, .neg (k KO), [k TXI, k START, k LEN, k SSC, k SVAL, k VL, k VH]⟩,
    ⟨REL_INT, .neg (.add (k KI) (k CBI)), [k TXI, k START]⟩,
    ⟨Sha.REL_DIGEST, .neg (k KO), (.add (.mul (cst 2) (k TXI)) one) :: (List.range 16).map (fun i => k (TLB i))⟩,
    ⟨URec.REL_UREC, .neg (k KI), [k J, k CLO, k CHI, k VL, k VH]⟩,
    ⟨FpWalk.REL_SEG, k KO, [cst 0, k START, k START, k LEN]⟩,
    ⟨FpWalk.REL_FP, .neg (.add (k KO) (k KI)),
      [k KI, k SIDC, k SLEN, k FH, k (FH + 1), k (FH + 2), k (FH + 3)]⟩,
    ⟨REL_BYTE, .neg (.mul (k KO) (om (k ZS))), [k SSC, k SB]⟩ ] ++
  (List.range 36).map (fun i => ⟨REL_BYTE, .neg (k KI), [.add (k START) (cst i), k (PB i)]⟩) ++
  (List.range 3).map (fun i => r8 (k (D i)) (.mul notFirst on)) ++
  [r8 (k (VB 0)) (k KO), r8 (k (VB 1)) (k KO), r8 (k VHI) (k KO), r8 (k (CB 0)) (k KO), r8 (k (CB 1)) (k KO),
    r8 (k CHI) (k KO)] ++
  (List.range 3).map (fun i => r8 (k (HB i)) (k KI)) ++
  (List.range 3).map (fun i => r8 (k (OB i)) (k KI)) ++
  (List.range 3).map (fun i => r8 (k (MB i)) (.mul (k KI) (k CBC))) ++
  (List.range 3).map (fun i => r8 (k (GB i)) (k KO)) ++
  (List.range 3).map (fun i => r8 (k (NB i)) (k MNB)) ++
  (List.range 3).map (fun i => r8 (k (Q1 i)) (k MC1)) ++
  (List.range 4).map (fun i => r8 (k (H1 i)) (k MC1)) ++
  (List.range 3).map (fun i => r8 (k (FB i)) on) ++
  (List.range 3).map (fun i => r8 (k (Q2 i)) (k MLO)) ++
  (List.range 4).map (fun i => r8 (k (H2 i)) (k MLO)) ++
  [r8 (k H1C) (k MC1), r8 (k H2C) (k MLO)] ++
  (List.range 3).map (fun i => r8 (k (Q3 i)) (k MC1)) ++
  (List.range 4).map (fun i => r8 (k (H3 i)) (k MC1)) ++
  [r8 (k H3C) (k MC1)]

/-- The use multiplicities that occur (every lookup but the segment yield, index 4). -/
def useMults : List Expr :=
  [ .neg (k KO), .neg (.add (k KI) (k CBI)), .neg (k KI), .neg (.add (k KO) (k KI)), .neg (.mul (k KO) (om (k ZS))),
    .neg (.mul notFirst on), .neg (.mul (k KI) (k CBC)), .neg (k MNB), .neg (k MC1), .neg on, .neg (k MLO) ]

set_option maxRecDepth 20000 in
theorem mult_cases : ∀ j < 94, j ≠ 4 → (lookups.getD j ⟨0, .const 0, []⟩).mult ∈ useMults := by decide

theorem lookups_len : lookups.length = 94 := by decide

def coin : Comp where
  air := { name := "block_coin", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Coin
