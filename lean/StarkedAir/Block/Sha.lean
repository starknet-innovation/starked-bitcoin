/-
**Block SHA-256 (M3a.3 `BLK-SHA`, SHA component).** The proven SHA-256 compression AIR
(`Gadgets/Sha256.lean`, constraints unchanged), one compression per 72-row period, plus per-period
values copied down the period: the message id `MID`, the block index `BLKI` and three exclusive flags:
`FST` (a message's first block: the init rows are the IV), `DBL` (the second hash of SHA256d: the IV,
message words 0..7 = the previous period's digest, 8..15 = constant padding), `NILS` (unused).
Other periods continue the previous one (same message, next block, init rows = its output).

Message words come from the message component (`msgw(id, 64·BLKI + 4t, lo, hi)`); a `DBL` period
checks that its message's padded length is `64 · (blocks so far)` (`mlen`), so no message stops
early. A `DBL` period's last row yields `digest(id, 16 limbs)`: SHA256d of the message.
-/
import StarkedAir.Block.Msg
import StarkedAir.Gadgets.HeaderChain

namespace StarkedAir.Block.Sha

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC limb)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.Msg (REL_MSGW REL_MLEN)

def REL_DIGEST : ℕ := 7
/-- Merkle node tuples `node(id, left, right, dup)` (M3a.4). -/
def REL_NODE : ℕ := 8

/-! ### Columns -/

def MID : ℕ := 124
def BLKI : ℕ := 125
def FST : ℕ := 126
def DBL : ℕ := 127
def NILS : ℕ := 128
/-- `1 − DBL − NILS`: the period reads message words. -/
def USEW : ℕ := 129
/-- `1 − FST − DBL − NILS`: the period continues the previous one. -/
def CHN : ℕ := 130
def YM : ℕ := 131
/-- M3a.4: a Merkle node's first block (words = the children's digests). -/
def NODE : ℕ := 132
/-- M3a.4: a Merkle node's second block (constant padding of a 64-byte message). -/
def NPAD : ℕ := 133
def LID : ℕ := 134
def RID : ℕ := 135
/-- The node duplicates an odd last child (no inequality check). -/
def NDUP : ℕ := 136
/-- Mutation check: is-zero flags and inverses of the two limb differences (word `t` vs `t − 8`), their
product, the running "all equal" flag, and `NODE · (1 − NDUP)`. -/
def ZL : ℕ := 137
def IL : ℕ := 138
def ZH : ℕ := 139
def IH : ℕ := 140
def ZZ : ℕ := 141
def ALLEQ : ℕ := 142
def NNE : ℕ := 143
def N_MAIN : ℕ := 144

def per72 (f : ℕ → ℕ) : PreCol := .periodic ((List.range Sha256.PERIOD).map f)

/-- Constant message words 8..15 of the second hash: `0x80000000`, zeros, `256` (bits). -/
def dblWord (t : ℕ) : ℕ := if t = 8 then 0x80000000 else if t = 15 then 256 else 0

/-- The padding block of a 64-byte message: `0x80000000`, zeros, `512` (bits). -/
def npadWord (t : ℕ) : ℕ := if t = 0 then 0x80000000 else if t = 15 then 512 else 0

/-- Preprocessed: SHA's five, then row 0, init rows, message rows (4..19), the row index, the
second hash's digest-word rows `4 + k` (k < 8), its constant-word rows and values, the IV words at
the init rows, the last row. -/
def preCols : List PreCol :=
  Sha256.preCols ++
  [ per72 (fun q => if q = 0 then 1 else 0),                                   -- 5 ROW0
    per72 (fun q => if q < 4 then 1 else 0),                                   -- 6 INIT
    per72 (fun q => if 4 ≤ q ∧ q < 20 then 1 else 0),                          -- 7 MSGROW
    per72 (fun q => q) ] ++                                                    -- 8 ROWIDX
  (List.range 8).map (fun k => per72 (fun q => if q = 4 + k then 1 else 0)) ++  -- 9..16 DMSG k
  [ per72 (fun q => if 12 ≤ q ∧ q < 20 then 1 else 0),                         -- 17 DCONST
    per72 (fun q => if 12 ≤ q ∧ q < 20 then dblWord (q - 4) % 2 ^ 16 else 0),  -- 18 DC_LO
    per72 (fun q => if 12 ≤ q ∧ q < 20 then dblWord (q - 4) / 2 ^ 16 else 0),  -- 19 DC_HI
    per72 (fun q => if q < 4 then HeaderChain.ivWords.getD (3 - q) 0 % 2 ^ 16 else 0),  -- 20 IVA_LO
    per72 (fun q => if q < 4 then HeaderChain.ivWords.getD (3 - q) 0 / 2 ^ 16 else 0),  -- 21 IVA_HI
    per72 (fun q => if q < 4 then HeaderChain.ivWords.getD (7 - q) 0 % 2 ^ 16 else 0),  -- 22 IVE_LO
    per72 (fun q => if q < 4 then HeaderChain.ivWords.getD (7 - q) 0 / 2 ^ 16 else 0),  -- 23 IVE_HI
    per72 (fun q => if q = 71 then 1 else 0),                                  -- 24 FIN3
    .isFirst,                                                                  -- 25 FIRST
    per72 (fun q => if 4 ≤ q ∧ q < 20 then npadWord (q - 4) % 2 ^ 16 else 0),  -- 26 NP_LO
    per72 (fun q => if 4 ≤ q ∧ q < 20 then npadWord (q - 4) / 2 ^ 16 else 0),  -- 27 NP_HI
    per72 (fun q => if q = 11 then 1 else 0),                                  -- 28 DLR
    per72 (fun q => if q = 19 then 1 else 0),                                  -- 29 DRR
    per72 (fun q => if q = 12 then 1 else 0),                                  -- 30 CMPF
    per72 (fun q => if 13 ≤ q ∧ q < 20 then 1 else 0) ]                        -- 31 CMPR

def ROW0 : ℕ := 5
def INIT : ℕ := 6
def MSGROW : ℕ := 7
def ROWIDX : ℕ := 8
def DMSG (k : ℕ) : ℕ := 9 + k
def DCONST : ℕ := 17
def DC_LO : ℕ := 18
def IVA_LO : ℕ := 20
def IVE_LO : ℕ := 22
def FIN3 : ℕ := 24
def FIRST : ℕ := 25
def NP_LO : ℕ := 26
def DLR : ℕ := 28
def DRR : ℕ := 29
def CMPF : ℕ := 30
def CMPR : ℕ := 31

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e

open StarkedAir.HeaderChain (eqLimbs)

def flagC : List Expr :=
  [FST, DBL, NILS].map (fun c => boolC (k c)) ++
  [ .mul (k FST) (k DBL), .mul (k FST) (k NILS), .mul (k DBL) (k NILS),
    .sub (k USEW) (om (.add (k DBL) (.add (k NILS) (.add (k NODE) (k NPAD))))),
    .sub (k CHN) (om (.add (k FST) (.add (k DBL) (.add (k NILS) (.add (k NODE) (k NPAD)))))) ] ++
  [MID, BLKI, FST, DBL, NILS].map (fun c => .mul (om (pre ROW0)) (.sub (k c) (kp c)))

/-- M3a.4 flags: `NODE`, `NPAD`, `NDUP` are bits, `NODE` and `NPAD` exclude the other kinds, and the
node values are constant per period. (`USEW` and `CHN` include them: see `kindDefC`.) -/
def nodeFlagC : List Expr :=
  [NODE, NPAD, NDUP].map (fun c => boolC (k c)) ++
  [ .mul (k NODE) (k FST), .mul (k NODE) (k DBL), .mul (k NODE) (k NILS), .mul (k NODE) (k NPAD),
    .mul (k NPAD) (k FST), .mul (k NPAD) (k DBL), .mul (k NPAD) (k NILS),
    .sub (k NNE) (.mul (k NODE) (om (k NDUP))) ] ++
  [NODE, NPAD, LID, RID, NDUP].map (fun c => .mul (om (pre ROW0)) (.sub (k c) (kp c)))

/-- Init rows: the IV for a first block or a second hash, else the previous period's output. -/
def initC : List Expr :=
  let ivSel := .mul (pre INIT) (.add (k FST) (.add (k DBL) (k NODE)))
  let chSel := .mul (pre INIT) (.add (k CHN) (k NPAD))
  eqLimbs ivSel Sha256.A 0 (fun h => pre (IVA_LO + h)) ++ eqLimbs ivSel Sha256.E 0 (fun h => pre (IVE_LO + h)) ++
  eqLimbs chSel Sha256.A 0 (fun h => limb Sha256.A h (-4)) ++ eqLimbs chSel Sha256.E 0 (fun h => limb Sha256.E h (-4))

/-- The second hash's message: the previous period's digest words, then the constant padding. -/
def dblC : List Expr :=
  (List.range 8).flatMap (fun t =>
    eqLimbs (.mul (k DBL) (pre (DMSG t))) Sha256.W 0 (fun h => limb (HeaderChain.msgSrc t).1 h (HeaderChain.msgSrc t).2)) ++
  eqLimbs (.mul (k DBL) (pre DCONST)) Sha256.W 0 (fun h => pre (DC_LO + h))

/-- Period boundaries: a continuation follows a block of the same message; a second hash follows
its message's last block; a first block is block 0. -/
def orderC : List Expr :=
  [ .mul (k FST) (k BLKI),
    .mul (pre ROW0) (.mul (k CHN) (.sub (k MID) (kp MID))),
    .mul (pre ROW0) (.mul (k CHN) (.sub (.sub (k BLKI) (kp BLKI)) one)),
    .mul (pre ROW0) (.mul (k CHN) (.add (kp DBL) (kp NILS))),
    .mul (pre ROW0) (.mul (k DBL) (.sub (k MID) (kp MID))),
    .mul (pre ROW0) (.mul (k DBL) (.add (kp DBL) (kp NILS))),
    .mul (k YM) (om (pre FIN3)),
    -- Period 0 starts a message or is unused (no wrap-around predecessor).
    .mul (pre FIRST) (.add (k CHN) (k DBL)) ]

/-- M3a.4: a node's padding block is constant. -/
def npadC : List Expr := eqLimbs (.mul (k NPAD) (pre MSGROW)) Sha256.W 0 (fun h => pre (NP_LO + h))

/-- M3a.4 order: a node's first block is block 0; its padding block follows it (same id); byte
continuations never follow node blocks; period 0 is not a padding block. -/
def nodeOrderC : List Expr :=
  [ .mul (k NODE) (k BLKI),
    .mul (pre ROW0) (.mul (k NPAD) (.sub (k MID) (kp MID))),
    .mul (pre ROW0) (.mul (k NPAD) (.sub (.sub (k BLKI) (kp BLKI)) one)),
    .mul (pre ROW0) (.mul (k NPAD) (om (kp NODE))),
    .mul (pre ROW0) (.mul (k CHN) (.add (kp NODE) (kp NPAD))),
    .mul (pre FIRST) (k NPAD) ]

/-- The limb differences between message word `t` (row `4 + t`) and word `t − 8`. -/
def dLimb (h : ℕ) : Expr := .sub (limb Sha256.W h 0) (limb Sha256.W h (-8))

/-- M3a.4 mutation check: on rows 12..19 of a node block, `ALLEQ` is whether words `8..t` equal words
`0..t − 8` limb by limb; at row 19 a non-duplicating node needs them to differ. -/
def mutC : List Expr :=
  [ .mul (k ZL) (dLimb 0), .mul (om (k ZL)) (.sub (.mul (dLimb 0) (k IL)) one),
    .mul (k ZH) (dLimb 1), .mul (om (k ZH)) (.sub (.mul (dLimb 1) (k IH)) one),
    .sub (k ZZ) (.mul (k ZL) (k ZH)),
    .mul (pre CMPF) (.sub (k ALLEQ) (k ZZ)),
    .mul (pre CMPR) (.sub (k ALLEQ) (.mul (kp ALLEQ) (k ZZ))),
    .mul (pre DRR) (.mul (k NNE) (k ALLEQ)) ]

def constraints : List Expr :=
  Sha256.constraints ++ flagC ++ initC ++ dblC ++ orderC ++ nodeFlagC ++ npadC ++ nodeOrderC ++ mutC

/-- The digest at a second hash's last row (row 71): word `i < 4` is `a` at offset `−i`, word
`4 + i` is `e` at offset `−i`; 16-bit limbs, low first. -/
def digestLimbs : List Expr :=
  (List.range 16).map fun j =>
    let w : ℕ := j / 2
    if w < 4 then limb Sha256.A (j % 2) (-(w : ℤ)) else limb Sha256.E (j % 2) (-((w - 4 : ℕ) : ℤ))

/-- The 8 words ending at the current row (offsets `−7 … 0`), 16-bit limbs, low first: the layout of a
digest tuple. -/
def nodeWordLimbs : List Expr :=
  (List.range 16).map fun j => limb Sha256.W (j % 2) ((j / 2 : ℕ) - 7 : ℤ)

def lookups : List Lookup :=
  [ ⟨REL_MSGW, .neg (.mul (pre MSGROW) (k USEW)),
      [k MID, .add (.mul (cst 64) (k BLKI)) (.sub (.mul (cst 4) (pre ROWIDX)) (cst 16)),
       limb Sha256.W 0, limb Sha256.W 1]⟩,
    ⟨REL_MLEN, .neg (.mul (pre ROW0) (k DBL)), [k MID, .add (.mul (cst 64) (kp BLKI)) (cst 64)]⟩,
    ⟨REL_DIGEST, .mul (k DBL) (k YM), k MID :: digestLimbs⟩,
    -- M3a.4: a node block reads its tuple and its children's digests (words 0..7 at row 11, 8..15 at 19)
    ⟨REL_NODE, .neg (.mul (pre ROW0) (k NODE)), [k MID, k LID, k RID, k NDUP]⟩,
    ⟨REL_DIGEST, .neg (.mul (pre DLR) (k NODE)), k LID :: nodeWordLimbs⟩,
    ⟨REL_DIGEST, .neg (.mul (pre DRR) (k NODE)), k RID :: nodeWordLimbs⟩ ]

def sha : Comp where
  air := { name := "block_sha", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Sha
