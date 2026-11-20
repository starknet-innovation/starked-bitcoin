/-
**Sigop walker (M3a.5d, D-035).** One row per script byte, walking each non-empty script `script(start,
len)` yielded by the fields component once, from its first byte. Each row reads its byte from the byte
table and is one of: an opcode (`OP`, classified through the opcode table), a length byte of
`PUSHDATA1/2/4` (`LN`), a skipped data byte (`DT`), or a data byte of a push of at least `2^25` bytes,
which always runs to the end (`INF`). This is the automaton `wstep` of `Spec/BlockFlat.lean`, whose
count equals `sigOps` (`walk_eq_sigOps`). `SUMS` adds each opcode's weight; the last row yields
`sigops(SUMS)`.

Each row stores the state the *next* row would have if the script continues (`N…` columns), so the
transitions stay at degree 3.
-/
import StarkedAir.Block.Fields

namespace StarkedAir.Block.Walk

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE REL_SCRIPT REL_ASPAN)

def REL_SIGOPS : ℕ := 15

def ACT : ℕ := 0
def FS : ℕ := 1
def POS : ℕ := 2
def REM : ℕ := 3
def B : ℕ := 4
def OP : ℕ := 5
def LN : ℕ := 6
def DT : ℕ := 7
def INF : ℕ := 8
/-- From the opcode table: push length, `PUSHDATA1/2/4` one-hot, sigop weight, direct push flag. -/
def PN : ℕ := 9
def K1 : ℕ := 10
def K2 : ℕ := 11
def K4 : ℕ := 12
def SG : ℕ := 13
def NZP : ℕ := 14
/-- A length byte: its index (one-hot `LI 0 … 3`), the length's byte count (one-hot), the bytes so far. -/
def LI (j : ℕ) : ℕ := 15 + j
def LK1 : ℕ := 19
def LK2 : ℕ := 20
def LK4 : ℕ := 21
def LACC : ℕ := 22
/-- A data byte: the data bytes left, this one included. -/
def DR : ℕ := 23
def ACC2 : ℕ := 24
def ENDC : ℕ := 25
def LE : ℕ := 26
def LEF : ℕ := 27
def TOPF : ℕ := 28
def L4 : ℕ := 29
def ZA : ℕ := 30
def INVA : ℕ := 31
def ZD : ℕ := 32
def INVD : ℕ := 33
def ZR : ℕ := 34
def INVR : ℕ := 35
def NOP : ℕ := 36
def NLN : ℕ := 37
def NDT : ℕ := 38
def NINF : ℕ := 39
def NDR : ℕ := 40
def NLACC : ℕ := 41
def NLI (j : ℕ) : ℕ := 42 + j
def NLK1 : ℕ := 46
def NLK2 : ℕ := 47
def NLK4 : ℕ := 48
def SUMS : ℕ := 49
def GC : ℕ := 50
/-! CONNECT-RULES step 3: the accurate count and the scriptSig's last push.

* A span is walked either as a **script** (legacy count, `AC = 0`: the scriptSigs and scriptPubKeys) or
  as an **accurate span** (`AC = 1`: a redeem script, weight 4, `W4 = 1`; or a witness script, weight 1).
  The accurate count of a multisig is the previous opcode's `DV` (`PV`, 20 at a span's start).
* Every script also outputs `PO` (it parses and no opcode is above `OP_16`: `IsPushOnly`) and the span
  `(RS, RL)` of its last operation's data (`RL = 0` when that operation carries none). These three are
  constant over the script, so its first row can offer them; they are fixed where they are known.
* `SUMS` adds the legacy weights of the scripts, `SUMA` the weighted accurate counts of the spans. -/
def AC : ℕ := 51
def W4 : ℕ := 52
/-- From the opcode table: above `OP_16`, multisig, the count a following multisig takes. -/
def HI : ℕ := 53
def MS : ℕ := 54
def DV : ℕ := 55
/-- Opcodes above `OP_16` so far in the span, this row included; its is-zero test. -/
def HCN : ℕ := 56
def ZH : ℕ := 57
def INVH : ℕ := 58
def PO : ℕ := 59
def RS : ℕ := 60
def RL : ℕ := 61
/-- Whether the data starting after this row ends with the span (`NDR = REM − 1`); `EZ`: and data starts. -/
def ZE : ℕ := 62
def INVE : ℕ := 63
def EZ : ℕ := 64
def PV : ℕ := 65
def NPV : ℕ := 66
def M1 : ℕ := 67
/-- The row's accurate amount (before `OP`), its legacy weight (`SG` on script rows), the second sum. -/
def AN : ℕ := 68
def LG : ℕ := 69
def SUMA : ℕ := 70
def N_MAIN : ℕ := 71

def preCols : List PreCol := [.isFirst, .notLast]

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := pre 0
def notFirst : Expr := om (pre 0)
def isLast : Expr := om (pre 1)

def isZero (z inv : ℕ) (e : Expr) : List Expr :=
  [boolC (k z), .mul (k z) e, .mul (om (k z)) (.sub (.mul e (k inv)) one)]

def bools : List ℕ := [ACT, FS, OP, LN, DT, INF, LI 0, LI 1, LI 2, LI 3, LK1, LK2, LK4, TOPF]

/-- Row-local definitions. -/
def localC : List Expr :=
  bools.map (fun x => boolC (k x)) ++
  [ .sub (.add (k OP) (.add (k LN) (.add (k DT) (k INF)))) (k ACT),
    .mul (k FS) (om (k ACT)),
    .mul (k FS) (om (k OP)),
    .sub (k ACC2) (.add (k LACC) (.mul (k B) (.add (k (LI 0)) (.add (.mul (cst 256) (k (LI 1)))
      (.add (.mul (cst 65536) (k (LI 2))) (.mul (cst 16777216) (k (LI 3)))))))),
    .sub (k ENDC) (.add (.mul (k (LI 0)) (k LK1)) (.add (.mul (k (LI 1)) (k LK2)) (.mul (k (LI 3)) (k LK4)))),
    .sub (k LE) (.mul (k LN) (k ENDC)),
    .sub (k LEF) (.mul (k LE) (om (k TOPF))),
    .mul (k TOPF) (om (k LK4)), .mul (k TOPF) (om (k LE)),
    .sub (k L4) (.mul (k LEF) (k LK4)),
    .mul (k L4) (.mul (k B) (.sub (k B) one)) ] ++
  isZero ZA INVA (k ACC2) ++ isZero ZD INVD (.sub (k DR) one) ++ isZero ZR INVR (.sub (k REM) one) ++
  [ .sub (k NOP) (.add (.mul (k OP) (om (.add (k NZP) (.add (k K1) (.add (k K2) (k K4))))))
      (.add (.mul (k LEF) (k ZA)) (.mul (k DT) (k ZD)))),
    .sub (k NDT) (.add (.mul (k OP) (k NZP)) (.add (.mul (k LEF) (om (k ZA))) (.mul (k DT) (om (k ZD))))),
    .sub (k NLN) (.add (.mul (k OP) (.add (k K1) (.add (k K2) (k K4)))) (.sub (k LN) (k LE))),
    .sub (k NINF) (.add (.mul (k LE) (k TOPF)) (k INF)),
    .sub (k NDR) (.add (.mul (k OP) (k PN)) (.add (.mul (k LEF) (k ACC2)) (.mul (k DT) (.sub (k DR) one)))),
    .sub (k NLACC) (.mul (.sub (k LN) (k LE)) (k ACC2)),
    .sub (k (NLI 0)) (.mul (k OP) (.add (k K1) (.add (k K2) (k K4)))),
    .sub (k (NLI 1)) (.mul (.sub (k LN) (k LE)) (k (LI 0))),
    .sub (k (NLI 2)) (.mul (.sub (k LN) (k LE)) (k (LI 1))),
    .sub (k (NLI 3)) (.mul (.sub (k LN) (k LE)) (k (LI 2))),
    .sub (k NLK1) (.add (.mul (k OP) (k K1)) (.mul (.sub (k LN) (k LE)) (k LK1))),
    .sub (k NLK2) (.add (.mul (k OP) (k K2)) (.mul (.sub (k LN) (k LE)) (k LK2))),
    .sub (k NLK4) (.add (.mul (k OP) (k K4)) (.mul (.sub (k LN) (k LE)) (k LK4))),
    .sub (k GC) (.mul (k ACT) (om (k FS))) ]

/-- Continuing a script: the state is the previous row's next state, one byte on. -/
def stepC : List Expr :=
  [ (OP, NOP), (LN, NLN), (DT, NDT), (INF, NINF), (DR, NDR), (LACC, NLACC), (LI 0, NLI 0), (LI 1, NLI 1),
    (LI 2, NLI 2), (LI 3, NLI 3), (LK1, NLK1), (LK2, NLK2), (LK4, NLK4) ].map
    (fun p => .mul (k GC) (.sub (k p.1) (kp p.2))) ++
  [ .mul (k GC) (.sub (.sub (k POS) (kp POS)) one),
    .mul (k GC) (.add (.sub (k REM) (kp REM)) one),
    .mul (k GC) (kp ZR) ]

/-- Scripts: active rows are a prefix starting with a script; a script starts only after the previous
one's last byte, and the active rows end on a script's last byte; the last row is inactive. -/
def scriptC : List Expr :=
  [ .mul first (.mul (k ACT) (om (k FS))),
    .mul notFirst (.mul (k ACT) (om (kp ACT))),
    .mul notFirst (.mul (k FS) (om (kp ZR))),
    .mul notFirst (.mul (.sub (kp ACT) (k ACT)) (om (kp ZR))),
    .mul isLast (k ACT),
    .mul first (.sub (k SUMS) (.mul (k OP) (k LG))),
    .mul notFirst (.sub (.sub (k SUMS) (kp SUMS)) (.mul (k OP) (k LG))) ]

/-- The data that starts after this row: after a direct push opcode, or after a `PUSHDATA`'s last
length byte when the length is not zero. -/
def entE : Expr := .add (.mul (k OP) (k NZP)) (.mul (k LEF) (om (k ZA)))

/-- CONNECT-RULES step 3 (see the columns' note). -/
def accC : List Expr :=
  [ boolC (k AC), boolC (k W4), .mul (k W4) (om (k AC)) ] ++
  [AC, W4, PO, RS, RL].map (fun x => .mul (k GC) (.sub (k x) (kp x))) ++
  [ .sub (k HCN) (.add (.mul (k GC) (kp HCN)) (.mul (k OP) (k HI))) ] ++
  isZero ZH INVH (k HCN) ++
  [ .mul (k ZR) (.sub (k PO) (.mul (k ZH) (k NOP))) ] ++
  isZero ZE INVE (.add (.sub (k NDR) (k REM)) one) ++
  [ .sub (k EZ) (.mul entE (k ZE)),
    .mul (k EZ) (.sub (k RL) (k NDR)),
    .mul (k EZ) (.sub (.sub (k RS) (k POS)) one),
    .mul (k ZR) (.mul (om (k DT)) (k RL)),
    .mul (k FS) (.sub (k PV) (cst 20)),
    .mul (k GC) (.sub (k PV) (kp NPV)),
    .sub (k NPV) (.add (.mul (k OP) (k DV)) (.mul (om (k OP)) (k PV))),
    .sub (k M1) (.mul (k MS) (k PV)),
    .sub (k AN) (.mul (.add (k AC) (.mul (cst 3) (k W4))) (.add (.sub (k SG) (.mul (cst 20) (k MS))) (k M1))),
    .sub (k LG) (.mul (om (k AC)) (k SG)),
    .mul first (.sub (k SUMA) (.mul (k OP) (k AN))),
    .mul notFirst (.sub (.sub (k SUMA) (kp SUMA)) (.mul (k OP) (k AN))) ]

def constraints : List Expr := localC ++ stepC ++ scriptC ++ accC

def lookups : List Lookup :=
  [ ⟨REL_SCRIPT, .neg (.mul (k FS) (om (k AC))), [k POS, k REM, k PO, k RS, k RL]⟩,
    ⟨REL_BYTE, .neg (k ACT), [k POS, k B]⟩,
    ⟨Tables.REL_OPC, .neg (k OP), [k B, k PN, k K1, k K2, k K4, k SG, k NZP, k HI, k MS, k DV]⟩,
    ⟨Tables.REL_R8, .neg (k TOPF), [.sub (k B) (cst 2)]⟩,
    ⟨REL_SIGOPS, isLast, [k SUMS, k SUMA]⟩,
    ⟨REL_ASPAN, .neg (.mul (k FS) (k AC)), [k POS, k REM, k W4]⟩ ]

def walk : Comp where
  air := { name := "block_walk", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Walk
