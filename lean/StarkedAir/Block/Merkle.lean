/-
**Block Merkle tree (M3a.4 `BLK-MERKLE`, Merkle component).** One row per internal node of the txid
tree, level by level, then one root row. Node ids are `NB + row` (`NB = 2^27`, disjoint from message
ids). A node row yields `node(id, left, right, dup)`, which the SHA component's `NODE` block reads,
and the node message's padded length `mlen(id, 128)`.

Level 1's children are the txid messages `1 + 4i` and `1 + 4i + 2`; level `l > 1`'s are the previous
level's nodes `NB + PBASE + 2i` and `+ 1`. The last child of an odd level pairs with itself (`dup`).
The leaf count is public input 1 (the block's transaction count). The root row reads the root's
digest (the single leaf when there is one transaction) and checks it against the header's Merkle field
(bytes 36..67), read as the header message's words 9..16.
-/
import StarkedAir.Block.Sha

namespace StarkedAir.Block.Merkle

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.Msg (REL_MSGW REL_MLEN)
open StarkedAir.Block.Sha (REL_DIGEST REL_NODE)

/-- The first node id. -/
def NB : ℕ := 2 ^ 27

/-! ### Columns -/

def ACTN : ℕ := 0
def RT : ℕ := 1
def FIRSTL : ℕ := 2
def LAST : ℕ := 3
def LINV : ℕ := 4
def I : ℕ := 5
def CNT : ℕ := 6
def PCNT : ℕ := 7
def ODD : ℕ := 8
def BASE : ℕ := 9
def PBASE : ℕ := 10
def L1 : ℕ := 11
def RIX : ℕ := 12
def LEFT : ℕ := 13
def RIGHT : ℕ := 14
def DUP : ℕ := 15
def C1 : ℕ := 16
def C1INV : ℕ := 17
def RN : ℕ := 18
def PINV : ℕ := 19
def NM : ℕ := 20
def MMC : ℕ := 21
def RIDC : ℕ := 22
def NF : ℕ := 23
def FS : ℕ := 24
/-- The root's digest limbs `RL 0 … RL 15` (word `j / 2`, low limb first). -/
def RL (j : ℕ) : ℕ := 25 + j
def N_MAIN : ℕ := 41

def preCols : List PreCol := [.isFirst, .notLast]
def FIRST : ℕ := 0
def NOTLAST : ℕ := 1

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def notFirst : Expr := om (pre FIRST)
def NTX : Expr := .pub 1

/-- Kinds: node rows are a prefix ending at the root node; the root row follows it (or is row 0 when
there is one transaction); the last row is not a node. -/
def kindC : List Expr :=
  [ACTN, RT, FIRSTL, ODD, L1].map (fun c => boolC (k c)) ++
  [ .mul (k ACTN) (k RT),
    .mul (pre FIRST) (.sub (.add (k ACTN) (k RT)) one),
    .mul notFirst (.sub (k ACTN) (.mul (kp ACTN) (om (kp RN)))),
    .mul notFirst (.sub (k RT) (.mul (kp ACTN) (kp RN))),
    .mul (pre FIRST) (.mul (k RT) (.sub NTX one)),
    .mul (om (pre NOTLAST)) (k ACTN) ]

/-- Is-zero flags: `LAST = [I = CNT − 1]`, `C1 = [CNT = 1]`; the root node `RN = LAST · C1`; a node's
previous level has at least two entries (`PCNT ≠ 1`). -/
def flagC : List Expr :=
  let e := Expr.add (.sub (k I) (k CNT)) one
  let f := Expr.sub (k CNT) one
  [ .mul (k LAST) e, .mul (om (k LAST)) (.sub (.mul e (k LINV)) one),
    .mul (k C1) f, .mul (om (k C1)) (.sub (.mul f (k C1INV)) one),
    .sub (k RN) (.mul (k LAST) (k C1)),
    .mul (k ACTN) (.sub (.mul (.sub (k PCNT) one) (k PINV)) one) ]

/-- Levels: row 0 starts level 1 over the `NTX` leaves; a node row continues its level or, after the
previous level's last node, starts the next one. -/
def levelC : List Expr :=
  [ .mul (k ACTN) (.sub (.mul (cst 2) (k CNT)) (.add (k PCNT) (k ODD))),
    .mul (pre FIRST) (k RIX),
    .mul (pre FIRST) (.sub (k FIRSTL) one),
    .mul (pre FIRST) (.sub (k L1) one),
    .mul (pre FIRST) (k BASE),
    .mul (pre FIRST) (.sub (k PCNT) NTX),
    .mul notFirst (.sub (.sub (k RIX) (kp RIX)) one),
    .mul notFirst (.mul (k ACTN) (.sub (k FIRSTL) (kp LAST))),
    .mul (k FIRSTL) (k I),
    .sub (k NF) (.mul (k ACTN) (om (k FIRSTL))),
    .sub (k FS) (.mul (k ACTN) (k FIRSTL)),
    .mul (k NF) (.sub (.sub (k I) (kp I)) one) ] ++
  [CNT, PCNT, BASE, PBASE, L1].map (fun c => .mul (k NF) (.sub (k c) (kp c))) ++
  [ .mul notFirst (.mul (k FS) (.sub (k PCNT) (kp CNT))),
    .mul notFirst (.mul (k FS) (.sub (k BASE) (k RIX))),
    .mul notFirst (.mul (k FS) (.sub (k PBASE) (kp BASE))),
    .mul notFirst (.mul (k FS) (k L1)) ]

/-- Children and the root id. -/
def childC : List Expr :=
  [ .sub (k DUP) (.mul (k ODD) (k LAST)),
    .sub (k LEFT) (.add (.mul (k L1) (.add (.mul (cst 4) (k I)) one))
      (.mul (om (k L1)) (.add (.add (cst NB) (k PBASE)) (.mul (cst 2) (k I))))),
    .sub (k RIGHT) (.add (k LEFT) (.mul (om (k DUP)) (.add (k L1) one))),
    .mul notFirst (.mul (k RT) (.sub (.add (k RIDC) one) (.add (cst NB) (k RIX)))),
    .mul (pre FIRST) (.mul (k RT) (.sub (k RIDC) one)) ]

def constraints : List Expr := kindC ++ flagC ++ levelC ++ childC

def nodeId : Expr := .add (cst NB) (k RIX)

def lookups : List Lookup :=
  [ ⟨REL_NODE, .mul (k ACTN) (k NM), [nodeId, k LEFT, k RIGHT, k DUP]⟩,
    ⟨REL_MLEN, .mul (k ACTN) (k MMC), [nodeId, cst 128]⟩,
    ⟨REL_DIGEST, .neg (k RT), k RIDC :: (List.range 16).map (fun j => k (RL j))⟩ ] ++
  (List.range 8).map fun w =>
    ⟨REL_MSGW, .neg (k RT), [cst 0, cst (36 + 4 * w), k (RL (2 * w)), k (RL (2 * w + 1))]⟩

def merkle : Comp where
  air := { name := "block_merkle", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Merkle
