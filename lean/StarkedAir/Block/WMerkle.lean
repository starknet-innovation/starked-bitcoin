/-
**Witness tree and commitment node (M3a.5e, D-035).** The txid tree's layout (`Merkle.lean`) over the
witness leaves `[0^32, wtxid(tx 1), …]`: one row per internal node, level by level, then the commitment
row. Node ids are `NBW + row` (`NBW = 2^27 + 2^26`, disjoint from message and txid-tree ids).

* Level 1's children are the wtxid messages `2 + 4i` and `+ 2`, except that leaf 0 is the pseudo-digest
  `ZERO_ID` (32 zero bytes, yielded by the context component). Higher levels as in the txid tree.
* Every node tuple's 4th entry is 1, which turns off the SHA component's mutation check: Core ignores
  mutation in the witness tree.
* The last row (`RT`) is the commitment node `(root, NONCE_ID)`; its digest is SHA256d of the witness
  root and the coinbase nonce. It yields `wcid(id)` for the context component, which compares that
  digest with the commitment output. The root is `ZERO_ID` when the block has one transaction.
* The component is active (`WON`) exactly when the context component uses `wcid`, that is when the
  commitment is checked.
-/
import StarkedAir.Block.Merkle
import StarkedAir.Block.Ctx

namespace StarkedAir.Block.WMerkle

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.Msg (REL_MLEN)
open StarkedAir.Block.Sha (REL_NODE)
open StarkedAir.Block.Ctx (ZERO_ID NONCE_ID REL_WCID)

def NBW : ℕ := 2 ^ 27 + 2 ^ 26

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
def WON : ℕ := 25
def LRAW : ℕ := 26
def N_MAIN : ℕ := 27

def preCols : List PreCol := [.isFirst, .notLast]
def FIRST : ℕ := 0
def NOTLAST : ℕ := 1

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def notFirst : Expr := om (pre FIRST)
def NTX : Expr := .pub 1

def kindC : List Expr :=
  [ACTN, RT, FIRSTL, ODD, L1, WON].map (fun c => boolC (k c)) ++
  [ .mul notFirst (.sub (k WON) (kp WON)),
    .mul (k ACTN) (k RT),
    .mul (pre FIRST) (.sub (.add (k ACTN) (k RT)) (k WON)),
    .mul notFirst (.sub (k ACTN) (.mul (kp ACTN) (om (kp RN)))),
    .mul notFirst (.sub (k RT) (.mul (kp ACTN) (kp RN))),
    .mul (pre FIRST) (.mul (k RT) (.sub NTX one)),
    .mul (om (pre NOTLAST)) (k ACTN) ]

def flagC : List Expr :=
  let e := Expr.add (.sub (k I) (k CNT)) one
  let f := Expr.sub (k CNT) one
  [ .mul (k LAST) e, .mul (om (k LAST)) (.sub (.mul e (k LINV)) one),
    .mul (k C1) f, .mul (om (k C1)) (.sub (.mul f (k C1INV)) one),
    .sub (k RN) (.mul (k LAST) (k C1)),
    .mul (k ACTN) (.sub (.mul (.sub (k PCNT) one) (k PINV)) one) ]

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

/-- Children: node rows as in the txid tree (wtxid leaves, leaf 0 the zero digest); the commitment row
hashes the root with the nonce. -/
def childC : List Expr :=
  [ .sub (k DUP) (.mul (k ODD) (k LAST)),
    .sub (k LRAW) (.add (.mul (k L1) (.add (.mul (cst 4) (k I)) (cst 2)))
      (.mul (om (k L1)) (.add (.add (cst NBW) (k PBASE)) (.mul (cst 2) (k I))))),
    .mul (om (k RT)) (.sub (k LEFT) (.add (k LRAW) (.mul (pre FIRST) (cst (ZERO_ID - 2))))),
    .mul (om (k RT)) (.sub (k RIGHT) (.add (k LRAW) (.mul (om (k DUP)) (.add (k L1) one)))),
    .mul (k RT) (.sub (k LEFT) (k RIDC)),
    .mul (k RT) (.sub (k RIGHT) (cst NONCE_ID)),
    .mul notFirst (.mul (k RT) (.sub (.add (k RIDC) one) (.add (cst NBW) (k RIX)))),
    .mul (pre FIRST) (.mul (k RT) (.sub (k RIDC) (cst ZERO_ID))) ]

def constraints : List Expr := kindC ++ flagC ++ levelC ++ childC

def nodeId : Expr := .add (cst NBW) (k RIX)

def lookups : List Lookup :=
  [ ⟨REL_NODE, .mul (.add (k ACTN) (k RT)) (k NM), [nodeId, k LEFT, k RIGHT, one]⟩,
    ⟨REL_MLEN, .mul (.add (k ACTN) (k RT)) (k MMC), [nodeId, cst 128]⟩,
    ⟨REL_WCID, k RT, [nodeId]⟩ ]

def wmerkle : Comp where
  air := { name := "block_wmerkle", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.WMerkle
