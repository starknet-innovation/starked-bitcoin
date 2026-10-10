/-
**Block context (M3a.5c and the commitment half of M3a.5e, D-035).** The once-per-block reads and
comparisons, one row per read, laid out by periodic preprocessed columns (period 256; rows `≥ 132` of a
period read nothing, and later periods repeat the same reads, which is harmless). Row `r` reads the byte
at `base + OFF r`, where the base is the header (0), the coinbase (`A0 + 2·SEG0`, after its marker and
flag), its witness section `W0`, or the commitment output's script `CPOS`, and may compare it with a
constant.

* **Coinbase** (rows 0–37): one input (`01`), the null prevout (32 zero bytes, `ff ff ff ff`), the
  scriptSig length `s ∈ [2 + 2·bip34, 100]` (1-byte CompactSize).
* **BIP34** (rows 38–41, when `pub 4`): `03 h0 h1 h2` with `h0 + 256·h1 + 65536·h2 = height`.
* **Time** (rows 42–45): the header's `nTime` limbs; the finality cutoff is the previous MTP once CSV is
  active (`pub 5`), else `nTime`. It is yielded as `ctx(lo, hi)` for the fields' lock-time rows.
* **Commitment** (rows 46–117, when `HC = segwit · HASC`): the coinbase witness is one 32-byte item
  (`01 20 nonce`, then the lock time) and the commitment script starts `6a24aa21a9ed`. The nonce is
  yielded as the digest `NONCE_ID`; the 32 bytes after the pattern must equal the digest of the
  commitment node (`wcid`).
* **Limits** (rows 118–131, byte decompositions through the range table): the commitment script is at
  least 38 bytes, `weight = 4·len − 3·W ≤ 4,000,000`, `sigops ≤ 20,000` (the spec's `·4 ≤ 80,000`), and
  the previous MTP's 16-bit limbs.
* **Without a commitment**: no transaction is segwit (`NSEG = 0`), which is `unexpected-witness`.

Digest limbs follow `Sha.digestLimbs`: limb `2w` is bytes `4w+2, 4w+3` and limb `2w+1` bytes `4w, 4w+1`
(big-endian pairs). Bytes are shifted in by pairs, so register `LG j` holds limb `j xor 1`.
-/
import StarkedAir.Block.Walk
import StarkedAir.Block.Sha

namespace StarkedAir.Block.Ctx

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC)
open StarkedAir.Block.Fields (degE REL_TX REL_TOT REL_CTX REL_COMMIT pat)
open StarkedAir.Block.Sha (REL_DIGEST)

def ZERO_ID : ℕ := 2 ^ 28
def NONCE_ID : ℕ := 2 ^ 28 + 1
/-- `wcid(id)`: the witness-commitment node's digest id (yielded by the witness tree). -/
def REL_WCID : ℕ := 16

/-! ### Row layout -/

/-- One row's role. `base`: 0 none, 1 header, 2 coinbase, 3 BIP34 (coinbase), 4 witness, 5 commitment. -/
structure Role where
  base : ℕ := 0
  off : ℕ := 0
  exp : Option ℕ := none
  rst : Bool := false
  wgt : ℕ := 0
  srcB : Bool := false
  srcR : Bool := false
  sc1 : Bool := false
  sc2 : Bool := false
  flip : Bool := false
  hi : Bool := false
  lo : Bool := false
  capT0 : Bool := false
  capT1 : Bool := false
  capM0 : Bool := false
  capM1 : Bool := false
  chkH : Bool := false
  chkL : Bool := false
  chkW : Bool := false
  chkS : Bool := false

def K : ℕ := 132

def role (r : ℕ) : Role :=
  if r = 0 then { base := 2, off := 4, exp := some 1, rst := true }
  else if r ≤ 32 then { base := 2, off := 4 + r, exp := some 0 }
  else if r ≤ 36 then { base := 2, off := 4 + r, exp := some 0xff }
  else if r = 37 then { base := 2, off := 41, sc1 := true }
  else if r = 38 then { base := 3, off := 42, exp := some 3, sc2 := true }
  else if r ≤ 41 then { base := 3, off := r + 4, rst := decide (r = 39), wgt := 256 ^ (r - 39), srcB := true, chkH := decide (r = 41) }
  else if r ≤ 45 then { base := 1, off := r + 26, rst := decide (r = 42 ∨ r = 44), wgt := 256 ^ ((r - 42) % 2), srcB := true, capT0 := decide (r = 43), capT1 := decide (r = 45) }
  else if r = 46 then { base := 4, off := 0, exp := some 1 }
  else if r = 47 then { base := 4, off := 1, exp := some 0x20 }
  else if r ≤ 79 then { base := 4, off := r - 46, hi := decide (r % 2 = 0), lo := decide (r % 2 = 1) }
  else if r ≤ 85 then { base := 5, off := r - 80, exp := some (pat.getD (r - 80) 0) }
  else if r ≤ 117 then { base := 5, off := r - 80, hi := decide (r % 2 = 0), lo := decide (r % 2 = 1) }
  else if r ≤ 121 then { rst := decide (r = 118), wgt := 256 ^ (r - 118), srcR := true, chkL := decide (r = 121) }
  else if r = 122 then { flip := true }
  else if r ≤ 125 then { rst := decide (r = 123), wgt := 256 ^ (r - 123), srcR := true, chkW := decide (r = 125) }
  else if r ≤ 127 then { rst := decide (r = 126), wgt := 256 ^ (r - 126), srcR := true, chkS := decide (r = 127) }
  else if r ≤ 131 then { rst := decide (r = 128 ∨ r = 130), wgt := 256 ^ ((r - 128) % 2), srcR := true, capM0 := decide (r = 129), capM1 := decide (r = 131) }
  else {}

def bn (b : Bool) : ℕ := if b then 1 else 0
def tabR (g : Role → ℕ) : PreCol := .periodic ((List.range 256).map fun r => g (role r))

/-- Preprocessed columns. -/
def preCols : List PreCol :=
  [ .isFirst, .notLast, .rowLt 79, .rowLt 80, .rowLt 117, .rowLt 118,
    tabR (·.off), tabR (fun x => bn (x.base = 1)), tabR (fun x => bn (x.base = 2)), tabR (fun x => bn (x.base = 3)),
    tabR (fun x => bn (x.base = 4)), tabR (fun x => bn (x.base = 5)),
    tabR (fun x => x.exp.getD 0), tabR (fun x => bn x.exp.isSome),
    tabR (fun x => bn x.rst), tabR (·.wgt), tabR (fun x => bn x.srcB), tabR (fun x => bn x.srcR),
    tabR (fun x => bn x.sc1), tabR (fun x => bn x.sc2), tabR (fun x => bn x.flip),
    tabR (fun x => bn x.hi), tabR (fun x => bn x.lo),
    tabR (fun x => bn x.capT0), tabR (fun x => bn x.capT1), tabR (fun x => bn x.capM0), tabR (fun x => bn x.capM1),
    tabR (fun x => bn x.chkH), tabR (fun x => bn x.chkL), tabR (fun x => bn x.chkW), tabR (fun x => bn x.chkS) ]

def P_FIRST : ℕ := 0
def P_NOTLAST : ℕ := 1
def P_LT79 : ℕ := 2
def P_LT80 : ℕ := 3
def P_LT117 : ℕ := 4
def P_LT118 : ℕ := 5
def P_OFF : ℕ := 6
def P_SHDR : ℕ := 7
def P_SCB : ℕ := 8
def P_SB34 : ℕ := 9
def P_SW : ℕ := 10
def P_SC : ℕ := 11
def P_EXP : ℕ := 12
def P_HEXP : ℕ := 13
def P_RST : ℕ := 14
def P_WGT : ℕ := 15
def P_SRCB : ℕ := 16
def P_SRCR : ℕ := 17
def P_SC1 : ℕ := 18
def P_SC2 : ℕ := 19
def P_FLIP : ℕ := 20
def P_HI : ℕ := 21
def P_LO : ℕ := 22
def P_CAPT0 : ℕ := 23
def P_CAPT1 : ℕ := 24
def P_CAPM0 : ℕ := 25
def P_CAPM1 : ℕ := 26
def P_CHKH : ℕ := 27
def P_CHKL : ℕ := 28
def P_CHKW : ℕ := 29
def P_CHKS : ℕ := 30

/-! ### Main columns -/

def ADDR : ℕ := 0
def B : ℕ := 1
def ACTR : ℕ := 2
def ACC : ℕ := 3
def RA : ℕ := 4
def PACC : ℕ := 5
/-- The digest register `LG 0 … 15`. -/
def LG (j : ℕ) : ℕ := 6 + j
/-- Block constants. -/
def A0 : ℕ := 22
def SEG0 : ℕ := 23
def W0 : ℕ := 24
def L0 : ℕ := 25
def WT : ℕ := 26
def NSEG : ℕ := 27
def HASC : ℕ := 28
def SIGS : ℕ := 29
def CPOS : ℕ := 30
def CLEN : ℕ := 31
def CLO : ℕ := 32
def CHI : ℕ := 33
def TL16 : ℕ := 34
def TH16 : ℕ := 35
def MLO : ℕ := 36
def MHI : ℕ := 37
def HC : ℕ := 38
def CID : ℕ := 39
def MZ : ℕ := 40
def N_MAIN : ℕ := 41

def consts : List ℕ := [A0, SEG0, W0, L0, WT, NSEG, HASC, SIGS, CPOS, CLEN, CLO, CHI, TL16, TH16, MLO, MHI, HC, CID]

def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def p (i : ℕ) : Expr := pre i
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def notFirst : Expr := om (p P_FIRST)

def constraints : List Expr :=
  [ .sub (k ADDR) (.add (.add (.mul (.add (p P_SCB) (p P_SB34)) (.add (k A0) (.mul (cst 2) (k SEG0))))
      (.add (.mul (p P_SW) (k W0)) (.mul (p P_SC) (k CPOS)))) (p P_OFF)),
    .sub (k ACTR) (.add (.add (p P_SCB) (p P_SHDR)) (.add (.mul (p P_SB34) (.pub 4))
      (.mul (.add (p P_SW) (p P_SC)) (k HC)))),
    .mul (p P_HEXP) (.mul (k ACTR) (.sub (k B) (p P_EXP))),
    .sub (k ACC) (.add (.mul (om (p P_RST)) (kp ACC))
      (.mul (p P_WGT) (.add (.mul (p P_SRCB) (k B)) (.mul (p P_SRCR) (k RA))))),
    .mul (p P_SC1) (.sub (k RA) (.sub (.sub (k B) (cst 2)) (.mul (cst 2) (.pub 4)))),
    .mul (p P_SC2) (.sub (k RA) (.sub (cst 100) (kp B))),
    .mul (p P_FLIP) (.sub (k RA) (om (kp RA))),
    .mul (p P_HI) (.sub (k PACC) (.mul (cst 256) (k B))),
    .mul (p P_LO) (.sub (.sub (k PACC) (kp PACC)) (k B)) ] ++
  (List.range 15).map (fun j => .mul (p P_LO) (.sub (k (LG j)) (kp (LG (j + 1))))) ++
  [ .mul (p P_LO) (.sub (k (LG 15)) (k PACC)) ] ++
  (List.range 16).map (fun j => .mul notFirst (.mul (om (p P_LO)) (.sub (k (LG j)) (kp (LG j))))) ++
  [ .mul (p P_CAPT0) (.sub (k TL16) (k ACC)), .mul (p P_CAPT1) (.sub (k TH16) (k ACC)),
    .mul (p P_CAPM0) (.sub (k MLO) (k ACC)), .mul (p P_CAPM1) (.sub (k MHI) (k ACC)),
    .mul (p P_CHKH) (.mul (.pub 4) (.sub (k ACC) (.pub 2))),
    .mul (p P_CHKL) (.mul (k HC) (.sub (k ACC) (.sub (k CLEN) (cst 38)))),
    .mul (p P_CHKW) (.sub (k ACC) (.add (.sub (cst 4000000) (.mul (cst 4) (.pub 0))) (.mul (cst 3) (k WT)))),
    .mul (p P_CHKS) (.sub (k ACC) (.sub (cst 20000) (k SIGS))) ] ++
  consts.map (fun x => .mul notFirst (.sub (k x) (kp x))) ++
  [ boolC (k ACTR), boolC (k HASC), boolC (k HC),
    .sub (k HC) (.mul (.pub 6) (k HASC)),
    .mul (k HC) (.sub (k L0) (.add (k W0) (cst 34))),
    .mul (om (k HC)) (k NSEG),
    .sub (.add (k MLO) (.mul (cst 65536) (k MHI))) (.pub 3),
    .sub (k CLO) (.add (.mul (.pub 5) (k MLO)) (.mul (om (.pub 5)) (k TL16))),
    .sub (k CHI) (.add (.mul (.pub 5) (k MHI)) (.mul (om (.pub 5)) (k TH16))) ]

/-- Digest limbs from the register: limb `j` is `LG (j xor 1)`. -/
def limbs : List Expr := (List.range 16).map fun j => k (LG (if j % 2 = 0 then j + 1 else j - 1))

def lookups : List Lookup :=
  [ ⟨REL_BYTE, .neg (k ACTR), [k ADDR, k B]⟩,
    ⟨Tables.REL_R8, .neg one, [k RA]⟩,
    ⟨REL_TX, .neg (p P_FIRST), [cst 0, k A0, k SEG0, k W0, k L0]⟩,
    ⟨REL_TOT, .neg (p P_FIRST), [k WT, k NSEG, k HASC]⟩,
    ⟨Walk.REL_SIGOPS, .neg (p P_FIRST), [k SIGS]⟩,
    ⟨REL_COMMIT, .neg (.mul (p P_FIRST) (k HASC)), [k CPOS, k CLEN]⟩,
    ⟨REL_CTX, p P_FIRST, [k CLO, k CHI]⟩,
    ⟨REL_DIGEST, .mul (p P_FIRST) (k MZ), cst ZERO_ID :: (List.range 16).map (fun _ => cst 0)⟩,
    ⟨REL_DIGEST, .mul (.sub (p P_LT80) (p P_LT79)) (k HC), cst NONCE_ID :: limbs⟩,
    ⟨REL_WCID, .neg (.mul (p P_FIRST) (k HC)), [k CID]⟩,
    ⟨REL_DIGEST, .neg (.mul (.sub (p P_LT118) (p P_LT117)) (k HC)), k CID :: limbs⟩ ]

def ctx : Comp where
  air := { name := "block_ctx", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

end StarkedAir.Block.Ctx
