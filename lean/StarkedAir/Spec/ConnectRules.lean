/-
**`ConnectBlock` rules outside scripts that read the spent coins (CONNECT-RULES).** Two rules Bitcoin
Core enforces even under assumevalid, next to the amounts and maturity of `Spec/Coins.lean`:

* **BIP68** relative locktimes: `SequenceLocks` (`consensus/tx_verify.cpp`), reject reason
  `bad-txns-nonfinal`;
* **the sigop cost**: `GetTransactionSigOpCost` summed over the block, at most
  `MAX_BLOCK_SIGOPS_COST`, reject reason `bad-blk-sigops`. `Spec/Block.lean` bounds the legacy part
  only (`CheckBlock`); this adds the P2SH and witness parts, which need the spent scripts.

Everything is executable. `tools/specfuzz/core_connect_cases.cpp` compares each definition with
Core's own code. Design: `docs/design/connect-rules.md`.
-/
import StarkedAir.Spec.Block

namespace StarkedAir.Spec.ConnectRules

open StarkedAir.Spec StarkedAir.Spec.Block

/-! ### Scripts with their pushed data (`CScript::GetOp` with `pvchRet`) -/

/-- The operations of a script with the data each pushes, and whether the whole script parsed
(`false`: a push runs past the end, where `GetOp` fails). The opcodes are `Block.ops`. -/
def opsD : Bytes → List (UInt8 × Bytes) × Bool
  | [] => ([], true)
  | o :: r =>
    let hdr := if o = 0x4c then 1 else if o = 0x4d then 2 else if o = 0x4e then 4 else 0
    if o ≤ 0x4e then
      if r.length < hdr then ([], false) else
      let n := if o < 0x4c then o.toNat else le (r.take hdr)
      let rest := r.drop hdr
      if rest.length < n then ([], false) else
      let p := opsD (rest.drop n)
      ((o, rest.take n) :: p.1, p.2)
    else
      let p := opsD r
      ((o, []) :: p.1, p.2)
termination_by b => b.length
decreasing_by all_goals (simp; try omega)

/-- `CScript::IsPushOnly`: the script parses and no opcode is above `OP_16`. -/
def pushOnly (s : Bytes) : Bool := (opsD s).2 && (opsD s).1.all fun p => p.1 ≤ 0x60

/-- The data of the last operation (empty for an empty script or a last opcode that pushes no bytes). -/
def lastPush (s : Bytes) : Bytes := ((opsD s).1.getLast?.map Prod.snd).getD []

/-! ### Accurate sigop counting (`CScript::GetSigOpCount(true)`) -/

/-- The count from a list of opcodes, `last` being the previous opcode: `OP_CHECKMULTISIG(VERIFY)`
after `OP_1 … OP_16` counts that number of keys, otherwise 20. -/
def accGo (last : UInt8) : List UInt8 → ℕ
  | [] => 0
  | o :: r =>
    (if o = 0xac ∨ o = 0xad then 1
     else if o = 0xae ∨ o = 0xaf then (if 0x51 ≤ last ∧ last ≤ 0x60 then last.toNat - 0x50 else 20)
     else 0) + accGo o r

/-- `GetSigOpCount(true)`; the previous opcode starts as `OP_INVALIDOPCODE`. -/
def sigOpsAccurate (s : Bytes) : ℕ := accGo 0xff (ops s)

/-! ### Spent script classes -/

/-- `CScript::IsPayToScriptHash`: `OP_HASH160 <20 bytes> OP_EQUAL`. -/
def isP2SH (s : Bytes) : Bool :=
  s.length == 23 && s[0]? == some 0xa9 && s[1]? == some 0x14 && s[22]? == some 0x87

/-- `CScript::IsWitnessProgram`: the version and the program. -/
def witnessProgram (s : Bytes) : Option (ℕ × Bytes) :=
  match s with
  | v :: l :: prog =>
    if 4 ≤ s.length ∧ s.length ≤ 42 ∧ (v = 0 ∨ (0x51 ≤ v ∧ v ≤ 0x60)) ∧ l.toNat + 2 = s.length then
      some (if v = 0 then 0 else v.toNat - 0x50, prog)
    else none
  | _ => none

/-! ### The sigop cost (`GetTransactionSigOpCost`) -/

/-- What `GetP2SHSigOpCount` adds for one input: for a P2SH spent script, the accurate count of the
redeem script, the last item a push-only `scriptSig` pushes; 0 if the `scriptSig` is not push-only. -/
def p2shSigOps (spent scriptSig : Bytes) : ℕ :=
  if isP2SH spent && pushOnly scriptSig then sigOpsAccurate (lastPush scriptSig) else 0

/-- `WitnessSigOps`: version 0 only. A 20-byte program is one signature; a 32-byte program counts its
witness script, the last witness item. -/
def witnessSigOps (version : ℕ) (prog : Bytes) (witness : List Bytes) : ℕ :=
  if version = 0 then
    if prog.length = 20 then 1
    else if prog.length = 32 then (witness.getLast?.map sigOpsAccurate).getD 0
    else 0
  else 0

/-- `CountWitnessSigOps` with the witness flag set: the program is the spent script, or the redeem
script of a P2SH spend with a push-only `scriptSig`. -/
def countWitnessSigOps (scriptSig spent : Bytes) (witness : List Bytes) : ℕ :=
  match witnessProgram spent with
  | some (v, prog) => witnessSigOps v prog witness
  | none =>
    if isP2SH spent && pushOnly scriptSig then
      match witnessProgram (lastPush scriptSig) with
      | some (v, prog) => witnessSigOps v prog witness
      | none => 0
    else 0

/-- `GetTransactionSigOpCost`. `spent` lists the scripts of the coins the inputs spend, in input
order. `strict` is `SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_WITNESS` being set: true for every mainnet block
except the BIP16 exception at height 170,060 (`script_flag_exceptions`, flags none). -/
def txSigOpCost (strict : Bool) (t : Tx) (spent : List Bytes) : ℕ :=
  4 * legacySigOps t +
    if t.isCoinbase || !strict then 0 else
      ((t.vin.zip spent).map fun p => 4 * p2shSigOps p.2 p.1.scriptSig +
        countWitnessSigOps p.1.scriptSig p.2 p.1.witness).sum

/-- `ConnectBlock`'s bound over a block's transactions, each with its spent scripts. -/
def SigOpCostOK (strict : Bool) (txs : List (Tx × List Bytes)) : Prop :=
  (txs.map fun p => txSigOpCost strict p.1 p.2).sum ≤ MAX_BLOCK_SIGOPS_COST

instance (strict : Bool) (txs : List (Tx × List Bytes)) : Decidable (SigOpCostOK strict txs) := by
  unfold SigOpCostOK; infer_instance

/-- The legacy bound of `CheckBlock` follows from the full one. -/
theorem legacy_le_cost (strict : Bool) (t : Tx) (spent : List Bytes) :
    4 * legacySigOps t ≤ txSigOpCost strict t spent := Nat.le_add_right _ _

/-! ### BIP68 (`CalculateSequenceLocks`, `EvaluateSequenceLocks`) -/

/-- What a block's sequence locks are checked against: its height, the median time past of its
predecessor, and the median time past of every earlier block on its chain. -/
structure LockCtx where
  height : ℕ
  prevMtp : ℕ
  mtpAt : ℕ → ℕ

/-- One input spending a coin created at `coinHeight`. Bit 31 of the sequence disables the lock; bit
22 selects time (units of 512 s, counted from the median time past of the block before the coin's)
or height; the low 16 bits are the lock. -/
def inputLockOk (c : LockCtx) (sequence coinHeight : ℕ) : Bool :=
  if sequence / 2 ^ 31 % 2 = 1 then true
  else
    let lock := sequence % 2 ^ 16
    if sequence / 2 ^ 22 % 2 = 1 then decide (c.mtpAt (coinHeight - 1) + 512 * lock ≤ c.prevMtp)
    else decide (coinHeight + lock ≤ c.height)

/-- `SequenceLocks` for a non-coinbase transaction. `enforce` is `LOCKTIME_VERIFY_SEQUENCE` (CSV
active); `heights` lists the creation heights of the coins the inputs spend. -/
def seqLocksOk (enforce : Bool) (c : LockCtx) (t : Tx) (heights : List ℕ) : Bool :=
  !(enforce && decide (2 ≤ t.version)) || (t.vin.zip heights).all fun p => inputLockOk c p.1.sequence p.2

/-- One input's step of `CalculateSequenceLocks`: the last invalid height and time so far. -/
def lockStep (c : LockCtx) (acc : ℤ × ℤ) (p : TxIn × ℕ) : ℤ × ℤ :=
  let s := p.1.sequence
  if s / 2 ^ 31 % 2 = 1 then acc
  else if s / 2 ^ 22 % 2 = 1 then (acc.1, max acc.2 ((c.mtpAt (p.2 - 1) : ℤ) + 512 * (s % 2 ^ 16 : ℕ) - 1))
  else (max acc.1 ((p.2 : ℤ) + (s % 2 ^ 16 : ℕ) - 1), acc.2)

/-- Core's own formulation, which the differential test compares value for value: the last invalid
height and time (`CalculateSequenceLocks`), `-1` when there is none. -/
def seqLockPair (enforce : Bool) (c : LockCtx) (t : Tx) (heights : List ℕ) : ℤ × ℤ :=
  if !(enforce && decide (2 ≤ t.version)) then (-1, -1) else (t.vin.zip heights).foldl (lockStep c) (-1, -1)

/-- `EvaluateSequenceLocks` on Core's pair. -/
def evalLockPair (c : LockCtx) (p : ℤ × ℤ) : Bool := decide (p.1 < c.height) && decide (p.2 < c.prevMtp)

theorem evalLockPair_step (c : LockCtx) (a : ℤ × ℤ) (p : TxIn × ℕ) :
    evalLockPair c (lockStep c a p) = (evalLockPair c a && inputLockOk c p.1.sequence p.2) := by
  unfold lockStep inputLockOk evalLockPair
  rw [Bool.eq_iff_iff]
  by_cases h1 : p.1.sequence / 2 ^ 31 % 2 = 1
  · simp only [h1, if_true, Bool.and_eq_true, decide_eq_true_eq, and_true]
  · by_cases h2 : p.1.sequence / 2 ^ 22 % 2 = 1 <;>
      simp only [h1, h2, if_true, if_false, Bool.and_eq_true, decide_eq_true_eq, max_lt_iff] <;> omega

theorem evalLockPair_foldl (c : LockCtx) (l : List (TxIn × ℕ)) (a : ℤ × ℤ) :
    evalLockPair c (l.foldl (lockStep c) a) =
      (evalLockPair c a && l.all fun p => inputLockOk c p.1.sequence p.2) := by
  induction l generalizing a with
  | nil => simp
  | cons p l ih => rw [List.foldl_cons, ih, evalLockPair_step, List.all_cons, Bool.and_assoc]

/-- **Core's maximum over the inputs, compared once, is every input passing on its own.** The block AIR
checks inputs one by one (`seqLocksOk`); the fuzzer checks `seqLockPair` against Core. -/
theorem seqLockPair_eval (enforce : Bool) (c : LockCtx) (t : Tx) (heights : List ℕ) :
    evalLockPair c (seqLockPair enforce c t heights) = seqLocksOk enforce c t heights := by
  have h0 : evalLockPair c (-1, -1) = true := by
    simp only [evalLockPair, Bool.and_eq_true, decide_eq_true_eq]; omega
  unfold seqLockPair seqLocksOk
  cases h : (enforce && decide (2 ≤ t.version))
  · simp [h0]
  · simp [evalLockPair_foldl, h0]

/-- The context of block `height` from the block times of its chain (`times[k]` is block `k`'s). -/
def lockCtxOfTimes (times : List ℕ) (height : ℕ) : LockCtx :=
  let mtp := fun k => Bitcoin.medianTimePast (((List.range (k + 1)).reverse.take 11).map fun i => times.getD i 0)
  ⟨height, mtp (height - 1), mtp⟩

/-- A block's rule: every non-coinbase transaction passes, at heights from `CSV_HEIGHT` on. -/
def SeqLocksOK (c : LockCtx) (txs : List (Tx × List ℕ)) : Prop :=
  ∀ p ∈ txs, p.1.isCoinbase = false → seqLocksOk (decide (CSV_HEIGHT ≤ c.height)) c p.1 p.2 = true

/-! ### Examples -/

-- 2-of-3 multisig: accurate 3, legacy 20.
#guard sigOpsAccurate [0x52, 0x21] = 0 ∧ sigOpsAccurate [0x52, 0x53, 0xae] = 3 ∧ sigOps [0x52, 0x53, 0xae] = 20
-- P2SH-P2WPKH: the scriptSig pushes `OP_0 <20 bytes>`.
#guard countWitnessSigOps (0x16 :: 0x00 :: 0x14 :: List.replicate 20 7)
  (0xa9 :: 0x14 :: List.replicate 20 1 ++ [0x87]) [] = 1
-- Taproot spends count nothing.
#guard countWitnessSigOps [] (0x51 :: 0x20 :: List.replicate 32 1) [[0xac]] = 0
-- A height lock of 10 on a coin from height 100 opens at height 110.
#guard inputLockOk ⟨109, 0, fun _ => 0⟩ 10 100 = false ∧ inputLockOk ⟨110, 0, fun _ => 0⟩ 10 100 = true

end StarkedAir.Spec.ConnectRules
