/-
**Block structure (M3a).** Bitcoin Core's mainnet block checks that need no UTXO set:
deserialization (`CTransaction::Unserialize`, `ReadCompactSize`), `CheckBlock` (Merkle root and
mutation, sizes, coinbase position, `CheckTransaction`, legacy sigops) and `ContextualCheckBlock`
(finality, BIP34 height in the coinbase, witness commitment, unexpected witness, weight).
Checks needing the UTXO set (fees, subsidy, BIP30, BIP68, full sigop cost, scripts) are M3b/M3c.

Everything is executable; `checkBlock` returns Core's reject reason, and `#guard`s plus
`BlockCheck.lean` run it on real mainnet blocks (`testdata/blocks/`).
-/
import BitcoinConsensus.Bitcoin
import BitcoinConsensus.Sha256Fast

namespace BitcoinConsensus.Block

open BitcoinConsensus.Sha256

abbrev Bytes := List UInt8

/-! ### SHA-256 and SHA256d on byte strings -/

/-- Big-endian 32-bit word `t` of a 64-byte chunk. -/
def chunkWords (c : Bytes) : ℕ → Word :=
  let a := c.toArray
  fun t => BitVec.ofNat 32 ((a.getD (4 * t) 0).toNat * 2 ^ 24 + (a.getD (4 * t + 1) 0).toNat * 2 ^ 16 +
    (a.getD (4 * t + 2) 0).toNat * 2 ^ 8 + (a.getD (4 * t + 3) 0).toNat)

/-- `n` as `k` bytes, big-endian. -/
def beBytes (k n : ℕ) : Bytes := (List.range k).reverse.map fun i => UInt8.ofNat (n / 2 ^ (8 * i))

/-- FIPS 180-4 padding: `0x80`, zeros, then the bit length as 64 bits. -/
def pad (m : Bytes) : Bytes :=
  m ++ [0x80] ++ List.replicate ((119 - m.length % 64) % 64) 0 ++ beBytes 8 (8 * m.length)

/-- Compresses consecutive 64-byte chunks into `H`. -/
def compressAll (H : State) : Bytes → State
  | [] => H
  | x :: xs => compressAll (compress H (chunkWords ((x :: xs).take 64))) ((x :: xs).drop 64)
termination_by b => b.length
decreasing_by all_goals (simp; try omega)

def stateBytes (s : State) : Bytes :=
  [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].flatMap fun w => beBytes 4 w.toNat

def sha256 (m : Bytes) : Bytes := stateBytes (compressAll IV (pad m))

/-- SHA256d; the result is in internal byte order (a block or tx id displays reversed). -/
def sha256d (m : Bytes) : Bytes := sha256 (sha256 m)

#guard sha256 "abc".toUTF8.toList =
  stateBytes ⟨0xba7816bf#32, 0x8f01cfea#32, 0x414140de#32, 0x5dae2223#32,
    0xb00361a3#32, 0x96177a9c#32, 0xb410ff61#32, 0xf20015ad#32⟩

/-! ### Deserialization (Core's `serialize.h`, `CTransaction::Unserialize`) -/

abbrev Parser := StateT Bytes Option

def byte : Parser UInt8 := fun s => match s with
  | [] => none
  | b :: r => some (b, r)

def take (n : ℕ) : Parser Bytes := fun s => if n ≤ s.length then some (s.take n, s.drop n) else none

/-- Little-endian value of a byte string. -/
def le (b : Bytes) : ℕ := b.foldr (fun x acc => x.toNat + 256 * acc) 0

def u32 : Parser ℕ := do return le (← take 4)

/-- Core's `MAX_SIZE`: the largest CompactSize a length may have. -/
def MAX_SIZE : ℕ := 0x02000000

/-- `ReadCompactSize` with `range_check`: canonical encodings only, at most `MAX_SIZE`. -/
def compactSize : Parser ℕ := do
  let b ← byte
  let v ← if b < 253 then pure b.toNat
    else if b = 253 then do
      let v := le (← take 2); if v < 253 then failure else pure v
    else if b = 254 then do
      let v := le (← take 4); if v < 0x10000 then failure else pure v
    else do
      let v := le (← take 8); if v < 0x100000000 then failure else pure v
  if v > MAX_SIZE then failure else pure v

def varBytes : Parser Bytes := do take (← compactSize)

def count {α : Type} (p : Parser α) : ℕ → Parser (List α)
  | 0 => pure []
  | n + 1 => do let x ← p; let xs ← count p n; pure (x :: xs)

def vec {α : Type} (p : Parser α) : Parser (List α) := do count p (← compactSize)

structure OutPoint where
  hash : Bytes
  n : ℕ
  deriving DecidableEq, Repr

structure TxIn where
  prevout : OutPoint
  scriptSig : Bytes
  sequence : ℕ
  witness : List Bytes
  deriving Repr

structure TxOut where
  /-- `CAmount` is a signed 64-bit integer. -/
  value : ℤ
  scriptPubKey : Bytes
  deriving Repr

structure Tx where
  version : ℕ
  vin : List TxIn
  vout : List TxOut
  lockTime : ℕ
  deriving Repr

def txIn : Parser TxIn := do
  let h ← take 32
  let n ← u32
  let s ← varBytes
  let q ← u32
  pure ⟨⟨h, n⟩, s, q, []⟩

def txOut : Parser TxOut := do
  let v := le (← take 8)
  let s ← varBytes
  pure ⟨if v < 2 ^ 63 then (v : ℤ) else (v : ℤ) - 2 ^ 64, s⟩

def Tx.hasWitness (tx : Tx) : Bool := tx.vin.any fun i => !i.witness.isEmpty

/-- `CTransaction::Unserialize` with witness allowed (as for blocks). -/
def tx : Parser Tx := do
  let version ← u32
  let vin0 ← vec txIn
  let (flags, vin, vout) ← if vin0.isEmpty then do
      let f ← byte
      if f ≠ 0 then do
        let vin ← vec txIn
        let vout ← vec txOut
        pure (f.toNat, vin, vout)
      else pure (0, vin0, [])
    else do
      let vout ← vec txOut
      pure (0, vin0, vout)
  let vin ← if flags % 2 = 1 then do
      let ws ← count (vec varBytes) vin.length
      let vin' := (vin.zip ws).map fun (i, w) => { i with witness := w }
      -- "Superfluous witness record"
      if vin'.all (·.witness.isEmpty) then failure else pure vin'
    else pure vin
  -- "Unknown transaction optional data"
  if flags / 2 ≠ 0 then failure
  let lockTime ← u32
  pure ⟨version, vin, vout, lockTime⟩

structure Blk where
  header : Bytes
  txs : List Tx
  deriving Repr

/-- A block's bytes; all of them must be consumed. Core's stream deserialization ignores trailing
bytes; this spec is stricter (sound), and the proven input is always the canonical serialization. -/
def parseBlock (b : Bytes) : Option Blk :=
  match (do let h ← take 80; let txs ← vec tx; pure (Blk.mk h txs) : Parser Blk) b with
  | some (blk, []) => some blk
  | _ => none

/-! ### Serialization (for txid, wtxid and sizes) -/

def leBytes (k n : ℕ) : Bytes := (List.range k).map fun i => UInt8.ofNat (n / 2 ^ (8 * i))

def serCompact (n : ℕ) : Bytes :=
  if n < 253 then [UInt8.ofNat n]
  else if n < 0x10000 then 253 :: leBytes 2 n
  else if n < 0x100000000 then 254 :: leBytes 4 n
  else 255 :: leBytes 8 n

def serVarBytes (b : Bytes) : Bytes := serCompact b.length ++ b

def serTxIn (i : TxIn) : Bytes := i.prevout.hash ++ leBytes 4 i.prevout.n ++ serVarBytes i.scriptSig ++ leBytes 4 i.sequence

def serTxOut (o : TxOut) : Bytes := leBytes 8 (o.value % 2 ^ 64).toNat ++ serVarBytes o.scriptPubKey

/-- `TX_NO_WITNESS` serialization (for the txid and the stripped size). -/
def serNoWit (t : Tx) : Bytes :=
  leBytes 4 t.version ++ serCompact t.vin.length ++ t.vin.flatMap serTxIn ++
    serCompact t.vout.length ++ t.vout.flatMap serTxOut ++ leBytes 4 t.lockTime

/-- `TX_WITH_WITNESS` serialization: the extended format when the transaction has witness data. -/
def serWit (t : Tx) : Bytes :=
  if t.hasWitness then
    leBytes 4 t.version ++ [0, 1] ++ serCompact t.vin.length ++ t.vin.flatMap serTxIn ++
      serCompact t.vout.length ++ t.vout.flatMap serTxOut ++
      t.vin.flatMap (fun i => serCompact i.witness.length ++ i.witness.flatMap serVarBytes) ++
      leBytes 4 t.lockTime
  else serNoWit t

def txid (t : Tx) : Bytes := sha256d (serNoWit t)
def wtxid (t : Tx) : Bytes := sha256d (serWit t)

def serBlock (b : Blk) : Bytes := b.header ++ serCompact b.txs.length ++ b.txs.flatMap serWit

/-! ### Merkle root (`ComputeMerkleRoot`, with mutation detection) -/

/-- Some pair at an even position has equal hashes (CVE-2012-2459). -/
def dupPair : List Bytes → Bool
  | a :: b :: r => a == b || dupPair r
  | _ => false

/-- One level: pair hashes, duplicating the last one if the count is odd. -/
def level : List Bytes → List Bytes
  | a :: b :: r => sha256d (a ++ b) :: level r
  | [a] => [sha256d (a ++ a)]
  | [] => []

theorem level_length : ∀ l : List Bytes, (level l).length = (l.length + 1) / 2
  | a :: b :: r => by simp only [level, List.length_cons, level_length r]; omega
  | [a] => by simp [level]
  | [] => by simp [level]

/-- `ComputeMerkleRoot`: the root (zero for no leaves) and whether some level was mutated. -/
def merkleRoot (l : List Bytes) : Bytes × Bool :=
  if h : l.length ≤ 1 then (l.headD (List.replicate 32 0), false)
  else
    let (r, m) := merkleRoot (level l)
    (r, m || dupPair l)
termination_by l.length
decreasing_by rw [level_length]; omega

/-! ### Scripts: legacy sigop counting (`CScript::GetSigOpCount(false)`) -/

/-- Opcodes from `pc` on, as `GetOp` reads them; stops at the end or a truncated push. -/
def ops : Bytes → List UInt8
  | [] => []
  | o :: r =>
    let n : Option ℕ :=
      if o < 0x4c then some o.toNat
      else if o = 0x4c then (if 1 ≤ r.length then some (le (r.take 1)) else none)
      else if o = 0x4d then (if 2 ≤ r.length then some (le (r.take 2)) else none)
      else if o = 0x4e then (if 4 ≤ r.length then some (le (r.take 4)) else none)
      else some 0
    match n with
    | none => []
    | some n =>
      let hdr := if o = 0x4c then 1 else if o = 0x4d then 2 else if o = 0x4e then 4 else 0
      let rest := r.drop hdr
      if o ≤ 0x4e ∧ rest.length < n then [] else o :: ops (rest.drop (if o ≤ 0x4e then n else 0))
termination_by b => b.length
decreasing_by all_goals (simp; try omega)

def sigOps (s : Bytes) : ℕ :=
  (ops s).foldl (fun n o => if o = 0xac ∨ o = 0xad then n + 1 else if o = 0xae ∨ o = 0xaf then n + 20 else n) 0

def legacySigOps (t : Tx) : ℕ :=
  (t.vin.map fun i => sigOps i.scriptSig).sum + (t.vout.map fun o => sigOps o.scriptPubKey).sum

/-! ### `CheckTransaction` and `CheckBlock` -/

def MAX_BLOCK_WEIGHT : ℕ := 4000000
def MAX_MONEY : ℤ := 21000000 * 100000000
def MAX_BLOCK_SIGOPS_COST : ℕ := 80000

def OutPoint.isNull (p : OutPoint) : Bool := p.hash.all (· == 0) && p.n == 0xffffffff
def Tx.isCoinbase (t : Tx) : Bool := match t.vin with
  | [i] => i.prevout.isNull
  | _ => false

def nodupBy {α : Type} [DecidableEq α] : List α → Bool
  | [] => true
  | a :: r => !r.contains a && nodupBy r

/-- `CheckTransaction`: `none` if valid, else Core's reject reason. -/
def checkTx (t : Tx) : Option String :=
  if t.vin.isEmpty then some "bad-txns-vin-empty"
  else if t.vout.isEmpty then some "bad-txns-vout-empty"
  else if (serNoWit t).length * 4 > MAX_BLOCK_WEIGHT then some "bad-txns-oversize"
  else
    let r := t.vout.foldl (fun (acc : Option String × ℤ) (o : TxOut) =>
      match acc.1 with
      | some e => (some e, acc.2)
      | none =>
        if o.value < 0 then (some "bad-txns-vout-negative", 0)
        else if o.value > MAX_MONEY then (some "bad-txns-vout-toolarge", 0)
        else if acc.2 + o.value > MAX_MONEY then (some "bad-txns-txouttotal-toolarge", 0)
        else (none, acc.2 + o.value)) (none, 0)
    if r.1.isSome then r.1
    else if !nodupBy (t.vin.map (·.prevout)) then some "bad-txns-inputs-duplicate"
    else if t.isCoinbase then
      match t.vin with
      | [i] => if i.scriptSig.length < 2 ∨ i.scriptSig.length > 100 then some "bad-cb-length" else none
      | _ => none
    else if t.vin.any (·.prevout.isNull) then some "bad-txns-prevout-null"
    else none

def strippedSize (b : Blk) : ℕ := 80 + (serCompact b.txs.length).length + (b.txs.map fun t => (serNoWit t).length).sum
def totalSize (b : Blk) : ℕ := 80 + (serCompact b.txs.length).length + (b.txs.map fun t => (serWit t).length).sum
def weight (b : Blk) : ℕ := strippedSize b * 3 + totalSize b

/-- The header's Merkle-root field (bytes 36..67, internal order). -/
def headerMerkle (b : Blk) : Bytes := (b.header.drop 36).take 32

/-- `CheckBlock` without the header's proof of work (proven by the header chain). -/
def checkBlockCtxFree (b : Blk) : Option String :=
  let (root, mutated) := merkleRoot (b.txs.map txid)
  if root != headerMerkle b then some "bad-txnmrklroot"
  else if mutated then some "bad-txns-duplicate"
  else if b.txs.isEmpty ∨ b.txs.length * 4 > MAX_BLOCK_WEIGHT ∨ strippedSize b * 4 > MAX_BLOCK_WEIGHT then
    some "bad-blk-length"
  else if !(b.txs.headD ⟨0, [], [], 0⟩).isCoinbase then some "bad-cb-missing"
  else if (b.txs.drop 1).any Tx.isCoinbase then some "bad-cb-multiple"
  else match (b.txs.map checkTx).filterMap id with
    | e :: _ => some e
    | [] => if (b.txs.map legacySigOps).sum * 4 > MAX_BLOCK_SIGOPS_COST then some "bad-blk-sigops" else none

/-! ### `ContextualCheckBlock` (mainnet buried deployments) -/

def BIP34_HEIGHT : ℕ := 227931
def CSV_HEIGHT : ℕ := 419328
def SEGWIT_HEIGHT : ℕ := 481824

/-- The context from the header chain: the block's height and the median time past of its
predecessor. (The block's own time is read from its header.) -/
structure Ctx where
  height : ℕ
  prevMtp : ℕ

/-- The header's `nTime` (bytes 68..71, little-endian). -/
def Blk.time (b : Blk) : ℕ := le ((b.header.drop 68).take 4)

/-- `IsFinalTx`. -/
def isFinal (t : Tx) (height cutoff : ℕ) : Bool :=
  t.lockTime == 0 || decide (t.lockTime < (if t.lockTime < 500000000 then height else cutoff)) ||
    t.vin.all (·.sequence == 0xffffffff)

/-- `CScriptNum::serialize`: minimal little-endian signed encoding (non-negative `n`). -/
def scriptNum (n : ℕ) : Bytes :=
  if n = 0 then [] else
  let b := leBytes ((Nat.log 256 n) + 1) n
  if (b.getLast?.getD 0) &&& 0x80 ≠ 0 then b ++ [0] else b

/-- `CScript() << n` for a non-negative height. -/
def pushHeight (n : ℕ) : Bytes :=
  if n = 0 then [0x00] else if n ≤ 16 then [UInt8.ofNat (0x50 + n)]
  else let d := scriptNum n; UInt8.ofNat d.length :: d

/-- `GetWitnessCommitmentIndex`: the last coinbase output that looks like a commitment. -/
def commitmentIndex (cb : Tx) : Option ℕ :=
  (List.range cb.vout.length).foldl (fun acc o =>
    let s := (cb.vout.getD o ⟨0, []⟩).scriptPubKey
    if s.length ≥ 38 ∧ s.take 6 = [0x6a, 0x24, 0xaa, 0x21, 0xa9, 0xed] then some o else acc) none

def checkBlockContextual (c : Ctx) (b : Blk) : Option String :=
  let cutoff := if c.height ≥ CSV_HEIGHT then c.prevMtp else b.time
  if !b.txs.all (fun t => isFinal t c.height cutoff) then some "bad-txns-nonfinal"
  else
  let cb := b.txs.headD ⟨0, [], [], 0⟩
  let ss := (cb.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig
  if c.height ≥ BIP34_HEIGHT ∧ ss.take (pushHeight c.height).length ≠ pushHeight c.height then some "bad-cb-height"
  else
  let commit := if c.height ≥ SEGWIT_HEIGHT then commitmentIndex cb else none
  let wit : Option (Option String) := commit.map fun pos =>
    let leaves := List.replicate 32 0 :: (b.txs.drop 1).map wtxid
    let stack := (cb.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).witness
    match stack with
    | [nonce] =>
      if nonce.length ≠ 32 then some "bad-witness-nonce-size"
      else if sha256d ((merkleRoot leaves).1 ++ nonce) ≠ (((cb.vout.getD pos ⟨0, []⟩).scriptPubKey.drop 6).take 32)
        then some "bad-witness-merkle-match" else none
    | _ => some "bad-witness-nonce-size"
  match wit with
  | some (some e) => some e
  | _ =>
    if wit.isNone ∧ b.txs.any Tx.hasWitness then some "unexpected-witness"
    else if weight b > MAX_BLOCK_WEIGHT then some "bad-blk-weight"
    else none

/-- **A block passes Core's UTXO-independent checks** in context `c`: it deserializes and
passes `CheckBlock` (minus the header PoW, proven by the header chain) and `ContextualCheckBlock`. -/
def checkBlock (c : Ctx) (raw : Bytes) : Option String :=
  match parseBlock raw with
  | none => some "deserialize"
  | some b => (checkBlockCtxFree b).orElse fun _ => checkBlockContextual c b

def BlockValid (c : Ctx) (raw : Bytes) : Prop := checkBlock c raw = none

/-! Tests on real mainnet blocks: `BlockCheck.lean` (reads `testdata/blocks/`, which
`scripts/fetch_blocks.py` binds to the proven header file). -/

end BitcoinConsensus.Block
