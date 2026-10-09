/-
Answers `tools/specfuzz/core_cases.cpp`'s cases from the Lean header spec (`Spec/Bitcoin.lean`):
reads `<case>\t<Core's answer>` lines on stdin and prints `<case>\t<Lean's answer>`.
Run: `lake env lean --run SpecCases.lean < cases.tsv` (see `tools/specfuzz/run.sh`).
-/
import StarkedAir.Spec.Bitcoin
import StarkedAir.Spec.Block

open StarkedAir.Spec.Bitcoin StarkedAir.Spec.Sha256

def hexDigit (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def parseHex (s : String) : Option ℕ :=
  s.foldl (fun acc c => do let a ← acc; let d ← hexDigit c; pure (16 * a + d)) (some 0)

def hex64 (n : ℕ) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (64 - s.length) '0') ++ s

/-- A hash given as its 32 bytes `data()[0..31]`, as the state whose `hashByte i` is byte `i`. -/
def stateOfBytes (b : List ℕ) : State :=
  let w (k : ℕ) : Word := BitVec.ofNat 32
    (b.getD (4 * k) 0 * 2 ^ 24 + b.getD (4 * k + 1) 0 * 2 ^ 16 + b.getD (4 * k + 2) 0 * 2 ^ 8 + b.getD (4 * k + 3) 0)
  ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

def bytesOfHex (s : String) : Option (List ℕ) :=
  let cs := s.toList
  if cs.length ≠ 64 then none else
  (List.range 32).mapM fun i => do
    let hi ← hexDigit (cs.getD (2 * i) ' ')
    let lo ← hexDigit (cs.getD (2 * i + 1) ' ')
    pure (16 * hi + lo)

/-- Hex to bytes (`-` is the empty string). -/
def bytesOfHexAny (s : String) : Option StarkedAir.Spec.Block.Bytes :=
  if s == "-" then some [] else
  let cs := s.toList
  if cs.length % 2 ≠ 0 then none else
  (List.range (cs.length / 2)).mapM fun i => do
    let hi ← hexDigit (cs.getD (2 * i) ' ')
    let lo ← hexDigit (cs.getD (2 * i + 1) ' ')
    pure (UInt8.ofNat (16 * hi + lo))

def hexOfBytes (b : StarkedAir.Spec.Block.Bytes) : String :=
  String.join (b.map fun x => let s := String.ofList (Nat.toDigits 16 x.toNat); if s.length = 1 then "0" ++ s else s)

/-- A whole transaction, as a block's transaction parser reads it. -/
def parseTx (b : StarkedAir.Spec.Block.Bytes) : Option StarkedAir.Spec.Block.Tx :=
  match StarkedAir.Spec.Block.tx b with
  | some (t, []) => some t
  | _ => none

def answer (kind : String) (args : List String) : Option String := do
  match kind, args with
  | "compact", [n] => let n ← n.toNat?; pure <| match compactTarget n with | none => "none" | some t => hex64 t
  | "getcompact", [t] => let t ← parseHex t; pure (toString (getCompact t))
  | "next", [b, p, f] | "nextany", [b, p, f] =>
    let b ← b.toNat?; let p ← p.toNat?; let f ← f.toNat?
    pure (toString (nextWork b p f))
  | "proof", [b] => let b ← b.toNat?; pure (hex64 (blockProof b))
  | "pow", [h, b] =>
    let bs ← bytesOfHex h; let b ← b.toNat?
    pure (if decide (powOk (stateOfBytes bs) b) then "1" else "0")
  | "mtp", [ts] =>
    let ts ← (ts.splitOn ",").mapM String.toNat?
    pure (toString (medianTimePast ts))
  | "sigops", [s] => let b ← bytesOfHexAny s; pure (toString (StarkedAir.Spec.Block.sigOps b))
  | "merkle", [l] =>
    let ls ← (l.splitOn ",").mapM bytesOfHexAny
    let r := StarkedAir.Spec.Block.merkleRoot ls
    pure s!"{hexOfBytes r.1} {if r.2 then 1 else 0}"
  | "checktx", [s] =>
    let b ← bytesOfHexAny s
    pure <| match parseTx b with
      | none => "deserialize"
      | some t => (StarkedAir.Spec.Block.checkTx t).getD "ok"
  | "txids", [s] =>
    let b ← bytesOfHexAny s
    pure <| match parseTx b with
      | none => "deserialize"
      | some t => s!"{hexOfBytes (StarkedAir.Spec.Block.txid t)} {hexOfBytes (StarkedAir.Spec.Block.wtxid t)}"
  | _, _ => none

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let clean := String.ofList (line.toList.filter fun c => c != '\n' && c != '\r')
  let caseStr := (clean.splitOn "\t").headD ""
  let ws := caseStr.splitOn " "
  match answer (ws.headD "") ws.tail with
  | some a => IO.println s!"{caseStr}\t{a}"
  | none => IO.println s!"{caseStr}\tPARSE-ERROR"
  loop stdin

def main : IO Unit := do loop (← IO.getStdin)
