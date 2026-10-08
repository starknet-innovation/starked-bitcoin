/-
Runs the M3a block spec (`Spec/Block.lean`) on sample mainnet blocks.
Usage (from lean/): `lake env lean --run BlockCheck.lean <height> [<height> ...]`
Context (height, time, previous MTP) comes from `../data/headers.bin`.
-/
import StarkedAir.Spec.Block

open StarkedAir.Spec.Block

def le4 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + 256 * b[i+1]!.toNat + 65536 * b[i+2]!.toNat + 16777216 * b[i+3]!.toNat

def timeAt (hs : ByteArray) (h : Nat) : Nat := le4 hs (80 * h + 68)

/-- Median of the up to 11 times before height `h` (Core's `GetMedianTimePast` of block h-1). -/
def prevMtp (hs : ByteArray) (h : Nat) : Nat :=
  if h = 0 then 0 else
  let ts := ((List.range (min 11 h)).map fun k => timeAt hs (h - 1 - k)).mergeSort (· ≤ ·)
  ts.getD (ts.length / 2) 0

def hex (b : Bytes) : String := String.join (b.reverse.map fun x =>
  let s := String.ofList (Nat.toDigits 16 x.toNat); if s.length = 1 then "0" ++ s else s)

/-- Sets the header's Merkle field to the transactions' root. -/
def fixMerkle (b : Blk) : Blk :=
  { b with header := b.header.take 36 ++ (merkleRoot (b.txs.map txid)).1 ++ b.header.drop 68 }

def mapTx (b : Blk) (i : Nat) (f : Tx → Tx) : Blk := { b with txs := b.txs.modify i f }

/-- Mutations of real blocks, each expecting Core's reject reason. -/
def negatives (hs : ByteArray) : IO Nat := do
  let load (h : Nat) : IO Blk := do
    let raw := (← IO.FS.readBinFile s!"../testdata/blocks/{h}.bin").toList
    match parseBlock raw with
    | some b => pure b
    | none => throw (IO.userError s!"{h}: unparsed")
  let ctx (h : Nat) : Ctx := ⟨h, prevMtp hs h⟩
  let b170 ← load 170
  let b774 ← load 774628
  let b481 ← load 481824
  let lastTx := b774.txs.getLast?.getD ⟨0, [], [], 0⟩
  let cases : List (String × Ctx × Blk × String) := [
    ("duplicate last tx (CVE-2012-2459), same root", ctx 774628, { b774 with txs := b774.txs ++ [lastTx] }, "bad-txns-duplicate"),
    ("tampered witness (txid unchanged)", ctx 774628,
      mapTx b774 1 (fun t => { t with vin := t.vin.modify 0 fun i => { i with witness := i.witness.modify 0 fun w => w.modify 0 (· + 1) } }),
      "bad-witness-merkle-match"),
    ("tampered output value", ctx 774628, mapTx b774 1 (fun t => { t with vout := t.vout.modify 0 fun o => { o with value := o.value + 1 } }), "bad-txnmrklroot"),
    ("wrong BIP34 height", ctx 481825 |> fun c => { c with height := 481825 }, b481, "bad-cb-height"),
    ("negative output value (root fixed)", ctx 170, fixMerkle (mapTx b170 1 fun t => { t with vout := t.vout.modify 0 fun o => { o with value := -1 } }), "bad-txns-vout-negative"),
    ("non-final tx (root fixed)", ctx 170, fixMerkle (mapTx b170 1 fun t => { t with lockTime := 1000, vin := t.vin.map fun i => { i with sequence := 0 } }), "bad-txns-nonfinal"),
    ("witness before segwit (txid unchanged)", ctx 170, mapTx b170 1 (fun t => { t with vin := t.vin.modify 0 fun i => { i with witness := [[1]] } }), "unexpected-witness"),
    ("second coinbase (root fixed)", ctx 170, fixMerkle { b170 with txs := b170.txs ++ [b170.txs.headD ⟨0, [], [], 0⟩] }, "bad-cb-multiple"),
    ("no transactions", ctx 170, { b170 with txs := [] }, "bad-txnmrklroot")
  ]
  let mut fails := 0
  for (name, c, b, want) in cases do
    let got := checkBlock c (serBlock b)
    let ok := got == some want
    IO.println s!"{if ok then "ok  " else "FAIL"} {name}: got {got.getD "VALID"}, want {want}"
    if !ok then fails := fails + 1
  return fails

def main (args : List String) : IO UInt32 := do
  let hs ← IO.FS.readBinFile "../data/headers.bin"
  if args == ["neg"] then
    return (if (← negatives hs) = 0 then 0 else 1)
  let mut fails := 0
  for a in args do
    let h := a.toNat!
    let raw := (← IO.FS.readBinFile s!"../testdata/blocks/{h}.bin").toList
    if raw.take 80 != ((hs.extract (80 * h) (80 * h + 80)).toList) then
      IO.println s!"{h}: header differs from ../data/headers.bin"; fails := fails + 1; continue
    let t0 ← IO.monoMsNow
    let c : Ctx := ⟨h, prevMtp hs h⟩
    let r := checkBlock c raw
    let info := match parseBlock raw with
      | some b => s!"{b.txs.length} txs, weight {weight b}, merkle {hex (merkleRoot (b.txs.map txid)).1}"
      | none => "unparsed"
    let t1 ← IO.monoMsNow
    IO.println s!"{h}: {r.getD "VALID"} ({info}; {t1 - t0} ms)"
    if r.isSome then fails := fails + 1
  return (if fails = 0 then 0 else 1)
