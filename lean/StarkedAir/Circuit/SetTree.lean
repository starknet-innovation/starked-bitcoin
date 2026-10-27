/-
**The set tree's glue (set-pass step 4), Lean-first.** Segment proofs (`SetPass.segSys`, 550 public
inputs) are folded into one proof by a binary tree, as the header chain's and the block forest's.

A segment's summary is 48 limbs: the 16-bit halves of two Blake2s digests, of its incoming and its
outgoing state vector (`inIdx`, `outIdx`: the challenge `(γ, z, α)`, then the carried state; the
outgoing `HASLAST` is the constant 1, since a segment ends on a record). The challenge is in both
vectors, so equal states mean equal challenges.

then its Merkle root's limbs (D-050).

- `setLeafOut`: hook 0 returns the segment's public inputs; the output is `pubsDigest(0, summary)`.
- `setNodeProgram`: two verified children whose summaries link (the left's outgoing digest is the
  right's incoming one); the output is `pubsDigest(key, (left's incoming, right's outgoing,
  node(left's root, right's root)))`, the roots folded with the header tree's node gadget (`treeNode`).

The verifier rebuilds the pass's start and end states natively (`begin`, the final state it reads) and
compares their digests with the root's summary.
-/
import StarkedAir.Circuit.BlockRec

namespace StarkedAir.Circuit.SetTree

open StarkedAir StarkedAir.Circuit Q

/-- The segment system's public inputs (`SetPass.N_PUB`). -/
def NP : ℕ := 567

/-- The challenge: `γ` (41–44), `z` (45–48), `α` (49–152). -/
def chal : List ℕ := (List.range 112).map (41 + ·)

/-- The incoming state vector: challenge, `i`, `HASLAST`, last key, height, sum, amount, Blake2s, SHA-256. -/
def inIdx : List ℕ :=
  chal ++ [1, 3] ++ (List.range 36).map (4 + ·) ++ [40] ++ (List.range 4).map (153 + ·) ++
    (List.range 12).map (162 + ·) ++ (List.range 82).map (222 + ·) ++ (List.range 82).map (386 + ·)

/-- The outgoing state vector, in the same layout; register `NP` holds the constant 1 (`HASLAST`). -/
def outIdx : List ℕ :=
  chal ++ [2, NP] ++ (List.range 36).map (186 + ·) ++ [161] ++ (List.range 4).map (157 + ·) ++
    (List.range 12).map (174 + ·) ++ (List.range 82).map (304 + ·) ++ (List.range 82).map (468 + ·)

/-- The state vector's length. -/
def NV : ℕ := 331

#guard inIdx.length = NV
#guard outIdx.length = NV

/-- Eight digest words split into 16 guessed u16 limbs that recombine to them (as `treeNode`). -/
def split16 (n : ℕ) (ws : List ℕ) : Out (List ℕ) :=
  ⟨.const n 0 1 0 0 :: (List.range 8).flatMap (fun w =>
      let word := ws.getD w 0
      let r := n + 1 + 4 * w
      [.guessU16 r (.coord 0 (.reg word)), .guessU16 (r + 1) (.coord 1 (.reg word)),
       .mul (r + 2) (r + 1) n, .add (r + 3) r (r + 2), .eq (r + 3) word]),
   (List.range 16).map (fun j => n + 1 + 4 * (j / 2) + j % 2), n + 33⟩

/-! ### The leaf -/

def hIn : Out (List ℕ) := pubsDigest (NP + 1) [] inIdx
def hOut : Out (List ℕ) := pubsDigest hIn.next [] outIdx
def sIn : Out (List ℕ) := split16 hOut.next hIn.res
def sOut : Out (List ℕ) := split16 sIn.next hOut.res
def leafKey : List ℕ := (List.range 8).map (sOut.next + ·)

/-- The summary: the incoming digest's limbs, the outgoing one's, the root's (public inputs 550–565). -/
def NS : ℕ := 48
def ROOT0 : ℕ := 550

def leafDg : Out (List ℕ) := pubsDigest (sOut.next + 8) leafKey (sIn.res ++ sOut.res ++ (List.range 16).map (ROOT0 + ·))

def leafOutOps : List Op :=
  [.hook 0 [] (List.range NP), .const NP 1 0 0 0] ++ hIn.ops ++ hOut.ops ++ sIn.ops ++ sOut.ops ++
    leafKey.map (fun r => constU32 r 0) ++ leafDg.ops

/-- **The set leaf's output program.** Results: the output digest's 8 words. -/
def setLeafOut : Program := ⟨"set_leaf_out", leafOutOps, leafDg.res⟩

def leafOutJson : String := setLeafOut.toJson

/-! ### The node -/

/-- A child's external values: its 32 summary limbs, key words, preprocessed root. -/
def EXT : ℕ := NS + 16

/-- A child's section (as `BlockNode.bchild`, with 32 summary limbs). -/
def schild (n i : ℕ) : Out ChildRegs :=
  let e := EXT * i
  let pubsOps := (List.range NS).map (fun k => Op.guessM31 (n + k) (.ext (e + k)))
  let key := guessHash (n + NS) (e + NS)
  let dg := pubsDigest key.next key.res ((List.range NS).map (n + ·))
  let root := guessHash dg.next (e + NS + 8)
  let ch := (List.range 8).map (root.next + ·)
  ⟨pubsOps ++ key.ops ++ dg.ops ++ root.ops ++ [.hook i (root.res ++ dg.res) ch],
   ⟨(n + ·), key.res, dg.res, ch⟩, root.next + 8⟩

def sC0 : Out ChildRegs := schild 0 0
def sC1 : Out ChildRegs := schild sC0.next 1
/-- The link: the right child's incoming digest is the left's outgoing one. -/
def sLink : List Op := (List.range 16).map (fun j => Op.eq (sC1.res.pubs j) (sC0.res.pubs (16 + j)))
def sKey : Out (List ℕ) :=
  blake2s sC1.next (sC0.res.chash ++ sC0.res.key ++ sC1.res.chash ++ sC1.res.key) 128
/-- The children's roots folded (`treeNode` reads root limbs at `TB …`). -/
def sRoot : Out (List ℕ) :=
  treeNode sKey.next (fun k => sC0.res.pubs (32 + (k - TB))) (fun k => sC1.res.pubs (32 + (k - TB)))
/-- The node's summary: the left's incoming digest, the right's outgoing one, the folded root. -/
def sOuts : List ℕ :=
  (List.range 16).map sC0.res.pubs ++ (List.range 16).map (fun j => sC1.res.pubs (16 + j)) ++ sRoot.res
def sDigest : Out (List ℕ) := pubsDigest sRoot.next sKey.res sOuts

/-- **The set node program.** Results: the output digest's 8 words. -/
def setNodeProgram : Program :=
  ⟨"set_node_glue", sC0.ops ++ sC1.ops ++ sLink ++ sKey.ops ++ sRoot.ops ++ sDigest.ops, sDigest.res⟩

def nodeJson : String := setNodeProgram.toJson

end StarkedAir.Circuit.SetTree
