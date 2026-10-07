/-
What a header-chain segment proof establishes, stated over Bitcoin objects only (no trace).

A segment is `H` consecutive headers `hs 0 … hs (H−1)` (each as 20 big-endian words). `SegIn`
describes the chain just before the segment and `SegOut` the chain at its end; consecutive
segments chain by `SegOut` → `SegIn`. All numeric fields are Core's integers (`nBits`, times
as `uint32`, work as `arith_uint256`).
-/
import StarkedAir.Spec.MtpMath

namespace StarkedAir.Spec.Bitcoin

open StarkedAir.Spec.Sha256

/-- The chain just before a segment. -/
structure SegIn where
  /-- Hash of the block before the segment's first header. -/
  prevHash : State
  /-- Height of the segment's first header. -/
  height : ℕ
  /-- nBits, time and period-start time of the block before the segment. -/
  prevNBits : ℕ
  prevTime : ℕ
  prevPst : ℕ
  /-- Times of the blocks before the segment, newest first (all of them, or at least 11). -/
  window : List ℕ
  /-- Chainwork up to and including the block before the segment. -/
  work : ℕ

/-- The chain at the end of a segment. -/
structure SegOut where
  tip : State
  height : ℕ
  nBits : ℕ
  time : ℕ
  pst : ℕ
  /-- The times of the 10 blocks before the last one, newest first (sentinel-padded near genesis). -/
  window : List ℕ
  work : ℕ

/-- Period-start time after header `j` of a segment starting at height `h0`. -/
def pstOf (h0 prevPst : ℕ) (hs : ℕ → ℕ → Word) : ℕ → ℕ
  | 0 => if h0 % 2016 = 0 then timeOf (hs 0) else prevPst
  | j + 1 => if (h0 + (j + 1)) % 2016 = 0 then timeOf (hs (j + 1)) else pstOf h0 prevPst hs j

/-- Times of all blocks before header `j`, newest first. -/
def prevTimes (hs : ℕ → ℕ → Word) (w : List ℕ) (j : ℕ) : List ℕ :=
  ((List.range j).reverse.map fun i => timeOf (hs i)) ++ w

/-- **A valid segment** (Bitcoin Core mainnet header rules, except wall-clock time). -/
def SegmentValid (H : ℕ) (hs : ℕ → ℕ → Word) (i : SegIn) (o : SegOut) : Prop :=
  0 < H ∧
  -- Proof of work and linkage.
  (∀ j < H, powOk (sha256d (hs j)) (nBitsOf (hs j))) ∧
  prevHash (hs 0) = i.prevHash ∧
  (∀ j < H, 1 ≤ j → prevHash (hs j) = sha256d (hs (j - 1))) ∧
  o.tip = sha256d (hs (H - 1)) ∧
  -- Heights.
  i.height + (H - 1) < 2 ^ 30 ∧ o.height = i.height + (H - 1) ∧
  -- Difficulty: constant inside a period, `GetNextWorkRequired` at each later boundary.
  (∀ j < H, (i.height + j) % 2016 ≠ 0 →
    nBitsOf (hs j) = if j = 0 then i.prevNBits else nBitsOf (hs (j - 1))) ∧
  (∀ j < H, (i.height + j) % 2016 = 0 → 0 < i.height + j →
    nBitsOf (hs j) = nextWork (if j = 0 then i.prevNBits else nBitsOf (hs (j - 1)))
      (if j = 0 then i.prevTime else timeOf (hs (j - 1)))
      (if j = 0 then i.prevPst else pstOf i.height i.prevPst hs (j - 1))) ∧
  -- Median time past.
  (∀ j < H, mtpOk (timeOf (hs j)) (prevTimes hs i.window j) = true) ∧
  -- Outputs for the next segment.
  o.nBits = nBitsOf (hs (H - 1)) ∧ o.time = timeOf (hs (H - 1)) ∧
  o.pst = pstOf i.height i.prevPst hs (H - 1) ∧
  o.window = ((prevTimes hs i.window (H - 1)) ++ sentinel).take 10 ∧
  -- Chainwork.
  o.work = i.work + ∑ j ∈ Finset.range H, blockProof (nBitsOf (hs j))

end StarkedAir.Spec.Bitcoin
