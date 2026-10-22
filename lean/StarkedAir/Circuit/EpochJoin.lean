/-
**The epoch join (BLOCK-REC), Lean-first.** Joins proven epochs into one running proof, one epoch at a
time, so a chain of epochs of any lengths is one proof (docs/design/block-rec.md § The epoch join).

A join verifies two children (hooks, as the node and the epoch root) and links them:
- **the left child** is an epoch root (`base` variants: the chain's first two epochs) or a join (`step`);
- **the right child** is an epoch root that starts from a previous set.

Each child's output digest is recomputed in-circuit from its guessed opening, so the join reads its
fields: an epoch root's `key ‖ fin ‖ prev ‖ from ‖ to ‖ rest` (`EpochRoot.digestOut`'s outer message), a
join's `key ‖ start ‖ end ‖ a ‖ b ‖ acc` (this program's output message). The links: the left ends at
height `b`, the right starts at `b + 1`; the left's end set digest is the right's previous set digest.
The output: `key = Blake2s(left hash ‖ left key ‖ right hash ‖ right key)`, the start set (the left's
previous set, or zero words for a chain from genesis), the end set (the right's final set), the range
`a … b`, and `acc`, a running hash over the epoch roots' output digests (`base`: `Blake2s(out₀ ‖ out₁)`;
`step`: `Blake2s(acc ‖ out)`), which the verifier recomputes from each epoch's public values.

External values, child by child: an epoch root's `key` (8), `fin` (8), `prev` (8), `from`, `to`, `rest`
(8) and its preprocessed root (8) — 42 values; a join's `key` (8), `start` (8), `end` (8), `a`, `b`, `acc`
(8) and its preprocessed root (8) — 42 values.
-/
import StarkedAir.Circuit.EpochRoot

namespace StarkedAir.Circuit.EpochJoin

open StarkedAir StarkedAir.Circuit Q

/-- External values per child. -/
def EXT : ℕ := 42

/-- A child's opened fields and its circuit hash registers. `lo`, `hi` are base registers (the range),
`loW`, `hiW` their u32 words; `first` is a root's previous set or a join's start set, `last` a root's
final set or a join's end set; `tail` a root's `rest` or a join's `acc`. -/
structure Child where
  key : List ℕ
  first : List ℕ
  last : List ℕ
  lo : ℕ
  hi : ℕ
  tail : List ℕ
  out : List ℕ
  chash : List ℕ

/-- An epoch root child `i` (registers from `n`, external values from `EXT · i`): guessed opening, the
root's output digest recomputed (`EpochRoot`'s outer message: key, fin, prev when `prevV`, from, to,
rest), the verifier hook. A root from genesis has no previous set: `first` is then 8 zero words. -/
def rootChild (i n : ℕ) (prevV : Bool) : Out Child :=
  let e := EXT * i
  let key := guessHash n e
  let fin := guessHash key.next (e + 8)
  let prev := guessHash fin.next (e + 16)
  let b := prev.next
  let rest := guessHash (b + 4) (e + 26)
  let zeros := (List.range 8).map (rest.next + ·)
  let z := rest.next + 8
  let msg := key.res ++ fin.res ++ (if prevV then prev.res else []) ++ [b + 2, b + 3] ++ rest.res
  let out := blake2s z msg (4 * msg.length)
  let root := guessHash out.next (e + 34)
  let ch := (List.range 8).map (root.next + ·)
  ⟨key.ops ++ fin.ops ++ (if prevV then prev.ops else []) ++
    [.guessM31 b (.ext (e + 24)), .guessM31 (b + 1) (.ext (e + 25)), .m2u (b + 2) b, .m2u (b + 3) (b + 1)] ++ rest.ops ++
    (if prevV then [] else (List.range 8).map (fun w => constU32 (rest.next + w) 0)) ++ out.ops ++ root.ops ++
    [.hook i (root.res ++ out.res) ch],
   ⟨key.res, if prevV then prev.res else zeros, fin.res, b, b + 1, rest.res, out.res, ch⟩, root.next + 8⟩

/-- A join child `i`: guessed opening (key, start, end, a, b, acc), its output digest recomputed (this
program's message), the verifier hook. -/
def joinChild (i n : ℕ) : Out Child :=
  let e := EXT * i
  let key := guessHash n e
  let st := guessHash key.next (e + 8)
  let en := guessHash st.next (e + 16)
  let b := en.next
  let acc := guessHash (b + 4) (e + 26)
  let msg := key.res ++ st.res ++ en.res ++ [b + 2, b + 3] ++ acc.res
  let out := blake2s acc.next msg (4 * msg.length)
  let root := guessHash out.next (e + 34)
  let ch := (List.range 8).map (root.next + ·)
  ⟨key.ops ++ st.ops ++ en.ops ++
    [.guessM31 b (.ext (e + 24)), .guessM31 (b + 1) (.ext (e + 25)), .m2u (b + 2) b, .m2u (b + 3) (b + 1)] ++ acc.ops ++
    out.ops ++ root.ops ++ [.hook i (root.res ++ out.res) ch],
   ⟨key.res, st.res, en.res, b, b + 1, acc.res, out.res, ch⟩, root.next + 8⟩

/-- Which join: the first (two epoch roots; the left one from a previous set or from genesis) or a step
(a join, then an epoch root). -/
inductive Variant where
  | base (leftPrev : Bool)
  | step

def Variant.tag : Variant → String
  | .base true => "base_prev"
  | .base false => "base_genesis"
  | .step => "step"

/-- **The epoch join program.** Results: the output digest's 8 words. -/
def epochJoin (v : Variant) : Program :=
  let L := match v with
    | .base lp => rootChild 0 0 lp
    | .step => joinChild 0 0
  let R := rootChild 1 L.next true
  let l := L.res
  let r := R.res
  let n := R.next
  -- The links: the right's previous set is the left's end set; the right starts at the left's end + 1;
  -- the output range below 2^30.
  let links := (List.range 8).map (fun w => Op.eq (r.first.getD w 0) (l.last.getD w 0)) ++
    [ONE n, .add (n + 1) l.hi n, .eq r.lo (n + 1)] ++ BlockNode.lt30 (n + 2) r.hi
  -- The range's words at `n + 11`, `n + 12` (lt30 uses `n + 2 … n + 10`), then acc from `n + 13`.
  let ab : List Op := [.m2u (n + 11) l.lo, .m2u (n + 12) r.hi]
  -- acc: base Blake2s(out_left ‖ out_right); step Blake2s(acc_left ‖ out_right).
  let accIn := (match v with | .base _ => l.out | .step => l.tail) ++ r.out
  let acc := blake2s (n + 13) accIn 64
  let key := blake2s acc.next (l.chash ++ l.key ++ r.chash ++ r.key) 128
  let msg := key.res ++ l.first ++ r.last ++ [n + 11, n + 12] ++ acc.res
  let dg := blake2s key.next msg (4 * msg.length)
  ⟨s!"epoch_join_{v.tag}", L.ops ++ R.ops ++ links ++ ab ++ acc.ops ++ key.ops ++ dg.ops, dg.res⟩

def epochJoinJson (v : Variant) : String := (epochJoin v).toJson

end StarkedAir.Circuit.EpochJoin
