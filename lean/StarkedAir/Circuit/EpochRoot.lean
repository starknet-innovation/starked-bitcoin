/-
**The epoch root (BLOCK-REC), Lean-first.** One circuit over an epoch's `M` aligned subtrees
(docs/design/block-rec.md § The epoch root): it verifies the `M` node-shaped child proofs (hooks, as
`blockNodeK`), and checks in-circuit what `block_tree.verifyForest` checks natively, but for the block
hashes against the chain's `T`:

1. the ranges: child 0 starts at `from`, each child starts where the previous one ends, the last ends
   at `to` (`from` and `to + 1` below `2^30`);
2. one challenge: every child's limbs 7–18 equal child 0's;
3. the sums: the partial sums (QM31) and the input counts, each running count below `2^30`;
4. each child's count is `2^k` (a one-hot over `k < 31`, read from the count by `isEq` hints);
5. the seed (`epoch.seedOfRoots`): Blake2s over the tag, `from`, `to`, the previous set's digest (the
   `prev` variant), the final set's, then per child its start, `k` and its seed root (limbs 35–50);
6. the challenge (`epoch.challenge`): `Blake2s(seed ‖ ctr)` for ctr = 0, 1; of each of the first 12
   words, its low 31 bits (the top bit split off: `hi = h + 2^15·t`, `t` boolean, `2h < 2^16`), which
   must not be `2^31 − 1` (a rejection makes the prover fail); they equal child 0's limbs 7–18.

The output digest is Blake2s over the key (the children's circuit hashes and keys), the final and
(`prev`) previous set digests, then `from`, `to`, the summed partial sum, the summed input count and
each child's block-hash root limbs (19–34), each through `m31_to_u32`.

External values: per child its 51 summary limbs, key and preprocessed root (`EXT_B` each, as the
node); then `from`, `to`, the final set's digest (8 words) and the previous one's (8 words, read only
by the `prev` variant).
-/
import StarkedAir.Circuit.BlockNodeK

namespace StarkedAir.Circuit.EpochRoot

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Circuit.BlockNode (LO NN SS NIN CH HR SR NSUM EXT_B lt30)
open StarkedAir.Circuit.BlockNodeK (kid kidsOps kidsNext keyMsg)

/-- The seed's tag, `"starked-bitcoin M3b epoch v3"` (28 bytes), as 7 little-endian words. -/
def TAG : List ℕ :=
  let s := "starked-bitcoin M3b epoch v3".toList.map Char.toNat
  (List.range 7).map fun w => s.getD (4 * w) 0 + 256 * s.getD (4 * w + 1) 0 + 65536 * s.getD (4 * w + 2) 0 + 16777216 * s.getD (4 * w + 3) 0

/-- The first external value after the children's. -/
def EB (M : ℕ) : ℕ := EXT_B * M

/-- The epoch's inputs: `from`, `to` (guessed M31), the final and previous set digests (u32 words). -/
structure Inputs where
  lo : ℕ
  hi : ℕ
  fin : List ℕ
  prev : List ℕ

def inputs (M n : ℕ) : Out Inputs :=
  let e := EB M
  let fin := guessHash (n + 2) (e + 2)
  let prev := guessHash fin.next (e + 10)
  ⟨[.guessM31 n (.ext e), .guessM31 (n + 1) (.ext (e + 1))] ++ fin.ops ++ prev.ops, ⟨n, n + 1, fin.res, prev.res⟩, prev.next⟩

/-- The links: child 0 starts at `lo`, child `i + 1` where child `i` ends, the last ends at `hi + 1`;
`lo` and `hi + 1` below `2^30`. Registers `n …`. -/
def links (M : ℕ) (p : ℕ → ℕ → ℕ) (lo hi n : ℕ) : Out Unit :=
  let ends := (List.range M).map fun i => Op.add (n + i) (p i LO) (p i NN)
  let chain := (List.range (M - 1)).map fun i => Op.eq (p (i + 1) LO) (n + i)
  let m := n + M
  ⟨[.eq (p 0 LO) lo] ++ ends ++ chain ++ [ONE m, .add (m + 1) hi m, .eq (n + M - 1) (m + 1)] ++
    lt30 (m + 2) lo ++ lt30 (m + 11) (m + 1), (), m + 20⟩

/-- One challenge: child `i`'s limbs 7–18 equal child 0's. -/
def sameChallenge (M : ℕ) (p : ℕ → ℕ → ℕ) : List Op :=
  (List.range (M - 1)).flatMap fun i => (List.range 12).map fun j => Op.eq (p (i + 1) (CH + j)) (p 0 (CH + j))

/-- The running sums from register `n`: after child `i`, `s` at `n + 14 i …` (4 limbs) and `nin` at
`n + 14 i + 4`, below `2^30` (`lt30`, 9 more registers). Child 0's are its own limbs. -/
def sumReg (p : ℕ → ℕ → ℕ) (n i j : ℕ) : ℕ := if i = 0 then p 0 (SS + j) else n + 14 * (i - 1) + j

def sums (M : ℕ) (p : ℕ → ℕ → ℕ) (n : ℕ) : Out (List ℕ) :=
  let step := fun i =>
    let b := n + 14 * i
    (List.range 5).map (fun j => Op.add (b + j) (sumReg p n i j) (p (i + 1) (SS + j))) ++ lt30 (b + 5) (b + 4)
  let first := lt30 (n + 14 * (M - 1)) (p 0 NIN)
  ⟨first ++ (List.range (M - 1)).flatMap step, (List.range 5).map (sumReg p n (M - 1)), n + 14 * (M - 1) + 9⟩

/-- Child `i`'s count is `2^k`: `b_j = [count = 2^j]` (hints), each boolean, `Σ b_j = 1`,
`Σ b_j 2^j = count`; the result is `k = Σ b_j j`. Registers `n … n + 4·31 + 6·31 + 4`. -/
def LOGS : ℕ := 31

def logOf (cnt n : ℕ) : Out ℕ :=
  let bs := (List.range LOGS).map fun j => n + j
  let bools := (List.range LOGS).flatMap fun j =>
    let r := n + LOGS + 3 * j
    [Op.guessM31 (n + j) (.isEq (.reg cnt) (2 ^ j)), ONE r, .sub (r + 1) (n + j) r, .mul (r + 2) (n + j) (r + 1)]
  let z := n + 4 * LOGS
  let zeroEqs := (List.range LOGS).map fun j => Op.eq (n + LOGS + 3 * j + 2) z
  -- Weighted sums: Σ b_j, Σ b_j 2^j, Σ b_j j, accumulated from registers `w …`.
  let w := z + 1
  let terms := (List.range LOGS).flatMap fun j =>
    let r := w + 6 * j
    [Op.const r (2 ^ j % 2147483647) 0 0 0, .mul (r + 1) (bs.getD j 0) r, Op.const (r + 2) j 0 0 0, .mul (r + 3) (bs.getD j 0) (r + 2),
     .add (r + 4) (if j = 0 then bs.getD 0 0 else w + 6 * (j - 1) + 4) (if j = 0 then z else bs.getD j 0),
     .add (r + 5) (if j = 0 then r + 1 else w + 6 * (j - 1) + 5) (if j = 0 then z else r + 1)]
  let kacc := w + 6 * LOGS
  let kSum := (List.range LOGS).map fun j =>
    Op.add (kacc + j) (if j = 0 then z else kacc + j - 1) (w + 6 * j + 3)
  let e := kacc + LOGS
  ⟨bools ++ [.const z 0 0 0 0] ++ zeroEqs ++ terms ++ kSum ++
    [ONE e, .eq (w + 6 * (LOGS - 1) + 4) e, .eq (w + 6 * (LOGS - 1) + 5) cnt], kacc + LOGS - 1, e + 1⟩

/-- A child's seed root (limbs 35–50) as 8 u32 words: each limb `< 2^16`, word `= lo + hi·i`.
Registers `n … n + 32`; the constant `i` at `n`. -/
def packRoot (p : ℕ → ℕ) (base n : ℕ) : Out (List ℕ) :=
  let ops := (List.range 8).flatMap fun w =>
    let r := n + 1 + 4 * w
    range16 r (p (base + 2 * w)) ++ range16 (r + 1) (p (base + 2 * w + 1)) ++
      [.mul (r + 2) (p (base + 2 * w + 1)) n, .add (r + 3) (p (base + 2 * w)) (r + 2)]
  ⟨.const n 0 1 0 0 :: ops, (List.range 8).map (fun w => n + 1 + 4 * w + 3), n + 33⟩

/-- A challenge word's low 31 bits as a base value, not `2^31 − 1`: `hi = h + 2^15 t` (`t` boolean
from the `divC` hint, `2h < 2^16`), `w = lo + hi·i`, `v = lo + 2^16 h`. Not `2^31 − 1` (which is P,
so not a field test on `v`): `(65535 − lo) + 2^17 (32767 − h)` is invertible, and it is 0 mod P only
when both halves are 0 (its integer value is below 2^32 and never P or 2P). Registers `n … n + 26`;
the constant `i` at `ci`. Result: `v`. -/
def low31 (w ci n : ℕ) : Out ℕ :=
  ⟨[.guessU16 n (.coord 0 (.reg w)), .guessM31 (n + 1) (.divC (.coord 1 (.reg w)) 32768),
    ONE (n + 2), .sub (n + 3) (n + 1) (n + 2), .mul (n + 4) (n + 1) (n + 3), .const (n + 5) 0 0 0 0, .eq (n + 4) (n + 5),
    .const (n + 6) 32768 0 0 0, .mul (n + 7) (n + 1) (n + 6),
    .guessM31 (n + 8) (.divC (.coord 1 (.reg w)) 1), .sub (n + 9) (n + 8) (n + 7),
    .const (n + 10) 2 0 0 0, .mul (n + 11) (n + 9) (n + 10)] ++ range16 (n + 12) (n + 11) ++
   [.mul (n + 14) (n + 8) ci, .add (n + 15) n (n + 14), .eq w (n + 15),
    .const (n + 16) 65536 0 0 0, .mul (n + 17) (n + 9) (n + 16), .add (n + 18) n (n + 17),
    .const (n + 19) 65535 0 0 0, .sub (n + 20) (n + 19) n, .const (n + 21) 32767 0 0 0, .sub (n + 22) (n + 21) (n + 9),
    .const (n + 23) 131072 0 0 0, .mul (n + 24) (n + 22) (n + 23), .add (n + 25) (n + 20) (n + 24), .inv (n + 26) (n + 25)],
   n + 18, n + 27⟩

/-- The program's parts, in register order. -/
structure Parts where
  inp : Out Inputs
  lk : Out Unit
  sm : Out (List ℕ)
  logs : List (Out ℕ)
  roots : List (Out (List ℕ))
  seed : Out (List ℕ)
  ctrs : ℕ
  s0 : Out (List ℕ)
  s1 : Out (List ℕ)
  ci : ℕ
  vals : List (Out ℕ)
  key : Out (List ℕ)
  dg : Out (List ℕ)

/-- Registers after `j` items of a list of gadgets each starting where the previous ended. -/
def chainOuts {α : Type} (f : ℕ → ℕ → Out α) (n : ℕ) : ℕ → List (Out α)
  | 0 => []
  | k + 1 =>
    let prev := chainOuts f n k
    prev ++ [f k (match prev.getLast? with | some o => o.next | none => n)]

def lastNext {α : Type} (l : List (Out α)) (n : ℕ) : ℕ := match l.getLast? with | some o => o.next | none => n

def parts (M : ℕ) (prevV : Bool) : Parts :=
  let p : ℕ → ℕ → ℕ := fun i => (kid i).res.pubs
  let inp := inputs M (kidsNext M)
  let lk := links M p inp.res.lo inp.res.hi inp.next
  let sm := sums M p lk.next
  let logs := chainOuts (fun i n => logOf (p i NN) n) sm.next M
  let roots := chainOuts (fun i n => packRoot (p i) SR n) (lastNext logs sm.next) M
  let rn := lastNext roots (lastNext logs sm.next)
  -- The seed message: tag, from, to, (prev), fin, then per child its start, k, seed root.
  let tagR := (List.range 7).map (rn + ·)
  let m2 := rn + 7
  let perChild := (List.range M).flatMap fun i => [m2 + 2 + 2 * i, m2 + 3 + 2 * i] ++ (roots.getD i ⟨[], [], 0⟩).res
  let msg := tagR ++ [m2, m2 + 1] ++ (if prevV then inp.res.prev else []) ++ inp.res.fin ++ perChild
  let msgOps := (List.range 7).map (fun w => constU32 (rn + w) (TAG.getD w 0)) ++
    [.m2u m2 inp.res.lo, .m2u (m2 + 1) inp.res.hi] ++
    (List.range M).flatMap (fun i => [.m2u (m2 + 2 + 2 * i) (p i LO), .m2u (m2 + 3 + 2 * i) (logs.getD i ⟨[], 0, 0⟩).res])
  let seed := blake2s (m2 + 2 + 2 * M) msg (4 * msg.length)
  let seed' : Out (List ℕ) := ⟨msgOps ++ seed.ops, seed.res, seed.next⟩
  let ctrs := seed.next
  let s0 := blake2s (ctrs + 2) (seed.res ++ [ctrs]) 36
  let s1 := blake2s s0.next (seed.res ++ [ctrs + 1]) 36
  let ci := s1.next
  let words := s0.res ++ s1.res
  let vals := chainOuts (fun j n => low31 (words.getD j 0) ci n) (ci + 1) 12
  let vn := lastNext vals (ci + 1)
  let key := blake2s vn (keyMsg M) (64 * M)
  -- The output digest.
  let pubs := [inp.res.lo, inp.res.hi] ++ sm.res ++ (List.range M).flatMap (fun i => (List.range 16).map fun k => p i (HR + k))
  let dn := key.next
  let words := key.res ++ inp.res.fin ++ (if prevV then inp.res.prev else []) ++ (List.range pubs.length).map (dn + ·)
  let h := blake2s (dn + pubs.length) words (4 * words.length)
  let dg : Out (List ℕ) := ⟨(List.range pubs.length).map (fun j => .m2u (dn + j) (pubs.getD j 0)) ++ h.ops, h.res, h.next⟩
  ⟨inp, lk, sm, logs, roots, seed', ctrs, s0, s1, ci, vals, key, dg⟩

/-- **The epoch root program** over `M` children (`prevV`: the epoch starts from a previous set).
Results: the output digest's 8 words. -/
def epochRoot (M : ℕ) (prevV : Bool) : Program :=
  let P := parts M prevV
  let p : ℕ → ℕ → ℕ := fun i => (kid i).res.pubs
  let chEq := (List.range 12).map fun j => Op.eq ((P.vals.getD j ⟨[], 0, 0⟩).res) (p 0 (CH + j))
  ⟨s!"epoch_root_{M}{if prevV then "_prev" else ""}",
    kidsOps M ++ P.inp.ops ++ P.lk.ops ++ sameChallenge M p ++ P.sm.ops ++ (P.logs.flatMap (·.ops)) ++
      (P.roots.flatMap (·.ops)) ++ P.seed.ops ++ [constU32 P.ctrs 0, constU32 (P.ctrs + 1) 1] ++ P.s0.ops ++ P.s1.ops ++
      [.const P.ci 0 1 0 0] ++ (P.vals.flatMap (·.ops)) ++ chEq ++ P.key.ops ++ P.dg.ops,
    P.dg.res⟩

def epochRootJson (M : ℕ) (prevV : Bool) : String := (epochRoot M prevV).toJson

end StarkedAir.Circuit.EpochRoot
