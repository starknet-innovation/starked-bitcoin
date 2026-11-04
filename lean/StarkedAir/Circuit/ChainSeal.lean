/-
**The chain seal (SEAL), Lean-first.** One circuit over a chain of epochs and its coin sets
(docs/design/chain-seal.md): the last join and the set-pass roots are verified in-circuit, and what
`verify-chain --set-proofs` checked natively on their public values is checked here instead: the joins'
`acc` opened epoch by epoch, each epoch root's `rest` opened to its sum, input count, challenge and
block-hash roots, each set root's summary opened to the pass's start and final state vectors, the
balance of every epoch under its challenge, the set digests linked (a pass's final Blake2s state
finishes to the digest the epoch root bound), the counts and heights in range.

Children (hooks): hook 0 the join (`EpochJoin.joinChild`), hooks `1 … S` the set roots (`setChild`:
a summary of 48 limbs, as `SetTree.schild`). `S = 2n − 1` when the first epoch starts from genesis
(no start set), `2n` otherwise; set child `2i − g` is epoch `i`'s start set, `2i + 1 − g` its end set
(`g = 1` from genesis).

The output digest's message: the key (Blake2s over every child's circuit hash and key), `a`, `b`
(the chain's range), the start set digest, the end set digest, `acc`, the end set's count, amount
(3 words), highest coin height and Merkle root, then the Blake2s digests of the end set's and the start
set's SHA-256 states (`shaDigest`; the verifier finishes them natively to Core's `hash_serialized`; a
chain from genesis has zero words for the start set's).

External values: the join's opening (42, as `EpochJoin.EXT`); per set child its 48 summary limbs, key
and preprocessed root (64); per epoch its root opening (key, fin, prev, from, to, rest: 34) and its
`rest` preimage (`s` 4, `nin`, the challenge 12, each child's block-hash root 16: `17 + 16 m`); per set
child its final state (`i`, last key 36, highest height, sum 4, amount 12, Blake2s state 82, SHA-256
state 82) and the file's count bytes 4 (222).
-/
import StarkedAir.Circuit.EpochJoin
import StarkedAir.Circuit.SetTree

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Circuit.EpochJoin (Child joinChild)
open StarkedAir.Circuit.EpochRoot (restOut chainOuts lastNext)
open StarkedAir.Circuit.BlockNode (lt30)

/-! ### Layout -/

/-- The join opening's external values (`EpochJoin.EXT`). -/
def JEXT : ℕ := 42
/-- A set root's: 48 summary limbs, key, preprocessed root (`SetTree.EXT`). -/
def SEXT : ℕ := 64
/-- The summary limbs (`SetTree.NS`). -/
def NS : ℕ := SetTree.NS
/-- A set's final state and count bytes. -/
def NST : ℕ := 222
/-- An epoch's root opening (34) and `rest` preimage (`17 + 16 m`). -/
def rootExt (m : ℕ) : ℕ := 51 + 16 * m

/-- The set children of `n` epochs: two per epoch, one for a first epoch from genesis. -/
def nSets (n : ℕ) (gen : Bool) : ℕ := 2 * n - (if gen then 1 else 0)

/-- Epoch `i`'s start set child (none for `i = 0` from genesis) and end set child. -/
def startIdx (gen : Bool) (i : ℕ) : ℕ := 2 * i - (if gen then 1 else 0)
def endIdx (gen : Bool) (i : ℕ) : ℕ := 2 * i + 1 - (if gen then 1 else 0)
/-- Whether epoch `i` has a start set. -/
def hasStart (gen : Bool) (i : ℕ) : Bool := i ≠ 0 || !gen

/-- Where epoch `i`'s external values start. -/
def eRoot (ms : List ℕ) (gen : Bool) (i : ℕ) : ℕ :=
  JEXT + SEXT * nSets ms.length gen + ((ms.take i).map rootExt).sum
/-- Where set child `j`'s final state starts. -/
def eState (ms : List ℕ) (gen : Bool) (j : ℕ) : ℕ := eRoot ms gen ms.length + NST * j

/-! ### Children -/

/-- A set root child (hook `hook`, external values from `e`): 48 guessed summary limbs, key, the
digest `pubsDigest(key, limbs)`, preprocessed root, the verifier hook (`SetTree.schild`). -/
def setChild (n e hook : ℕ) : Out ChildRegs :=
  let pubsOps := (List.range NS).map (fun k => Op.guessM31 (n + k) (.ext (e + k)))
  let key := guessHash (n + NS) (e + NS)
  let dg := pubsDigest key.next key.res ((List.range NS).map (n + ·))
  let root := guessHash dg.next (e + NS + 8)
  let ch := (List.range 8).map (root.next + ·)
  ⟨pubsOps ++ key.ops ++ dg.ops ++ root.ops ++ [.hook hook (root.res ++ dg.res) ch],
   ⟨(n + ·), key.res, dg.res, ch⟩, root.next + 8⟩

/-- An epoch root's opening, no hook (as `EpochJoin.rootChild` reads it): `key ‖ fin ‖ prev (prevV) ‖
from ‖ to ‖ rest`, its output digest recomputed. A root from genesis has 8 zero words for `prev`. -/
structure RootRegs where
  key : List ℕ
  fin : List ℕ
  prev : List ℕ
  lo : ℕ
  hi : ℕ
  rest : List ℕ
  out : List ℕ

def rootOpen (n e : ℕ) (prevV : Bool) : Out RootRegs :=
  let key := guessHash n e
  let fin := guessHash key.next (e + 8)
  let prev := guessHash fin.next (e + 16)
  let b := prev.next
  let rest := guessHash (b + 4) (e + 26)
  let zeros := (List.range 8).map (rest.next + ·)
  let z := rest.next + 8
  let msg := key.res ++ fin.res ++ (if prevV then prev.res else []) ++ [b + 2, b + 3] ++ rest.res
  let out := blake2s z msg (4 * msg.length)
  ⟨key.ops ++ fin.ops ++ (if prevV then prev.ops else []) ++
    [.guessM31 b (.ext (e + 24)), .guessM31 (b + 1) (.ext (e + 25)), .m2u (b + 2) b, .m2u (b + 3) (b + 1)] ++ rest.ops ++
    (if prevV then [] else (List.range 8).map (fun w => constU32 (rest.next + w) 0)) ++ out.ops,
   ⟨key.res, fin.res, if prevV then prev.res else zeros, b, b + 1, rest.res, out.res⟩, out.next⟩

/-- An epoch root's `rest` opened: `s` (4 limbs), `nin`, the challenge `(γ, z, α)` (12 limbs), each of
the `m` children's block-hash root (16 limbs); `restOut` over them (each through `m31_to_u32`, then
Blake2s) must equal `rest`. -/
structure RestRegs where
  s : List ℕ
  nin : ℕ
  ch : List ℕ
  hr : List ℕ

def restOpen (n e m : ℕ) (rest : List ℕ) : Out RestRegs :=
  let k := 17 + 16 * m
  let guesses := (List.range k).map fun j => Op.guessM31 (n + j) (.ext (e + j))
  let r := restOut ((List.range k).map (n + ·)) (n + k)
  ⟨guesses ++ r.ops ++ (List.range 8).map (fun w => Op.eq (r.res.getD w 0) (rest.getD w 0)),
   ⟨(List.range 4).map (n + ·), n + 4, (List.range 12).map (n + 5 + ·), (List.range (16 * m)).map (n + 17 + ·)⟩,
   r.next⟩

/-! ### Constants -/

/-- The constants every set opening uses, by register. -/
structure Consts where
  zero : ℕ
  one : ℕ
  e1 : ℕ
  e2 : ℕ
  e3 : ℕ
  c64 : ℕ
  c256 : ℕ
  c1024 : ℕ
  c4096 : ℕ
  c65536 : ℕ
  c16M : ℕ
  four : ℕ
  /-- `k` for `k < 65` (the pending-length one-hot). -/
  small : ℕ → ℕ
  /-- Blake2s's `h0` (the IV with the parameter block), 16-bit halves. -/
  b2iv : List ℕ
  /-- SHA-256's IV, 16-bit halves. -/
  shaiv : List ℕ

/-- The 16-bit halves of a word. -/
def halves (w : ℕ) : List ℕ := [w % 65536, w / 65536]

def b2ivWords : List ℕ := (List.range 8).map fun i =>
  if i = 0 then Nat.xor (Spec.Blake2s.IVn.getD 0 0) 0x01010020 else Spec.Blake2s.IVn.getD i 0
def shaIvWords : List ℕ := (List.range 8).map fun i => (Spec.Bitcoin.stateWord Spec.Sha256.IV i).toNat

/-- Registers `n … n + 12 + 65 + 32`. -/
def consts (n : ℕ) : Out Consts :=
  let sm := n + 12
  let b2 := sm + 65
  let sha := b2 + 16
  let fixed := [Op.const n 0 0 0 0, .const (n + 1) 1 0 0 0, .const (n + 2) 0 1 0 0, .const (n + 3) 0 0 1 0,
    .const (n + 4) 0 0 0 1, .const (n + 5) 64 0 0 0, .const (n + 6) 256 0 0 0, .const (n + 7) 1024 0 0 0,
    .const (n + 8) 4096 0 0 0, .const (n + 9) 65536 0 0 0, .const (n + 10) 16777216 0 0 0, .const (n + 11) 4 0 0 0]
  let smalls := (List.range 65).map fun k => Op.const (sm + k) k 0 0 0
  let b2c := (List.range 16).map fun j => Op.const (b2 + j) ((b2ivWords.flatMap halves).getD j 0) 0 0 0
  let shac := (List.range 16).map fun j => Op.const (sha + j) ((shaIvWords.flatMap halves).getD j 0) 0 0 0
  ⟨fixed ++ smalls ++ b2c ++ shac,
   ⟨n, n + 1, n + 2, n + 3, n + 4, n + 5, n + 6, n + 7, n + 8, n + 9, n + 10, n + 11, (sm + ·),
    (List.range 16).map (b2 + ·), (List.range 16).map (sha + ·)⟩, sha + 16⟩

/-! ### Small gadgets -/

/-- `x < 256` for a u16 `x`: `256 x` is a u16. Registers `n`, `n + 1`. -/
def byteOps (n x c256 : ℕ) : List Op :=
  [.mul n x c256, .guessU16 (n + 1) (.coord 0 (.reg n)), .eq (n + 1) n]

/-- Every `x` in `xs` is a byte (two registers each). -/
def bytes (n c256 : ℕ) (xs : List ℕ) : Out Unit :=
  ⟨(List.range xs.length).flatMap (fun k => byteOps (n + 2 * k) (xs.getD k 0) c256), (), n + 2 * xs.length⟩

/-- `x < 2^k` for a u16 `x` and `k ≤ 16`, by `2^(16−k) x` a u16: `c` holds `2^(16−k)`. -/
def below (n x c : ℕ) : List Op := byteOps n x c

/-- A QM31 register from four base limbs: `l0 + l1·e1 + l2·e2 + l3·e3`. Registers `n … n + 5`. -/
def qm (n : ℕ) (l : List ℕ) (C : Consts) : Out ℕ :=
  ⟨[.mul n (l.getD 1 0) C.e1, .mul (n + 1) (l.getD 2 0) C.e2, .mul (n + 2) (l.getD 3 0) C.e3,
    .add (n + 3) (l.getD 0 0) n, .add (n + 4) (n + 3) (n + 1), .add (n + 5) (n + 4) (n + 2)], n + 5, n + 6⟩

/-- The four coordinates of a QM31 register as base registers (`coord` hints), recombined to it.
Registers `n … n + 9`. -/
def coords (n x : ℕ) (C : Consts) : Out (List ℕ) :=
  ⟨(List.range 4).map (fun j => Op.guessM31 (n + j) (.coord j (.reg x))) ++
    [.mul (n + 4) (n + 1) C.e1, .mul (n + 5) (n + 2) C.e2, .mul (n + 6) (n + 3) C.e3,
     .add (n + 7) n (n + 4), .add (n + 8) (n + 7) (n + 5), .add (n + 9) (n + 8) (n + 6), .eq (n + 9) x],
   (List.range 4).map (n + ·), n + 10⟩

/-- The 112 challenge limbs of a set's state vector from an epoch's 12 (`γ`, `z`, `α`): `γ`, `z`, then
the coordinates of `α^0 … α^25`. `α` at `n … n + 5`, the powers at `n + 6 … n + 31` (`α^0 = 1`), the
coordinates from `n + 32`. -/
def chal (n : ℕ) (ch : List ℕ) (C : Consts) : Out (List ℕ) :=
  let al := qm n (ch.drop 8) C
  let p := n + 6
  let pw : ℕ → ℕ := fun w => p + w
  let pows := ONE p :: (List.range 25).map (fun w => Op.mul (pw (w + 1)) (pw w) al.res)
  let cs := (List.range 26).map fun w => coords (n + 32 + 10 * w) (pw w) C
  ⟨al.ops ++ pows ++ cs.flatMap (·.ops), ch.take 8 ++ (List.range 104).map (fun i => n + 32 + 10 * (i / 4) + i % 4), n + 292⟩

/-- The count from its four bytes, below `2^30` (`c3 < 64`): registers `n … n + 7`, the count at `n + 5`. -/
def count (n : ℕ) (cnt : List ℕ) (C : Consts) : Out ℕ :=
  ⟨[.mul n (cnt.getD 1 0) C.c256, .add (n + 1) (cnt.getD 0 0) n, .mul (n + 2) (cnt.getD 2 0) C.c65536,
    .add (n + 3) (n + 1) (n + 2), .mul (n + 4) (cnt.getD 3 0) C.c16M, .add (n + 5) (n + 3) (n + 4)] ++
    below (n + 6) (cnt.getD 3 0) C.c1024, n + 5, n + 8⟩

/-- Eight words packed from 16 limbs (`lo + hi·e1`), each equal to `words`. Registers `n … n + 15`. -/
def packEq (n : ℕ) (limbs : ℕ → ℕ) (words : List ℕ) (C : Consts) : List Op :=
  (List.range 8).flatMap fun w =>
    [.mul (n + 2 * w) (limbs (2 * w + 1)) C.e1, .add (n + 2 * w + 1) (limbs (2 * w)) (n + 2 * w),
     .eq (n + 2 * w + 1) (words.getD w 0)]

/-- Eight words packed from 16 limbs. Registers `n … n + 15`; results `n + 2w + 1`. -/
def packW (n : ℕ) (limbs : List ℕ) (C : Consts) : Out (List ℕ) :=
  ⟨(List.range 8).flatMap (fun w =>
    [.mul (n + 2 * w) (limbs.getD (2 * w + 1) 0) C.e1, .add (n + 2 * w + 1) (limbs.getD (2 * w) 0) (n + 2 * w)]),
   (List.range 8).map (fun w => n + 2 * w + 1), n + 16⟩

/-- `nw` words from `4 nw` bytes: `b0 + 256 b1 + (b2 + 256 b3)·e1`. Registers `n + 6w …`; results
`n + 6w + 5`. -/
def packBytes (n : ℕ) (bs : List ℕ) (nw : ℕ) (C : Consts) : Out (List ℕ) :=
  ⟨(List.range nw).flatMap (fun w =>
    let r := n + 6 * w
    [.mul r (bs.getD (4 * w + 1) 0) C.c256, .add (r + 1) (bs.getD (4 * w) 0) r,
     .mul (r + 2) (bs.getD (4 * w + 3) 0) C.c256, .add (r + 3) (bs.getD (4 * w + 2) 0) (r + 2),
     .mul (r + 4) (r + 3) C.e1, .add (r + 5) (r + 1) (r + 4)]),
   (List.range nw).map (fun w => n + 6 * w + 5), n + 6 * nw⟩

/-- A one-hot of `x` over `0 … 64` (`isEq` hints): each bit boolean, one bit set, `Σ k b_k = x`.
Registers: bits `n … n + 64`, then 2 per bit (boolean), 65 (`Σ b`), 130 (`Σ k b`). -/
def oneHot65 (n x : ℕ) (C : Consts) : Out (List ℕ) :=
  let bits := (List.range 65).map (n + ·)
  let b : ℕ → ℕ := fun k => n + k
  let bo := n + 65
  let bools := (List.range 65).flatMap fun k =>
    [Op.guessM31 (b k) (.isEq (.reg x) k), .sub (bo + 2 * k) (b k) C.one, .mul (bo + 2 * k + 1) (b k) (bo + 2 * k),
     .eq (bo + 2 * k + 1) C.zero]
  let s := bo + 130
  let sums := (List.range 65).map fun k => Op.add (s + k) (if k = 0 then C.zero else s + k - 1) (b k)
  let w := s + 65
  let wsum := (List.range 65).flatMap fun k =>
    [Op.mul (w + 2 * k) (b k) (C.small k), .add (w + 2 * k + 1) (if k = 0 then C.zero else w + 2 * k - 1) (w + 2 * k)]
  ⟨bools ++ sums ++ wsum ++ [.eq (s + 64) C.one, .eq (w + 129) x], bits, w + 130⟩

/-- `lt_j = [j < plen]` for `j < 64` from the one-hot `bits` of `plen`: suffix sums. Registers
`n … n + 63`; `lt_j` at `n + j`. -/
def ltMask (n : ℕ) (bits : List ℕ) (C : Consts) : Out (List ℕ) :=
  ⟨(List.range 64).reverse.map (fun j =>
    Op.add (n + j) (if j = 63 then C.zero else n + j + 1) (bits.getD (j + 1) 0)),
   (List.range 64).map (n + ·), n + 64⟩

/-- Pending bytes masked past the pending length: `m_j = pend_j · lt_j`. Registers `n … n + 63`. -/
def mask (n : ℕ) (pend lt : List ℕ) : Out (List ℕ) :=
  ⟨(List.range 64).map (fun j => Op.mul (n + j) (pend.getD j 0) (lt.getD j 0)), (List.range 64).map (n + ·), n + 64⟩

/-- The final Blake2s counter `t = 64 nb + plen` as two u32 words `(t0, t1)` from `nb < 2^30` and
`plen ≤ 64`: `nb = 1024 q + r`, `64 r + plen = a + 2^16 c`, `q + c = b + 2^16 t1`; `t0 = a + b·e1`.
Every equation is below `2^22`, so exact in the field. Registers `n … n + 29`. -/
def counter (n nb plen : ℕ) (C : Consts) : Out (ℕ × ℕ) :=
  let r := n
  let q := n + 1
  ⟨[.guessU16 r (.modC (.reg nb) 1024), .guessM31 q (.divC (.reg nb) 1024)] ++
    below (n + 2) r C.c64 ++
    [.guessU16 (n + 4) (.modC (.reg q) 65536), .guessU16 (n + 5) (.divC (.reg q) 65536)] ++
    below (n + 6) (n + 5) C.c4096 ++
    [.mul (n + 8) (n + 5) C.c65536, .add (n + 9) (n + 4) (n + 8), .eq (n + 9) q,
     .mul (n + 10) q C.c1024, .add (n + 11) (n + 10) r, .eq (n + 11) nb,
     .mul (n + 12) r C.c64, .add (n + 13) (n + 12) plen,
     .guessU16 (n + 14) (.modC (.reg (n + 13)) 65536), .guessM31 (n + 15) (.divC (.reg (n + 13)) 65536),
     .sub (n + 16) (n + 15) C.one, .mul (n + 17) (n + 15) (n + 16), .eq (n + 17) C.zero,
     .mul (n + 18) (n + 15) C.c65536, .add (n + 19) (n + 14) (n + 18), .eq (n + 19) (n + 13),
     .add (n + 20) q (n + 15),
     .guessU16 (n + 21) (.modC (.reg (n + 20)) 65536), .guessU16 (n + 22) (.divC (.reg (n + 20)) 65536)] ++
    below (n + 23) (n + 22) C.c4096 ++
    [.mul (n + 25) (n + 22) C.c65536, .add (n + 26) (n + 21) (n + 25), .eq (n + 26) (n + 20),
     .mul (n + 27) (n + 21) C.e1, .add (n + 28) (n + 14) (n + 27)],
   (n + 28, n + 22), n + 29⟩

/-- **One final Blake2s compression** from chaining words `h` (8 u32 registers), message words `m`
(16), counter words `t0`, `t1`: `v[8..16]` are `IV0 … IV3`, `IV4 ⊕ t0`, `IV5 ⊕ t1`, `IV6 ⊕ 0xFFFFFFFF`,
`IV7`; 80 G gates; the xors with `h`. Registers `n … n + 338`: the zero word at `n`, `IV4`, `IV5` at
`n + 1`, `n + 2`, `v[8..16]` at `n + 3 …`, the G outputs from `n + 11`, the results at `n + 331 …`. -/
def compressFinal (n : ℕ) (h m : List ℕ) (t0 t1 : ℕ) : Out (List ℕ) :=
  let iv := Spec.Blake2s.IVn
  let base := n + 3
  let st0 : ℕ → ℕ := fun j => if j < 8 then h.getD j 0 else base + (j - 8)
  let g0 := n + 11
  let msg : ℕ → ℕ := fun j => m.getD j n
  ⟨[constU32 n 0, constU32 (n + 1) (iv.getD 4 0), constU32 (n + 2) (iv.getD 5 0),
    constU32 base (iv.getD 0 0), constU32 (base + 1) (iv.getD 1 0), constU32 (base + 2) (iv.getD 2 0),
    constU32 (base + 3) (iv.getD 3 0), .xor3 (base + 4) (n + 1) t0 n, .xor3 (base + 5) (n + 2) t1 n,
    constU32 (base + 6) (Nat.xor (iv.getD 6 0) 0xFFFFFFFF), constU32 (base + 7) (iv.getD 7 0)] ++
    (List.range 80).map (gOp st0 g0 msg) ++
    (List.range 8).map (fun i =>
      let st := gState st0 g0 80
      .xor3 (n + 331 + i) (h.getD i 0) (st i) (st (i + 8))),
   (List.range 8).map (n + 331 + ·), n + 339⟩

/-! ### A set's final state -/

/-- A set's final state registers (one per external value, in the layout's order). -/
structure StRegs where
  i : ℕ
  last : List ℕ
  maxh : ℕ
  sum : List ℕ
  amt : List ℕ
  b2 : List ℕ
  sha : List ℕ
  cnt : List ℕ

def StRegs.b2h (s : StRegs) : List ℕ := s.b2.take 16
def StRegs.nb (s : StRegs) : ℕ := s.b2.getD 16 0
def StRegs.plen (s : StRegs) : ℕ := s.b2.getD 17 0
def StRegs.pend (s : StRegs) : List ℕ := s.b2.drop 18

/-- The final state and count bytes guessed at `n … n + 221` (u16 where a byte or a hash limb). -/
def stateOpen (n e : ℕ) : Out StRegs :=
  let kind : ℕ → Bool := fun k => decide ((42 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 70) ∨ k = 71 ∨ (72 ≤ k ∧ k < 136) ∨
    (136 ≤ k ∧ k < 152) ∨ k = 153 ∨ (154 ≤ k ∧ k < 222))
  ⟨(List.range NST).map (fun k => if kind k then Op.guessU16 (n + k) (.ext (e + k)) else Op.guessM31 (n + k) (.ext (e + k))),
   ⟨n, (List.range 36).map (n + 1 + ·), n + 37, (List.range 4).map (n + 38 + ·), (List.range 12).map (n + 42 + ·),
    (List.range 82).map (n + 54 + ·), (List.range 82).map (n + 136 + ·), (List.range 4).map (n + 218 + ·)⟩,
   n + NST⟩

/-- The outgoing state vector's registers (`SetTree.outIdx`'s layout): the challenge, `i`, 1, the last
key, the height, the sum, the amount, the Blake2s and SHA-256 states. -/
def outVec (ch : List ℕ) (s : StRegs) (C : Consts) : List ℕ :=
  ch ++ [s.i, C.one] ++ s.last ++ [s.maxh] ++ s.sum ++ s.amt ++ s.b2 ++ s.sha

/-- The pass's start vector (`begin(count)` under the challenge): everything zero but the Blake2s
chaining value `h0`, its pending length 4 and pending bytes the count's, and SHA-256's IV. -/
def inVec (ch : List ℕ) (s : StRegs) (C : Consts) : List ℕ :=
  ch ++ [C.zero, C.zero] ++ List.replicate 36 C.zero ++ [C.zero] ++ List.replicate 4 C.zero ++
    List.replicate 12 C.zero ++ (C.b2iv ++ [C.zero, C.four] ++ s.cnt ++ List.replicate 60 C.zero) ++
    (C.shaiv ++ [C.zero, C.zero] ++ List.replicate 64 C.zero)

#guard (outVec (List.replicate 112 0) ⟨0, List.replicate 36 0, 0, List.replicate 4 0, List.replicate 12 0,
  List.replicate 82 0, List.replicate 82 0, List.replicate 4 0⟩ ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, id, [], []⟩).length = 331
#guard (inVec (List.replicate 112 0) ⟨0, List.replicate 36 0, 0, List.replicate 4 0, List.replicate 12 0,
  List.replicate 82 0, List.replicate 82 0, List.replicate 4 0⟩
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, id, List.replicate 16 0, List.replicate 16 0⟩).length = 331

/-- What a set opening gives back: the count register, the end facts' words (count, amount 3, height,
Merkle root 8), the SHA-256 state's digest. -/
structure SetRegs where
  st : StRegs
  n : ℕ
  cntW : ℕ
  amtW : List ℕ
  maxhW : ℕ
  mroot : List ℕ
  shaDg : List ℕ
  fin : List ℕ

/-- **A set root opened to its pass** (set child `c`, challenge limbs `ch`, final state at `e`): the
bytes checked; the count from its bytes equals `i`; the outgoing vector's digest is the summary's
second digest, the start vector's its first; the Blake2s state finishes (pending bytes masked past
`plen`, counter `64 nb + plen`) to `fin`; the Merkle root packed; the SHA-256 state digested. -/
def setOpen (n : ℕ) (c : ChildRegs) (ch : List ℕ) (e : ℕ) (C : Consts) : Out SetRegs :=
  let st := stateOpen n e
  let s := st.res
  let by1 := bytes st.next C.c256 (s.amt ++ s.cnt ++ s.pend)
  let cnt := count by1.next s.cnt C
  let dout := pubsDigest cnt.next [] (outVec ch s C)
  let eqOut := packEq dout.next (fun k => c.pubs (16 + k)) dout.res C
  let din := pubsDigest (dout.next + 16) [] (inVec ch s C)
  let eqIn := packEq din.next c.pubs din.res C
  let oh := oneHot65 (din.next + 16) s.plen C
  let lt := ltMask oh.next oh.res C
  let mk := mask lt.next s.pend lt.res
  let m := packBytes mk.next mk.res 16 C
  let h := packW m.next s.b2h C
  let ct := counter h.next s.nb s.plen C
  let fin := compressFinal ct.next h.res m.res ct.res.1 ct.res.2
  let mr := packW fin.next (((List.range 16).map fun k => c.pubs (32 + k))) C
  let sd := pubsDigest mr.next [] s.sha
  let aw := packBytes sd.next s.amt 3 C
  let cw := aw.next
  ⟨st.ops ++ by1.ops ++ cnt.ops ++ [.eq s.i cnt.res] ++ dout.ops ++ eqOut ++ din.ops ++ eqIn ++ oh.ops ++ lt.ops ++
    mk.ops ++ m.ops ++ h.ops ++ ct.ops ++ fin.ops ++ mr.ops ++ sd.ops ++ aw.ops ++ [.m2u cw cnt.res, .m2u (cw + 1) s.maxh],
   ⟨s, cnt.res, cw, aw.res, cw + 1, mr.res, sd.res, fin.res⟩, cw + 2⟩

/-! ### The program -/

/-- The epochs' parts, in register order. -/
structure Parts where
  J : Out Child
  sets : List (Out ChildRegs)
  roots : List (Out RootRegs)
  rests : List (Out RestRegs)
  C : Out Consts
  chals : List (Out (List ℕ))
  opens : List (Out SetRegs)
  accs : List (Out (List ℕ))
  checks : Out Unit
  key : Out (List ℕ)
  dg : Out (List ℕ)
  /-- The output message's registers. -/
  msg : List ℕ

/-- `acc` over the epoch roots' outputs `rout`: `Blake2s(out₀ ‖ out₁)`, then `Blake2s(acc ‖ outₖ₊₁)`;
`k` hashes from register `r`. -/
def accChain (rout : ℕ → List ℕ) (r : ℕ) : ℕ → List (Out (List ℕ))
  | 0 => []
  | k + 1 =>
    let prev := accChain rout r k
    let left := match prev.getLast? with | some o => o.res | none => rout 0
    prev ++ [blake2s (lastNext prev r) (left ++ rout (k + 1)) 64]

/-- The epoch of set child `j`. -/
def epochOf (gen : Bool) (j : ℕ) : ℕ := (j + (if gen then 1 else 0)) / 2

/-- The seal's checks after the openings: the digest links and ranges, the balance, the join's
opening against the epochs', `acc`. Registers from `n`. -/
def checksOps (ms : List ℕ) (gen : Bool) (J : Child) (roots : List RootRegs) (rests : List RestRegs)
    (opens : List SetRegs) (accs : List (List ℕ)) (C : Consts) (n : ℕ) : Out Unit :=
  let nE := ms.length
  let root : ℕ → RootRegs := fun i => (roots.getD i ⟨[], [], [], 0, 0, [], []⟩)
  let rest : ℕ → RestRegs := fun i => (rests.getD i ⟨[], 0, [], []⟩)
  let op : ℕ → SetRegs := fun j => (opens.getD j ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩)
  let eq8 : List ℕ → List ℕ → List Op := fun a b => (List.range 8).map fun w => Op.eq (a.getD w 0) (b.getD w 0)
  -- The join's opening is the epochs': range, start and end sets, `acc`.
  let joinEqs := [Op.eq J.lo (root 0).lo, .eq J.hi (root (nE - 1)).hi] ++ eq8 J.first (root 0).prev ++
    eq8 J.last (root (nE - 1)).fin ++ eq8 J.tail (accs.getD (nE - 2) [])
  -- The epochs link: consecutive heights, the end set is the next start set.
  let linkEqs := (List.range (nE - 1)).flatMap fun i =>
    [Op.add (n + i) (root i).hi C.one, .eq (n + i) (root (i + 1)).lo] ++ eq8 (root i).fin (root (i + 1)).prev
  -- A chain from genesis: the join's start set is zero words.
  let genEqs := if gen then (List.range 8).map (fun w => Op.eq (J.first.getD w 0) C.zero) else []
  -- Per epoch: its end set finishes to `fin`, its start set to `prev`; the balance; the ranges.
  let per := (List.range nE).map fun i =>
    let r := n + nE + 60 * i
    let E := op (endIdx gen i)
    let finE := eq8 E.fin (root i).fin
    if hasStart gen i then
      let B := op (startIdx gen i)
      finE ++ eq8 B.fin (root i).prev ++
        (List.range 4).flatMap (fun k => [Op.add (r + k) ((rest i).s.getD k 0) (B.st.sum.getD k 0), .eq (r + k) (E.st.sum.getD k 0)]) ++
        [.add (r + 4) (rest i).nin E.n, .add (r + 5) (r + 4) B.n] ++ lt30 (r + 6) (r + 5) ++
        [.sub (r + 17) (root i).lo B.st.maxh, .sub (r + 18) (r + 17) C.one] ++ lt30 (r + 19) (r + 18)
    else
      finE ++ (List.range 4).map (fun k => Op.eq ((rest i).s.getD k 0) (E.st.sum.getD k 0)) ++
        [.add (r + 4) (rest i).nin E.n] ++ lt30 (r + 6) (r + 4)
  ⟨joinEqs ++ linkEqs ++ genEqs ++ per.flatten, (), n + nE + 60 * nE⟩

def parts (ms : List ℕ) (gen : Bool) : Parts :=
  let nE := ms.length
  let S := nSets nE gen
  let J := joinChild 0 0
  let sets := chainOuts (fun j r => setChild r (JEXT + SEXT * j) (j + 1)) J.next S
  let r1 := lastNext sets J.next
  let roots := chainOuts (fun i r => rootOpen r (eRoot ms gen i) (hasStart gen i)) r1 nE
  let r2 := lastNext roots r1
  let rests := chainOuts (fun i r => restOpen r (eRoot ms gen i + 34) (ms.getD i 0) ((roots.getD i ⟨[], ⟨[], [], [], 0, 0, [], []⟩, 0⟩).res.rest)) r2 nE
  let r3 := lastNext rests r2
  let C := consts r3
  let chals := chainOuts (fun i r => chal r ((rests.getD i ⟨[], ⟨[], 0, [], []⟩, 0⟩).res.ch) C.res) C.next nE
  let r4 := lastNext chals C.next
  let opens := chainOuts (fun j r => setOpen r (sets.getD j ⟨[], ⟨id, [], [], []⟩, 0⟩).res
    ((chals.getD (epochOf gen j) ⟨[], [], 0⟩).res) (eState ms gen j) C.res) r4 S
  let r5 := lastNext opens r4
  -- `acc`: Blake2s(out₀ ‖ out₁), then Blake2s(acc ‖ outᵢ).
  let rout : ℕ → List ℕ := fun i => (roots.getD i ⟨[], ⟨[], [], [], 0, 0, [], []⟩, 0⟩).res.out
  let accs := accChain rout r5 (nE - 1)
  let r6 := lastNext accs r5
  let checks := checksOps ms gen J.res (roots.map (·.res)) (rests.map (·.res)) (opens.map (·.res)) (accs.map (·.res)) C.res r6
  let keyMsg := J.res.chash ++ J.res.key ++ sets.flatMap (fun c => c.res.chash ++ c.res.key)
  let key := blake2s checks.next keyMsg (4 * keyMsg.length)
  let E := (opens.getD (S - 1) ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩).res
  let shaStart := if gen then List.replicate 8 C.res.zero else
    (opens.getD 0 ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩).res.shaDg
  let ab := key.next
  let msg := key.res ++ [ab, ab + 1] ++ J.res.first ++ J.res.last ++ J.res.tail ++ [E.cntW] ++ E.amtW ++ [E.maxhW] ++
    E.mroot ++ E.shaDg ++ shaStart
  let dg := blake2s (ab + 2) msg (4 * msg.length)
  ⟨J, sets, roots, rests, C, chals, opens, accs, checks, key,
   ⟨[.m2u ab J.res.lo, .m2u (ab + 1) J.res.hi] ++ dg.ops, dg.res, dg.next⟩, msg⟩

def tag (ms : List ℕ) (gen : Bool) : String :=
  "_".intercalate (ms.map toString) ++ (if gen then "_genesis" else "")

/-- **The chain seal program** over epochs of `ms` children (the first from genesis when `gen`).
Results: the output digest's 8 words. -/
def chainSeal (ms : List ℕ) (gen : Bool) : Program :=
  let P := parts ms gen
  ⟨s!"chain_seal_{tag ms gen}",
   P.J.ops ++ P.sets.flatMap (·.ops) ++ P.roots.flatMap (·.ops) ++ P.rests.flatMap (·.ops) ++ P.C.ops ++
     P.chals.flatMap (·.ops) ++ P.opens.flatMap (·.ops) ++ P.accs.flatMap (·.ops) ++ P.checks.ops ++ P.key.ops ++ P.dg.ops,
   P.dg.res⟩

def chainSealJson (ms : List ℕ) (gen : Bool) : String := (chainSeal ms gen).toJson

end StarkedAir.Circuit.ChainSeal
