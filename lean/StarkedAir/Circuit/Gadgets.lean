/-
**Glue gadgets and programs.** Each gadget takes the next free register `n` and returns its ops,
its result registers and the next free register. Op order is exactly the order of the builder
calls in the Zig code it replaces (stwo-zig `blake.zig`, `wrappers.zig`; our `leaf.zig`,
`node.zig`), which the parity test checks through circuit hashes.
-/
import StarkedAir.Circuit.Ops

namespace StarkedAir.Circuit

open Spec.Blake2s (IVn SIGMA sigma gIdx)

/-- A gadget's output. -/
structure Out (α : Type) where
  ops : List Op
  res : α
  next : ℕ

/-- `guessU32`: two u16 guesses, the constant `i`, `lo + hi·i`. Value: `ext k` (a packed u32). -/
def guessU32 (n : ℕ) (h : Hint) : Out ℕ :=
  ⟨[.guessU16 n (.coord 0 h), .guessU16 (n + 1) (.coord 1 h), .const (n + 2) 0 1 0 0,
    .mul (n + 3) (n + 1) (n + 2), .add (n + 4) n (n + 3)], n + 4, n + 5⟩

/-- `guessHash`: eight `guessU32`s of `ext (e + w)`. Result registers: `n + 5w + 4`. -/
def guessHash (n e : ℕ) : Out (List ℕ) :=
  ⟨(List.range 8).flatMap (fun w => (guessU32 (n + 5 * w) (.ext (e + w))).ops),
    (List.range 8).map (fun w => n + 5 * w + 4), n + 40⟩

/-- The constant u32 wire of `w`. -/
def constU32 (o w : ℕ) : Op := .const o (w % 65536) (w / 65536) 0 0

/-! ### Blake2s (`blake2sU32s`) -/

/-- The 16 state registers after `k` G steps of a block whose G outputs start at `g0` and whose
initial state registers are `st0`. -/
def gState (st0 : ℕ → ℕ) (g0 : ℕ) : ℕ → ℕ → ℕ
  | 0 => st0
  | k + 1 => fun j =>
    let (ia, ib, ic, id) := gIdx (k % 8)
    if j = ia then g0 + 4 * k else if j = ib then g0 + 4 * k + 1
    else if j = ic then g0 + 4 * k + 2 else if j = id then g0 + 4 * k + 3 else gState st0 g0 k j

/-- The `k`-th G gate of a block (message registers `msg`). -/
def gOp (st0 : ℕ → ℕ) (g0 : ℕ) (msg : ℕ → ℕ) (k : ℕ) : Op :=
  let st := gState st0 g0 k
  let (ia, ib, ic, id) := gIdx (k % 8)
  .blakeG (g0 + 4 * k) (st ia) (st ib) (st ic) (st id) (msg (sigma (k / 8) (2 * (k % 8)))) (msg (sigma (k / 8) (2 * (k % 8) + 1)))

/-- The registers of block `b`: 8 constants, 80 G gates (4 outputs each), 8 xors. -/
def BLOCK : ℕ := 8 + 320 + 8

/-- `v[8 + i]`'s constant for block `b` of `nb` with byte counter `t`. -/
def ivWord (i t : ℕ) (last : Bool) : ℕ :=
  let iv := IVn.getD i 0
  if i = 4 then Nat.xor iv t else if i = 6 ∧ last then Nat.xor iv 0xFFFFFFFF else iv

/-- Chaining registers after `b` blocks (`hb 0` are the IV constants at `n + 1 …`). -/
def chain (n : ℕ) : ℕ → ℕ → ℕ
  | 0 => fun i => n + 1 + i
  | b + 1 => fun i => n + 9 + BLOCK * b + 328 + i

/-- Block `b`'s ops: the `v[8..16]` constants, 80 G gates, then the xors with the chaining value. -/
def blockOps (n : ℕ) (msg : ℕ → ℕ) (nBytes nb b : ℕ) : List Op :=
  let base := n + 9 + BLOCK * b
  let t := min nBytes (64 * (b + 1))
  let st0 : ℕ → ℕ := fun j => if j < 8 then chain n b j else base + (j - 8)
  let g0 := base + 8
  let m : ℕ → ℕ := fun j => msg (16 * b + j)
  (List.range 8).map (fun i => constU32 (base + i) (ivWord i t (b + 1 = nb))) ++
  (List.range 80).map (gOp st0 g0 m) ++
  (List.range 8).map (fun i =>
    let st := gState st0 g0 80
    .xor3 (base + 328 + i) (chain n b i) (st i) (st (i + 8)))

def nBlocks (nBytes : ℕ) : ℕ := max 1 ((nBytes + 63) / 64)

/-- **`blake2sU32s(message, n_bytes)`.** Message words beyond `msg.length` are the zero word. -/
def blake2s (n : ℕ) (msg : List ℕ) (nBytes : ℕ) : Out (List ℕ) :=
  let nb := nBlocks nBytes
  let m : ℕ → ℕ := fun j => msg.getD j n
  ⟨constU32 n 0 :: (List.range 8).map (fun i => constU32 (n + 1 + i) (if i = 0 then Nat.xor (IVn.getD 0 0) 0x01010020 else IVn.getD i 0)) ++
    (List.range nb).flatMap (blockOps n m nBytes nb),
   (List.range 8).map (chain n nb), n + 9 + BLOCK * nb⟩

/-! ### Public-input digest, range checks -/

/-- `pubsDigestVars(key, pubs)`: each public input through `m31_to_u32`, then Blake2s of
`key ‖ pubs` (4 bytes per word). -/
def pubsDigest (n : ℕ) (key pubs : List ℕ) : Out (List ℕ) :=
  let words := key ++ (List.range pubs.length).map (n + ·)
  let h := blake2s (n + pubs.length) words (4 * words.length)
  ⟨(List.range pubs.length).map (fun j => .m2u (n + j) (pubs.getD j 0)) ++ h.ops, h.res, h.next⟩

/-- `x < 2^16`: `m31_to_u32(x) = x`. -/
def range16 (n x : ℕ) : List Op := [.m2u n x, .eq n x]

/-! ### The node's link checks (`linkChecks`) -/

def ONE : ℕ → Op := fun o => .const o 1 0 0 0

/-- `PubLink pL pR`, constraint by constraint; `pl`, `pr` are the children's public-input
registers. Uses registers `n … n + 11`. -/
def linkChecks (n : ℕ) (pl pr : ℕ → ℕ) : Out Unit :=
  let eqs := (List.range 16).map (fun k => Op.eq (pr k) (pl (16 + k))) ++
    [(34, 40), (35, 41), (36, 42), (37, 43), (44, 46), (45, 47)].map (fun p => Op.eq (pr p.1) (pl p.2)) ++
    (List.range 20).map (fun k => Op.eq (pr (48 + k)) (pl (68 + k))) ++
    (List.range 10).map (fun l => Op.eq (pr (88 + l)) (pl (98 + l)))
  let c := n + 4
  ⟨eqs ++ range16 n (pr 32) ++ range16 (n + 1) (pr 33) ++ range16 (n + 2) (pl 38) ++ range16 (n + 3) (pl 39) ++
    [.guessM31 c (.isEq (.coord 0 (.reg (pl 38))) 0xffff),
     ONE (n + 5), .sub (n + 6) c (n + 5), .mul (n + 7) c (n + 6), .const (n + 8) 0 0 0 0, .eq (n + 7) (n + 8),
     .const (n + 9) 65536 0 0 0,
     .add (n + 10) (pl 38) (n + 5), .mul (n + 11) (n + 9) c, .sub (n + 12) (n + 10) (n + 11), .eq (pr 32) (n + 12),
     .add (n + 13) (pl 39) c, .eq (pr 33) (n + 13)],
   (), n + 14⟩

/-! ### The node's tree root (`treeNode`) -/

/-- Base of the root limbs in the public inputs. -/
def TB : ℕ := 108

/-- `node(T_L, T_R)` over the children's root limbs at `TB …`: range checks and packing per
word (`n + 4q …` for word `q < 16`), Blake2s, then each output word split into two guessed
u16 limbs that recombine to it. -/
def treeNode (n : ℕ) (pl pr : ℕ → ℕ) : Out (List ℕ) :=
  let iC := n
  let p : ℕ → ℕ → ℕ := fun c => if c = 0 then pl else pr
  let pack := (List.range 16).flatMap fun q =>
    let c := q / 8
    let w := q % 8
    let r := n + 1 + 4 * q
    range16 r (p c (TB + 2 * w)) ++ range16 (r + 1) (p c (TB + 2 * w + 1)) ++
      [.mul (r + 2) (p c (TB + 2 * w + 1)) iC, .add (r + 3) (p c (TB + 2 * w)) (r + 2)]
  let msg := (List.range 16).map (fun q => n + 1 + 4 * q + 3)
  let h := blake2s (n + 65) msg 64
  let s := h.next
  let split := (List.range 8).flatMap fun w =>
    let word := h.res.getD w 0
    let r := s + 4 * w
    [.guessU16 r (.coord 0 (.reg word)), .guessU16 (r + 1) (.coord 1 (.reg word)),
     .mul (r + 2) (r + 1) iC, .add (r + 3) r (r + 2), .eq (r + 3) word]
  ⟨.const iC 0 1 0 0 :: pack ++ h.ops ++ split,
   (List.range 16).map (fun j => s + 4 * (j / 2) + j % 2), s + 32⟩

/-! ### Programs -/

def N_PUB : ℕ := 124

/-- Layout of a child's external values: public inputs, key words, preprocessed root. -/
def EXT_CHILD : ℕ := N_PUB + 16

/-- The indices of the input state (`isIn` in Aggregate.lean). -/
def isIn (k : ℕ) : Bool :=
  k < 16 || (32 ≤ k && k < 38) || k == 44 || k == 45 || (48 ≤ k && k < 68) || (88 ≤ k && k < 98)

/-- A child's section of the node program, starting at register `n`: guessed public inputs
(`n + k`), key, digest, preprocessed root, then the verifier hook `i` (args: root, digest; it
defines the child's circuit hash). -/
structure ChildRegs where
  pubs : ℕ → ℕ
  key : List ℕ
  digest : List ℕ
  chash : List ℕ

def child (n i : ℕ) : Out ChildRegs :=
  let e := EXT_CHILD * i
  let pubsOps := (List.range N_PUB).map (fun k => Op.guessM31 (n + k) (.ext (e + k)))
  let key := guessHash (n + N_PUB) (e + N_PUB)
  let dg := pubsDigest key.next key.res ((List.range N_PUB).map (n + ·))
  let root := guessHash dg.next (e + N_PUB + 8)
  let ch := (List.range 8).map (root.next + ·)
  ⟨pubsOps ++ key.ops ++ dg.ops ++ root.ops ++ [.hook i (root.res ++ dg.res) ch],
   ⟨(n + ·), key.res, dg.res, ch⟩, root.next + 8⟩

/-- **The node program.** Results: the output digest's 8 words. -/
def nodeProgram : Program :=
  let c0 := child 0 0
  let c1 := child c0.next 1
  let L := linkChecks c1.next c0.res.pubs c1.res.pubs
  let key := blake2s L.next (c0.res.chash ++ c0.res.key ++ c1.res.chash ++ c1.res.key) 128
  let T := treeNode key.next c0.res.pubs c1.res.pubs
  let outs := (List.range N_PUB).map fun k =>
    if k < TB then (if isIn k then c0.res.pubs k else c1.res.pubs k) else T.res.getD (k - TB) 0
  let dg := pubsDigest T.next key.res outs
  ⟨"node_glue", c0.ops ++ c1.ops ++ L.ops ++ key.ops ++ T.ops ++ dg.ops, dg.res⟩

/-- **The leaf program**: the verifier hooks (0: proof guess; 1: the system statement with the
public entry, args: the public inputs), the zero key, the digest. -/
def leafProgram : Program :=
  let pubs := (List.range N_PUB).map (2 + ·)
  let dg := pubsDigest (2 + N_PUB + 8) ((List.range 8).map (2 + N_PUB + ·)) pubs
  ⟨"leaf_glue",
   [.hook 0 [] []] ++ (List.range N_PUB).map (fun k => Op.guessM31 (2 + k) (.ext k)) ++ [.hook 1 pubs []] ++
     (List.range 8).map (fun w => constU32 (2 + N_PUB + w) 0) ++ dg.ops,
   dg.res⟩

end StarkedAir.Circuit
