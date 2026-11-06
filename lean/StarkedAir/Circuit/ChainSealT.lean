/-
**The chain seal with the header chain in-circuit (SEAL-T, D-052).** `chainSealT ms gen D` is the seal
(`chainSeal ms gen`, every part and check kept) plus:

- **the header chain root as one more child** (hook `S + 1`, `hdrChild`): its 124 public inputs, key,
  digest `pubsDigest(key, pubs)` and preprocessed root, as the header node's children are opened
  (`Circuit.child`); the **genesis checks** (`HeaderTree.genesisChecks`: the start state is genesis's) as
  50 equalities on its public inputs;
- **`T`** (the MMR root over the chain's block hashes, public inputs 108–123) packed into 8 words;
- **an MMR inclusion path per epoch child**, from the child's block-hash root (16 limbs of its epoch's
  `rest` preimage) to `T`, and **one for the genesis block hash**: `D` steps, each `node(l, r)` (one
  Blake2s compression of 64 bytes) of the current value and a guessed sibling in the order a guessed
  side bit gives, taken when the step is active (`s < len`, from the one-hot of a guessed `len`); the
  last value equals `T`;
- **the output message** extended by the chain's tip (8 words), the tip height, the chainwork (5
  words), and per path its side bits (two words of 30 bits) and its length. The verifier recomputes the
  sides and lengths from the positions and the header count (`HT.inclusionSides`, arithmetic only),
  which binds each path to its position.

The key covers the header root child's circuit hash and key too. External values after the set states:
the header child's (`N_PUB + 16`), then per path `9 D + 1` (siblings, side bits, length).
-/
import StarkedAir.Circuit.ChainSeal
import StarkedAir.Gadgets.RootChecks

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Circuit.EpochJoin (Child joinChild)
open StarkedAir.Circuit.EpochRoot (chainOuts lastNext)

/-! ### The header chain root child -/

/-- The header chain root (hook `hook`, external values from `e`): `N_PUB` guessed public inputs, key,
digest, preprocessed root, the verifier hook (as `Circuit.child`). -/
def hdrChild (n e hook : ℕ) : Out ChildRegs :=
  let pubsOps := (List.range N_PUB).map (fun k => Op.guessM31 (n + k) (.ext (e + k)))
  let key := guessHash (n + N_PUB) (e + N_PUB)
  let dg := pubsDigest key.next key.res ((List.range N_PUB).map (n + ·))
  let root := guessHash dg.next (e + N_PUB + 8)
  let ch := (List.range 8).map (root.next + ·)
  ⟨pubsOps ++ key.ops ++ dg.ops ++ root.ops ++ [.hook hook (root.res ++ dg.res) ch],
   ⟨(n + ·), key.res, dg.res, ch⟩, root.next + 8⟩

/-- `k` words packed from `2 k` limbs (`lo + hi·e1`). Registers `n … n + 2k − 1`; results `n + 2w + 1`. -/
def packN (n : ℕ) (limbs : List ℕ) (k : ℕ) (C : Consts) : Out (List ℕ) :=
  ⟨(List.range k).flatMap (fun w =>
    [.mul (n + 2 * w) (limbs.getD (2 * w + 1) 0) C.e1, .add (n + 2 * w + 1) (limbs.getD (2 * w) 0) (n + 2 * w)]),
   (List.range k).map (fun w => n + 2 * w + 1), n + 2 * k⟩

/-- The genesis checks on the header root's public inputs `p` (`c65535` holds 65535). -/
def genesisOps (p : ℕ → ℕ) (C : Consts) (c65535 : ℕ) : List Op :=
  HeaderTree.genesisChecks.map fun c => Op.eq (p c.1) (if c.2 = 0 then C.zero else c65535)

/-! ### MMR inclusion paths -/

/-- One step: `node(l, r)` with `(l, r) = (sib, cur)` when `b = 1`, `(cur, sib)` when `b = 0`, taken when
`a = 1`. Registers: the selections `n … n + 31`, the compression, the mux (24). -/
def pathStep (n : ℕ) (cur sib : List ℕ) (b a : ℕ) : Out (List ℕ) :=
  let sel := (List.range 8).flatMap fun w =>
    [Op.sub (n + 4 * w) (sib.getD w 0) (cur.getD w 0), .mul (n + 4 * w + 1) b (n + 4 * w),
     .add (n + 4 * w + 2) (cur.getD w 0) (n + 4 * w + 1), .sub (n + 4 * w + 3) (sib.getD w 0) (n + 4 * w + 1)]
  let msg := (List.range 8).map (fun w => n + 4 * w + 2) ++ (List.range 8).map (fun w => n + 4 * w + 3)
  let h := blake2s (n + 32) msg 64
  let m := h.next
  let mux := (List.range 8).flatMap fun w =>
    [Op.sub (m + 3 * w) (h.res.getD w 0) (cur.getD w 0), .mul (m + 3 * w + 1) a (m + 3 * w),
     .add (m + 3 * w + 2) (cur.getD w 0) (m + 3 * w + 1)]
  ⟨sel ++ h.ops ++ mux, (List.range 8).map (fun w => m + 3 * w + 2), m + 24⟩

/-- Steps `s, s + 1, …` (`k` of them) from `cur`: ops, the final value, the next register. -/
def pathSteps (sib : ℕ → List ℕ) (b a : ℕ → ℕ) : ℕ → ℕ → ℕ → List ℕ → List Op × List ℕ × ℕ
  | _, 0, r, cur => ([], cur, r)
  | s, k + 1, r, cur =>
    let st := pathStep r cur (sib s) (b s) (a s)
    let rest := pathSteps sib b a (s + 1) k st.next st.res
    (st.ops ++ rest.1, rest.2.1, rest.2.2)

/-- `Σ_{s ∈ [lo, lo + k)} b_s 2^(s − lo)` (`pw j` holds `2^j`): a running sum from `C.zero`. Registers
`n … n + 2k − 1`; the result at `n + 2k − 1` (`C.zero` when `k = 0`). -/
def bitsWord (n : ℕ) (b : ℕ → ℕ) (pw : ℕ → ℕ) (lo k : ℕ) (C : Consts) : Out ℕ :=
  ⟨(List.range k).flatMap (fun j =>
    [Op.mul (n + 2 * j) (b (lo + j)) (pw j), .add (n + 2 * j + 1) (if j = 0 then C.zero else n + 2 * j - 1) (n + 2 * j)]),
   if k = 0 then C.zero else n + 2 * k - 1, n + 2 * k⟩

/-- A path's registers: the final value, the side bits' two words, the length. -/
structure PathRegs where
  res : List ℕ
  sLo : ℕ
  sHi : ℕ
  len : ℕ

/-- **An MMR inclusion path** of `D ≤ 60` steps from `leaf` (8 u32 registers), external values from
`e`: `D` siblings (8 words each), `D` side bits (boolean), the length `len ≤ 64` (its one-hot, the active
mask `s < len`), the steps, the side bits packed into two words of 30 bits. -/
def pathOps (n e : ℕ) (leaf : List ℕ) (D : ℕ) (C : Consts) (pw : ℕ → ℕ) : Out PathRegs :=
  let sibs := (List.range D).map fun s => guessHash (n + 40 * s) (e + 8 * s)
  let nb := n + 40 * D
  let bit : ℕ → ℕ := fun s => nb + 4 * s
  let bits := (List.range D).flatMap fun s =>
    [Op.guessM31 (bit s) (.ext (e + 8 * D + s)), .sub (bit s + 1) (bit s) C.one, .mul (bit s + 2) (bit s) (bit s + 1),
     .eq (bit s + 2) C.zero]
  let nl := nb + 4 * D
  let oh := oneHot65 (nl + 1) nl C
  let lt := ltMask oh.next oh.res C
  let st := pathSteps (fun s => (sibs.getD s ⟨[], [], 0⟩).res) bit (fun s => lt.res.getD s 0) 0 D lt.next leaf
  let lo := bitsWord st.2.2 bit pw 0 (min D 30) C
  let hi := bitsWord lo.next bit pw 30 (D - 30) C
  ⟨sibs.flatMap (·.ops) ++ bits ++ [.guessM31 nl (.ext (e + 9 * D))] ++ oh.ops ++ lt.ops ++ st.1 ++ lo.ops ++ hi.ops,
   ⟨st.2.1, lo.res, hi.res, nl⟩, hi.next⟩

/-! ### The program -/

/-- External values per path. -/
def pathExt (D : ℕ) : ℕ := 9 * D + 1

/-- The block-hash root limbs of epoch `i`'s child `c` (in its `rest` preimage). -/
def childLimbs (P : Parts) (i c : ℕ) : List ℕ :=
  ((P.rests.getD i ⟨[], ⟨[], 0, [], []⟩, 0⟩).res.hr.drop (16 * c)).take 16

/-- The paths' leaves after genesis's: `(epoch, child)` in chain order. -/
def childIdx (ms : List ℕ) : List (ℕ × ℕ) :=
  (List.range ms.length).flatMap fun i => (List.range (ms.getD i 0)).map fun c => (i, c)

/-- The genesis block hash (`store.GENESIS_HASH`, as `HT.blockHash` words). -/
def genesisHash : List ℕ :=
  [0x6fe28c0a, 0xb6f1b372, 0xc1a6a246, 0xae63f74f, 0x931e8365, 0xe15a089c, 0x68d61900, 0x00000000]

/-- The T part's gadgets, in register order. -/
structure PartsT where
  P : Parts
  hc : Out ChildRegs
  k65535 : ℕ
  pws : List Op
  pw : ℕ → ℕ
  gen : List Op
  T : Out (List ℕ)
  tip : Out (List ℕ)
  hgt : Out (List ℕ)
  work : Out (List ℕ)
  gleaf : List Op
  paths : List (Out PathRegs)
  ends : List Op
  key : Out (List ℕ)
  dg : Out (List ℕ)
  msg : List ℕ

def partsT (ms : List ℕ) (gen : Bool) (D : ℕ) : PartsT :=
  let P := parts ms gen
  let S := nSets ms.length gen
  let C := P.C.res
  let eH := eState ms gen S
  let hc := hdrChild P.checks.next eH (S + 1)
  let k65535 := hc.next
  let pwBase := k65535 + 1
  let pws := (List.range 30).map fun j => Op.const (pwBase + j) (2 ^ j) 0 0 0
  let pw : ℕ → ℕ := (pwBase + ·)
  let genOps := genesisOps hc.res.pubs C k65535
  let T := packN (pwBase + 30) ((List.range 16).map (fun j => hc.res.pubs (108 + j))) 8 C
  let tip := packN T.next ((List.range 16).map (fun j => hc.res.pubs (16 + j))) 8 C
  let hgt := packN tip.next [hc.res.pubs 38, hc.res.pubs 39] 1 C
  let work := packN hgt.next ((List.range 10).map (fun j => hc.res.pubs (98 + j))) 5 C
  let gl := work.next
  let gleaf := (List.range 8).map fun w => constU32 (gl + w) (genesisHash.getD w 0)
  let gpath := pathOps (gl + 8) (eH + N_PUB + 16) ((List.range 8).map (gl + ·)) D C pw
  let cpaths := chainOuts (fun p r =>
      let ic := (childIdx ms).getD p (0, 0)
      let lw := packN r (childLimbs P ic.1 ic.2) 8 C
      let pa := pathOps lw.next (eH + N_PUB + 16 + pathExt D * (p + 1)) lw.res D C pw
      ⟨lw.ops ++ pa.ops, pa.res, pa.next⟩) gpath.next (childIdx ms).length
  let paths := gpath :: cpaths
  let r7 := lastNext cpaths gpath.next
  let ends := paths.flatMap fun pa => (List.range 8).map fun w => Op.eq (pa.res.res.getD w 0) (T.res.getD w 0)
  let keyMsg := P.J.res.chash ++ P.J.res.key ++ P.sets.flatMap (fun c => c.res.chash ++ c.res.key) ++
    hc.res.chash ++ hc.res.key
  let key := blake2s r7 keyMsg (4 * keyMsg.length)
  let E := (P.opens.getD (S - 1) ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩).res
  let shaStart := if gen then List.replicate 8 C.zero else
    (P.opens.getD 0 ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩).res.shaDg
  let ab := key.next
  let pm := ab + 2
  let np := paths.length
  let pathW : ℕ → List ℕ := fun p => [pm + 3 * p, pm + 3 * p + 1, pm + 3 * p + 2]
  let m2us := (List.range np).flatMap fun p =>
    let pa := (paths.getD p ⟨[], ⟨[], 0, 0, 0⟩, 0⟩).res
    [Op.m2u (pm + 3 * p) pa.sLo, .m2u (pm + 3 * p + 1) pa.sHi, .m2u (pm + 3 * p + 2) pa.len]
  let msg := key.res ++ [ab, ab + 1] ++ P.J.res.first ++ P.J.res.last ++ P.J.res.tail ++ [E.cntW] ++ E.amtW ++
    [E.maxhW] ++ E.mroot ++ E.shaDg ++ shaStart ++ tip.res ++ hgt.res ++ work.res ++
    (List.range np).flatMap pathW
  let dgn := pm + 3 * np
  let dg := blake2s dgn msg (4 * msg.length)
  ⟨P, hc, k65535, pws, pw, genOps, T, tip, hgt, work, gleaf, paths, ends, key,
   ⟨[.m2u ab P.J.res.lo, .m2u (ab + 1) P.J.res.hi] ++ m2us ++ dg.ops, dg.res, dg.next⟩, msg⟩

def tagT (ms : List ℕ) (gen : Bool) (D : ℕ) : String := s!"t{D}_" ++ tag ms gen

/-- **The chain seal with the header chain in-circuit** over epochs of `ms` children (the first from
genesis when `gen`), inclusion paths of `D ≤ 60` steps. Results: the output digest's 8 words. -/
def chainSealT (ms : List ℕ) (gen : Bool) (D : ℕ) : Program :=
  let Q := partsT ms gen D
  let P := Q.P
  ⟨s!"chain_seal_{tagT ms gen D}",
   P.J.ops ++ P.sets.flatMap (·.ops) ++ P.roots.flatMap (·.ops) ++ P.rests.flatMap (·.ops) ++ P.C.ops ++
     P.chals.flatMap (·.ops) ++ P.opens.flatMap (·.ops) ++ P.accs.flatMap (·.ops) ++ P.checks.ops ++
     Q.hc.ops ++ [.const Q.k65535 65535 0 0 0] ++ Q.pws ++ Q.gen ++ Q.T.ops ++ Q.tip.ops ++ Q.hgt.ops ++ Q.work.ops ++
     Q.gleaf ++ Q.paths.flatMap (·.ops) ++ Q.ends ++ Q.key.ops ++ Q.dg.ops,
   Q.dg.res⟩

def chainSealTJson (ms : List ℕ) (gen : Bool) (D : ℕ) : String := (chainSealT ms gen D).toJson

-- The mainnet seal's message: 63 + 8 + 1 + 5 + 3 · (1 + 32) = 176 words.
#guard (partsT [16, 16] false 32).msg.length = 176
#guard (partsT [1, 2, 3] true 32).msg.length = 63 + 14 + 3 * 7

end StarkedAir.Circuit.ChainSeal
