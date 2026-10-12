/-
**The block recursion tree, end to end, modulo named hypotheses (VL-NODE).**

A block node circuit is the replay of `blockNodeProgram` (`Circuit/BlockNode.lean`) with stwo-zig's
recursive verifier at its two hooks (`block_rec.zig` `buildNodeCircuit`, `node.zig` `RecHook`). Every
gate of ours is in the program: the guessed child summaries and keys, the recomputed child digests
`pubsDigest(key, summary)`, the hook's inputs (the guessed preprocessed root and that digest) and
outputs (the child's circuit hash), the node key `K = Blake2s(hL ‖ kL ‖ hR ‖ kR)`, the link checks
and sums (`nodeOut`), the output digest `pubsDigest(K, out)`, and the outputs (the program's results;
`glue.runOutputs`).

The block leaf's summary and digest are Lean-first too (`blockLeafOut`, exported as
`airs/block_leaf_out.json`, replayed by `block_rec.zig` `buildLeafCircuit`): `leafOut_vec`.

This file proves:
- `bchild_digest`, `bnode_key`, `bnode_digest`: the digest each hook checks, the node key and the output
  digest, as Blake2s of the right words;
- `block_node_sound`: a satisfied node program over two `SumOk` children outputs the digest of a `SumOk`
  summary under the key of its children's circuit hashes and keys;
- `leafOut_sound`, `leafOut_vec`: the block leaf outputs `pubsDigest(0, leafVec p)`;
- `tree_sound`: a circuit whose hash and key are those of a tree shape `t` (`Tree.hash`, `Tree.key`, as
  the outer verifier's `expected` computes them), satisfied with output `sumDigest t.key v`, has a
  proven summary `v`, or there is a Blake2s collision;
- `forest_sound`: the outer verifier's checks (`block_forest.zig` `verifyForest`) give one proven
  range over the epoch (`RngOk`), or a Blake2s collision; `forest_epoch` gives `epoch_hyps_of_rng`'s
  conclusion.

**Named hypotheses** (fields of `Trust`; none is an axiom):
- `stwoSound`: Stwo soundness of the native circuit verifier (with the pinned config): an accepted
  circuit proof for (circuit hash `h`, output digest `d`) means a satisfied circuit with hash `h` and
  output `d`.
- `nodeCircuit`: the circuit AIR's soundness and the replay's faithfulness for the node circuit: a
  satisfied circuit whose hash is the node's satisfies the program's ops (`Op.holds`), its outputs are
  the results' words, and the verifier gates at each hook hold (`VGates`, left abstract).
- `recVerifies` (**`RecVerifies`**): stwo-zig's in-circuit verifier is sound: if its gates at hook `i`
  hold with args `root ‖ digest` and outputs `ch`, then a satisfied circuit with hash `ch` outputs
  `digest`.
- `leafSound` (**`BlockLeafSound`** here, `LeafOut`): a satisfied block leaf circuit (hash `leafH L`)
  outputs `sumDigest zeroKey (leafVec p)` for public inputs `p` meeting `sumOk_leaf`'s premises. It is
  the composition of `plain_sound` (`StarkSound`, `SZGood`) for the block system, `checks_sound`,
  `ctx_sound`, `seedLeaf_sound`, `leafOut_vec`, and the leaf hooks' binding of the verified public inputs.

Blake2s collision resistance is not assumed: the conclusions are disjunctions with `Collision`.
-/
import StarkedAir.Circuit.BlockTree

namespace StarkedAir.Circuit.BlockRec

open StarkedAir StarkedAir.Circuit StarkedAir.Block Q Spec.Blake2s
open StarkedAir.Circuit.BlockNode
open StarkedAir.Circuit.BlockTree (SumOk SumOkP leafVec rngOf Linked' forest_rng forest_rngP)

/-! ### Digests, keys, collisions -/

/-- Blake2s of a word-aligned message: its 8 digest words. -/
def H (m : List Word) : List Word := (List.range 8).map (blake2sWords m (4 * m.length))

/-- A summary's 51 limbs as words. -/
def vals (v : ℕ → F) : List Word := (List.range NSUM).map fun i => BitVec.ofNat 32 (v i).val

/-- `pubsDigest(key, v)` (`leaf.pubsDigest`). -/
def sumDigest (key : List Word) (v : ℕ → F) : List Word := H (key ++ vals v)

def zeroKey : List Word := List.replicate 8 0

/-- A node's key `Blake2s(hL ‖ kL ‖ hR ‖ kR)` (`node.nodeKey`). -/
def keyOf (hl kl hr kr : List Word) : List Word := H (hl ++ kl ++ hr ++ kr)

/-- **A Blake2s collision**: two different word-aligned messages with one digest. -/
def Collision : Prop :=
  ∃ a b : List Word, a ≠ b ∧ 4 * a.length < 2 ^ 32 ∧ 4 * b.length < 2 ^ 32 ∧ H a = H b

theorem H_length (m : List Word) : (H m).length = 8 := by simp [H]

theorem H_eq {a b : List Word} (ha : 4 * a.length < 2 ^ 32) (hb : 4 * b.length < 2 ^ 32) (h : H a = H b) :
    a = b ∨ Collision := by
  by_cases e : a = b
  · exact Or.inl e
  · exact Or.inr ⟨a, b, e, ha, hb, h⟩

theorem vals_length (v : ℕ → F) : (vals v).length = NSUM := by simp [vals]

theorem ofNat_val_inj {x y : F} (h : BitVec.ofNat 32 x.val = BitVec.ofNat 32 y.val) : x = y := by
  have hx : x.val < 2 ^ 32 := lt_trans (ZMod.val_lt x) (by unfold P; norm_num)
  have hy : y.val < 2 ^ 32 := lt_trans (ZMod.val_lt y) (by unfold P; norm_num)
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact ZMod.val_injective _ this

theorem vals_inj {v w : ℕ → F} (h : vals v = vals w) : ∀ i < NSUM, v i = w i := by
  intro i hi
  have := congrArg (fun l => l.getD i 0) h
  simp only [vals, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact ofNat_val_inj this

/-- Digests of `key ++ summary` with 8-word keys agree: equal keys and summaries, or a collision. -/
theorem sumDigest_eq {k k' : List Word} {v w : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8)
    (h : sumDigest k v = sumDigest k' w) : (k = k' ∧ ∀ i < NSUM, v i = w i) ∨ Collision := by
  rcases H_eq (by simp [hk, vals_length, NSUM]) (by simp [hk', vals_length, NSUM]) h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, vals_inj e2⟩
  · exact Or.inr c

/-- Keys agree: equal circuit hashes and keys, or a collision. -/
theorem keyOf_eq {a b c d a' b' c' d' : List Word} (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (hd : d.length = 8) (ha' : a'.length = 8) (hb' : b'.length = 8) (hc' : c'.length = 8) (hd' : d'.length = 8)
    (h : keyOf a b c d = keyOf a' b' c' d') : (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∨ Collision := by
  rcases H_eq (by simp [ha, hb, hc, hd]) (by simp [ha', hb', hc', hd']) h with e | col
  · obtain ⟨e1, e4⟩ := List.append_inj e (by simp [ha, hb, hc, ha', hb', hc'])
    obtain ⟨e1, e3⟩ := List.append_inj e1 (by simp [ha, hb, ha', hb'])
    obtain ⟨e1, e2⟩ := List.append_inj e1 (by rw [ha, ha'])
    exact Or.inl ⟨e1, e2, e3, e4⟩
  · exact Or.inr col

/-! ### `SumOk` depends only on the 51 limbs -/

theorem rngOf_congr {v w : ℕ → F} (h : ∀ i < NSUM, v i = w i) (ℓ : ℕ) : rngOf v ℓ = rngOf w ℓ := by
  have q : ∀ k, k + 3 < NSUM → RunSum.pQ v k = RunSum.pQ w k := fun k hk =>
    BlockTree.pQ_congr fun j hj => h _ (by omega)
  simp only [rngOf, h 0 (by decide), h 6 (by decide), q 2 (by decide), q 7 (by decide), q 11 (by decide),
    q 15 (by decide)]

/-- `sumOk_congr` for any `ok`. -/
theorem sumOk_congrP {ok : (ℕ → F) → Prop}  {v w : ℕ → F} (h : ∀ i < NSUM, v i = w i) (hv : SumOkP ok v) : SumOkP ok w := by
  obtain ⟨ℓ, P, h1, h2, h3, h4, hb, hs, hn, hh, hsd⟩ := hv
  have q2 : RunSum.pQ v 2 = RunSum.pQ w 2 := BlockTree.pQ_congr fun j hj => h _ (by unfold NSUM; omega)
  refine ⟨ℓ, P, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [← h 1 (by decide)]
  · rwa [← h 0 (by decide)]
  · rwa [← h 1 (by decide)]
  · rwa [← h 6 (by decide)]
  · intro i hi; rw [← rngOf_congr h, ← h 0 (by decide)]; exact hb i hi
  · rw [← q2]; exact hs
  · rw [← h 6 (by decide)]; exact hn
  · intro j hj; rw [← h (19 + j) (by unfold NSUM; omega)]; exact hh j hj
  · intro j hj; rw [← h (35 + j) (by unfold NSUM; omega)]; exact hsd j hj

theorem sumOk_congr {v w : ℕ → F} (h : ∀ i < NSUM, v i = w i) (hv : SumOk v) : SumOk w :=
  sumOk_congrP h hv

/-! ### The block node program's digests and key -/

theorem wordsOf_eq {ρ : ℕ → Q} {res : List ℕ} (hl : res.length = 8) {f : ℕ → Word}
    (h : ∀ i < 8, word (ρ (res.getD i 0)) = f i) : wordsOf ρ res = (List.range 8).map f := by
  apply List.ext_getElem (by simp [wordsOf, hl])
  intro i h1 h2
  have hi : i < 8 := by simpa [wordsOf, hl] using h1
  simp only [wordsOf, List.getElem_map, List.getElem_range, Function.comp]
  have := h i hi
  rwa [List.getD_eq_getElem _ _ (by rw [hl]; exact hi)] at this

theorem pubsDigest_length (n : ℕ) (key pubs : List ℕ) : (pubsDigest n key pubs).res.length = 8 := by
  simp [pubsDigest, blake2s]

theorem blake2s_length (n : ℕ) (msg : List ℕ) (nb : ℕ) : (blake2s n msg nb).res.length = 8 := by
  simp [blake2s]

theorem guessHash_length (n e : ℕ) : (guessHash n e).res.length = 8 := by simp [guessHash]

/-- `pubsDigest` over an 8-register key and 51 summary registers is `sumDigest`. -/
theorem pubsDigest_sum {ρ : ℕ → Q} {n : ℕ} {key : List ℕ} {f : ℕ → ℕ} (hk : key.length = 8)
    (h : Holds ρ (pubsDigest n key ((List.range NSUM).map f)).ops) :
    wordsOf ρ (pubsDigest n key ((List.range NSUM).map f)).res = sumDigest (wordsOf ρ key) (fun i => (ρ (f i)).a) := by
  rw [wordsOf_eq (pubsDigest_length _ _ _) (pubsDigest_sound h (by simp [hk, NSUM]))]
  simp only [sumDigest, H, wordsOf, vals, List.length_append, List.length_map, List.length_range, hk, List.map_map]
  rfl

def bpubs (c : Out ChildRegs) : ℕ → ℕ := c.res.pubs

/-- A child's summary, key and circuit hash (as words), and the digest its hook checks. -/
def childSum (ρ : ℕ → Q) (c : Out ChildRegs) : ℕ → F := fun k => (ρ (c.res.pubs k)).a

theorem bchild_key_length (n i : ℕ) : (bchild n i).res.key.length = 8 := by simp [bchild, guessHash]
theorem bchild_chash_length (n i : ℕ) : (bchild n i).res.chash.length = 8 := by simp [bchild]

/-- **What child `i`'s verifier hook checks against**: the digest of its key and summary. -/
theorem bchild_digest {ρ : ℕ → Q} {n i : ℕ} (h : Holds ρ (bchild n i).ops) :
    wordsOf ρ (bchild n i).res.digest = sumDigest (wordsOf ρ (bchild n i).res.key) (childSum ρ (bchild n i)) := by
  dsimp only [bchild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hdg⟩, -⟩, -⟩ := h
  exact pubsDigest_sum (f := (n + ·)) (guessHash_length _ _) hdg

/-- The hook op of child `i`: args (root ‖ digest), outputs (circuit hash). -/
theorem bchild_hook (n i : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (bchild n i).res.digest) (bchild n i).res.chash ∈ (bchild n i).ops := by
  refine ⟨(guessHash (pubsDigest (guessHash (n + NSUM) (EXT_B * i + NSUM)).next
    (guessHash (n + NSUM) (EXT_B * i + NSUM)).res ((List.range NSUM).map (n + ·))).next (EXT_B * i + NSUM + 8)).res,
    guessHash_length _ _, ?_⟩
  simp [bchild]

/-- The node's output summary. -/
def outSum (ρ : ℕ → Q) : ℕ → F := fun i => (ρ (outReg bC0.res.pubs bC1.res.pubs bC1.next i)).a

theorem bnode_parts {ρ : ℕ → Q} (h : Holds ρ blockNodeProgram.ops) :
    Holds ρ bC0.ops ∧ Holds ρ bC1.ops ∧ Holds ρ bJoin.ops ∧ Holds ρ bKey.ops ∧ Holds ρ bDigest.ops := by
  simp only [blockNodeProgram, holds_append] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, hj⟩, hk⟩, hd⟩ := h
  exact ⟨h0, h1, hj, hk, hd⟩

/-- **The node key**: Blake2s of `hL ‖ kL ‖ hR ‖ kR` (the hooks' outputs and the guessed keys). -/
theorem bnode_key {ρ : ℕ → Q} (h : Holds ρ blockNodeProgram.ops) :
    wordsOf ρ bKey.res = keyOf (wordsOf ρ bC0.res.chash) (wordsOf ρ bC0.res.key) (wordsOf ρ bC1.res.chash)
      (wordsOf ρ bC1.res.key) := by
  have hk := (bnode_parts h).2.2.2.1
  rw [bKey, wordsOf_eq (blake2s_length _ _ _) (blake2s_words hk (by norm_num))]
  simp only [keyOf, H, wordsOf, List.map_append, List.length_append, List.length_map,
    bchild_chash_length, bchild_key_length, bC0, bC1]

/-- **The node's output digest**: `pubsDigest(K, out)`. -/
theorem bnode_digest {ρ : ℕ → Q} (h : Holds ρ blockNodeProgram.ops) :
    wordsOf ρ blockNodeProgram.results = sumDigest (wordsOf ρ bKey.res) (outSum ρ) := by
  have hd := (bnode_parts h).2.2.2.2
  show wordsOf ρ bDigest.res = _
  have e : bJoin.res = (List.range NSUM).map (outReg bC0.res.pubs bC1.res.pubs bC1.next) := rfl
  rw [bDigest, e] at hd ⊢
  exact pubsDigest_sum (blake2s_length _ _ _) hd

/-- `block_node_sound` for any per-block statement `ok`. -/
theorem block_node_soundP {ok : (ℕ → F) → Prop}  {ρ : ℕ → Q} (h : Holds ρ blockNodeProgram.ops)
    (hL : SumOkP ok (childSum ρ bC0)) (hR : SumOkP ok (childSum ρ bC1)) :
    SumOkP ok (outSum ρ) ∧
    wordsOf ρ blockNodeProgram.results = sumDigest (keyOf (wordsOf ρ bC0.res.chash) (wordsOf ρ bC0.res.key)
      (wordsOf ρ bC1.res.chash) (wordsOf ρ bC1.res.key)) (outSum ρ) ∧
    wordsOf ρ bC0.res.digest = sumDigest (wordsOf ρ bC0.res.key) (childSum ρ bC0) ∧
    wordsOf ρ bC1.res.digest = sumDigest (wordsOf ρ bC1.res.key) (childSum ρ bC1) := by
  obtain ⟨h0, h1, hj, -, -⟩ := bnode_parts h
  refine ⟨BlockTree.sumOk_nodeP hj hL hR, ?_, bchild_digest h0, bchild_digest h1⟩
  rw [bnode_digest h, bnode_key h]

/-- **The block node is sound.** If the node program holds and both children's summaries are proven,
the node outputs the digest, under the key of its children's circuit hashes and keys, of a proven
summary; and each child's hook checked the digest of that child's key and summary. -/
theorem block_node_sound {ρ : ℕ → Q} (h : Holds ρ blockNodeProgram.ops)
    (hL : SumOk (childSum ρ bC0)) (hR : SumOk (childSum ρ bC1)) :
    SumOk (outSum ρ) ∧
    wordsOf ρ blockNodeProgram.results = sumDigest (keyOf (wordsOf ρ bC0.res.chash) (wordsOf ρ bC0.res.key)
      (wordsOf ρ bC1.res.chash) (wordsOf ρ bC1.res.key)) (outSum ρ) ∧
    wordsOf ρ bC0.res.digest = sumDigest (wordsOf ρ bC0.res.key) (childSum ρ bC0) ∧
    wordsOf ρ bC1.res.digest = sumDigest (wordsOf ρ bC1.res.key) (childSum ρ bC1) :=
  block_node_soundP h hL hR

/-! ### The block leaf's output, Lean-first -/

/-- Hook 0's outputs: registers `0 … 160` are the block's public inputs (the plain verifier's), `161 …
176` the seed leaf's limbs (`seedLeafProg`'s results). -/
def LSEED : ℕ := 161
def LIN : ℕ := 177

/-- The register of summary limb `i` (`leafVec`'s layout). -/
def sReg (i : ℕ) : ℕ :=
  if i = 0 then 2 else if i = 1 then LIN + 18 else if i < 6 then Coin.PUB_S + (i - 2) else if i = 6 then Coin.PUB_NIN
  else if i < 15 then 41 + (i - 7) else if i < 19 then Coin.PUB_ALPHA 1 + (i - 15)
  else if i < 35 then 25 + (i - 19) else LSEED + (i - 35)

def leafKey : List ℕ := (List.range 8).map (LIN + 19 + ·)
def leafDg : Out (List ℕ) := pubsDigest (LIN + 27) leafKey ((List.range NSUM).map sReg)

/-- The block leaf's output: the height and input count below `2^30`, the count 1, the zero key, the
digest of the 51-limb summary. -/
def leafOutOps : List Op :=
  [.hook 0 [] (List.range LIN)] ++ lt30 LIN 2 ++ lt30 (LIN + 9) Coin.PUB_NIN ++ [.const (LIN + 18) 1 0 0 0] ++
    leafKey.map (fun r => constU32 r 0) ++ leafDg.ops

/-- **The block leaf output program.** Results: the output digest's 8 words. -/
def blockLeafOut : Program := ⟨"block_leaf_out", leafOutOps, leafDg.res⟩

theorem vals_congr {v w : ℕ → F} (h : ∀ i < NSUM, v i = w i) : vals v = vals w := by
  apply List.ext_getElem (by simp [vals])
  intro i h1 _
  have hi : i < NSUM := by simpa [vals] using h1
  simp [vals, h i hi]

/-- **The leaf's output is sound.** The height and input count are base values below `2^30`, and the
output is `pubsDigest(0, summary)` over the summary registers. -/
theorem leafOut_sound {ρ : ℕ → Q} (h : Holds ρ leafOutOps) :
    wordsOf ρ blockLeafOut.results = sumDigest zeroKey (fun i => (ρ (sReg i)).a) ∧
    (IsBase (ρ 2) ∧ (ρ 2).a.val < 2 ^ 30) ∧ (IsBase (ρ Coin.PUB_NIN) ∧ (ρ Coin.PUB_NIN).a.val < 2 ^ 30) ∧
    ρ (LIN + 18) = lit 1 0 0 0 := by
  simp only [leafOutOps, holds_append] at h
  obtain ⟨⟨⟨⟨⟨-, l1⟩, l2⟩, hc⟩, hk⟩, hd⟩ := h
  have hz : wordsOf ρ leafKey = zeroKey := by
    apply List.ext_getElem (by simp [wordsOf, leafKey, zeroKey])
    intro j hj _
    have hj8 : j < 8 := by simpa [wordsOf, leafKey] using hj
    have := hk _ (List.mem_map.mpr ⟨LIN + 19 + j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj8, rfl⟩, rfl⟩)
    simp only [wordsOf, leafKey, List.getElem_map, List.getElem_range, Function.comp, const_word this (by norm_num),
      zeroKey, List.getElem_replicate]
    rfl
  refine ⟨?_, lt30_sound l1, lt30_sound l2, ?_⟩
  · show wordsOf ρ leafDg.res = _
    rw [leafDg, pubsDigest_sum (by simp [leafKey]) hd, hz]
  · have := hc _ List.mem_cons_self
    simpa [Op.holds] using this

/-- **The leaf outputs its block's summary.** If hook 0's outputs are the public inputs `p` and the
limbs of the seed leaf `hnode(hash, C_h)` (`seedLeaf_sound`), the output is `sumDigest 0 (leafVec p)`. -/
theorem leafOut_vec {ρ : ℕ → Q} (h : Holds ρ leafOutOps) {p : ℕ → F} (hp : ∀ j < LSEED, (ρ j).a = p j)
    (hs : ∀ j < 16, (ρ (LSEED + j)).a = (HeaderTree.limbsOf (BlockTree.seedOf p)).getD j 0) :
    wordsOf ρ blockLeafOut.results = sumDigest zeroKey (leafVec p) := by
  obtain ⟨hd, -, -, h1⟩ := leafOut_sound h
  rw [hd, sumDigest, sumDigest, vals_congr]
  intro i hi
  unfold NSUM at hi
  simp only [sReg, leafVec]
  by_cases e0 : i = 0
  · simp only [e0, if_true]; exact hp 2 (by decide)
  by_cases e1 : i = 1
  · simp only [e1, if_neg (show (1 : ℕ) ≠ 0 by decide), if_true, h1, lit]; simp
  simp only [if_neg e0, if_neg e1]
  by_cases e2 : i < 6
  · simp only [if_pos e2]; exact hp _ (by unfold LSEED Coin.PUB_S; omega)
  simp only [if_neg e2]
  by_cases e6 : i = 6
  · simp only [if_pos e6]; exact hp _ (by unfold LSEED Coin.PUB_NIN; omega)
  simp only [if_neg e6]
  by_cases e15 : i < 15
  · simp only [if_pos e15]; exact hp _ (by unfold LSEED; omega)
  simp only [if_neg e15]
  by_cases e19 : i < 19
  · simp only [if_pos e19]; exact hp _ (by unfold LSEED Coin.PUB_ALPHA; omega)
  simp only [if_neg e19]
  by_cases e35 : i < 35
  · simp only [if_pos e35]; exact hp _ (by unfold LSEED; omega)
  simp only [if_neg e35]
  exact hs _ (by omega)

def leafOutJson : String := blockLeafOut.toJson

/-! ### The tree, under named hypotheses -/

/-- A recursion tree's shape: block leaves (by block trace log size) and nodes. -/
inductive Tree where
  | leaf (L : ℕ)
  | node (l r : Tree)

section
variable (leafH : ℕ → List Word) (nodeH : List Word)

/-- The circuit hash the outer verifier expects at a tree's root (`block_forest.zig` `expected`). -/
def Tree.hash : Tree → List Word
  | .leaf L => leafH L
  | .node _ _ => nodeH

/-- The key the outer verifier expects (`expected`, `node.nodeKey`): zero at a leaf. -/
def Tree.key : Tree → List Word
  | .leaf _ => zeroKey
  | .node l r => keyOf (l.hash leafH nodeH) (l.key) (r.hash leafH nodeH) (r.key)

theorem Tree.key_length : ∀ t : Tree, (t.key leafH nodeH).length = 8
  | .leaf _ => by simp [Tree.key, zeroKey]
  | .node _ _ => by simp [Tree.key, keyOf, H_length]

end

/-- The verifier gates at every hook of `ops` hold (`VGates`: stwo-zig's `CircuitStatement.init` and
`verify` at hook `i` with these args and outputs; left abstract). -/
def HookGates (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop) (ρ : ℕ → Q) (ops : List Op) : Prop :=
  ∀ i args outs, Op.hook i args outs ∈ ops → VGates ρ i args outs

/-- What a block leaf guarantees of its output `d`: the digest, under the zero key, of the summary
`leafVec p` of public inputs `p` meeting `sumOk_leaf`'s premises. -/
def LeafOut (d : List Word) : Prop :=
  ∃ (p : ℕ → F) (Hh : ℕ), BlockPubOk p ∧ Hh < 2 ^ 30 ∧ p 2 = (Hh : F) ∧
    p Coin.PUB_LOST = (if Spec.Coins.bip30Lost Hh then 1 else 0) ∧
    (∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ p (Coin.PUB_ALPHA 1) ^ k) ∧
    (p Coin.PUB_NIN).val < 2 ^ 30 ∧ (∀ j < 16, (p (25 + j)).val < 65536) ∧ d = sumDigest zeroKey (leafVec p)

/-- `LeafOut` for any per-block statement `ok`: a lifted block leaf guarantees `LeafOutP BlockPubOk'`
(D-045). `LeafOut = LeafOutP BlockPubOk`. -/
def LeafOutP (ok : (ℕ → F) → Prop) (d : List Word) : Prop :=
  ∃ (p : ℕ → F) (Hh : ℕ), ok p ∧ Hh < 2 ^ 30 ∧ p 2 = (Hh : F) ∧
    p Coin.PUB_LOST = (if Spec.Coins.bip30Lost Hh then 1 else 0) ∧
    (∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ p (Coin.PUB_ALPHA 1) ^ k) ∧
    (p Coin.PUB_NIN).val < 2 ^ 30 ∧ (∀ j < 16, (p (25 + j)).val < 65536) ∧ d = sumDigest zeroKey (leafVec p)

theorem leafOut_iff {d : List Word} : LeafOut d ↔ LeafOutP BlockPubOk d := Iff.rfl

theorem LeafOutP.mono {ok ok' : (ℕ → F) → Prop} (hm : ∀ p, ok p → ok' p) {d : List Word} (h : LeafOutP ok d) :
    LeafOutP ok' d := by
  obtain ⟨p, Hh, hp, rest⟩ := h
  exact ⟨p, Hh, hm p hp, rest⟩

/-- A uniform block leaf's guarantee is a per-component one. -/
theorem LeafOut.toV {d : List Word} (h : LeafOut d) : LeafOutP BlockPubOk' d := LeafOutP.mono (fun _ => BlockPubOk.toV) h

/-- **The named hypotheses** (see the header), for a tree whose nodes run the glue program `prog` and
whose leaves guarantee `LeafOk` of their output. `Acc h d`: the native circuit verifier accepts a proof
with circuit hash `h` and output digest `d` under the pinned config. `SatC h d`: some circuit with hash
`h` is satisfied and outputs `d`. -/
structure Trust (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : List Word) (prog : Program) (LeafOk : List Word → Prop) : Prop where
  /-- Stwo soundness (native circuit verifier). -/
  stwoSound : ∀ h d, Acc h d → SatC h d
  /-- Circuit AIR soundness and replay faithfulness for the node circuit. -/
  nodeCircuit : ∀ d, SatC nodeH d → ∃ ρ, Holds ρ prog.ops ∧ wordsOf ρ prog.results = d ∧ HookGates VGates ρ prog.ops
  /-- **`RecVerifies`**: the in-circuit verifier's gates at a hook with args `root ‖ digest` and
  outputs `ch` mean a satisfied circuit with hash `ch` outputs `digest`. -/
  recVerifies : ∀ ρ i args outs, VGates ρ i args outs → SatC (wordsOf ρ outs) (wordsOf ρ (args.drop 8))
  /-- The leaf guarantee: for the block tree **`BlockLeafSound`** (`LeafOut`: `plain_sound` for the
  block system with `StarkSound` and `SZGood`, the leaf's Lean checks, `leafOut_vec`, and the hook's
  binding of the verified public inputs); for the header tree `plain_leaf_valid` and `leaf_digest`. -/
  leafSound : ∀ L d, SatC (leafH L) d → LeafOk d

/-- Weakening the leaf guarantee keeps the named hypotheses (e.g. uniform leaves under `LeafOutP BlockPubOk'`). -/
theorem Trust.mono {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
    {leafH : ℕ → List Word} {nodeH : List Word} {prog : Program} {LeafOk LeafOk' : List Word → Prop}
    (T : Trust Acc SatC VGates leafH nodeH prog LeafOk) (hm : ∀ d, LeafOk d → LeafOk' d) :
    Trust Acc SatC VGates leafH nodeH prog LeafOk' :=
  ⟨T.stwoSound, T.nodeCircuit, T.recVerifies, fun L d h => hm d (T.leafSound L d h)⟩

theorem wordsOf_length (ρ : ℕ → Q) (rs : List ℕ) : (wordsOf ρ rs).length = rs.length := by simp [wordsOf]

theorem hook_mem0 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 0 (root ++ bC0.res.digest) bC0.res.chash ∈ blockNodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := bchild_hook 0 0
  exact ⟨r, hr, by simp only [blockNodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hm)))⟩

theorem hook_mem1 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 1 (root ++ bC1.res.digest) bC1.res.chash ∈ blockNodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := bchild_hook bC0.next 1
  exact ⟨r, hr, by simp only [blockNodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hm)))⟩

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word}

/-- **A tree is sound**, for leaves guaranteeing `LeafOutP ok` (`BlockPubOk'` for lifted leaves, D-045). -/
theorem tree_soundP {ok : (ℕ → F) → Prop}  (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram (LeafOutP ok)) (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : Tree) (v : ℕ → F), SatC (t.hash leafH nodeH) (sumDigest (t.key leafH nodeH) v) → SumOkP ok v ∨ Collision
  | .leaf L, v, hs => by
    obtain ⟨p, Hh, hp, hH, h2, hlost, hα, hnin, hlimbs, hd⟩ := T.leafSound L _ hs
    rcases sumDigest_eq (Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (sumOk_congrP (fun i hi => (e i hi).symm) (BlockTree.sumOk_leafP hp hH h2 hlost hα hnin hlimbs))
    · exact Or.inr c
  | .node l r, v, hs => by
    obtain ⟨ρ, hρ, hres, hg⟩ := T.nodeCircuit _ hs
    obtain ⟨r0, hr0, hm0⟩ := hook_mem0
    obtain ⟨r1, hr1, hm1⟩ := hook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0] at s0
    rw [List.drop_left' hr1] at s1
    obtain ⟨h0, h1, -, -, -⟩ := bnode_parts hρ
    have d0 : wordsOf ρ bC0.res.digest = sumDigest (wordsOf ρ bC0.res.key) (childSum ρ bC0) := bchild_digest h0
    have d1 : wordsOf ρ bC1.res.digest = sumDigest (wordsOf ρ bC1.res.key) (childSum ρ bC1) := bchild_digest h1
    rw [d0] at s0
    rw [d1] at s1
    rw [bnode_digest hρ] at hres
    have kl : (wordsOf ρ bKey.res).length = 8 := by rw [wordsOf_length]; exact blake2s_length _ _ _
    rcases sumDigest_eq kl (Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr c
    rw [bnode_key hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eq (w8 _ (bchild_chash_length _ _)) (w8 _ (bchild_key_length _ _)) (w8 _ (bchild_chash_length _ _))
      (w8 _ (bchild_key_length _ _)) (by cases l <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH l)
      (by cases r <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH r) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr c
    have e1' : wordsOf ρ bC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ bC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ bC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ bC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases tree_soundP T hl hn l _ s0 with sl | c
    swap; · exact Or.inr c
    rcases tree_soundP T hl hn r _ s1 with sr | c
    swap; · exact Or.inr c
    exact Or.inl (sumOk_congrP ev (block_node_soundP hρ sl sr).1)

/-- **A tree is sound.** A satisfied circuit with the hash and key of tree shape `t`, outputting
`sumDigest key v`, has a proven summary `v` (or Blake2s has a collision). -/
theorem tree_sound (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram LeafOut) (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : Tree) (v : ℕ → F), SatC (t.hash leafH nodeH) (sumDigest (t.key leafH nodeH) v) → SumOk v ∨ Collision :=
  tree_soundP T hl hn

/-- `forest_rng'` for any `ok`. -/
theorem forest_rng'P {ok : (ℕ → F) → Prop}  (vs : List (ℕ → F)) (v0 : ℕ → F) (h0 : SumOkP ok v0) (hs : ∀ v ∈ vs, SumOkP ok v)
    (hlink : Linked' v0 vs) (hch : ∀ v ∈ vs, ∀ i < 12, v (7 + i) = v0 (7 + i)) :
    ∃ n, 0 < n ∧ RngOkP ok ⟨(v0 0).val, n, RunSum.pQ v0 2 + (vs.map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + (vs.map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11, RunSum.pQ v0 15⟩ := by
  obtain ⟨ℓ0, hn0, hr0⟩ := h0.rng
  have hrs : ∀ v ∈ vs, ∃ ℓ, (v 1).val = 2 ^ ℓ ∧ RngOkP ok (rngOf v ℓ) := fun v hv => (hs v hv).rng
  choose! ℓs hℓs using hrs
  have key := BlockTree.rng_forestP (vs.map fun v => rngOf v (ℓs v)) (rngOf v0 ℓ0) hr0
    (fun r hr => by obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr; exact (hℓs v hv).2)
    (BlockTree.linked_of vs v0 ℓ0 hn0 hlink fun v hv => (hℓs v hv).1)
    (fun r hr => by
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hr
      have q : ∀ k ∈ [7, 11, 15], RunSum.pQ v k = RunSum.pQ v0 k := fun k hk =>
        BlockTree.pQ_congr fun j hj => by
          have : k + j = 7 + (k - 7 + j) := by simp at hk; omega
          rw [this]; exact hch v hv _ (by simp at hk; omega)
      exact ⟨q 7 (by simp), q 11 (by simp), q 15 (by simp)⟩)
  rw [List.map_map, List.map_map, List.map_map] at key
  exact ⟨_, by simp only [rngOf]; positivity, key⟩

/-- `forest_rng` with the size kept positive. -/
theorem forest_rng' (vs : List (ℕ → F)) (v0 : ℕ → F) (h0 : SumOk v0) (hs : ∀ v ∈ vs, SumOk v)
    (hlink : Linked' v0 vs) (hch : ∀ v ∈ vs, ∀ i < 12, v (7 + i) = v0 (7 + i)) :
    ∃ n, 0 < n ∧ RngOk ⟨(v0 0).val, n, RunSum.pQ v0 2 + (vs.map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + (vs.map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11, RunSum.pQ v0 15⟩ :=
  forest_rng'P vs v0 h0 hs hlink hch

/-- **The outer verifier, composed**, for leaves guaranteeing `LeafOutP ok`. -/
theorem forest_soundP {ok : (ℕ → F) → Prop}  (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram (LeafOutP ok)) (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : Tree) (v0 : ℕ → F) (rest : List (Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ RngOkP ok ⟨(v0 0).val, n, RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + ((rest.map Prod.snd).map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11,
      RunSum.pQ v0 15⟩) ∨ Collision := by
  by_cases hc : Collision
  · exact Or.inr hc
  refine Or.inl (forest_rng'P _ v0 ((tree_soundP T hl hn t0 v0 (T.stwoSound _ _ h0)).resolve_right hc) ?_ hlink ?_)
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact (tree_soundP T hl hn tv.1 tv.2 (T.stwoSound _ _ (hs tv htv))).resolve_right hc
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact hch tv htv

/-- **The outer verifier, composed.** Roots `(t₀, v₀), (t₁, v₁), …` (tree shapes as `expected` folds
them, summaries as stored): if the native verifier accepts each root's proof with the expected hash and
the output `sumDigest key v` (`Acc`), consecutive summaries are linked (`(v 0)` of each is the previous
`(v 0) + (v 1)`, `verifyForest`'s range checks) and share the challenge limbs 7–18, then the blocks from
`(v₀ 0)` on form one proven range whose partial sum and input count are the roots' sums (or Blake2s
has a collision). -/
theorem forest_sound (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram LeafOut) (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : Tree) (v0 : ℕ → F) (rest : List (Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ RngOk ⟨(v0 0).val, n, RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + ((rest.map Prod.snd).map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11,
      RunSum.pQ v0 15⟩) ∨ Collision :=
  forest_soundP T hl hn t0 v0 rest h0 hs hlink hch

/-- **The epoch's blocks are proven, per-component sizes.** With block leaves guaranteeing
`LeafOutP BlockPubOk'` (uniform leaves do too: `LeafOut.toV`, `Trust.mono`), `epoch_systems_core`'s block
hypotheses hold with a size per block and component (or Blake2s has a collision). -/
theorem forest_epochV (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram (LeafOutP BlockPubOk'))
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : Tree) (v0 : ℕ → F) (rest : List (Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, ∀ c < 15, L i c ≤ 23) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨ Collision := by
  rcases forest_soundP T hl hn t0 v0 rest h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng' hr hn0⟩
  · exact Or.inr c

/-- **The epoch's blocks are proven.** Under the outer verifier's checks, `epoch_systems_core`'s block
hypotheses hold for the `n ≥ 1` blocks from `(v₀ 0)`, with the roots' summed partial sum (or Blake2s
has a collision). -/
theorem forest_epoch (T : Trust Acc SatC VGates leafH nodeH blockNodeProgram LeafOut) (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : Tree) (v0 : ℕ → F) (rest : List (Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, L i ≤ 23) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨ Collision := by
  rcases forest_soundP (ok := BlockPubOk) T hl hn t0 v0 rest h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng hr hn0⟩
  · exact Or.inr c

end

end StarkedAir.Circuit.BlockRec
