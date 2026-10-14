/-
**The wide block node (BLOCK-REC): `2^a` children in one circuit.** Block sizes change from block
to block (the chain survey, 2026-10-14), so packing several block proofs into one leaf circuit would give
a leaf circuit per tuple of sizes. The width goes into the node instead: one circuit verifies `2^a`
child circuit proofs (block leaves or nodes, all of one shared shape, so any mix of block sizes) and
joins their summaries.

`blockNodeK a`: the children's sections (`BlockNode.bchild`, hooks `0 … 2^a − 1`), the balanced join of
their summaries (`joinT`: `BlockNode.nodeOut` at every inner vertex, the binary node's link checks, sums
and root folds), the node key `Blake2s(h₀ ‖ k₀ ‖ … ‖ h_{2^a−1} ‖ k_{2^a−1})`, the output digest
`pubsDigest(K, out)`. Its output summary is what a perfect binary subtree of height `a` over the same
children outputs; only the key differs.

This file proves:
- `joinT_sound`: the join keeps summaries proven (`SumOkP`), by induction from `sumOk_nodeP`;
- `nodeK_sound`: a satisfied wide node over proven children outputs the digest, under the key of its
  children's circuit hashes and keys, of a proven summary; each child's hook checked its digest;
- `treeK_sound`, `forestK_sound`, `forestK_epochV`: the tree and the outer verifier over trees with
  wide nodes (`TreeK`), under the same named hypotheses as `BlockRec.Trust`, per arity. Their
  `∨ Collision` is vacuous (`RecCR.collision_true`); `RecCR.treeK_soundW` and `RecCR.forestK_epochVW`
  name the colliding messages.
-/
import StarkedAir.Circuit.BlockRec

namespace StarkedAir.Circuit.BlockNodeK

open StarkedAir StarkedAir.Circuit StarkedAir.Block Q Spec.Blake2s
open StarkedAir.Circuit.BlockNode
open StarkedAir.Circuit.BlockTree (SumOkP)
open StarkedAir.Circuit.BlockRec

/-! ### The program -/

/-- Child `i`'s section; child `i + 1` starts where child `i` ends. -/
def kid : ℕ → Out ChildRegs
  | 0 => bchild 0 0
  | i + 1 => bchild (kid i).next (i + 1)

/-- Child `i`'s 51 summary registers. -/
def kidRes (i : ℕ) : List ℕ := (List.range NSUM).map (kid i).res.pubs

/-- The balanced join of the summaries of children `s … s + 2^ℓ − 1`, from register `b`. -/
def joinT : ℕ → ℕ → ℕ → Out (List ℕ)
  | 0, s, b => ⟨[], kidRes s, b⟩
  | ℓ + 1, s, b =>
    let L := joinT ℓ s b
    let R := joinT ℓ (s + 2 ^ ℓ) L.next
    let N := BlockNode.nodeOut (fun i => L.res.getD i 0) (fun i => R.res.getD i 0) R.next
    ⟨L.ops ++ R.ops ++ N.ops, N.res, N.next⟩

/-- The children's ops, in order. -/
def kidsOps (c : ℕ) : List Op := (List.range c).flatMap fun i => (kid i).ops

/-- The first register after `c ≥ 1` children. -/
def kidsNext (c : ℕ) : ℕ := (kid (c - 1)).next

/-- The key's message: each child's circuit hash, then its key. -/
def keyMsg (c : ℕ) : List ℕ := (List.range c).flatMap fun i => (kid i).res.chash ++ (kid i).res.key

def kJoin (a : ℕ) : Out (List ℕ) := joinT a 0 (kidsNext (2 ^ a))
def kKey (a : ℕ) : Out (List ℕ) := blake2s (kJoin a).next (keyMsg (2 ^ a)) (64 * 2 ^ a)
def kDigest (a : ℕ) : Out (List ℕ) := pubsDigest (kKey a).next (kKey a).res (kJoin a).res

/-- **The wide block node program** over `2^a` children. Results: the output digest's 8 words. -/
def blockNodeK (a : ℕ) : Program :=
  ⟨s!"block_node_k{a}", kidsOps (2 ^ a) ++ (kJoin a).ops ++ (kKey a).ops ++ (kDigest a).ops, (kDigest a).res⟩

def nodeKJson (a : ℕ) : String := (blockNodeK a).toJson

/-! ### The join -/

variable {ρ : ℕ → Q}

theorem joinT_length : ∀ ℓ s b, (joinT ℓ s b).res.length = NSUM
  | 0, s, b => by simp [joinT, kidRes]
  | ℓ + 1, s, b => by simp [joinT, BlockNode.nodeOut]

theorem list_eq_map_getD (l : List ℕ) : l = (List.range l.length).map (l.getD · 0) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]

/-- **The join keeps summaries proven**, for any per-block statement `ok`. -/
theorem joinT_sound {ok : (ℕ → F) → Prop} : ∀ ℓ s b, Holds ρ (joinT ℓ s b).ops →
    (∀ i < 2 ^ ℓ, SumOkP ok (childSum ρ (kid (s + i)))) →
    SumOkP ok (fun k => (ρ ((joinT ℓ s b).res.getD k 0)).a)
  | 0, s, b, _, hk => by
    apply sumOk_congrP _ (hk 0 (by norm_num))
    intro i hi
    simp [joinT, kidRes, childSum, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  | ℓ + 1, s, b, h, hk => by
    simp only [joinT, holds_append] at h ⊢
    obtain ⟨⟨hL, hR⟩, hN⟩ := h
    have sL := joinT_sound ℓ s b hL (fun i hi => hk i (by rw [pow_succ]; omega))
    have sR := joinT_sound ℓ (s + 2 ^ ℓ) (joinT ℓ s b).next hR (fun i hi => by
      have := hk (2 ^ ℓ + i) (by rw [pow_succ]; omega)
      rwa [← Nat.add_assoc] at this)
    have := BlockTree.sumOk_nodeP hN sL sR
    exact sumOk_congrP (fun i hi => by rw [BlockTree.out_getD i hi]) this

/-! ### Keys -/

/-- The wide node's key: Blake2s over each child's circuit hash and key. -/
def keyOfK (c : ℕ) (hs ks : ℕ → List Word) : List Word := H ((List.range c).flatMap fun i => hs i ++ ks i)

theorem flat_length {c : ℕ} {hs ks : ℕ → List Word} (hh : ∀ i, (hs i).length = 8) (hk : ∀ i, (ks i).length = 8) :
    ((List.range c).flatMap fun i => hs i ++ ks i).length = 16 * c := by
  induction c with
  | zero => simp
  | succ c ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp [hh, hk]; ring

theorem flat_inj : ∀ {c : ℕ} {hs ks hs' ks' : ℕ → List Word}, (∀ i, (hs i).length = 8) → (∀ i, (ks i).length = 8) →
    (∀ i, (hs' i).length = 8) → (∀ i, (ks' i).length = 8) →
    ((List.range c).flatMap fun i => hs i ++ ks i) = ((List.range c).flatMap fun i => hs' i ++ ks' i) →
    ∀ i < c, hs i = hs' i ∧ ks i = ks' i
  | 0, _, _, _, _, _, _, _, _, _ => fun i hi => absurd hi (Nat.not_lt_zero _)
  | c + 1, hs, ks, hs', ks', hh, hk, hh', hk', e => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (by rw [flat_length hh hk, flat_length hh' hk'])
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at e2
    obtain ⟨e3, e4⟩ := List.append_inj e2 (by rw [hh, hh'])
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact flat_inj hh hk hh' hk' e1 i hi
    · exact ⟨e3, e4⟩

/-- Wide keys agree: equal circuit hashes and keys child by child, or a collision. -/
theorem keyOfK_eq {c : ℕ} {hs ks hs' ks' : ℕ → List Word} (hc : 64 * c < 2 ^ 32)
    (hh : ∀ i, (hs i).length = 8) (hk : ∀ i, (ks i).length = 8)
    (hh' : ∀ i, (hs' i).length = 8) (hk' : ∀ i, (ks' i).length = 8)
    (h : keyOfK c hs ks = keyOfK c hs' ks') : (∀ i < c, hs i = hs' i ∧ ks i = ks' i) ∨ Collision := by
  rcases H_eq (by rw [flat_length hh hk]; omega) (by rw [flat_length hh' hk']; omega) h with e | col
  · exact Or.inl (flat_inj hh hk hh' hk' e)
  · exact Or.inr col

/-! ### The program's facts -/

theorem kid_key_length (i : ℕ) : (kid i).res.key.length = 8 := by cases i <;> simp [kid, bchild, guessHash]
theorem kid_chash_length (i : ℕ) : (kid i).res.chash.length = 8 := by cases i <;> simp [kid, bchild]

theorem kid_ops_mem {c i : ℕ} (hi : i < c) {o : Op} (ho : o ∈ (kid i).ops) : o ∈ kidsOps c :=
  List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ho⟩

theorem kid_holds {c i : ℕ} (hi : i < c) (h : Holds ρ (kidsOps c)) : Holds ρ (kid i).ops :=
  fun o ho => h o (kid_ops_mem hi ho)

/-- Child `i`'s hook: args (root ‖ digest), outputs (circuit hash). -/
theorem kid_hook (i : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (kid i).res.digest) (kid i).res.chash ∈ (kid i).ops := by
  cases i with
  | zero => exact bchild_hook 0 0
  | succ i => exact bchild_hook (kid i).next (i + 1)

theorem kid_digest {i : ℕ} (h : Holds ρ (kid i).ops) :
    wordsOf ρ (kid i).res.digest = sumDigest (wordsOf ρ (kid i).res.key) (childSum ρ (kid i)) := by
  cases i with
  | zero => exact bchild_digest h
  | succ i => exact bchild_digest h

theorem keyMsg_words (c : ℕ) : (keyMsg c).map (word ∘ ρ) =
    (List.range c).flatMap fun i => wordsOf ρ (kid i).res.chash ++ wordsOf ρ (kid i).res.key := by
  simp [keyMsg, wordsOf, List.map_flatMap]

theorem nodeK_parts {a : ℕ} (h : Holds ρ (blockNodeK a).ops) :
    Holds ρ (kidsOps (2 ^ a)) ∧ Holds ρ (kJoin a).ops ∧ Holds ρ (kKey a).ops ∧ Holds ρ (kDigest a).ops := by
  simp only [blockNodeK, holds_append] at h
  obtain ⟨⟨⟨h0, hj⟩, hk⟩, hd⟩ := h
  exact ⟨h0, hj, hk, hd⟩

/-- The wide node's output summary. -/
def outSumK (ρ : ℕ → Q) (a : ℕ) : ℕ → F := fun i => (ρ ((kJoin a).res.getD i 0)).a

/-- **The key** of the wide node. -/
theorem nodeK_key {a : ℕ} (ha : a < 26) (h : Holds ρ (blockNodeK a).ops) :
    wordsOf ρ (kKey a).res = keyOfK (2 ^ a) (fun i => wordsOf ρ (kid i).res.chash) (fun i => wordsOf ρ (kid i).res.key) := by
  have hk := (nodeK_parts h).2.2.1
  have hb : 64 * 2 ^ a < 2 ^ 32 := by
    calc 64 * 2 ^ a < 64 * 2 ^ 26 := by gcongr; norm_num
      _ = 2 ^ 32 := by norm_num
  rw [kKey, wordsOf_eq (blake2s_length _ _ _) (blake2s_words hk hb)]
  simp only [keyOfK, H, keyMsg_words]
  rw [flat_length (by simp [wordsOf, kid_chash_length]) (by simp [wordsOf, kid_key_length])]
  ring_nf

/-- **The output digest**: `pubsDigest(K, out)`. -/
theorem nodeK_digest {a : ℕ} (h : Holds ρ (blockNodeK a).ops) :
    wordsOf ρ (blockNodeK a).results = sumDigest (wordsOf ρ (kKey a).res) (outSumK ρ a) := by
  have hd := (nodeK_parts h).2.2.2
  show wordsOf ρ (kDigest a).res = _
  have e : (kJoin a).res = (List.range NSUM).map ((kJoin a).res.getD · 0) := by
    conv_lhs => rw [list_eq_map_getD (kJoin a).res]
    rw [kJoin, joinT_length]
  rw [kDigest, e] at hd ⊢
  exact pubsDigest_sum (blake2s_length _ _ _) hd

/-- **The wide node is sound.** If the program holds and the `2^a` children's summaries are proven, the
node outputs the digest, under the key of its children's circuit hashes and keys, of a proven summary;
each child's hook checked the digest of that child's key and summary. -/
theorem nodeK_sound {ok : (ℕ → F) → Prop} {a : ℕ} (ha : a < 26) (h : Holds ρ (blockNodeK a).ops)
    (hk : ∀ i < 2 ^ a, SumOkP ok (childSum ρ (kid i))) :
    SumOkP ok (outSumK ρ a) ∧
    wordsOf ρ (blockNodeK a).results =
      sumDigest (keyOfK (2 ^ a) (fun i => wordsOf ρ (kid i).res.chash) (fun i => wordsOf ρ (kid i).res.key)) (outSumK ρ a) ∧
    ∀ i < 2 ^ a, wordsOf ρ (kid i).res.digest = sumDigest (wordsOf ρ (kid i).res.key) (childSum ρ (kid i)) := by
  obtain ⟨h0, hj, -, -⟩ := nodeK_parts h
  refine ⟨joinT_sound a 0 _ hj (fun i hi => by simpa using hk i hi), ?_, fun i hi => kid_digest (kid_holds hi h0)⟩
  rw [nodeK_digest h, nodeK_key ha h]

/-! ### Trees with wide nodes, under named hypotheses -/

/-- A recursion tree's shape: block leaves (by block trace size key) and wide nodes of `2^a` children
(children `cs 0 … cs (2^a − 1)`). -/
inductive TreeK where
  | leaf (L : ℕ)
  | node (a : ℕ) (cs : ℕ → TreeK)

section
variable (leafH : ℕ → List Word) (nodeH : ℕ → List Word)

/-- The circuit hash the outer verifier expects at a tree's root. -/
def TreeK.hash : TreeK → List Word
  | .leaf L => leafH L
  | .node a _ => nodeH a

/-- The key the outer verifier expects: zero at a leaf. -/
def TreeK.key : TreeK → List Word
  | .leaf _ => zeroKey
  | .node a cs => keyOfK (2 ^ a) (fun i => (cs i).hash leafH nodeH) (fun i => (cs i).key)

/-- The arities are below `2^26` (the key's message length fits Blake2s's counter). -/
def TreeK.Ok : TreeK → Prop
  | .leaf _ => True
  | .node a cs => a < 26 ∧ ∀ i < 2 ^ a, (cs i).Ok

theorem TreeK.key_length : ∀ t : TreeK, (t.key leafH nodeH).length = 8
  | .leaf _ => by simp [TreeK.key, zeroKey]
  | .node _ _ => by simp [TreeK.key, keyOfK, H_length]

end

/-- **The named hypotheses** (`BlockRec.Trust`), for wide nodes: the node circuit of arity `2^a` has hash
`nodeH a` and runs `blockNodeK a`. -/
structure TrustK (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : ℕ → List Word) (LeafOk : List Word → Prop) : Prop where
  stwoSound : ∀ h d, Acc h d → SatC h d
  nodeCircuit : ∀ a d, SatC (nodeH a) d →
    ∃ ρ, Holds ρ (blockNodeK a).ops ∧ wordsOf ρ (blockNodeK a).results = d ∧ HookGates VGates ρ (blockNodeK a).ops
  recVerifies : ∀ ρ i args outs, VGates ρ i args outs → SatC (wordsOf ρ outs) (wordsOf ρ (args.drop 8))
  leafSound : ∀ L d, SatC (leafH L) d → LeafOk d

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → List Word}

theorem hookK_mem {a i : ℕ} (hi : i < 2 ^ a) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (kid i).res.digest) (kid i).res.chash ∈ (blockNodeK a).ops := by
  obtain ⟨r, hr, hm⟩ := kid_hook i
  exact ⟨r, hr, by simp only [blockNodeK, List.mem_append]; exact Or.inl (Or.inl (Or.inl (kid_ops_mem hi hm)))⟩

/-- **A tree with wide nodes is sound**, for leaves guaranteeing `LeafOutP ok`. A satisfied circuit with
the hash and key of tree shape `t`, outputting `sumDigest key v`, has a proven summary `v` (or Blake2s has
a collision). -/
theorem treeK_soundP {ok : (ℕ → F) → Prop} (T : TrustK Acc SatC VGates leafH nodeH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8) :
    ∀ (t : TreeK), t.Ok → ∀ (v : ℕ → F), SatC (t.hash leafH nodeH) (sumDigest (t.key leafH nodeH) v) → SumOkP ok v ∨ Collision
  | .leaf L, _, v, hs => by
    obtain ⟨p, Hh, hp, hH, h2, hlost, hα, hnin, hlimbs, hd⟩ := T.leafSound L _ hs
    rcases sumDigest_eq (TreeK.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (sumOk_congrP (fun i hi => (e i hi).symm) (BlockTree.sumOk_leafP hp hH h2 hlost hα hnin hlimbs))
    · exact Or.inr c
  | .node a cs, hok, v, hs => by
    by_cases col : Collision
    · exact Or.inr col
    obtain ⟨ha, hok⟩ := hok
    obtain ⟨ρ, hρ, hres, hg⟩ := T.nodeCircuit a _ hs
    obtain ⟨h0, -, -, -⟩ := nodeK_parts hρ
    rw [nodeK_digest hρ] at hres
    have kl : (wordsOf ρ (kKey a).res).length = 8 := by rw [wordsOf_length]; exact blake2s_length _ _ _
    obtain ⟨ek, ev⟩ := (sumDigest_eq kl (TreeK.key_length leafH nodeH (.node a cs)) hres).resolve_right col
    rw [nodeK_key ha hρ] at ek
    have hb : 64 * 2 ^ a < 2 ^ 32 := by
      calc 64 * 2 ^ a < 64 * 2 ^ 26 := by gcongr; norm_num
        _ = 2 ^ 32 := by norm_num
    have hkh : ∀ t : TreeK, (t.hash leafH nodeH).length = 8 := fun t => by cases t <;> simp [TreeK.hash, hl, hn]
    have eks := (keyOfK_eq hb (fun i => by rw [wordsOf_length, kid_chash_length])
      (fun i => by rw [wordsOf_length, kid_key_length]) (fun i => hkh (cs i))
      (fun i => TreeK.key_length leafH nodeH (cs i)) ek).resolve_right col
    have hkids : ∀ i < 2 ^ a, SumOkP ok (childSum ρ (kid i)) := by
      intro i hi
      obtain ⟨r, hr, hm⟩ := hookK_mem (a := a) hi
      have s := T.recVerifies ρ _ _ _ (hg _ _ _ hm)
      rw [List.drop_left' hr, kid_digest (kid_holds hi h0), (eks i hi).1, (eks i hi).2] at s
      exact (treeK_soundP T hl hn (cs i) (hok i hi) _ s).resolve_right col
    exact Or.inl (sumOk_congrP ev (nodeK_sound ha hρ hkids).1)

/-- **The outer verifier, composed**, over trees with wide nodes (`BlockRec.forest_soundP`). -/
theorem forestK_soundP {ok : (ℕ → F) → Prop} (T : TrustK Acc SatC VGates leafH nodeH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8)
    (t0 : TreeK) (v0 : ℕ → F) (rest : List (TreeK × (ℕ → F))) (hok0 : t0.Ok) (hok : ∀ tv ∈ rest, tv.1.Ok)
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : BlockTree.Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ RngOkP ok ⟨(v0 0).val, n, RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + ((rest.map Prod.snd).map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11,
      RunSum.pQ v0 15⟩) ∨ Collision := by
  by_cases hc : Collision
  · exact Or.inr hc
  refine Or.inl (forest_rng'P _ v0 ((treeK_soundP T hl hn t0 hok0 v0 (T.stwoSound _ _ h0)).resolve_right hc) ?_ hlink ?_)
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact (treeK_soundP T hl hn tv.1 (hok tv htv) tv.2 (T.stwoSound _ _ (hs tv htv))).resolve_right hc
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact hch tv htv

/-- **The epoch's blocks are proven, per-component sizes**, over trees with wide nodes
(`BlockRec.forest_epochV`). -/
theorem forestK_epochV (T : TrustK Acc SatC VGates leafH nodeH (LeafOutP BlockPubOk'))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8)
    (t0 : TreeK) (v0 : ℕ → F) (rest : List (TreeK × (ℕ → F))) (hok0 : t0.Ok) (hok : ∀ tv ∈ rest, tv.1.Ok)
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : BlockTree.Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, SizeOk (L i)) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨ Collision := by
  rcases forestK_soundP T hl hn t0 v0 rest hok0 hok h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng' hr hn0⟩
  · exact Or.inr c

end

end StarkedAir.Circuit.BlockNodeK
