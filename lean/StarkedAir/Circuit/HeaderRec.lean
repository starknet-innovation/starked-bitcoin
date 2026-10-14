/-
**The header-chain recursion tree, end to end, modulo named hypotheses (VL-NODE).** The header node
circuit is the replay of `nodeProgram` (`Circuit/Gadgets.lean`) with stwo-zig's recursive verifier at
its two hooks (`node.zig` `buildNodeCircuit`, `RecHook`), exactly as the block node (`BlockRec.lean`).
`NodeSound.lean` proves the program's facts (`node_sound`, `node_child_digests`, `node_key`,
`node_digest`); this file composes them with `Trust` (the same named hypotheses as the block tree, with
the leaf guarantee `plain_leaf_valid` + `leaf_digest`):
- `htree_sound`: a satisfied circuit with the hash and key of a tree shape, outputting
  `pubsDigest(key, p)`, has proven public inputs `PubValidT p` (or a Blake2s collision);
- `header_root_sound`: the outer verifier's checks (`node.verifyRoot`: the root's digest under the
  expected key, the genesis checks) give `chain_from_genesis_T`'s conclusion (or a collision).

`Collision` is provable (`RecCR.collision_true`), so the `∨ Collision` forms are vacuous;
`RecCR.htree_soundW` and `RecCR.header_root_soundW` name the colliding messages.
-/
import StarkedAir.Circuit.BlockRec
import StarkedAir.Gadgets.RootChecks

namespace StarkedAir.Circuit.HeaderRec

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec Q Spec.Blake2s
open StarkedAir.HeaderTree (PubValidT)

/-- The 124 public inputs as words. -/
def valsH (p : ℕ → F) : List Word := (List.range N_PUB).map fun k => BitVec.ofNat 32 (p k).val

/-- `pubsDigest(key, p)` (`leaf.pubsDigest`) over the header tree's 124 public inputs. -/
def pubDigest (key : List Word) (p : ℕ → F) : List Word := H (key ++ valsH p)

theorem valsH_length (p : ℕ → F) : (valsH p).length = N_PUB := by simp [valsH]

theorem valsH_inj {p q : ℕ → F} (h : valsH p = valsH q) : ∀ k < N_PUB, p k = q k := by
  intro k hk
  have := congrArg (fun l => l.getD k 0) h
  simp only [valsH, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some] at this
  exact ofNat_val_inj this

theorem pubDigest_eq {k k' : List Word} {p q : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8)
    (h : pubDigest k p = pubDigest k' q) : (k = k' ∧ ∀ i < N_PUB, p i = q i) ∨ Collision := by
  rcases H_eq (by simp [hk, valsH_length, N_PUB]) (by simp [hk', valsH_length, N_PUB]) h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, valsH_inj e2⟩
  · exact Or.inr c

/-- `PubValidT` depends only on the 124 public inputs. -/
theorem pubValidT_congr {p q : ℕ → F} (h : ∀ k < N_PUB, p k = q k) (hp : PubValidT p) : PubValidT q := by
  have hl : HeaderTree.Low p q := fun k hk => h k (by unfold N_PUB; omega)
  have ht : HeaderTree.pubT p = HeaderTree.pubT q :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; unfold N_PUB; omega)
  intro hin
  rw [← HeaderTree.workIn_low hl] at hin
  obtain ⟨o, Hh, hs, f, t, lv, rt⟩ := hp hin
  exact ⟨(HeaderTree.workOut_low hl).mp o, Hh, hs, (HeaderTree.pubSeg_low hl).mp f, t, lv, ht ▸ rt⟩

/-! ### The header node program in word form -/

theorem child_key_length (n i : ℕ) : (child n i).res.key.length = 8 := by simp [child, guessHash]
theorem child_chash_length (n i : ℕ) : (child n i).res.chash.length = 8 := by simp [child]
theorem child_digest_length (n i : ℕ) : (child n i).res.digest.length = 8 := by
  simp [child, pubsDigest, blake2s]

theorem child_hook (n i : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (child n i).res.digest) (child n i).res.chash ∈ (child n i).ops := by
  refine ⟨(guessHash (pubsDigest (guessHash (n + N_PUB) (EXT_CHILD * i + N_PUB)).next
    (guessHash (n + N_PUB) (EXT_CHILD * i + N_PUB)).res ((List.range N_PUB).map (n + ·))).next
    (EXT_CHILD * i + N_PUB + 8)).res, guessHash_length _ _, ?_⟩
  simp [child]

theorem valsOf_map (ρ : ℕ → Q) (f : ℕ → ℕ) :
    valsOf ρ ((List.range N_PUB).map f) = valsH (fun k => (ρ (f k)).a) := by
  simp [valsOf, valsH, List.map_map, Function.comp_def]

theorem hdigest0 {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    wordsOf ρ nodeC0.res.digest = pubDigest (wordsOf ρ nodeC0.res.key) (nodePL ρ) := by
  show wordsOf ρ (child 0 0).res.digest = _
  rw [wordsOf_eq (child_digest_length _ _) (node_child_digests h).1, pubDigest, H, valsOf_map]
  simp only [List.length_append, wordsOf_length, child_key_length, valsH_length, nodeC0]
  rfl

theorem hdigest1 {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    wordsOf ρ nodeC1.res.digest = pubDigest (wordsOf ρ nodeC1.res.key) (nodePR ρ) := by
  show wordsOf ρ (child nodeC0.next 1).res.digest = _
  rw [wordsOf_eq (child_digest_length _ _) (node_child_digests h).2, pubDigest, H, valsOf_map]
  simp only [List.length_append, wordsOf_length, child_key_length, valsH_length, nodeC1]
  rfl

theorem hkey {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    wordsOf ρ nodeKey.res = keyOf (wordsOf ρ nodeC0.res.chash) (wordsOf ρ nodeC0.res.key) (wordsOf ρ nodeC1.res.chash)
      (wordsOf ρ nodeC1.res.key) := by
  rw [wordsOf_eq (by simp [nodeKey, blake2s]) (node_key h), keyOf, H]
  simp only [wordsOf, List.map_append, List.length_append, List.length_map, nodeC0, nodeC1, child_chash_length,
    child_key_length]

theorem nodeOuts_vals (ρ : ℕ → Q) : valsOf ρ nodeOuts = valsH (nodeOut ρ) := by
  apply List.ext_getElem (by simp [valsOf, valsH, nodeOuts])
  intro k h1 _
  have hk : k < N_PUB := by simpa [valsOf, nodeOuts] using h1
  simp only [valsOf, valsH, List.getElem_map, List.getElem_range, nodeOut]
  rw [List.getD_eq_getElem _ _ (by simp [nodeOuts]; exact hk)]

theorem hdigest {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    wordsOf ρ nodeProgram.results = pubDigest (wordsOf ρ nodeKey.res) (nodeOut ρ) := by
  rw [wordsOf_eq (by simp [nodeProgram, nodeDigest, pubsDigest, blake2s]) (node_digest h), pubDigest, H,
    nodeOuts_vals]
  simp only [List.length_append, wordsOf_length, valsH_length]
  rfl

theorem hook_mem0 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 0 (root ++ nodeC0.res.digest) nodeC0.res.chash ∈ nodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := child_hook 0 0
  exact ⟨r, hr, by simp only [nodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm))))⟩

theorem hook_mem1 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 1 (root ++ nodeC1.res.digest) nodeC1.res.chash ∈ nodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := child_hook nodeC0.next 1
  exact ⟨r, hr, by simp only [nodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))⟩

/-! ### The tree -/

/-- A header leaf's guarantee: its output is `pubsDigest(0, p)` with `PubValidT p` (`plain_leaf_valid`,
`leaf_digest`, and the leaf's hook wiring). -/
def LeafOutH (d : List Word) : Prop := ∃ p : ℕ → F, PubValidT p ∧ d = pubDigest zeroKey p

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word}

/-- **A header tree is sound.** -/
theorem htree_sound (T : Trust Acc SatC VGates leafH nodeH nodeProgram LeafOutH) (hl : ∀ L, (leafH L).length = 8)
    (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (p : ℕ → F), SatC (t.hash leafH nodeH) (pubDigest (t.key leafH nodeH) p) → PubValidT p ∨ Collision
  | .leaf L, p, hs => by
    obtain ⟨q, hq, hd⟩ := T.leafSound L _ hs
    rcases pubDigest_eq (Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (pubValidT_congr (fun i hi => (e i hi).symm) hq)
    · exact Or.inr c
  | .node l r, p, hs => by
    obtain ⟨ρ, hρ, hres, hg⟩ := T.nodeCircuit _ hs
    obtain ⟨r0, hr0, hm0⟩ := hook_mem0
    obtain ⟨r1, hr1, hm1⟩ := hook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0, hdigest0 hρ] at s0
    rw [List.drop_left' hr1, hdigest1 hρ] at s1
    rw [hdigest hρ] at hres
    have kl : (wordsOf ρ nodeKey.res).length = 8 := by rw [wordsOf_length]; simp [nodeKey, blake2s]
    rcases pubDigest_eq kl (Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr c
    rw [hkey hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eq (w8 _ (child_chash_length _ _)) (w8 _ (child_key_length _ _)) (w8 _ (child_chash_length _ _))
      (w8 _ (child_key_length _ _)) (by cases l <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH l)
      (by cases r <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH r) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr c
    have e1' : wordsOf ρ nodeC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ nodeC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ nodeC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ nodeC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases htree_sound T hl hn l _ s0 with vl | c
    swap; · exact Or.inr c
    rcases htree_sound T hl hn r _ s1 with vr | c
    swap; · exact Or.inr c
    exact Or.inl (pubValidT_congr ev (node_compose hρ vl vr))

end

section
open StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin StarkedAir.Spec.HeaderTree StarkedAir.HeaderTree
variable {Acc SatC : List Spec.Blake2s.Word → List Spec.Blake2s.Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Spec.Blake2s.Word} {nodeH : List Spec.Blake2s.Word}

/-- **The header tree's outer verifier, composed** (`node.verifyRoot`): the native verifier accepts the
root proof with the expected hash and the digest of the expected key and `p`, and `p` passes the
genesis checks (`genesisChecks`, Lean-exported): then the headers form a valid chain from genesis to
the tip `p` states, with its block-hash tree root (or Blake2s has a collision). -/
theorem header_root_sound (T : Trust Acc SatC VGates leafH nodeH nodeProgram LeafOutH)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) (t : BlockRec.Tree) (p : ℕ → F)
    (hacc : Acc (t.hash leafH nodeH) (HeaderRec.pubDigest (t.key leafH nodeH) p))
    (hgen : ∀ c ∈ HeaderTree.genesisChecks, (p c.1).val = c.2) :
    (∃ n hs, SegmentValid n hs ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 ∧
      ∃ t : HTree, t.leaves = (List.range n).map (fun j => sha256d (hs j)) ∧ pubT p = limbsOf t.root) ∨ Collision := by
  rcases htree_sound T hl hn t p (T.stwoSound _ _ hacc) with v | c
  · obtain ⟨g1, g2, g3, g4⟩ := HeaderTree.genesis_checks_sound hgen
    exact Or.inl (HeaderTree.chain_from_genesis_T v g1 g2 g3 g4)
  · exact Or.inr c

end

end StarkedAir.Circuit.HeaderRec
