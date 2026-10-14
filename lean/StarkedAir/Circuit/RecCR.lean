/-
**Recursion soundness with per-instance collisions (VL-NODE).**

`BlockRec.Collision` (two different word-aligned messages with one Blake2s digest) is provable:
9-word messages outnumber 8-word digests (`collision_true`). So every conclusion `… ∨ Collision` in
`BlockRec`, `HeaderRec` and `BlockNodeK` (`tree_sound`, `forest_sound`, `forest_epoch`, `htree_sound`,
`header_root_sound`, `treeK_soundP`, `forestK_epochV`, …) holds trivially. Those theorems stay (they
are true), but they say nothing.

This file restates them so the collision is one a verifier can exhibit:
- **Witness-explicit named hypotheses** (`TrustW`, `TrustKW`): the node circuit's assignment and the
  leaf's public inputs are *functions* of the claimed digest (`nodeWit`, `leafWit`), what a knowledge
  extractor computes, instead of `∃`. `TrustW.toTrust` and `Trust.exists_w` show this is the same
  hypothesis as `Trust` (by choice), so nothing new is trusted.
- **Conclusions `… ∨ Collides ps`**, where `ps` (`pairs`, `pairsK`, `pairsH`, the forest's) is a finite
  list of message pairs computed from the tree shape, the summaries and the witness functions: the
  pairs the proof compares (each node's output digest message against the expected one, its key
  message against the expected children, and each leaf's digest message). `Collides ps` says one of
  those pairs differs and has one digest: a concrete Blake2s collision, found by checking the pairs.

Read with an efficient extractor as the witness functions, this is the usual reduction: a set of
accepted root proofs for a false statement yields a Blake2s collision. No statement here is provable
without one (unlike `Collision`).
-/
import StarkedAir.Circuit.BlockNodeK
import StarkedAir.Circuit.HeaderRec

namespace StarkedAir.Circuit.RecCR

open StarkedAir StarkedAir.Circuit StarkedAir.Block Q Spec.Blake2s
open StarkedAir.Circuit.BlockTree (SumOkP leafVec Linked')
open StarkedAir.Circuit.BlockRec
open StarkedAir.Circuit.BlockNode

/-! ### `Collision` is vacuous -/

theorem card_lt : Fintype.card (Fin 8 → Word) < Fintype.card (Fin 9 → Word) := by
  have hW : Fintype.card Word = 2 ^ 32 := by
    rw [Fintype.card_congr (BitVec.equivFin (m := 32)).toEquiv, Fintype.card_fin]
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hW]
  exact Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by norm_num)) (by norm_num)

/-- **`Collision` is provable** (pigeonhole): 9-word messages outnumber 8-word digests. Every
`… ∨ Collision` conclusion is therefore trivially true. -/
theorem collision_true : Collision := by
  obtain ⟨x, y, hne, hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun (x : Fin 9 → Word) (i : Fin 8) => (H (List.ofFn x)).getD i 0) card_lt
  refine ⟨List.ofFn x, List.ofFn y, fun e => hne (List.ofFn_injective e), ?_, ?_, ?_⟩
  · rw [List.length_ofFn]; norm_num
  · rw [List.length_ofFn]; norm_num
  · apply List.ext_getElem (by rw [H_length, H_length])
    intro i h1 h2
    have hi : i < 8 := by rw [H_length] at h1; exact h1
    have := congrFun hxy ⟨i, hi⟩
    change (H (List.ofFn x)).getD i 0 = (H (List.ofFn y)).getD i 0 at this
    rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-! ### Collisions among given pairs -/

/-- `a` and `b` differ and have one Blake2s digest. -/
def CollidesAt (a b : List Word) : Prop := a ≠ b ∧ H a = H b

/-- A collision among the message pairs `ps`. -/
def Collides (ps : List (List Word × List Word)) : Prop := ∃ ab ∈ ps, CollidesAt ab.1 ab.2

theorem Collides.mono {ps qs : List (List Word × List Word)} (c : Collides ps) (h : ∀ x ∈ ps, x ∈ qs) :
    Collides qs := by
  obtain ⟨ab, hm, hc⟩ := c
  exact ⟨ab, h ab hm, hc⟩

theorem collides_head {a b : List Word} {ps : List (List Word × List Word)} (c : CollidesAt a b) :
    Collides ((a, b) :: ps) := ⟨(a, b), List.mem_cons_self .., c⟩

theorem collides_second {a b : List Word} {p : List Word × List Word} {ps : List (List Word × List Word)}
    (c : CollidesAt a b) : Collides (p :: (a, b) :: ps) :=
  ⟨(a, b), List.mem_cons_of_mem _ (List.mem_cons_self ..), c⟩

theorem H_eqC (a b : List Word) (h : H a = H b) : a = b ∨ CollidesAt a b := by
  by_cases e : a = b
  · exact Or.inl e
  · exact Or.inr ⟨e, h⟩

/-- `sumDigest_eq`, naming the colliding messages. -/
theorem sumDigest_eqC {k k' : List Word} {v w : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8)
    (h : sumDigest k v = sumDigest k' w) :
    (k = k' ∧ ∀ i < BlockNode.NSUM, v i = w i) ∨ CollidesAt (k ++ vals v) (k' ++ vals w) := by
  rcases H_eqC _ _ h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, vals_inj e2⟩
  · exact Or.inr c

/-- `keyOf_eq`, naming the colliding messages. -/
theorem keyOf_eqC {a b c d a' b' c' d' : List Word} (ha : a.length = 8) (hb : b.length = 8) (hc : c.length = 8)
    (ha' : a'.length = 8) (hb' : b'.length = 8) (hc' : c'.length = 8)
    (h : keyOf a b c d = keyOf a' b' c' d') :
    (a = a' ∧ b = b' ∧ c = c' ∧ d = d') ∨ CollidesAt (a ++ b ++ c ++ d) (a' ++ b' ++ c' ++ d') := by
  rcases H_eqC _ _ h with e | col
  · obtain ⟨e1, e4⟩ := List.append_inj e (by simp [ha, hb, hc, ha', hb', hc'])
    obtain ⟨e1, e3⟩ := List.append_inj e1 (by simp [ha, hb, ha', hb'])
    obtain ⟨e1, e2⟩ := List.append_inj e1 (by rw [ha, ha'])
    exact Or.inl ⟨e1, e2, e3, e4⟩
  · exact Or.inr col

/-! ### Witness-explicit named hypotheses -/

/-- `LeafOutP ok d` for the leaf's public inputs `p`: `LeafOutP ok d ↔ ∃ p, LeafAt ok d p`. -/
def LeafAt (ok : (ℕ → F) → Prop) (d : List Word) (p : ℕ → F) : Prop :=
  ∃ Hh : ℕ, ok p ∧ Hh < 2 ^ 30 ∧ p 2 = (Hh : F) ∧
    p Coin.PUB_LOST = (if Spec.Coins.bip30Lost Hh then 1 else 0) ∧
    (∀ k < Coin.W, RunSum.pQ p (Coin.PUB_ALPHA k) = RunSum.pQ p (Coin.PUB_ALPHA 1) ^ k) ∧
    (p Coin.PUB_NIN).val < 2 ^ 30 ∧ (∀ j < 16, (p (25 + j)).val < 65536) ∧ d = sumDigest zeroKey (leafVec p)

theorem leafOutP_iff {ok : (ℕ → F) → Prop} {d : List Word} : LeafOutP ok d ↔ ∃ p, LeafAt ok d p :=
  ⟨fun ⟨p, Hh, r⟩ => ⟨p, Hh, r⟩, fun ⟨p, Hh, r⟩ => ⟨p, Hh, r⟩⟩

theorem LeafAt.mono {ok ok' : (ℕ → F) → Prop} (hm : ∀ p, ok p → ok' p) {d : List Word} {p : ℕ → F}
    (h : LeafAt ok d p) : LeafAt ok' d p := by
  obtain ⟨Hh, hp, rest⟩ := h
  exact ⟨Hh, hm p hp, rest⟩

/-- **`Trust` with explicit witnesses.** `nodeWit d` is the node circuit's assignment for output `d`
and `leafWit L d` a leaf's public inputs (what an extractor computes from the proofs); the leaf
guarantee `LeafW d p` is about the given `p`. -/
structure TrustW {α : Type} (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : List Word) (prog : Program) (LeafW : List Word → α → Prop)
    (nodeWit : List Word → ℕ → Q) (leafWit : ℕ → List Word → α) : Prop where
  stwoSound : ∀ h d, Acc h d → SatC h d
  nodeCircuit : ∀ d, SatC nodeH d →
    Holds (nodeWit d) prog.ops ∧ wordsOf (nodeWit d) prog.results = d ∧ HookGates VGates (nodeWit d) prog.ops
  recVerifies : ∀ ρ i args outs, VGates ρ i args outs → SatC (wordsOf ρ outs) (wordsOf ρ (args.drop 8))
  leafSound : ∀ L d, SatC (leafH L) d → LeafW d (leafWit L d)

section
variable {α : Type} {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {prog : Program} {LeafW : List Word → α → Prop}

theorem TrustW.toTrust {nw : List Word → ℕ → Q} {lw : ℕ → List Word → α}
    (T : TrustW Acc SatC VGates leafH nodeH prog LeafW nw lw) :
    Trust Acc SatC VGates leafH nodeH prog (fun d => ∃ p, LeafW d p) :=
  ⟨T.stwoSound, fun d h => ⟨nw d, T.nodeCircuit d h⟩, T.recVerifies, fun L d h => ⟨lw L d, T.leafSound L d h⟩⟩

/-- `Trust` gives witness functions (by choice): `TrustW` trusts nothing more. -/
theorem Trust.exists_w [Inhabited α] (T : Trust Acc SatC VGates leafH nodeH prog (fun d => ∃ p, LeafW d p)) :
    ∃ nw lw, TrustW Acc SatC VGates leafH nodeH prog LeafW nw lw := by
  classical
  refine ⟨fun d => if h : SatC nodeH d then Classical.choose (T.nodeCircuit d h) else fun _ => Q.lit 0 0 0 0,
    fun L d => if h : SatC (leafH L) d then Classical.choose (T.leafSound L d h) else default,
    T.stwoSound, fun d h => ?_, T.recVerifies, fun L d h => ?_⟩
  · simp only [dif_pos h]; exact Classical.choose_spec (T.nodeCircuit d h)
  · simp only [dif_pos h]; exact Classical.choose_spec (T.leafSound L d h)

theorem TrustW.mono {LeafW' : List Word → α → Prop} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → α}
    (T : TrustW Acc SatC VGates leafH nodeH prog LeafW nw lw) (hm : ∀ d p, LeafW d p → LeafW' d p) :
    TrustW Acc SatC VGates leafH nodeH prog LeafW' nw lw :=
  ⟨T.stwoSound, T.nodeCircuit, T.recVerifies, fun L d h => hm d _ (T.leafSound L d h)⟩

end

/-! ### The binary block tree -/

/-- **The pairs a block tree's soundness compares**: at a leaf its digest message against the leaf's;
at a node (witness `ρ = nodeWit d` for the expected digest `d`) the output digest message against the
expected one, the key message against the expected children's hashes and keys, then the children's
pairs under the summaries `ρ` gives them. -/
noncomputable def pairs (leafH : ℕ → List Word) (nodeH : List Word) (nw : List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F) :
    BlockRec.Tree → (ℕ → F) → List (List Word × List Word)
  | .leaf L, v => [(zeroKey ++ vals v, zeroKey ++ vals (leafVec (lw L (sumDigest zeroKey v))))]
  | .node l r, v =>
    let ρ := nw (sumDigest ((BlockRec.Tree.node l r).key leafH nodeH) v)
    (wordsOf ρ bKey.res ++ vals (outSum ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ vals v) ::
    (wordsOf ρ bC0.res.chash ++ wordsOf ρ bC0.res.key ++ wordsOf ρ bC1.res.chash ++ wordsOf ρ bC1.res.key,
      l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
    (pairs leafH nodeH nw lw l (childSum ρ bC0) ++ pairs leafH nodeH nw lw r (childSum ρ bC1))

/-- The pairs of a forest's roots. -/
noncomputable def forestPairs (leafH : ℕ → List Word) (nodeH : List Word) (nw : List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F)
    (t0 : BlockRec.Tree) (v0 : ℕ → F) (rest : List (BlockRec.Tree × (ℕ → F))) : List (List Word × List Word) :=
  pairs leafH nodeH nw lw t0 v0 ++ rest.flatMap fun tv => pairs leafH nodeH nw lw tv.1 tv.2

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **A block tree is sound, up to a named collision.** A satisfied circuit with the hash and key of
tree shape `t`, outputting `sumDigest key v`, has a proven summary `v`, or two of `pairs t v` collide. -/
theorem tree_soundW {ok : (ℕ → F) → Prop} (T : TrustW Acc SatC VGates leafH nodeH blockNodeProgram (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (v : ℕ → F), SatC (t.hash leafH nodeH) (sumDigest (t.key leafH nodeH) v) →
      SumOkP ok v ∨ Collides (pairs leafH nodeH nw lw t v)
  | .leaf L, v, hs => by
    obtain ⟨Hh, hp, hH, h2, hlost, hα, hnin, hlimbs, hd⟩ := T.leafSound L _ hs
    rcases sumDigest_eqC (BlockRec.Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (sumOk_congrP (fun i hi => (e i hi).symm) (BlockTree.sumOk_leafP hp hH h2 hlost hα hnin hlimbs))
    · exact Or.inr (collides_head c)
  | .node l r, v, hs => by
    obtain ⟨hρ, hres, hg⟩ := T.nodeCircuit _ hs
    set ρ := nw (sumDigest ((BlockRec.Tree.node l r).key leafH nodeH) v) with eρ
    have hp : pairs leafH nodeH nw lw (.node l r) v =
        (wordsOf ρ bKey.res ++ vals (outSum ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ vals v) ::
        (wordsOf ρ bC0.res.chash ++ wordsOf ρ bC0.res.key ++ wordsOf ρ bC1.res.chash ++ wordsOf ρ bC1.res.key,
          l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
        (pairs leafH nodeH nw lw l (childSum ρ bC0) ++ pairs leafH nodeH nw lw r (childSum ρ bC1)) := by
      rw [pairs]
    rw [hp]
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
    rcases sumDigest_eqC kl (BlockRec.Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr (collides_head c)
    rw [bnode_key hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eqC (w8 _ (bchild_chash_length _ _)) (w8 _ (bchild_key_length _ _)) (w8 _ (bchild_chash_length _ _))
      (by cases l <;> simp [BlockRec.Tree.hash, hl, hn]) (BlockRec.Tree.key_length leafH nodeH l)
      (by cases r <;> simp [BlockRec.Tree.hash, hl, hn]) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr (collides_second c)
    have e1' : wordsOf ρ bC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ bC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ bC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ bC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases tree_soundW T hl hn l _ s0 with sl | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    rcases tree_soundW T hl hn r _ s1 with sr | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    exact Or.inl (sumOk_congrP ev (block_node_soundP hρ sl sr).1)

/-- **The outer verifier, composed, up to a named collision** (`forest_soundP`). -/
theorem forest_soundW {ok : (ℕ → F) → Prop} (T : TrustW Acc SatC VGates leafH nodeH blockNodeProgram (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : BlockRec.Tree) (v0 : ℕ → F) (rest : List (BlockRec.Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ RngOkP ok ⟨(v0 0).val, n, RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + ((rest.map Prod.snd).map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11,
      RunSum.pQ v0 15⟩) ∨ Collides (forestPairs leafH nodeH nw lw t0 v0 rest) := by
  by_cases hc : Collides (forestPairs leafH nodeH nw lw t0 v0 rest)
  · exact Or.inr hc
  have s0 := (tree_soundW T hl hn t0 v0 (T.stwoSound _ _ h0)).resolve_right
    fun c => hc (c.mono fun x hx => List.mem_append_left _ hx)
  refine Or.inl (forest_rng'P _ v0 s0 ?_ hlink ?_)
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact (tree_soundW T hl hn tv.1 tv.2 (T.stwoSound _ _ (hs tv htv))).resolve_right
      fun c => hc (c.mono fun x hx => List.mem_append_right _ (List.mem_flatMap.mpr ⟨tv, htv, hx⟩))
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact hch tv htv

/-- **The epoch's blocks are proven, per-component sizes, up to a named collision** (`forest_epochV`). -/
theorem forest_epochVW (T : TrustW Acc SatC VGates leafH nodeH blockNodeProgram (LeafAt BlockPubOk') nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : BlockRec.Tree) (v0 : ℕ → F) (rest : List (BlockRec.Tree × (ℕ → F)))
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, SizeOk (L i)) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨
      Collides (forestPairs leafH nodeH nw lw t0 v0 rest) := by
  rcases forest_soundW T hl hn t0 v0 rest h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng' hr hn0⟩
  · exact Or.inr c

/-- **The epoch's blocks are proven, up to a named collision** (`forest_epoch`, uniform leaves). -/
theorem forest_epochW (T : TrustW Acc SatC VGates leafH nodeH blockNodeProgram (LeafAt BlockPubOk) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8)
    (t0 : BlockRec.Tree) (v0 : ℕ → F) (rest : List (BlockRec.Tree × (ℕ → F)))
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
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨
      Collides (forestPairs leafH nodeH nw lw t0 v0 rest) := by
  rcases forest_soundW (ok := BlockPubOk) T hl hn t0 v0 rest h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng hr hn0⟩
  · exact Or.inr c

end

/-! ### Trees with wide nodes -/

section
open StarkedAir.Circuit.BlockNodeK

/-- **`TrustK` with explicit witnesses** (`TrustW` per arity). -/
structure TrustKW (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : ℕ → List Word) (LeafW : List Word → (ℕ → F) → Prop)
    (nodeWit : ℕ → List Word → ℕ → Q) (leafWit : ℕ → List Word → ℕ → F) : Prop where
  stwoSound : ∀ h d, Acc h d → SatC h d
  nodeCircuit : ∀ a d, SatC (nodeH a) d →
    Holds (nodeWit a d) (blockNodeK a).ops ∧ wordsOf (nodeWit a d) (blockNodeK a).results = d ∧
      HookGates VGates (nodeWit a d) (blockNodeK a).ops
  recVerifies : ∀ ρ i args outs, VGates ρ i args outs → SatC (wordsOf ρ outs) (wordsOf ρ (args.drop 8))
  leafSound : ∀ L d, SatC (leafH L) d → LeafW d (leafWit L d)

theorem TrustKW.toTrustK {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
    {leafH : ℕ → List Word} {nodeH : ℕ → List Word} {LeafW : List Word → (ℕ → F) → Prop}
    {nw : ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F} (T : TrustKW Acc SatC VGates leafH nodeH LeafW nw lw) :
    TrustK Acc SatC VGates leafH nodeH (fun d => ∃ p, LeafW d p) :=
  ⟨T.stwoSound, fun a d h => ⟨nw a d, T.nodeCircuit a d h⟩, T.recVerifies, fun L d h => ⟨lw L d, T.leafSound L d h⟩⟩

/-- **The pairs a wide tree's soundness compares** (`pairs`, with `2^a` children per node). -/
noncomputable def pairsK (leafH : ℕ → List Word) (nodeH : ℕ → List Word) (nw : ℕ → List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F) :
    TreeK → (ℕ → F) → List (List Word × List Word)
  | .leaf L, v => [(zeroKey ++ vals v, zeroKey ++ vals (leafVec (lw L (sumDigest zeroKey v))))]
  | .node a cs, v =>
    let ρ := nw a (sumDigest ((TreeK.node a cs).key leafH nodeH) v)
    (wordsOf ρ (kKey a).res ++ vals (outSumK ρ a), (TreeK.node a cs).key leafH nodeH ++ vals v) ::
    ((List.range (2 ^ a)).flatMap (fun i => wordsOf ρ (kid i).res.chash ++ wordsOf ρ (kid i).res.key),
      (List.range (2 ^ a)).flatMap (fun i => (cs i).hash leafH nodeH ++ (cs i).key leafH nodeH)) ::
    (List.range (2 ^ a)).flatMap fun i => pairsK leafH nodeH nw lw (cs i) (childSum ρ (kid i))

/-- The pairs of a forest of wide trees. -/
noncomputable def forestPairsK (leafH : ℕ → List Word) (nodeH : ℕ → List Word) (nw : ℕ → List Word → ℕ → Q)
    (lw : ℕ → List Word → ℕ → F) (t0 : TreeK) (v0 : ℕ → F) (rest : List (TreeK × (ℕ → F))) :
    List (List Word × List Word) :=
  pairsK leafH nodeH nw lw t0 v0 ++ rest.flatMap fun tv => pairsK leafH nodeH nw lw tv.1 tv.2

/-- `keyOfK_eq`, naming the colliding messages. -/
theorem keyOfK_eqC {c : ℕ} {hs ks hs' ks' : ℕ → List Word}
    (hh : ∀ i, (hs i).length = 8) (hk : ∀ i, (ks i).length = 8)
    (hh' : ∀ i, (hs' i).length = 8) (hk' : ∀ i, (ks' i).length = 8)
    (h : keyOfK c hs ks = keyOfK c hs' ks') :
    (∀ i < c, hs i = hs' i ∧ ks i = ks' i) ∨
      CollidesAt ((List.range c).flatMap fun i => hs i ++ ks i) ((List.range c).flatMap fun i => hs' i ++ ks' i) := by
  rcases H_eqC _ _ h with e | col
  · exact Or.inl (flat_inj hh hk hh' hk' e)
  · exact Or.inr col

variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → List Word} {nw : ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **A tree with wide nodes is sound, up to a named collision** (`treeK_soundP`). -/
theorem treeK_soundW {ok : (ℕ → F) → Prop} (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8) :
    ∀ (t : TreeK), t.Ok → ∀ (v : ℕ → F), SatC (t.hash leafH nodeH) (sumDigest (t.key leafH nodeH) v) →
      SumOkP ok v ∨ Collides (pairsK leafH nodeH nw lw t v)
  | .leaf L, _, v, hs => by
    obtain ⟨Hh, hp, hH, h2, hlost, hα, hnin, hlimbs, hd⟩ := T.leafSound L _ hs
    rcases sumDigest_eqC (TreeK.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (sumOk_congrP (fun i hi => (e i hi).symm) (BlockTree.sumOk_leafP hp hH h2 hlost hα hnin hlimbs))
    · exact Or.inr (collides_head c)
  | .node a cs, hok, v, hs => by
    obtain ⟨hρ, hres, hg⟩ := T.nodeCircuit a _ hs
    set ρ := nw a (sumDigest ((TreeK.node a cs).key leafH nodeH) v) with eρ
    have hp : pairsK leafH nodeH nw lw (.node a cs) v =
        (wordsOf ρ (kKey a).res ++ vals (outSumK ρ a), (TreeK.node a cs).key leafH nodeH ++ vals v) ::
        ((List.range (2 ^ a)).flatMap (fun i => wordsOf ρ (kid i).res.chash ++ wordsOf ρ (kid i).res.key),
          (List.range (2 ^ a)).flatMap (fun i => (cs i).hash leafH nodeH ++ (cs i).key leafH nodeH)) ::
        (List.range (2 ^ a)).flatMap (fun i => pairsK leafH nodeH nw lw (cs i) (childSum ρ (kid i))) := by
      rw [pairsK]
    rw [hp]
    by_cases col : Collides ((wordsOf ρ (kKey a).res ++ vals (outSumK ρ a), (TreeK.node a cs).key leafH nodeH ++ vals v) ::
        ((List.range (2 ^ a)).flatMap (fun i => wordsOf ρ (kid i).res.chash ++ wordsOf ρ (kid i).res.key),
          (List.range (2 ^ a)).flatMap (fun i => (cs i).hash leafH nodeH ++ (cs i).key leafH nodeH)) ::
        (List.range (2 ^ a)).flatMap (fun i => pairsK leafH nodeH nw lw (cs i) (childSum ρ (kid i))))
    · exact Or.inr col
    obtain ⟨ha, hok⟩ := hok
    obtain ⟨h0, -, -, -⟩ := nodeK_parts hρ
    rw [nodeK_digest hρ] at hres
    have kl : (wordsOf ρ (kKey a).res).length = 8 := by rw [wordsOf_length]; exact blake2s_length _ _ _
    obtain ⟨ek, ev⟩ := (sumDigest_eqC kl (TreeK.key_length leafH nodeH (.node a cs)) hres).resolve_right
      fun c => col (collides_head c)
    rw [nodeK_key ha hρ] at ek
    have hkh : ∀ t : TreeK, (t.hash leafH nodeH).length = 8 := fun t => by cases t <;> simp [TreeK.hash, hl, hn]
    have eks := (keyOfK_eqC (fun i => by rw [wordsOf_length, kid_chash_length])
      (fun i => by rw [wordsOf_length, kid_key_length]) (fun i => hkh (cs i))
      (fun i => TreeK.key_length leafH nodeH (cs i)) ek).resolve_right fun c => col (collides_second c)
    have hkids : ∀ i < 2 ^ a, SumOkP ok (childSum ρ (kid i)) := by
      intro i hi
      obtain ⟨r, hr, hm⟩ := hookK_mem (a := a) hi
      have s := T.recVerifies ρ _ _ _ (hg _ _ _ hm)
      rw [List.drop_left' hr, kid_digest (kid_holds hi h0), (eks i hi).1, (eks i hi).2] at s
      exact (treeK_soundW T hl hn (cs i) (hok i hi) _ s).resolve_right fun c => col (c.mono fun x hx =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩)))
    exact Or.inl (sumOk_congrP ev (nodeK_sound ha hρ hkids).1)

/-- **The outer verifier over wide trees, up to a named collision** (`forestK_soundP`). -/
theorem forestK_soundW {ok : (ℕ → F) → Prop} (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8)
    (t0 : TreeK) (v0 : ℕ → F) (rest : List (TreeK × (ℕ → F))) (hok0 : t0.Ok) (hok : ∀ tv ∈ rest, tv.1.Ok)
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ RngOkP ok ⟨(v0 0).val, n, RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum,
      (v0 6).val + ((rest.map Prod.snd).map fun v => (v 6).val).sum, RunSum.pQ v0 7, RunSum.pQ v0 11,
      RunSum.pQ v0 15⟩) ∨ Collides (forestPairsK leafH nodeH nw lw t0 v0 rest) := by
  by_cases hc : Collides (forestPairsK leafH nodeH nw lw t0 v0 rest)
  · exact Or.inr hc
  have s0 := (treeK_soundW T hl hn t0 hok0 v0 (T.stwoSound _ _ h0)).resolve_right
    fun c => hc (c.mono fun x hx => List.mem_append_left _ hx)
  refine Or.inl (forest_rng'P _ v0 s0 ?_ hlink ?_)
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact (treeK_soundW T hl hn tv.1 (hok tv htv) tv.2 (T.stwoSound _ _ (hs tv htv))).resolve_right
      fun c => hc (c.mono fun x hx => List.mem_append_right _ (List.mem_flatMap.mpr ⟨tv, htv, hx⟩))
  · intro v hv
    obtain ⟨tv, htv, rfl⟩ := List.mem_map.mp hv
    exact hch tv htv

/-- **The epoch's blocks are proven over wide trees, up to a named collision** (`forestK_epochV`). -/
theorem forestK_epochVW (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt BlockPubOk') nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a, (nodeH a).length = 8)
    (t0 : TreeK) (v0 : ℕ → F) (rest : List (TreeK × (ℕ → F))) (hok0 : t0.Ok) (hok : ∀ tv ∈ rest, tv.1.Ok)
    (h0 : Acc (t0.hash leafH nodeH) (sumDigest (t0.key leafH nodeH) v0))
    (hs : ∀ tv ∈ rest, Acc (tv.1.hash leafH nodeH) (sumDigest (tv.1.key leafH nodeH) tv.2))
    (hlink : Linked' v0 (rest.map Prod.snd)) (hch : ∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) :
    (∃ n, 0 < n ∧ ∃ (pub : ℕ → ℕ → F) (inst : ℕ → ℕ → Inst) (L : ℕ → ℕ → ℕ) (_ : ∀ i, Setup (inst i) (pub i) (L i 1)),
      (∀ i < n, ∀ c < 15, (inst i c).logSize = L i c) ∧ (∀ i < n, hashSys.SatisfiedExt (inst i) (pub i) []) ∧
      (∀ i < n, SizeOk (L i)) ∧ (∀ i < n, pub i 2 = (((v0 0).val + i : ℕ) : F)) ∧
      (∀ i < n, pub i Coin.PUB_LOST = if Spec.Coins.bip30Lost ((v0 0).val + i) then 1 else 0) ∧
      (∀ i < n, FpWalk.gQ (pub i) = RunSum.pQ v0 7) ∧ (∀ i < n, RunSum.pQ (pub i) Coin.PUB_Z = RunSum.pQ v0 11) ∧
      (∀ i < n, ∀ k < Coin.W, RunSum.pQ (pub i) (Coin.PUB_ALPHA k) = RunSum.pQ v0 15 ^ k) ∧
      ∑ i ∈ Finset.range n, RunSum.pQ (pub i) Coin.PUB_S =
        RunSum.pQ v0 2 + ((rest.map Prod.snd).map fun v => RunSum.pQ v 2).sum) ∨
      Collides (forestPairsK leafH nodeH nw lw t0 v0 rest) := by
  rcases forestK_soundW T hl hn t0 v0 rest hok0 hok h0 hs hlink hch with ⟨n, hn0, hr⟩ | c
  · exact Or.inl ⟨n, hn0, epoch_hyps_of_rng' hr hn0⟩
  · exact Or.inr c

end

/-! ### The header tree -/

section
open StarkedAir.Circuit.HeaderRec
open StarkedAir.HeaderTree (PubValidT)

/-- `LeafOutH d` for the leaf's public inputs `p`. -/
def LeafAtH (d : List Word) (p : ℕ → F) : Prop := PubValidT p ∧ d = pubDigest zeroKey p

/-- `pubDigest_eq`, naming the colliding messages. -/
theorem pubDigest_eqC {k k' : List Word} {p q : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8)
    (h : pubDigest k p = pubDigest k' q) :
    (k = k' ∧ ∀ i < N_PUB, p i = q i) ∨ CollidesAt (k ++ valsH p) (k' ++ valsH q) := by
  rcases H_eqC _ _ h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, valsH_inj e2⟩
  · exact Or.inr c

/-- **The pairs a header tree's soundness compares** (`pairs`, over `pubDigest`). -/
noncomputable def pairsH (leafH : ℕ → List Word) (nodeH : List Word) (nw : List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F) :
    BlockRec.Tree → (ℕ → F) → List (List Word × List Word)
  | .leaf L, p => [(zeroKey ++ valsH p, zeroKey ++ valsH (lw L (pubDigest zeroKey p)))]
  | .node l r, p =>
    let ρ := nw (pubDigest ((BlockRec.Tree.node l r).key leafH nodeH) p)
    (wordsOf ρ nodeKey.res ++ valsH (StarkedAir.Circuit.nodeOut ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ valsH p) ::
    (wordsOf ρ nodeC0.res.chash ++ wordsOf ρ nodeC0.res.key ++ wordsOf ρ nodeC1.res.chash ++ wordsOf ρ nodeC1.res.key,
      l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
    (pairsH leafH nodeH nw lw l (nodePL ρ) ++ pairsH leafH nodeH nw lw r (nodePR ρ))

variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **A header tree is sound, up to a named collision** (`htree_sound`). -/
theorem htree_soundW (T : TrustW Acc SatC VGates leafH nodeH nodeProgram LeafAtH nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (p : ℕ → F), SatC (t.hash leafH nodeH) (pubDigest (t.key leafH nodeH) p) →
      PubValidT p ∨ Collides (pairsH leafH nodeH nw lw t p)
  | .leaf L, p, hs => by
    obtain ⟨hq, hd⟩ := T.leafSound L _ hs
    rcases pubDigest_eqC (BlockRec.Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (pubValidT_congr (fun i hi => (e i hi).symm) hq)
    · exact Or.inr (collides_head c)
  | .node l r, p, hs => by
    obtain ⟨hρ, hres, hg⟩ := T.nodeCircuit _ hs
    set ρ := nw (pubDigest ((BlockRec.Tree.node l r).key leafH nodeH) p) with eρ
    have hp : pairsH leafH nodeH nw lw (.node l r) p =
        (wordsOf ρ nodeKey.res ++ valsH (StarkedAir.Circuit.nodeOut ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ valsH p) ::
        (wordsOf ρ nodeC0.res.chash ++ wordsOf ρ nodeC0.res.key ++ wordsOf ρ nodeC1.res.chash ++ wordsOf ρ nodeC1.res.key,
          l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
        (pairsH leafH nodeH nw lw l (nodePL ρ) ++ pairsH leafH nodeH nw lw r (nodePR ρ)) := by
      rw [pairsH]
    rw [hp]
    obtain ⟨r0, hr0, hm0⟩ := HeaderRec.hook_mem0
    obtain ⟨r1, hr1, hm1⟩ := HeaderRec.hook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0, hdigest0 hρ] at s0
    rw [List.drop_left' hr1, hdigest1 hρ] at s1
    rw [hdigest hρ] at hres
    have kl : (wordsOf ρ nodeKey.res).length = 8 := by rw [wordsOf_length]; simp [nodeKey, blake2s]
    rcases pubDigest_eqC kl (BlockRec.Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr (collides_head c)
    rw [hkey hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eqC (w8 _ (child_chash_length _ _)) (w8 _ (child_key_length _ _)) (w8 _ (child_chash_length _ _))
      (by cases l <;> simp [BlockRec.Tree.hash, hl, hn]) (BlockRec.Tree.key_length leafH nodeH l)
      (by cases r <;> simp [BlockRec.Tree.hash, hl, hn]) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr (collides_second c)
    have e1' : wordsOf ρ nodeC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ nodeC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ nodeC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ nodeC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases htree_soundW T hl hn l _ s0 with vl | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    rcases htree_soundW T hl hn r _ s1 with vr | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    exact Or.inl (pubValidT_congr ev (node_compose hρ vl vr))

end

section
open StarkedAir.Circuit.HeaderRec
open StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin StarkedAir.Spec.HeaderTree StarkedAir.HeaderTree
variable {Acc SatC : List Spec.Blake2s.Word → List Spec.Blake2s.Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Spec.Blake2s.Word} {nodeH : List Spec.Blake2s.Word} {nw : List Spec.Blake2s.Word → ℕ → Q}
  {lw : ℕ → List Spec.Blake2s.Word → ℕ → F}

/-- **The header tree's outer verifier, up to a named collision** (`header_root_sound`). -/
theorem header_root_soundW (T : TrustW Acc SatC VGates leafH nodeH nodeProgram LeafAtH nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) (t : BlockRec.Tree) (p : ℕ → F)
    (hacc : Acc (t.hash leafH nodeH) (HeaderRec.pubDigest (t.key leafH nodeH) p))
    (hgen : ∀ c ∈ HeaderTree.genesisChecks, (p c.1).val = c.2) :
    (∃ n hs, SegmentValid n hs ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 ∧
      ∃ t : HTree, t.leaves = (List.range n).map (fun j => sha256d (hs j)) ∧ pubT p = limbsOf t.root) ∨
      Collides (pairsH leafH nodeH nw lw t p) := by
  rcases htree_soundW T hl hn t p (T.stwoSound _ _ hacc) with v | c
  · obtain ⟨g1, g2, g3, g4⟩ := HeaderTree.genesis_checks_sound hgen
    exact Or.inl (HeaderTree.chain_from_genesis_T v g1 g2 g3 g4)
  · exact Or.inr c

end

end StarkedAir.Circuit.RecCR
