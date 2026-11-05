/-
**The coin-set pass from its root proof, up to a named collision** (`RecCR`'s style for
`SetTree.stree_sound` and `SetPass.set_root_sound`).

`stree_sound` and `set_root_sound` conclude `… ∨ Collision`, which `RecCR.collision_true` makes
vacuous. Here they are restated as `RecCR.tree_soundW`:
- **Witness-explicit named hypotheses**: `RecCR.TrustW` for the set tree (`setNodeProgram`) with the
  leaf guarantee `LeafAtS SegOk d p` (`LeafOkS SegOk d ↔ ∃ p, LeafAtS SegOk d p`): the node assignments
  and the leaves' public inputs are functions of the claimed digest (`nw`, `lw`).
- **The segment tree is computed from the witnesses** (`segOf`), so is every pair the proof compares:
  `spairs` (each node's output digest message and key message against the expected ones, each leaf's
  digest message), `linkPairs` (consecutive segments' outgoing and incoming state vectors) and the
  start and end vectors against the verifier's (`setPairs`). `Collides ps` is a concrete Blake2s
  collision, found by checking the pairs.

- `stree_soundW`: a satisfied set tree circuit (shape `t`, output `sd key v`) has `v` the summary of a
  chain of proven, linked segments over `segOf t v`, or two of `spairs t v` collide;
- `set_root_soundW`: `set_root_sound` from `SatC` (as a hook gives it), the segment tree `segOf t v`
  and `… ∨ Collides (setPairs …)`.
-/
import StarkedAir.SetPass.PassChain
import StarkedAir.Circuit.RecCR

namespace StarkedAir.SetPass

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec StarkedAir.Circuit.SetTree
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.Spec.CoinEpoch (CEv)
open StarkedAir.HeaderTree (limbsOf)
open StarkedAir.Circuit.RecCR (TrustW Collides CollidesAt collides_head collides_second H_eqC keyOf_eqC)
local notation "Word" => Spec.Blake2s.Word

/-! ### Named collisions for the set tree's comparisons -/

/-- `sd_eq`, naming the colliding messages. -/
theorem sd_eqC {k k' : List Word} {v w : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8) (h : sd k v = sd k' w) :
    (k = k' ∧ ∀ i < NS, v i = w i) ∨ CollidesAt (k ++ vals32 v) (k' ++ vals32 w) := by
  rcases H_eqC _ _ h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, vals32_inj e2⟩
  · exact Or.inr c

/-- `vec_of_half`, naming the colliding messages. -/
theorem vec_of_halfC {p q : ℕ → F} {a b : List ℕ} (ha : a.length = NV) (hb : b.length = NV)
    (h : ∀ j < 16, half (H (vecW p a)) j = half (H (vecW q b)) j) :
    (∀ t < NV, p (a.getD t 0) = q (b.getD t 0)) ∨ CollidesAt (vecW p a) (vecW q b) := by
  rcases H_eqC _ _ (half_inj (H_length _) (H_length _) h) with e | c
  · exact Or.inl (vecW_eq ha hb e)
  · exact Or.inr c

/-- A set leaf's guarantee for its public inputs `p`: `LeafOkS SegOk d ↔ ∃ p, LeafAtS SegOk d p`. -/
def LeafAtS (SegOk : (ℕ → F) → Prop) (d : List Word) (p : ℕ → F) : Prop := SegOk p ∧ d = sd zeroKey (summ p)

theorem leafOkS_iff {SegOk : (ℕ → F) → Prop} {d : List Word} : LeafOkS SegOk d ↔ ∃ p, LeafAtS SegOk d p :=
  ⟨fun ⟨p, h1, h2⟩ => ⟨p, h1, h2⟩, fun ⟨p, h1, h2⟩ => ⟨p, h1, h2⟩⟩

/-! ### The segment tree and the pairs, from the witnesses -/

section
variable (leafH : ℕ → List Word) (nodeH : List Word) (nw : List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F)

/-- **The segment tree the witnesses give** for tree shape `t` and summary `v`: at a leaf the leaf's public
inputs for the digest `sd zeroKey v`, at a node (assignment `nw` of its digest) the children's under the
summaries the node gives them. -/
noncomputable def segOf : BlockRec.Tree → (ℕ → F) → SegTree
  | .leaf L, v => .leaf (lw L (sd ((BlockRec.Tree.leaf L).key leafH nodeH) v))
  | .node l r, v =>
    let ρ := nw (sd ((BlockRec.Tree.node l r).key leafH nodeH) v)
    .node (segOf l (SetTree.childSum ρ sC0)) (segOf r (SetTree.childSum ρ sC1))

/-- **The pairs a set tree's soundness compares** (as `RecCR.pairs`). -/
noncomputable def spairs : BlockRec.Tree → (ℕ → F) → List (List Word × List Word)
  | .leaf L, v => [((BlockRec.Tree.leaf L).key leafH nodeH ++ vals32 v,
      zeroKey ++ vals32 (summ (lw L (sd ((BlockRec.Tree.leaf L).key leafH nodeH) v))))]
  | .node l r, v =>
    let ρ := nw (sd ((BlockRec.Tree.node l r).key leafH nodeH) v)
    (wordsOf ρ sKey.res ++ vals32 (SetTree.outSum ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ vals32 v) ::
    (wordsOf ρ sC0.res.chash ++ wordsOf ρ sC0.res.key ++ wordsOf ρ sC1.res.chash ++ wordsOf ρ sC1.res.key,
      l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
    (spairs l (SetTree.childSum ρ sC0) ++ spairs r (SetTree.childSum ρ sC1))

end

/-- **The links' pairs**: each segment's outgoing vector against the next one's incoming vector. -/
def linkPairs : List (ℕ → F) → List (List Word × List Word)
  | p :: q :: ps => (vecW (withOne p) outIdx, vecW q inIdx) :: linkPairs (q :: ps)
  | _ => []

/-! ### The set tree -/

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {SegOk : (ℕ → F) → Prop}
  {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **A set tree is sound, up to a named collision.** A satisfied circuit with the hash and key of tree
shape `t`, outputting `sd key v`, has `v` the summary of a chain of proven, linked segments over the
segment tree `segOf t v` (of shape `t`), or two of `spairs t v` collide. -/
theorem stree_soundW (T : TrustW Acc SatC VGates leafH nodeH setNodeProgram (LeafAtS SegOk) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (v : ℕ → F), SatC (t.hash leafH nodeH) (sd (t.key leafH nodeH) v) →
      ((segOf leafH nodeH nw lw t v).Fits t ∧ ChainT SegOk (segOf leafH nodeH nw lw t v) v) ∨
        Collides (spairs leafH nodeH nw lw t v)
  | .leaf L, v, hs => by
    obtain ⟨hp, hd⟩ := T.leafSound L _ hs
    rcases sd_eqC (BlockRec.Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · refine Or.inl ⟨trivial, by simpa [segOf, SegTree.segs] using hp, List.isChain_singleton _,
        fun hval => ?_, _, _, rfl, rfl, fun j hj => e j (by unfold NS; omega),
        fun j hj => e (16 + j) (by unfold NS; omega)⟩
      rw [rootL_congr e, rootL_summ]
      exact hval _ (by simp [segOf, SegTree.segs])
    · exact Or.inr (by rw [spairs]; exact collides_head c)
  | .node l r, v, hs => by
    obtain ⟨hρ, hres, hg⟩ := T.nodeCircuit _ hs
    set ρ := nw (sd ((BlockRec.Tree.node l r).key leafH nodeH) v) with eρ
    have hseg : segOf leafH nodeH nw lw (.node l r) v =
        .node (segOf leafH nodeH nw lw l (SetTree.childSum ρ sC0)) (segOf leafH nodeH nw lw r (SetTree.childSum ρ sC1)) := by
      rw [segOf]
    have hp : spairs leafH nodeH nw lw (.node l r) v =
        (wordsOf ρ sKey.res ++ vals32 (SetTree.outSum ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ vals32 v) ::
        (wordsOf ρ sC0.res.chash ++ wordsOf ρ sC0.res.key ++ wordsOf ρ sC1.res.chash ++ wordsOf ρ sC1.res.key,
          l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
        (spairs leafH nodeH nw lw l (SetTree.childSum ρ sC0) ++ spairs leafH nodeH nw lw r (SetTree.childSum ρ sC1)) := by
      rw [spairs]
    rw [hseg, hp]
    obtain ⟨r0, hr0, hm0⟩ := shook_mem0
    obtain ⟨r1, hr1, hm1⟩ := shook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0] at s0
    rw [List.drop_left' hr1] at s1
    obtain ⟨h0, h1, -, -, -, -⟩ := snode_parts hρ
    have d0 : wordsOf ρ sC0.res.digest = sd (wordsOf ρ sC0.res.key) (SetTree.childSum ρ sC0) := schild_digest h0
    have d1 : wordsOf ρ sC1.res.digest = sd (wordsOf ρ sC1.res.key) (SetTree.childSum ρ sC1) := schild_digest h1
    rw [d0] at s0
    rw [d1] at s1
    rw [snode_digest hρ] at hres
    have kl : (wordsOf ρ sKey.res).length = 8 := by rw [wordsOf_length]; exact blake2s_length _ _ _
    rcases sd_eqC kl (BlockRec.Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr (collides_head c)
    rw [snode_key hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eqC (w8 _ (schild_chash_length _ _)) (w8 _ (schild_key_length _ _)) (w8 _ (schild_chash_length _ _))
      (by cases l <;> simp [BlockRec.Tree.hash, hl, hn]) (BlockRec.Tree.key_length leafH nodeH l)
      (by cases r <;> simp [BlockRec.Tree.hash, hl, hn]) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr (collides_second c)
    have e1' : wordsOf ρ sC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ sC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ sC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ sC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases stree_soundW T hl hn l _ s0 with ⟨fl, cl⟩ | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    rcases stree_soundW T hl hn r _ s1 with ⟨fr, cr⟩ | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    refine Or.inl ⟨⟨fl, fr⟩, chainT_join cl cr (snode_link hρ) (fun i hi => ?_) ?_⟩
    · rw [← ev i (by unfold NS; omega)]
      simp only [SetTree.outSum, outR, SetTree.childSum]
      split_ifs <;> rfl
    · intro h0 h1'
      rw [← rootL_congr ev]; exact snode_root hρ h0 h1'

end

/-! ### The pass -/

/-- The link of two segments as equal vectors, or their vectors collide. -/
theorem link_vecC {p q : ℕ → F} (h : Links p q) :
    (∀ t < NV, q (fIn t) = withOne p (fOut t)) ∨ CollidesAt (vecW (withOne p) outIdx) (vecW q inIdx) := by
  rcases vec_of_halfC (p := withOne p) (q := q) outIdx_length inIdx_length (fun j hj => by
    have := h j hj
    simp only [summ, if_neg (show ¬ 16 + j < 16 by omega), if_pos (show 16 + j < 32 by omega), if_pos hj,
      show 16 + j - 16 = j by omega] at this
    exact this) with hv | c
  · exact Or.inl fun t ht => by rw [← inIdx_get t ht, ← outIdx_get t ht]; exact (hv t ht).symm
  · exact Or.inr c

/-- **A chain of proven segments folds the pass, up to a named collision** (`pass_chain`). -/
theorem pass_chainW : ∀ (ps : List (ℕ → F)) (p0 : ℕ → F) (s : Spec.SetFile.St QM), (∀ p ∈ p0 :: ps, SegOk p) →
    (p0 :: ps).IsChain Links → EncIn p0 s →
    (∃ (segs : List (ℕ × List CEv)) (pk : ℕ → F), (p0 :: ps).getLast? = some pk ∧
      EncOut pk (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s) ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s).n = s.n ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s).ok = s.ok ∧
      (∀ p ∈ p0 :: ps, RootValid p) ∧ (p0 :: ps).map decodeRoot = Spec.SetMerkle.passRoots s.last segs) ∨
    Collides (linkPairs (p0 :: ps))
  | [], p0, s, hok, _, hin => by
    obtain ⟨seg, hne, hout, hn, hk, -, hv, hd⟩ := seg_step (hok p0 (by simp)) hin
    refine Or.inl ⟨[((p0 PUB_HALF).val, seg)], p0, rfl, by simpa using hout, by simpa using hn, by simpa using hk,
      by simpa using hv, ?_⟩
    simp [Spec.SetMerkle.passRoots, hd]
  | p1 :: ps, p0, s, hok, hc, hin => by
    obtain ⟨seg, hne, hout, hn, hk, hlast, hv, hd⟩ := seg_step (hok p0 (by simp)) hin
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hl, hc'⟩ := hc
    have hlp : linkPairs (p0 :: p1 :: ps) = (vecW (withOne p0) outIdx, vecW p1 inIdx) :: linkPairs (p1 :: ps) := rfl
    rcases link_vecC hl with hv' | c
    swap; · exact Or.inr (by rw [hlp]; exact collides_head c)
    have hfr : Rec.frac p1 = Rec.frac p0 := frac_congr fun t ht => by
      have := hv' t (by unfold NV; omega)
      rw [(f_ch ht).1, (f_ch ht).2, withOne_ne (by unfold NP; omega)] at this
      exact this
    rcases pass_chainW ps p1 _ (fun p hp => hok p (List.mem_cons_of_mem _ hp)) hc' (encIn_of_out hv' hout) with
      ⟨segs, pk, hpk, hout', hn', hk', hval', hroots'⟩ | c
    swap; · exact Or.inr (by rw [hlp]; exact c.mono fun x hx => List.mem_cons_of_mem _ hx)
    rw [hfr] at hout' hn' hk'
    refine Or.inl ⟨((p0 PUB_HALF).val, seg) :: segs, pk, by rw [List.getLast?_cons_cons]; exact hpk, ?_, ?_, ?_,
      ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, List.foldl_append]; exact hout'
    · simp only [List.map_cons, List.flatten_cons, List.foldl_append]; rw [hn', hn]
    · simp only [List.map_cons, List.flatten_cons, List.foldl_append]; rw [hk', hk]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | h
      · exact hv
      · exact hval' p h
    · rw [List.map_cons, hroots', Spec.SetMerkle.passRoots, hd, ← hlast]
      congr 2
      obtain ⟨x, hx⟩ : ∃ x, seg.getLast? = some x := by
        cases h : seg.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) hne
        | some x => exact ⟨x, rfl⟩
      rw [hlast, hx]; rfl

/-- **Every pair the pass's soundness compares**: the tree's (`spairs`), the links' (`linkPairs` over the
segments), the first segment's incoming vector against `pb`'s and `pf`'s outgoing vector against the
last segment's. -/
noncomputable def setPairs (leafH : ℕ → List Word) (nodeH : List Word) (nw : List Word → ℕ → Q)
    (lw : ℕ → List Word → ℕ → F) (t : BlockRec.Tree) (pb pf R : ℕ → F) : List (List Word × List Word) :=
  let τ := segOf leafH nodeH nw lw t (summ2 pb pf R)
  spairs leafH nodeH nw lw t (summ2 pb pf R) ++ linkPairs τ.segs ++
    [(vecW (τ.segs.headD pb) inIdx, vecW pb inIdx), (vecW (withOne pf) outIdx, vecW (withOne (τ.segs.getLastD pf)) outIdx)]

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **The coin-set pass is sound, from its root proof, up to a named collision** (`set_root_sound` from
`SatC`, as a verifier hook gives it). The records `es` (the segments' records in order) fold the pass
from `s0` to a state `pf` encodes, and the root limbs `R` are those of the segment tree `segOf t …` (of
shape `t`) whose leaves are the segments' Merkle roots; or two of `setPairs t pb pf R` collide. -/
theorem set_root_soundW (T : TrustW Acc SatC VGates leafH nodeH setNodeProgram (LeafAtS SegOk) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) (t : BlockRec.Tree) (pb pf R : ℕ → F)
    (s0 : Spec.SetFile.St QM) (hb : EncIn pb s0)
    (hs : SatC (t.hash leafH nodeH) (sd (t.key leafH nodeH) (summ2 pb pf R))) :
    (∃ segs : List (ℕ × List CEv),
      EncOut pf (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0) ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0).n = s0.n ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0).ok = s0.ok ∧
      (segOf leafH nodeH nw lw t (summ2 pb pf R)).Fits t ∧
      (segOf leafH nodeH nw lw t (summ2 pb pf R)).segs.map decodeRoot = Spec.SetMerkle.passRoots s0.last segs ∧
        (List.range 16).map R = limbsOf (segOf leafH nodeH nw lw t (summ2 pb pf R)).root) ∨
      Collides (setPairs leafH nodeH nw lw t pb pf R) := by
  set τ := segOf leafH nodeH nw lw t (summ2 pb pf R) with eτ
  have hsp : setPairs leafH nodeH nw lw t pb pf R = spairs leafH nodeH nw lw t (summ2 pb pf R) ++ linkPairs τ.segs ++
      [(vecW (τ.segs.headD pb) inIdx, vecW pb inIdx),
        (vecW (withOne pf) outIdx, vecW (withOne (τ.segs.getLastD pf)) outIdx)] := rfl
  rw [hsp]
  rcases stree_soundW T hl hn t _ hs with ⟨hfit, hok, hc, hR, p0, pk, h0, hk, hi, ho⟩ | c
  swap; · exact Or.inr (c.mono fun x hx => List.mem_append_left _ (List.mem_append_left _ hx))
  rw [← eτ] at hfit hok hc hR h0 hk
  have hhd : τ.segs.headD pb = p0 := by rw [List.headD_eq_head?_getD, h0]; rfl
  have hld : τ.segs.getLastD pf = pk := by rw [List.getLastD_eq_getLast?, hk]; rfl
  rw [hhd, hld]
  -- the start: `p0`'s incoming vector is `pb`'s
  rcases vec_of_halfC (p := p0) (q := pb) inIdx_length inIdx_length (fun j hj => by
    have := hi j hj
    simp only [summ2, if_pos hj, summ] at this
    exact this.symm) with hv0 | c
  swap; · exact Or.inr ⟨_, List.mem_append_right _ List.mem_cons_self, c⟩
  have hin0 : EncIn p0 s0 := encIn_congr (fun t ht => by rw [← inIdx_get t ht]; exact hv0 t ht) hb
  have hfr : Rec.frac p0 = Rec.frac pb := frac_congr fun t ht => by
    have := hv0 t (by unfold NV; omega)
    rw [inIdx_get t (by unfold NV; omega), (f_ch ht).1] at this
    exact this
  -- the end: `pk`'s outgoing vector is `pf`'s
  rcases vec_of_halfC (p := withOne pf) (q := withOne pk) outIdx_length outIdx_length (fun j hj => by
    have := ho j hj
    simp only [summ2, if_neg (show ¬ 16 + j < 16 by omega), if_pos (show 16 + j < 32 by omega), summ,
      show 16 + j - 16 = j by omega] at this
    exact this) with hvk | c
  swap; · exact Or.inr ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), c⟩
  obtain ⟨rest, hrest⟩ : ∃ rest, τ.segs = p0 :: rest := by
    cases e : τ.segs with
    | nil => rw [e] at h0; simp at h0
    | cons a r => rw [e] at h0; simp at h0; exact ⟨r, by rw [h0]⟩
  rw [hrest] at hok hc hk hR
  rcases pass_chainW rest p0 s0 hok hc hin0 with ⟨segs, pk', hpk', hout, hn', hk', hval, hroots⟩ | c
  swap
  · exact Or.inr (c.mono fun x hx => List.mem_append_left _ (List.mem_append_right _ (by rw [hrest]; exact hx)))
  rw [hk] at hpk'
  cases hpk'
  rw [hfr] at hout hn' hk'
  refine Or.inl ⟨segs, encOut_congr (fun t ht => by rw [← outIdx_get t ht]; exact hvk t ht) hout, hn', hk',
    hfit, by rw [hrest]; exact hroots, ?_⟩
  rw [← hR hval]
  simp only [rootL, summ2]
  exact List.map_congr_left fun j _ => by
    rw [if_neg (by omega), if_neg (by omega), show 32 + j - 32 = j by omega]

end

end StarkedAir.SetPass
