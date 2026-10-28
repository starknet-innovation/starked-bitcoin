/-
**The coin-set pass from its root proof (set-pass step 4).**

- `pass_chain`: a chain of proven, linked segments, the first one's incoming inputs encoding `s`, folds
  the pass from `s` to a state the last one's outgoing inputs encode (one challenge throughout), or
  Blake2s has a collision.
- `set_root_sound`: the native verifier accepts a set tree root (shape `t`) whose summary is the digests
  of `pb`'s incoming vector (the start state `s0` the verifier builds), `pf`'s outgoing vector (the
  final state it is given) and root limbs `R`; then some record list folds the pass from `s0` to a state
  `pf` encodes, the checks holding iff they held in `s0`, and `R` is the root of a segment tree of shape
  `t` over the proven segments, each leaf its segment's public root (or a collision). With
  `SetFile.pass_sound` the final state's `finish` is the file's facts.
-/
import StarkedAir.SetPass.PassRoot
import StarkedAir.SetPass.SegRoot

namespace StarkedAir.SetPass

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec StarkedAir.Circuit.SetTree
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.Spec.CoinEpoch (CEv)
open StarkedAir.HeaderTree (limbsOf)

/-- The link of two segments as equal vectors (or a collision). -/
theorem link_vec {p q : ℕ → F} (h : Links p q) :
    (∀ t < NV, q (fIn t) = withOne p (fOut t)) ∨ Collision := by
  rcases vec_of_half (p := withOne p) (q := q) outIdx_length inIdx_length (fun j hj => by
    have := h j hj
    simp only [summ, if_neg (show ¬ 16 + j < 16 by omega), if_pos (show 16 + j < 32 by omega), if_pos hj,
      show 16 + j - 16 = j by omega] at this
    exact this) with hv | c
  · exact Or.inl fun t ht => by rw [← inIdx_get t ht, ← outIdx_get t ht]; exact (hv t ht).symm
  · exact Or.inr c

/-- **One proven segment**: its records fold the state, and its public root is their Merkle root. -/
theorem seg_step {p0 : ℕ → F} {s : Spec.SetFile.St QM} (hok : SegOk p0) (hin : EncIn p0 s) :
    ∃ seg : List CEv, seg ≠ [] ∧ EncOut p0 (seg.foldl (Spec.SetFile.step [Rec.frac p0]) s) ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac p0]) s).n = s.n ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac p0]) s).ok = s.ok ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac p0]) s).last = seg.getLast? ∧
      RootValid p0 ∧ decodeRoot p0 = Spec.SetMerkle.segRoot (p0 PUB_HALF).val s.last seg := by
  obtain ⟨inst, Ls, hL, hsat, hsz⟩ := hok
  obtain ⟨seg, hne, -, -, hout, hn, hk, hroot⟩ := set_seg_root hL hsat hsz s hin
  have hl : segRootL p0 = limbsOf (Spec.SetMerkle.segRoot (p0 PUB_HALF).val s.last seg) := by
    apply List.ext_getElem (by simp [segRootL, limbsOf])
    intro j h1 _
    have hj : j < 16 := by simpa [segRootL] using h1
    simp only [segRootL, List.getElem_map, List.getElem_range]
    rw [show ROOT0 + j = PUB_ROOT j from rfl, hroot j hj, List.getD_eq_getElem]
  obtain ⟨hd, hv⟩ := decode_of_limbs hl
  exact ⟨seg, hne, hout, hn, hk, (Spec.SetFile.fold_step _ seg s hne).2.2.2.2.2.2.2.1, hv, hd⟩

/-- **A chain of proven segments folds the pass**, and their roots are their records' Merkle roots. -/
theorem pass_chain : ∀ (ps : List (ℕ → F)) (p0 : ℕ → F) (s : Spec.SetFile.St QM), (∀ p ∈ p0 :: ps, SegOk p) →
    (p0 :: ps).IsChain Links → EncIn p0 s →
    (∃ (segs : List (ℕ × List CEv)) (pk : ℕ → F), (p0 :: ps).getLast? = some pk ∧
      EncOut pk (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s) ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s).n = s.n ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac p0]) s).ok = s.ok ∧
      (∀ p ∈ p0 :: ps, RootValid p) ∧ (p0 :: ps).map decodeRoot = Spec.SetMerkle.passRoots s.last segs) ∨
    Collision
  | [], p0, s, hok, _, hin => by
    obtain ⟨seg, hne, hout, hn, hk, -, hv, hd⟩ := seg_step (hok p0 (by simp)) hin
    refine Or.inl ⟨[((p0 PUB_HALF).val, seg)], p0, rfl, by simpa using hout, by simpa using hn, by simpa using hk,
      by simpa using hv, ?_⟩
    simp [Spec.SetMerkle.passRoots, hd]
  | p1 :: ps, p0, s, hok, hc, hin => by
    obtain ⟨seg, hne, hout, hn, hk, hlast, hv, hd⟩ := seg_step (hok p0 (by simp)) hin
    rw [List.isChain_cons_cons] at hc
    obtain ⟨hl, hc'⟩ := hc
    rcases link_vec hl with hv' | c
    swap; · exact Or.inr c
    have hfr : Rec.frac p1 = Rec.frac p0 := frac_congr fun t ht => by
      have := hv' t (by unfold NV; omega)
      rw [(f_ch ht).1, (f_ch ht).2, withOne_ne (by unfold NP; omega)] at this
      exact this
    rcases pass_chain ps p1 _ (fun p hp => hok p (List.mem_cons_of_mem _ hp)) hc' (encIn_of_out hv' hout) with
      ⟨segs, pk, hpk, hout', hn', hk', hval', hroots'⟩ | c
    swap; · exact Or.inr c
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

/-- The summary the verifier expects: the incoming digest of `pb`, the outgoing digest of `pf`, the root
limbs `R`. -/
def summ2 (pb pf R : ℕ → F) (j : ℕ) : F := if j < 16 then summ pb j else if j < 32 then summ pf j else R (j - 32)

section
variable {Acc SatC : List Spec.Blake2s.Word → List Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List Spec.Blake2s.Word}
  {nodeH : List Spec.Blake2s.Word}

/-- **The coin-set pass is sound, from its root proof.** The records `es` (the segments' records in order)
fold the pass from `s0` to a state `pf` encodes, and the root limbs `R` are those of the segment tree of
shape `t` whose leaves are the segments' Merkle roots (`passRoots`). -/
theorem set_root_sound (T : Trust Acc SatC VGates leafH nodeH setNodeProgram (LeafOkS SegOk))
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) (t : BlockRec.Tree) (pb pf R : ℕ → F)
    (s0 : Spec.SetFile.St QM) (hb : EncIn pb s0)
    (hacc : Acc (t.hash leafH nodeH) (sd (t.key leafH nodeH) (summ2 pb pf R))) :
    (∃ segs : List (ℕ × List CEv),
      EncOut pf (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0) ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0).n = s0.n ∧
      (((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [Rec.frac pb]) s0).ok = s0.ok ∧
      ∃ τ : SegTree, τ.Fits t ∧ τ.segs.map decodeRoot = Spec.SetMerkle.passRoots s0.last segs ∧
        (List.range 16).map R = limbsOf τ.root) ∨ Collision := by
  rcases stree_sound T hl hn t _ (T.stwoSound _ _ hacc) with ⟨τ, hfit, hok, hc, hR, p0, pk, h0, hk, hi, ho⟩ | c
  swap; · exact Or.inr c
  -- the start: `p0`'s incoming vector is `pb`'s
  rcases vec_of_half (p := p0) (q := pb) inIdx_length inIdx_length (fun j hj => by
    have := hi j hj
    simp only [summ2, if_pos hj, summ] at this
    exact this.symm) with hv0 | c
  swap; · exact Or.inr c
  have hin0 : EncIn p0 s0 := encIn_congr (fun t ht => by rw [← inIdx_get t ht]; exact hv0 t ht) hb
  have hfr : Rec.frac p0 = Rec.frac pb := frac_congr fun t ht => by
    have := hv0 t (by unfold NV; omega)
    rw [inIdx_get t (by unfold NV; omega), (f_ch ht).1] at this
    exact this
  -- the end: `pk`'s outgoing vector is `pf`'s
  rcases vec_of_half (p := withOne pf) (q := withOne pk) outIdx_length outIdx_length (fun j hj => by
    have := ho j hj
    simp only [summ2, if_neg (show ¬ 16 + j < 16 by omega), if_pos (show 16 + j < 32 by omega), summ,
      show 16 + j - 16 = j by omega] at this
    exact this) with hvk | c
  swap; · exact Or.inr c
  obtain ⟨rest, hrest⟩ : ∃ rest, τ.segs = p0 :: rest := by
    cases e : τ.segs with
    | nil => rw [e] at h0; simp at h0
    | cons a r => rw [e] at h0; simp at h0; exact ⟨r, by rw [h0]⟩
  rw [hrest] at hok hc hk hR
  rcases pass_chain rest p0 s0 hok hc hin0 with ⟨segs, pk', hpk', hout, hn', hk', hval, hroots⟩ | c
  swap; · exact Or.inr c
  rw [hk] at hpk'
  cases hpk'
  rw [hfr] at hout hn' hk'
  refine Or.inl ⟨segs, encOut_congr (fun t ht => by rw [← outIdx_get t ht]; exact hvk t ht) hout, hn', hk',
    τ, hfit, by rw [hrest]; exact hroots, ?_⟩
  rw [← hR hval]
  simp only [rootL, summ2]
  exact List.map_congr_left fun j _ => by
    rw [if_neg (by omega), if_neg (by omega), show 32 + j - 32 = j by omega]

end

end StarkedAir.SetPass
