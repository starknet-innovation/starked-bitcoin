/-
Composition of segments (roadmap REC-COMPOSE): two valid segments, where the second's input
state is the first's output state, form one valid segment. Aggregation therefore only has to
check the linking equalities `link`; validity of the whole chain follows by this theorem.
-/
import StarkedAir.Spec.Chain

namespace StarkedAir.Spec.Bitcoin

open StarkedAir.Spec.Sha256

/-- Headers of segment 1 followed by those of segment 2. -/
def catHs (H1 : ℕ) (hs1 hs2 : ℕ → ℕ → Word) : ℕ → ℕ → Word :=
  fun j => if j < H1 then hs1 j else hs2 (j - H1)

/-- Segment 2 starts where segment 1 ends. -/
def Link (H1 : ℕ) (hs1 : ℕ → ℕ → Word) (i1 : SegIn) (o1 : SegOut) (i2 : SegIn) : Prop :=
  i2.prevHash = o1.tip ∧ i2.height = o1.height + 1 ∧ i2.prevNBits = o1.nBits ∧
  i2.prevTime = o1.time ∧ i2.prevPst = o1.pst ∧ i2.window = prevTimes hs1 i1.window H1 ∧
  i2.work = o1.work

theorem pstOf_pre {h0 p H1 : ℕ} (hs1 hs2 : ℕ → ℕ → Word) :
    ∀ k < H1, pstOf h0 p (catHs H1 hs1 hs2) k = pstOf h0 p hs1 k := by
  intro k hk
  induction k with
  | zero => simp [pstOf, catHs, hk]
  | succ k ih => simp only [pstOf, catHs, if_pos hk]; rw [ih (by omega)]

theorem prevTimes_pre {H1 : ℕ} (hs1 hs2 : ℕ → ℕ → Word) (w : List ℕ) :
    ∀ k ≤ H1, prevTimes (catHs H1 hs1 hs2) w k = prevTimes hs1 w k := by
  intro k hk
  unfold prevTimes; congr 1
  refine List.map_congr_left (fun i hi => ?_)
  simp at hi; simp [catHs, show i < H1 by omega]

theorem pstOf_cat {h0 p H1 : ℕ} (hH1 : 0 < H1) (hs1 hs2 : ℕ → ℕ → Word) :
    ∀ j, pstOf h0 p (catHs H1 hs1 hs2) (H1 + j) =
      pstOf (h0 + H1) (pstOf h0 p hs1 (H1 - 1)) hs2 j := by
  intro j
  induction j with
  | zero =>
    obtain ⟨m, rfl⟩ : ∃ m, H1 = m + 1 := ⟨H1 - 1, by omega⟩
    simp only [Nat.add_zero, pstOf, catHs, lt_irrefl, if_false, Nat.sub_self, Nat.add_sub_cancel]
    rw [pstOf_pre hs1 hs2 m (by omega)]
  | succ j ih =>
    rw [show H1 + (j + 1) = (H1 + j) + 1 by ring]
    simp only [pstOf, catHs, show ¬ (H1 + j + 1 < H1) by omega, if_false, show H1 + j + 1 - H1 = j + 1 by omega]
    rw [ih, show h0 + (H1 + j + 1) = h0 + H1 + (j + 1) by ring]

theorem prevTimes_cat (H1 : ℕ) (hs1 hs2 : ℕ → ℕ → Word) (w : List ℕ) :
    ∀ j, prevTimes (catHs H1 hs1 hs2) w (H1 + j) = prevTimes hs2 (prevTimes hs1 w H1) j := by
  intro j
  induction j with
  | zero => rw [Nat.add_zero, prevTimes_pre hs1 hs2 w H1 le_rfl]; simp [prevTimes]
  | succ j ih =>
    have h1 : ∀ (g : ℕ → ℕ → Word) (v : List ℕ) (n : ℕ), prevTimes g v (n + 1) = timeOf (g n) :: prevTimes g v n :=
      fun g v n => by simp [prevTimes, List.range_succ]
    rw [show H1 + (j + 1) = (H1 + j) + 1 by ring, h1, h1, ih]
    simp [catHs, show ¬ (H1 + j < H1) by omega]

/-- **Composition.** Two valid segments joined by `Link` form one valid segment. -/
theorem segment_compose {H1 H2 : ℕ} {hs1 hs2 : ℕ → ℕ → Word} {i1 i2 : SegIn} {o1 o2 : SegOut}
    (v1 : SegmentValid H1 hs1 i1 o1) (v2 : SegmentValid H2 hs2 i2 o2) (l : Link H1 hs1 i1 o1 i2) :
    SegmentValid (H1 + H2) (catHs H1 hs1 hs2) i1 o2 := by
  obtain ⟨p1, pow1, first1, link1, tip1, hb1, oh1, cont1, rt1, mtp1, ver1, nb1, time1, pst1, win1, work1⟩ := v1
  obtain ⟨p2, pow2, first2, link2, tip2, hb2, oh2, cont2, rt2, mtp2, ver2, nb2, time2, pst2, win2, work2⟩ := v2
  obtain ⟨lh, lht, lnb, ltm, lpst, lwin, lwork⟩ := l
  have c1 : ∀ j < H1, catHs H1 hs1 hs2 j = hs1 j := fun j hj => by simp [catHs, hj]
  have c2 : ∀ k, catHs H1 hs1 hs2 (H1 + k) = hs2 k := fun k => by simp [catHs]
  have split : ∀ j, j < H1 + H2 → (j < H1) ∨ (∃ k, k < H2 ∧ j = H1 + k) :=
    fun j hj => by by_cases h : j < H1; exact Or.inl h; exact Or.inr ⟨j - H1, by omega, by omega⟩
  -- Segment 2's height and period start, in segment 1's terms.
  have hh2 : i2.height = i1.height + H1 := by rw [lht, oh1]; omega
  have hp2 : i2.prevPst = pstOf i1.height i1.prevPst hs1 (H1 - 1) := by rw [lpst, pst1]
  have hpc : ∀ k, pstOf i2.height i2.prevPst hs2 k = pstOf i1.height i1.prevPst (catHs H1 hs1 hs2) (H1 + k) :=
    fun k => by rw [pstOf_cat p1, hh2, hp2]
  refine ⟨by omega, fun j hj => ?_, by rw [c1 0 p1]; exact first1, fun j hj hj1 => ?_, ?_, by omega, by omega,
    fun j hj hm => ?_, fun j hj hm hpos => ?_, fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h]; exact pow1 j h
    · rw [c2]; exact pow2 k hk
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h, c1 (j - 1) (by omega)]; exact link1 j h hj1
    · rw [c2]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [Nat.add_zero, c1 (H1 - 1) (by omega), first2, lh, tip1]
      · rw [show H1 + k - 1 = H1 + (k - 1) by omega, c2]; exact link2 k hk hk0
  · rw [tip2, show H1 + H2 - 1 = H1 + (H2 - 1) by omega, c2]
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h, cont1 j h hm]
      by_cases h0 : j = 0
      · simp [h0]
      · rw [if_neg h0, if_neg h0, c1 (j - 1) (by omega)]
    · rw [c2, cont2 k hk (by rw [hh2]; convert hm using 2; omega), if_neg (show H1 + k ≠ 0 by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [if_pos rfl, lnb, nb1, Nat.add_zero, c1 (H1 - 1) (by omega)]
      · rw [if_neg (by omega), show H1 + k - 1 = H1 + (k - 1) by omega, c2]
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h, rt1 j h hm hpos]
      by_cases h0 : j = 0
      · simp [h0]
      · rw [if_neg h0, if_neg h0, if_neg h0, if_neg h0, if_neg h0, if_neg h0, c1 (j - 1) (by omega),
          pstOf_pre hs1 hs2 (j - 1) (by omega)]
    · rw [c2, rt2 k hk (by rw [hh2]; convert hm using 2; omega) (by omega),
        if_neg (show H1 + k ≠ 0 by omega), if_neg (show H1 + k ≠ 0 by omega), if_neg (show H1 + k ≠ 0 by omega)]
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rw [if_pos rfl, if_pos rfl, if_pos rfl, lnb, ltm, hp2, nb1, time1, Nat.add_zero, c1 (H1 - 1) (by omega),
          pstOf_pre hs1 hs2 (H1 - 1) (by omega)]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show H1 + k - 1 = H1 + (k - 1) by omega, c2,
          hpc]
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h, prevTimes_pre hs1 hs2 i1.window j (by omega)]; exact mtp1 j h
    · rw [c2, prevTimes_cat, ← lwin]; exact mtp2 k hk
  · rcases split j hj with h | ⟨k, hk, rfl⟩
    · rw [c1 j h]; exact ver1 j h
    · rw [c2, ← Nat.add_assoc, ← hh2]; exact ver2 k hk
  · rw [nb2, show H1 + H2 - 1 = H1 + (H2 - 1) by omega, c2]
  · rw [time2, show H1 + H2 - 1 = H1 + (H2 - 1) by omega, c2]
  · rw [pst2, show H1 + H2 - 1 = H1 + (H2 - 1) by omega, hpc]
  · rw [win2, show H1 + H2 - 1 = H1 + (H2 - 1) by omega, prevTimes_cat, lwin]
  · rw [work2, lwork, work1, Finset.sum_range_add, add_assoc]
    congr 2
    · exact Finset.sum_congr rfl (fun j hj => by rw [c1 j (by simpa using hj)])
    · exact Finset.sum_congr rfl (fun k _ => by rw [c2])

end StarkedAir.Spec.Bitcoin
