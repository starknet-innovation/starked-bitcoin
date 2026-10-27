/-
**The coin-set pass from its root (set-pass step 4), composed.** `pass_chain`: a chain of proven,
linked segments from a state encoded by the first one's incoming inputs folds the pass to a state
encoded by the last one's outgoing inputs (or a Blake2s collision). `set_root_sound`: the root theorem.
-/
import StarkedAir.SetPass.PassSound

namespace StarkedAir.SetPass

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec StarkedAir.Circuit.SetTree
open StarkedAir.Spec.QM31 (QM)

/-- Equal incoming vectors encode the same states. -/
theorem encIn_congr {q r : ℕ → F} {s : Spec.SetFile.St QM} (hv : ∀ t < NV, q (fIn t) = r (fIn t)) (h : EncIn r s) :
    EncIn q s := by
  have get : ∀ t a, t < NV → fIn t = a → q a = r a := fun t a ht ha => by rw [← ha]; exact hv t ht
  have blk := fun t (ht : t < NV) => f_blk (t := t) ht
  have hlast : ∀ j < 36, q (PUB_LAST_IN j) = r (PUB_LAST_IN j) := fun j hj =>
    get (114 + j) _ (by unfold NV; omega) (by rw [((blk _ (by unfold NV; omega)).2.2.1 (by omega) (by omega)).1]; simp [PUB_LAST_IN])
  have h3 : q PUB_HASLAST = r PUB_HASLAST := get 113 _ (by decide) rfl
  refine ⟨?_, ?_, fun j hj => by rw [hlast j hj]; exact h.lastB j hj, ?_, h.maxh_lt, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [get 112 PUB_I_IN (by decide) rfl]; exact h.i
  · rw [h3]
    rcases h.last with ⟨a, b⟩ | ⟨a, p, hp, hok, hk⟩
    · exact Or.inl ⟨a, b⟩
    · exact Or.inr ⟨a, p, hp, hok, fun j hj => by rw [hlast j hj]; exact hk j hj⟩
  · rw [get 150 PUB_MAXH_IN (by decide) rfl]; exact h.maxh
  · have := ((blk (155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)).1
    rw [get (155 + j) _ (by unfold NV; omega) (by rw [this]; simp [PUB_AMT_IN])]; exact h.amtB j hj
  · rw [← h.amt]
    exact Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_range.mp hj
      have := ((blk (155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)).1
      rw [get (155 + j) _ (by unfold NV; omega) (by rw [this]; simp [PUB_AMT_IN])]
  · rw [h.sums]
    congr 1
    refine pQ_congr fun j hj => ?_
    have := ((blk (151 + j) (by unfold NV; omega)).2.2.2.2.1 (by omega) (by omega)).1
    exact (get (151 + j) _ (by unfold NV; omega) (by rw [this]; simp [PUB_SUM_IN])).symm
  · exact encB2_congr (fun j hj => by
      have := ((blk (167 + j) (by unfold NV; omega)).2.2.2.2.2.2.1 (by omega) (by omega)).1
      exact get (167 + j) _ (by unfold NV; omega) (by rw [this]; simp [B2_IN]; try ring)) h.b2
  · exact encSha_congr (fun j hj => by
      have := ((blk (249 + j) (by unfold NV; omega)).2.2.2.2.2.2.2 (by omega)).1
      exact get (249 + j) _ (by unfold NV; omega) (by rw [this]; simp [SHA_IN]; try ring)) h.sha

/-- Equal outgoing vectors encode the same states. -/
theorem encOut_congr {q r : ℕ → F} {s : Spec.SetFile.St QM} (hv : ∀ t < NV, withOne q (fOut t) = withOne r (fOut t))
    (h : EncOut r s) : EncOut q s := by
  have get : ∀ t a, t < NV → t ≠ 113 → fOut t = a → q a = r a := fun t a ht h13 ha => by
    have := hv t ht
    rw [withOne_ne (fOut_ne ht h13), withOne_ne (fOut_ne ht h13)] at this
    rw [← ha]; exact this
  have blk := fun t (ht : t < NV) => f_blk (t := t) ht
  have hlast : ∀ j < 36, q (PUB_LAST_OUT j) = r (PUB_LAST_OUT j) := fun j hj =>
    get (114 + j) _ (by unfold NV; omega) (by omega)
      (by rw [((blk _ (by unfold NV; omega)).2.2.1 (by omega) (by omega)).2]; simp [PUB_LAST_OUT])
  obtain ⟨p, hp, hok, hk⟩ := h.last
  refine ⟨?_, ⟨p, hp, hok, fun j hj => by rw [hlast j hj]; exact hk j hj⟩, ?_, h.maxh_lt, fun j hj => ?_, ?_, ?_, ?_, ?_⟩
  · rw [get 112 PUB_I_OUT (by decide) (by decide) rfl]; exact h.i
  · rw [get 150 PUB_MAXH_OUT (by decide) (by decide) rfl]; exact h.maxh
  · have := ((blk (155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)).2
    rw [get (155 + j) _ (by unfold NV; omega) (by omega) (by rw [this]; simp [PUB_AMT_OUT])]; exact h.amtB j hj
  · rw [← h.amt]
    exact Finset.sum_congr rfl fun j hj => by
      have hj' := Finset.mem_range.mp hj
      have := ((blk (155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)).2
      rw [get (155 + j) _ (by unfold NV; omega) (by omega) (by rw [this]; simp [PUB_AMT_OUT])]
  · rw [h.sums]
    congr 1
    refine pQ_congr fun j hj => ?_
    have := ((blk (151 + j) (by unfold NV; omega)).2.2.2.2.1 (by omega) (by omega)).2
    exact (get (151 + j) _ (by unfold NV; omega) (by omega) (by rw [this]; simp [PUB_SUM_OUT])).symm
  · exact encB2_congr (fun j hj => by
      have := ((blk (167 + j) (by unfold NV; omega)).2.2.2.2.2.2.1 (by omega) (by omega)).2
      exact get (167 + j) _ (by unfold NV; omega) (by omega) (by rw [this]; simp [B2_OUT]; try ring)) h.b2
  · exact encSha_congr (fun j hj => by
      have := ((blk (249 + j) (by unfold NV; omega)).2.2.2.2.2.2.2 (by omega)).2
      exact get (249 + j) _ (by unfold NV; omega) (by omega) (by rw [this]; simp [SHA_OUT]; try ring)) h.sha

/-- The fraction depends only on the challenge's public inputs (41–152). -/
theorem frac_congr {p q : ℕ → F} (h : ∀ t < 112, q (41 + t) = p (41 + t)) : Rec.frac q = Rec.frac p := by
  have g : ∀ a, 41 ≤ a → a < 153 → q a = p a := fun a h1 h2 => by
    have := h (a - 41) (by omega); rwa [show 41 + (a - 41) = a by omega] at this
  have pq : ∀ a, 41 ≤ a → a + 3 < 153 → Block.RunSum.pQ q a = Block.RunSum.pQ p a := fun a h1 h2 => by
    simp only [Block.RunSum.pQ, g a h1 (by omega), g (a + 1) (by omega) (by omega), g (a + 2) (by omega) (by omega),
      g (a + 3) (by omega) (by omega)]
  have hg : Block.FpWalk.gQ q = Block.FpWalk.gQ p := by
    simp only [Block.FpWalk.gQ, Block.FpWalk.PUB_G, g 41 le_rfl (by norm_num), g 42 (by norm_num) (by norm_num),
      g 43 (by norm_num) (by norm_num), g 44 (by norm_num) (by norm_num)]
  funext x
  unfold Rec.frac Block.phiOf
  rw [hg, pq PUB_Z (by decide) (by decide)]
  congr 3
  apply List.map_congr_left
  intro k hk
  have hk' : k < 26 := by simpa [Block.Coin.W] using hk
  rw [pq (Block.Coin.PUB_ALPHA k) (by simp only [Block.Coin.PUB_ALPHA]; omega) (by simp only [Block.Coin.PUB_ALPHA]; omega)]

end StarkedAir.SetPass
