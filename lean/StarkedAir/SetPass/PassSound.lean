/-
**The coin-set pass, from its root proof (set-pass step 4).** A set tree root accepted by the native
verifier (`set_tree.verifyRoot`), under the recursion trust hypotheses (`Trust`, as the block and header
trees), whose summary is the digests of the verifier's start state and of a final state: then some list
of records folds the pass (`SetFile.step`) from the start state to the final state, the checks holding
after iff before (`set_root_sound`), or Blake2s has a collision. With `SetFile.pass_sound`, the final
state's `finish` is then the set file's facts.

The parts: `stree_sound` (a chain of proven, linked segments); a link is equal state vectors, so a
segment's outgoing state is the next one's incoming state (`encIn_of_out`); `set_seg_sound` per segment
(`pass_chain`).
-/
import StarkedAir.SetPass.PassIdx

namespace StarkedAir.SetPass

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec StarkedAir.Circuit.SetTree
open StarkedAir.Spec.QM31 (QM)

/-- A proven segment: a satisfied, balanced segment system below the size bound with public inputs `p`. -/
def SegOk (p : ℕ → F) : Prop :=
  ∃ (inst : ℕ → Inst) (Ls : ℕ → ℕ), (∀ i < 12, (inst i).logSize = Ls i) ∧ segSys.SatisfiedExt inst p [] ∧ SegSizeOk Ls

/-! ### Vector entries -/

theorem f_ch {t : ℕ} (ht : t < 112) : fIn t = 41 + t ∧ fOut t = 41 + t := by
  constructor <;> simp [fIn, fOut, ht]

theorem f_blk {t : ℕ} (ht : t < NV) :
    (t = 112 → fIn t = 1 ∧ fOut t = 2) ∧ (t = 113 → fIn t = 3 ∧ fOut t = NP) ∧
    (114 ≤ t → t < 150 → fIn t = 4 + (t - 114) ∧ fOut t = 186 + (t - 114)) ∧
    (t = 150 → fIn t = 40 ∧ fOut t = 161) ∧ (151 ≤ t → t < 155 → fIn t = 153 + (t - 151) ∧ fOut t = 157 + (t - 151)) ∧
    (155 ≤ t → t < 167 → fIn t = 162 + (t - 155) ∧ fOut t = 174 + (t - 155)) ∧
    (167 ≤ t → t < 249 → fIn t = 222 + (t - 167) ∧ fOut t = 304 + (t - 167)) ∧
    (249 ≤ t → fIn t = 386 + (t - 249) ∧ fOut t = 468 + (t - 249)) := by
  unfold NV at ht
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h => ?_⟩ <;> (constructor <;> (simp only [fIn, fOut]; split_ifs <;> omega))

theorem fOut_ne {t : ℕ} (ht : t < NV) (h : t ≠ 113) : fOut t ≠ NP := by
  unfold NV at ht; unfold NP; simp only [fOut]; split_ifs <;> omega

theorem withOne_ne {p : ℕ → F} {k : ℕ} (h : k ≠ NP) : withOne p k = p k := by simp [withOne, h]

/-! ### Moving a state between equal public values -/

theorem encB2_congr {p q : ℕ → F} {bs bs' : ℕ} {s : Spec.SetFile.B2} (h : ∀ j < 82, q (bs + j) = p (bs' + j))
    (e : EncB2 p bs' s) : EncB2 q bs s := by
  obtain ⟨hl, hn, ht, hp, h64, hb⟩ := e
  refine ⟨fun w hw k hk => ?_, ?_, ?_, ?_, h64, fun j hj => ?_⟩
  · rw [H_LIMB, h _ (by omega)]; exact hl w hw k hk
  · rw [H_NB, h _ (by omega)]; exact hn
  · rw [H_NB, h _ (by omega)]; exact ht
  · rw [H_PLEN, h _ (by omega)]; exact hp
  · rw [H_PEND, Nat.add_assoc, h _ (by omega), ← Nat.add_assoc]; exact hb j hj

theorem encSha_congr {p q : ℕ → F} {bs bs' : ℕ} {s : Spec.SetFile.Sha} (h : ∀ j < 82, q (bs + j) = p (bs' + j))
    (e : EncSha p bs' s) : EncSha q bs s := by
  obtain ⟨hl, hn, hp, hpl, hb⟩ := e
  have h64 : s.pend.length < 64 := by rw [hpl]; exact Nat.mod_lt _ (by norm_num)
  refine ⟨fun w hw k hk => ?_, ?_, ?_, hpl, fun j hj => ?_⟩
  · rw [H_LIMB, h _ (by omega)]; exact hl w hw k hk
  · rw [H_NB, h _ (by omega)]; exact hn
  · rw [H_PLEN, h _ (by omega)]; exact hp
  · rw [H_PEND, Nat.add_assoc, h _ (by omega), ← Nat.add_assoc]; exact hb j hj

theorem keyB_lt (x : Spec.CoinEpoch.CEv) (j : ℕ) : Rec.keyB x j < 256 := by
  unfold Rec.keyB; split_ifs
  · exact UInt8.toNat_lt _
  · exact Nat.mod_lt _ (by norm_num)

theorem pQ_congr {p q : ℕ → F} {a b : ℕ} (h : ∀ j < 4, q (a + j) = p (b + j)) :
    Block.RunSum.pQ q a = Block.RunSum.pQ p b := by
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num)
  simp only [Nat.add_zero] at h0
  simp only [Block.RunSum.pQ, h0, h1, h2, h3]

theorem pubAmt_congr {p q : ℕ → F} (h : ∀ j < 12, q (PUB_AMT_IN j) = p (PUB_AMT_OUT j)) :
    Rec.pubAmt q PUB_AMT_IN = Rec.pubAmt p PUB_AMT_OUT :=
  Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.mp hj)]

/-- **A segment's outgoing state is the next one's incoming state**, when their vectors are equal. -/
theorem encIn_of_out {p q : ℕ → F} {s : Spec.SetFile.St QM} (hv : ∀ t < NV, q (fIn t) = withOne p (fOut t))
    (ho : EncOut p s) : EncIn q s := by
  have v : ∀ t < NV, t ≠ 113 → q (fIn t) = p (fOut t) := fun t ht h => by
    rw [hv t ht, withOne_ne (fOut_ne ht h)]
  have get : ∀ t a b, t < NV → t ≠ 113 → fIn t = a → fOut t = b → q a = p b := fun t a b ht h ha hb => by
    rw [← ha, ← hb]; exact v t ht h
  have hlast : ∀ j < 36, q (PUB_LAST_IN j) = p (PUB_LAST_OUT j) := fun j hj => by
    have := (f_blk (t := 114 + j) (by unfold NV; omega)).2.2.1 (by omega) (by omega)
    exact get (114 + j) _ _ (by unfold NV; omega) (by omega) (by rw [this.1]; simp [PUB_LAST_IN])
      (by rw [this.2]; simp [PUB_LAST_OUT])
  obtain ⟨pk, hpk, hok, hkey⟩ := ho.last
  refine ⟨?_, Or.inr ⟨?_, pk, hpk, hok, fun j hj => by rw [hlast j hj]; exact hkey j hj⟩,
    fun j hj => by rw [hlast j hj, hkey j hj]; exact keyB_lt _ _, ?_, ho.maxh_lt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show PUB_I_IN = fIn 112 by rfl, v 112 (by decide) (by decide), show fOut 112 = PUB_I_OUT by rfl]; exact ho.i
  · have := hv 113 (by decide)
    rw [show fIn 113 = PUB_HASLAST by rfl, show fOut 113 = NP by rfl] at this
    rw [this]; simp [withOne]
  · rw [show PUB_MAXH_IN = fIn 150 by rfl, v 150 (by decide) (by decide), show fOut 150 = PUB_MAXH_OUT by rfl]; exact ho.maxh
  · intro j hj
    have := (f_blk (t := 155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)
    rw [show PUB_AMT_IN j = fIn (155 + j) by rw [this.1]; simp [PUB_AMT_IN],
      v _ (by unfold NV; omega) (by omega), this.2]
    have := ho.amtB j hj; simpa [PUB_AMT_OUT] using this
  · rw [← ho.amt]
    exact pubAmt_congr fun j hj => by
      have := (f_blk (t := 155 + j) (by unfold NV; omega)).2.2.2.2.2.1 (by omega) (by omega)
      exact get (155 + j) _ _ (by unfold NV; omega) (by omega) (by rw [this.1]; simp [PUB_AMT_IN])
        (by rw [this.2]; simp [PUB_AMT_OUT])
  · rw [ho.sums]
    congr 1
    refine (pQ_congr fun j hj => ?_).symm
    have := (f_blk (t := 151 + j) (by unfold NV; omega)).2.2.2.2.1 (by omega) (by omega)
    exact get (151 + j) _ _ (by unfold NV; omega) (by omega) (by rw [this.1]; simp [PUB_SUM_IN]; try ring)
      (by rw [this.2]; simp [PUB_SUM_OUT]; try ring)
  · exact encB2_congr (fun j hj => by
      have := (f_blk (t := 167 + j) (by unfold NV; omega)).2.2.2.2.2.2.1 (by omega) (by omega)
      exact get (167 + j) _ _ (by unfold NV; omega) (by omega) (by rw [this.1]; simp [B2_IN]; try ring)
        (by rw [this.2]; simp [B2_OUT]; try ring)) ho.b2
  · exact encSha_congr (fun j hj => by
      have := (f_blk (t := 249 + j) (by unfold NV; omega)).2.2.2.2.2.2.2 (by omega)
      exact get (249 + j) _ _ (by unfold NV; omega) (by omega) (by rw [this.1]; simp [SHA_IN]; try ring)
        (by rw [this.2]; simp [SHA_OUT]; try ring)) ho.sha

end StarkedAir.SetPass
