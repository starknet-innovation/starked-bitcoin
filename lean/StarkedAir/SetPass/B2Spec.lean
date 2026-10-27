/-
**Streaming Blake2s, block by block (the segment system's Blake2s side).** Feeding is associative
(`b2Feed_append`), so a segment's records may be fed one at a time or all at once; and feeding a
segment whose pending-plus-new bytes are `64·m + p` long (`1 ≤ p ≤ 64`) compresses exactly `m` blocks
from the incoming chaining value with counters `t + 64·(b + 1)` (`b2Feed_chain`, in `chainS` form), and
holds back the last `p` bytes.
-/
import StarkedAir.Spec.SetFile
import StarkedAir.Spec.Blake2sBlocks

namespace StarkedAir.Spec.SetFile

open StarkedAir.Spec.Block

/-- Absorbing in two steps is absorbing the concatenation. -/
theorem b2Absorb_append (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) :
    ∀ y, b2Absorb h t (b ++ y) =
      b2Absorb (b2Absorb h t b).h (b2Absorb h t b).t ((b2Absorb h t b).pend ++ y) := by
  induction h, t, b using b2Absorb.induct with
  | case1 h t b hb ih =>
    intro y
    have hl : 64 < (b ++ y).length := by rw [List.length_append]; omega
    have e1 : b2Next h t (b ++ y) = b2Next h t b := by
      unfold b2Next; rw [List.take_append_of_le_length (by omega)]
    rw [b2Absorb_pos hl, b2Absorb_pos hb, e1, List.drop_append_of_le_length (by omega), ih y]
  | case2 h t b hb => intro y; rw [b2Absorb_neg hb]

/-- **Feeding is associative.** -/
theorem b2Feed_append (s : B2) (x y : Bytes) : b2Feed (b2Feed s x) y = b2Feed s (x ++ y) := by
  unfold b2Feed
  rw [← List.append_assoc]
  exact (b2Absorb_append s.h s.t (s.pend ++ x) y).symm

/-- `chainS` reads its starting value at the eight chaining words only. -/
theorem chainS_congr {h h' : ℕ → Blake2s.Word} (hh : ∀ w < 8, h w = h' w) (t : ℕ) (b : Bytes) :
    ∀ i, ∀ w < 8, Blake2s.chainS h t b i w = Blake2s.chainS h' t b i w := by
  intro i
  induction i with
  | zero => exact hh
  | succ i ih =>
    intro w hw
    simp only [Blake2s.chainS, if_pos hw]
    exact Blake2s.compress_congr ih (fun _ _ => rfl) _ _ _ hw

/-- One `b2Next` is `chainS`'s first step. -/
theorem b2Next_eq (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) :
    ∀ w < 8, b2Next h t b w = (fun w => if w < 8 then Blake2s.compress h (Blake2s.wordAt b 0) (t + 64) false w else 0) w := by
  intro w hw
  simp only [b2Next, if_pos hw]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp only [List.getElem_map, List.getElem_range]
  exact Blake2s.compress_congr (fun _ _ => rfl) (fun k hk => Blake2s.leWord_take b k hk) _ _ _ hw

/-- Absorbing `64·m + p` bytes (`1 ≤ p ≤ 64`) compresses `m` blocks and holds back the last `p`. -/
theorem b2Absorb_chain : ∀ (m : ℕ) (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) (p : ℕ), b.length = 64 * m + p →
    1 ≤ p → p ≤ 64 →
    (b2Absorb h t b).t = t + 64 * m ∧ (b2Absorb h t b).pend = b.drop (64 * m) ∧
      ∀ w < 8, (b2Absorb h t b).h w = Blake2s.chainS h t b m w := by
  intro m
  induction m with
  | zero =>
    intro h t b p hl _ hp
    rw [b2Absorb_neg (by omega)]
    exact ⟨by simp, by simp, fun w _ => rfl⟩
  | succ m ih =>
    intro h t b p hl hp1 hp
    rw [b2Absorb_pos (by omega)]
    obtain ⟨ht, hpd, hh⟩ := ih (b2Next h t b) (t + 64) (b.drop 64) p (by simp; omega) hp1 hp
    refine ⟨by rw [ht]; ring, by rw [hpd, List.drop_drop]; congr 1; ring, fun w hw => ?_⟩
    rw [hh w hw, chainS_congr (b2Next_eq h t b) _ _ m w hw]
    exact Blake2s.chainS_shift h t b m w hw

/-- **A segment's Blake2s step.** If the pending and new bytes are `64·m + p` long, `1 ≤ p ≤ 64`, feeding
compresses `m` blocks (`chainS`, counters `t + 64·(b + 1)`) and the last `p` bytes are pending. -/
theorem b2Feed_chain (s : B2) (x : Bytes) (m p : ℕ) (hl : (s.pend ++ x).length = 64 * m + p) (hp1 : 1 ≤ p)
    (hp : p ≤ 64) :
    (b2Feed s x).t = s.t + 64 * m ∧ (b2Feed s x).pend = (s.pend ++ x).drop (64 * m) ∧
      ∀ w < 8, (b2Feed s x).h w = Blake2s.chainS s.h s.t (s.pend ++ x) m w :=
  b2Absorb_chain m s.h s.t _ p hl hp1 hp

end StarkedAir.Spec.SetFile
