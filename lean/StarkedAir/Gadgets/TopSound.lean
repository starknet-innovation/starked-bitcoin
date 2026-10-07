/-
**Header-chain soundness (top level).** Any trace satisfying the header-chain AIR proves
`SegmentValid` (Spec/Chain.lean) for its headers and its decoded public inputs, given the two
verifier obligations on the inputs: the window inputs are the real predecessor times padded
with the sentinel, and the input-work limbs are 16-bit.
-/
import StarkedAir.Gadgets.VersionSound
import StarkedAir.Spec.Chain

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-- The median-time-past window inputs (`T_1..T_11` of the first header), numeric. -/
def pubWindow (pub : ℕ → F) : List ℕ :=
  leN (pubWord pub 44) :: (List.range 10).map fun k => leN (pubWord pub (48 + 2 * k))

/-- The segment's input, decoded from public inputs (the real window is supplied separately). -/
def decodeIn (pub : ℕ → F) (realWindow : List ℕ) : SegIn where
  prevHash := pubState pub 0
  height := (pubWord pub 32).toNat
  prevNBits := leN (pubWord pub 34)
  prevTime := leN (pubWord pub 44)
  prevPst := leN (pubWord pub 36)
  window := realWindow
  work := pubWork pub 88

/-- The segment's output, decoded from public inputs. -/
def decodeOut (pub : ℕ → F) : SegOut where
  tip := pubState pub 16
  height := (pubWord pub 38).toNat
  nBits := leN (pubWord pub 40)
  time := leN (pubWord pub 46)
  pst := leN (pubWord pub 42)
  window := (List.range 10).map fun k => leN (pubWord pub (68 + 2 * k))
  work := pubWork pub 98

/-- Numeric window of header `j`. -/
def winNum (main : ℕ → ℕ → F) (j : ℕ) : List ℕ := (List.range 11).map fun k => leN (winAt main j (k + 1))

theorem take_append_take (a b : List ℕ) (n m : ℕ) (h : n ≤ a.length + m) :
    (a ++ b.take m).take n = (a ++ b).take n := by
  rw [List.take_append, List.take_append, List.take_take]
  congr 2; omega

section Top

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
include hsat

/-- The last header's own time is public (inputs 46/47). -/
theorem out_time {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hlast : 2 ^ logSize = 256 * (j + 1)) :
    headerWord main j 17 = pubWord pub 46 := by
  have hr : 256 * j + 220 < 2 ^ logSize := by omega
  have hP : (pre PREV).eval (2 ^ logSize) preCols pub main (256 * j + 220) = 1 := by
    rw [eval_oneRow (show preCols.getD PREV (.periodic [0]) = oneRow 220 from rfl) hr,
      show (256 * j + 220) % 256 = 220 by omega]; simp
  have hL : (pre LAST).eval (2 ^ logSize) preCols pub main (256 * j + 220) = 1 := by
    rw [eval_last hr]; simp; omega
  have e : ∀ h ≤ 1, ((half16 (word main W (256 * j + 77)) h : ℕ) : F) = pub (46 + h) := fun h hh => by
    have := copy_sat hsat hj hh _ (show Expr.mul (.mul (pre PREV) (pre LAST)) (.sub (limb W h (-143)) (.pub (46 + h)))
      ∈ copyFam h by simp [copyFam])
    have hw : wrap (2 ^ logSize) (256 * j + 220) (-143) = 256 * j + 77 := by
      have := wrapN (N := 2 ^ logSize) (k := 143) (show 143 ≤ 256 * j + 220 by omega) hr
      simp only [Nat.cast_ofNat] at this; rw [this]; omega
    rw [eval_mul', eval_mul', hP, hL, one_mul, one_mul, eval_sub',
      eval_limb hw (bits (chainSat_of hsat) (by omega) (by decide)) hh] at this
    exact sub_eq_zero.mp this
  rw [show headerWord main j 17 = word main W (256 * j + 77) by simp [headerWord]]
  exact word_of_pubs (by simpa using e 0 (by norm_num)) (e 1 (by norm_num))

/-- The trace's period-start time is `pstOf`. -/
theorem pst_eq (hlog : 8 ≤ logSize) :
    ∀ j < 2 ^ logSize / 256, leN (pstAt main j) =
      pstOf (pubWord pub 32).toNat (leN (pubWord pub 36)) (headerWord main) j := by
  obtain ⟨-, h0, hstep, -, hpst, -⟩ := state_sound hsat hlog
  have hh : ∀ j < 2 ^ logSize / 256, heightAt main j = (pubWord pub 32).toNat + j := by
    intro j hj
    induction j with
    | zero => simpa using h0
    | succ j ih => rw [hstep (j + 1) hj (by omega), show j + 1 - 1 = j by omega, ih (by omega)]; ring
  intro j hj
  induction j with
  | zero =>
    rw [hpst 0 hj, hh 0 hj]
    simp only [pstOf, add_zero, if_true]
    split <;> rfl
  | succ j ih =>
    rw [hpst (j + 1) hj, hh (j + 1) hj]
    simp only [pstOf, show j + 1 ≠ 0 by omega, if_false]
    split
    · rfl
    · simp only [Nat.add_sub_cancel]; exact ih (by omega)

omit hsat in
theorem hj_of (hlog : 8 ≤ logSize) {j : ℕ} (hj : j < 2 ^ logSize / 256) : 256 * (j + 1) ≤ 2 ^ logSize := by
  have h256 : 256 ∣ 2 ^ logSize := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num]; exact pow_dvd_pow 2 hlog
  obtain ⟨c, hc⟩ := h256
  rw [hc, Nat.mul_div_cancel_left _ (by norm_num)] at hj; rw [hc]; omega

/-- Times of the segment's headers before `j`, newest first. -/
def segTimes (main : ℕ → ℕ → F) (j : ℕ) : List ℕ := (List.range j).reverse.map fun i => timeOf (headerWord main i)

omit hsat in
theorem segTimes_succ (j : ℕ) : segTimes main (j + 1) = timeOf (headerWord main j) :: segTimes main j := by
  simp [segTimes, List.range_succ]

/-- Each header's window is the segment's earlier times followed by the window inputs. -/
theorem win_eq (hlog : 8 ≤ logSize) :
    ∀ j < 2 ^ logSize / 256, winNum main j = (segTimes main j ++ pubWindow pub).take 11 := by
  have hjj : ∀ j < 2 ^ logSize / 256, 256 * (j + 1) ≤ 2 ^ logSize := fun j hj => hj_of hlog hj
  intro j hj
  induction j with
  | zero =>
    obtain ⟨h1, hrest⟩ := mtp_window hsat (hjj 0 hj)
    have hlen : (pubWindow pub).length = 11 := by simp [pubWindow]
    simp only [segTimes, List.range_zero, List.reverse_nil, List.map_nil, List.nil_append,
      List.take_of_length_le (le_of_eq hlen)]
    apply List.ext_getElem (by simp [winNum, hlen])
    intro k hk1 hk2
    simp only [winNum, List.length_map, List.length_range] at hk1
    simp only [winNum, List.getElem_map, List.getElem_range, pubWindow]
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [h1, prevTime]
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      rw [hrest (i + 1) (by omega) (by omega)]
      simp
  | succ j ih =>
    obtain ⟨h1, hrest⟩ := mtp_window hsat (hjj (j + 1) hj)
    have h10 : (segTimes main j ++ pubWindow pub).take 10 = (winNum main j).take 10 := by
      rw [ih (by omega), List.take_take]; simp
    rw [segTimes_succ, List.cons_append, List.take_succ_cons, h10]
    apply List.ext_getElem (by simp [winNum])
    intro k hk1 hk2
    simp only [winNum, List.length_map, List.length_range] at hk1
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp [winNum, h1, prevTime, timeOf_eq]
    · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
      simp only [winNum, List.getElem_map, List.getElem_range, List.getElem_cons_succ, List.getElem_take]
      rw [hrest (i + 1) (by omega) (by omega), if_neg (by omega)]
      simp

/-- Chainwork after header `j`: the input work plus each header's `GetBlockProof`. -/
theorem work_eq (hlog : 8 ≤ logSize) (hwork : ∀ l < 10, (pub (88 + l)).val < 65536) :
    ∀ j < 2 ^ logSize / 256, workAt main j =
      pubWork pub 88 + ∑ i ∈ Finset.range (j + 1), blockProof (nBitsOf (headerWord main i)) := by
  have hjj : ∀ j < 2 ^ logSize / 256, 256 * (j + 1) ≤ 2 ^ logSize := fun j hj => hj_of hlog hj
  intro j hj
  induction j with
  | zero =>
    rw [work_step hsat (hjj 0 hj) (fun _ => hwork), if_pos rfl]; simp
  | succ j ih =>
    rw [work_step hsat (hjj (j + 1) hj) (fun h => absurd h (by omega)), if_neg (by omega),
      show j + 1 - 1 = j by omega, ih (by omega), Finset.sum_range_succ (n := j + 1)]
    ring

theorem height_eq (hlog : 8 ≤ logSize) :
    ∀ j < 2 ^ logSize / 256, heightAt main j = (pubWord pub 32).toNat + j := by
  obtain ⟨-, h0, hstep, -⟩ := state_sound hsat hlog
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih => rw [hstep (j + 1) hj (by omega), show j + 1 - 1 = j by omega, ih (by omega)]; ring

/-- **Header-chain soundness.** A trace satisfying the header-chain AIR with `2^logSize` rows
proves a valid segment of `2^logSize / 256` mainnet headers, from the decoded input state to the
decoded output state. Obligations on the public inputs: the window inputs are the real
predecessor times padded with the sentinel (`hwin`), and the input-work limbs are 16-bit. -/
theorem header_chain_sound (hlog : 8 ≤ logSize) (realWindow : List ℕ)
    (hwin : pubWindow pub = (realWindow ++ sentinel).take 11)
    (hwork : ∀ l < 10, (pub (88 + l)).val < 65536) :
    SegmentValid (2 ^ logSize / 256) (headerWord main) (decodeIn pub realWindow) (decodeOut pub) := by
  have h256 : 256 ≤ 2 ^ logSize := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ logSize := Nat.pow_le_pow_right (by norm_num) hlog
  have hH : 0 < 2 ^ logSize / 256 := Nat.div_pos h256 (by norm_num)
  have hlast : 2 ^ logSize = 256 * (2 ^ logSize / 256 - 1 + 1) := by
    rw [Nat.sub_add_cancel hH]
    exact (Nat.mul_div_cancel' (by rw [show (256 : ℕ) = 2 ^ 8 by norm_num]; exact pow_dvd_pow 2 hlog)).symm
  have hHl : 2 ^ logSize / 256 - 1 < 2 ^ logSize / 256 := by omega
  obtain ⟨hhash, hlink, hfirst, htip⟩ := chain_sound_v2 hsat hlog
  obtain ⟨hbound, -, -, hcont, -, hout_h, hout_nb, hout_pst⟩ := state_sound hsat hlog
  have hh := height_eq hsat hlog
  unfold SegmentValid
  dsimp only [decodeIn, decodeOut]
  refine ⟨hH, fun j hj => ?_, hfirst, fun j hj h1 => ?_, ?_, ?_, ?_, fun j hj hm => ?_, fun j hj hm hpos => ?_,
    fun j hj => ?_, fun j hj => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hhash j hj).1]; exact (hhash j hj).2
  · rw [hlink j hj h1, (hhash (j - 1) (by omega)).1]
  · rw [← htip, (hhash _ hHl).1]
  · rw [← hh _ hHl]; exact hbound _ hHl
  · rw [← hout_h, hh _ hHl]
  · have := hcont j hj (by rw [hh j hj]; exact hm)
    rw [nBitsOf_eq, this]; split <;> rfl
  · have := retarget_sound hsat (hj_of hlog hj) (by rw [hh j hj]; exact hm) (by rw [hh j hj]; exact hpos)
    rw [this]
    unfold prevNB prevTime prevPst
    by_cases h0 : j = 0
    · simp only [h0, if_true]
    · simp only [h0, if_false, nBitsOf_eq, timeOf_eq, pst_eq hsat hlog (j - 1) (by omega)]
  · apply mtp_core hsat (hj_of hlog hj)
    show winNum main j = _
    rw [win_eq hsat hlog j hj, hwin, take_append_take _ _ 11 11 (by omega), ← List.append_assoc]
    rfl
  · rw [← hh j hj]; exact version_sound hsat (hj_of hlog hj)
  · rw [← hout_nb, nBitsOf_eq]
  · rw [← out_time hsat (hj_of hlog hHl) hlast, timeOf_eq]
  · rw [← hout_pst, pst_eq hsat hlog _ hHl]
  · have hw := win_eq hsat hlog _ hHl
    rw [hwin, take_append_take _ _ 11 11 (by omega), ← List.append_assoc] at hw
    have : (List.range 10).map (fun k => leN (pubWord pub (68 + 2 * k))) = (winNum main (2 ^ logSize / 256 - 1)).take 10 := by
      apply List.ext_getElem (by simp [winNum])
      intro k hk1 hk2
      simp only [List.length_map, List.length_range] at hk1
      simp only [winNum, List.getElem_map, List.getElem_range, List.getElem_take]
      rw [mtp_out hsat (hj_of hlog hHl) hlast hk1]
    rw [this, hw, List.take_take]; rfl
  · rw [← work_out hsat (hj_of hlog hHl) hlast, work_eq hsat hlog hwork _ hHl, Nat.sub_add_cancel hH]

end Top

end StarkedAir.HeaderChain
