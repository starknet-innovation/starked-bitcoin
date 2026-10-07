/-
Soundness of the minimum-block-version constraints (header chain v6, `Version.lean`):
every header satisfies Bitcoin Core's mainnet "bad-version" rule for its height (`version_sound`).
-/
import StarkedAir.Gadgets.WorkSound

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

section Ver

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem ver_sat {c : Expr} (hc : c ∈ versionCs) :
    c.eval (2 ^ logSize) preCols pub main (256 * j + 254) = 0 :=
  hsat _ (by omega) c (by show c ∈ constraints; simp only [constraints, List.mem_append]; tauto)

/-- The three height flags are exact. -/
theorem ver_flag {k : ℕ} (hk : k < 3) :
    bit main (108 + k) (256 * j + 254) = decide (verT k ≤ heightAt main j) := by
  set r := 256 * j + 254
  have hr : r < 2 ^ logSize := by omega
  have c := ver_sat hsat hj (c := verFlag k) (List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  have hsel : verSel.eval (2 ^ logSize) preCols pub main r = 1 := by
    unfold verSel
    rw [eval_oneRow (i := VER) (row := 254) rfl hr, show r % 256 = 254 by omega]; simp
  have w36 : wrap (2 ^ logSize) r (-36) = 256 * j + 218 := by
    have := wrapN (N := 2 ^ logSize) (k := 36) (show 36 ≤ r by omega) hr
    simp only [Nat.cast_ofNat] at this; rw [this]; omega
  have hh : verHeight.eval (2 ^ logSize) preCols pub main r = ((heightAt main j : ℕ) : F) := by
    unfold verHeight
    rw [ev_window (by norm_num) w36 (bA hsat hj (by omega) (by decide))]
    have := (state_row hsat (j := j) hj).1
    unfold heightAt at this ⊢; rw [pow_zero, Nat.div_one, Nat.mod_eq_of_lt this]
  have hd : (verD k).eval (2 ^ logSize) preCols pub main r =
      (((word main (if k = 0 then A else if k = 1 then E else W) r).toNat % 2 ^ 30 : ℕ) : F) := by
    unfold verD
    rw [ev_window (by norm_num) (wrap_zero hr) (bA hsat hj hr (by split_ifs <;> decide))]; simp
  have hf : (verF k).eval (2 ^ logSize) preCols pub main r = ((bit main (108 + k) r).toNat : F) :=
    ev_bit (wrap_zero hr) (bool_val (sha_sat (chainSat_of hsat)) hr (Or.inr ⟨by omega, by omega⟩))
  unfold verFlag at c
  rw [eval_mul', hsel, one_mul, eval_add', eval_mul', eval_mul', eval_sub', eval_sub', eval_sub', eval_sub',
    eval_sub', eval_cst, eval_cst, eval_cst, hh, hd, hf] at c
  have hT : verT k ≤ 388381 := by unfold verT; split_ifs <;> norm_num
  have hT1 : 1 ≤ verT k := by unfold verT; split_ifs <;> norm_num
  have hH := (state_row hsat (j := j) hj).1
  set d := (word main (if k = 0 then A else if k = 1 then E else W) r).toNat % 2 ^ 30
  have hdl : d < 2 ^ 30 := Nat.mod_lt _ (by norm_num)
  cases hb : bit main (108 + k) r
  · simp only [hb, Bool.toNat_false, Nat.cast_zero, zero_mul, zero_add, sub_zero, one_mul] at c
    have : verT k - 1 = heightAt main j + d :=
      natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by push_cast; linear_combination c)
    symm; simp only [decide_eq_false_iff_not, not_le]; omega
  · simp only [hb, Bool.toNat_true, Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at c
    have : heightAt main j = verT k + d :=
      natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by push_cast; linear_combination c)
    symm; simp only [decide_eq_true_eq]; omega

/-- **Minimum block version.** -/
theorem version_sound : versionOk (heightAt main j) (versionOf (headerWord main j)) = true := by
  set r := 256 * j + 254
  have hr : r < 2 ^ logSize := by omega
  have f0 : bit main 108 r = decide (227931 ≤ heightAt main j) := by
    have := ver_flag hsat hj (k := 0) (by norm_num); simpa [verT] using this
  have f1 : bit main (108 + 1) r = decide (363725 ≤ heightAt main j) := by
    have := ver_flag hsat hj (k := 1) (by norm_num); simpa [verT] using this
  have f2 : bit main (108 + 2) r = decide (388381 ≤ heightAt main j) := by
    have := ver_flag hsat hj (k := 2) (by norm_num); simpa [verT] using this
  unfold versionOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  by_cases h0 : 227931 ≤ heightAt main j
  swap
  · exact ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, Or.inl (by omega)⟩
  -- BIP34 active: the version relation is enforced.
  have hsel : verSel.eval (2 ^ logSize) preCols pub main r = 1 := by
    unfold verSel
    rw [eval_oneRow (i := VER) (row := 254) rfl hr, show r % 256 = 254 by omega]; simp
  have hbool : ∀ c, 108 ≤ c → c < 124 → ∀ rr, rr < 2 ^ logSize → (main c rr).val ≤ 1 :=
    fun c h1 h2 rr h => bool_val (sha_sat (chainSat_of hsat)) h (Or.inr ⟨h1, h2⟩)
  have hF : ∀ k < 3, (verF k).eval (2 ^ logSize) preCols pub main r = ((bit main (108 + k) r).toNat : F) :=
    fun k hk => ev_bit (wrap_zero hr) (hbool _ (by omega) (by omega) _ hr)
  have hf0 : (verF 0).eval (2 ^ logSize) preCols pub main r = 1 := by
    rw [hF 0 (by norm_num), show (108 : ℕ) + 0 = 108 from rfl, f0, decide_eq_true h0]; simp
  have w250 : wrap (2 ^ logSize) r (-250) = 256 * j + 4 := by
    have := wrapN (N := 2 ^ logSize) (k := 250) (show 250 ≤ r by omega) hr
    simp only [Nat.cast_ofNat] at this; rw [this]; omega
  have w1 : wrap (2 ^ logSize) r 1 = r + 1 := wrap_one (by omega)
  have hy : headerWord main j 0 = word main W (256 * j + 4) := by simp [headerWord]
  have bW := bA hsat hj (rr := 256 * j + 4) (by omega) (base := W) (by decide)
  have bA1 := bA hsat hj (rr := r + 1) (by omega) (base := A) (by decide)
  have ev : ∀ h ≤ 1, (timeLimb W h (-250)).eval (2 ^ logSize) preCols pub main r =
      ((tl (headerWord main j 0) h : ℕ) : F) := fun h hh => by
    unfold timeLimb
    rw [eval_add', eval_mul', eval_cst, ev_beByte (by omega) w250 bW, ev_beByte (by omega) w250 bW, hy]
    unfold tl; push_cast; ring
  have ee : ∀ h ≤ 1, (verE h).eval (2 ^ logSize) preCols pub main r =
      (((word main A (r + 1)).toNat / 2 ^ (16 * h) % 2 ^ 16 : ℕ) : F) :=
    fun h hh => ev_window (by omega) w1 bA1
  have ec : verC.eval (2 ^ logSize) preCols pub main r = ((bit main 108 (r + 1)).toNat : F) :=
    ev_bit w1 (hbool 108 (by norm_num) (by norm_num) _ (by omega))
  have hmin : verMin.eval (2 ^ logSize) preCols pub main r =
      (((1 + (bit main 108 r).toNat + (bit main (108 + 1) r).toNat + (bit main (108 + 2) r).toNat) : ℕ) : F) := by
    unfold verMin; rw [eval_add', eval_add', eval_add', eval_cst, hF 0 (by norm_num), hF 1 (by norm_num),
      hF 2 (by norm_num)]; push_cast; ring
  have cLo := ver_sat hsat hj (c := verLo) (by simp [versionCs])
  have cHi := ver_sat hsat hj (c := verHi) (by simp [versionCs])
  have cSg := ver_sat hsat hj (c := verSign) (by simp [versionCs])
  unfold verLo at cLo; unfold verHi at cHi; unfold verSign at cSg
  rw [eval_mul', eval_mul', hsel, hf0, one_mul, one_mul, eval_sub', eval_add', eval_add', eval_mul', eval_cst,
    hmin, ee 0 (by norm_num), ev 0 (by norm_num), ec] at cLo
  rw [eval_mul', eval_mul', hsel, hf0, one_mul, one_mul, eval_sub', eval_add', ee 1 (by norm_num),
    ev 1 (by norm_num), ec] at cHi
  rw [eval_mul', eval_mul', hsel, hf0, one_mul, one_mul,
    ev_bit w250 (bW 7 (by norm_num))] at cSg
  -- Lift the two limb equations.
  set m := 1 + (bit main 108 r).toNat + (bit main (108 + 1) r).toNat + (bit main (108 + 2) r).toNat
  have hm4 : m ≤ 4 := by
    have := Bool.toNat_le (bit main 108 r); have := Bool.toNat_le (bit main (108 + 1) r)
    have := Bool.toNat_le (bit main (108 + 2) r); omega
  set e0 := (word main A (r + 1)).toNat / 2 ^ (16 * 0) % 2 ^ 16
  set e1 := (word main A (r + 1)).toNat / 2 ^ (16 * 1) % 2 ^ 16
  have he0 : e0 < 65536 := Nat.mod_lt _ (by norm_num)
  have he1 : e1 < 65536 := Nat.mod_lt _ (by norm_num)
  have hc := Bool.toNat_le (bit main 108 (r + 1))
  have l0 := tl_lt (headerWord main j 0) 0
  have l1 := tl_lt (headerWord main j 0) 1
  have n0 : m + e0 = tl (headerWord main j 0) 0 + 65536 * (bit main 108 (r + 1)).toNat :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cLo)
  have n1 : e1 + (bit main 108 (r + 1)).toNat = tl (headerWord main j 0) 1 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cHi)
  have hv : versionOf (headerWord main j) = leN (headerWord main j 0) := rfl
  have hvm : m ≤ versionOf (headerWord main j) := by rw [hv, leN_tl]; omega
  -- Sign bit: numeric bit 31 is raw bit 7, which is 0.
  have hsign : versionOf (headerWord main j) < 2 ^ 31 := by
    have hb : bit main (W + 7) (256 * j + 4) = false := by
      cases h : bit main (W + 7) (256 * j + 4)
      · rfl
      · rw [h] at cSg; simp at cSg
    have hg : (headerWord main j 0).getLsbD 7 = false := by rw [hy, word_getLsbD _ _ (by norm_num)]; exact hb
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at hg
    have hw := (headerWord main j 0).isLt
    rw [hv]; unfold leN; simp at hg; omega
  have hvi : versionInt (versionOf (headerWord main j)) = versionOf (headerWord main j) := by
    unfold versionInt; rw [if_pos hsign]
  rw [hvi]
  have b1 := Bool.toNat_le (bit main (108 + 1) r)
  have b2 := Bool.toNat_le (bit main (108 + 2) r)
  have e0' : (bit main 108 r).toNat = 1 := by rw [f0, decide_eq_true h0]; rfl
  refine ⟨⟨Or.inr (by omega), ?_⟩, ?_⟩
  · by_cases h1 : 363725 ≤ heightAt main j
    · have : (bit main (108 + 1) r).toNat = 1 := by rw [f1, decide_eq_true h1]; rfl
      exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · by_cases h2 : 388381 ≤ heightAt main j
    · have : (bit main (108 + 1) r).toNat = 1 := by rw [f1, decide_eq_true (by omega)]; rfl
      have : (bit main (108 + 2) r).toNat = 1 := by rw [f2, decide_eq_true h2]; rfl
      exact Or.inr (by omega)
    · exact Or.inl (by omega)

end Ver

end StarkedAir.HeaderChain
