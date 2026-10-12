/-
Number-theoretic facts about Bitcoin's compact target encoding used by the retarget proof.
-/
import BitcoinConsensus.Bitcoin

namespace BitcoinConsensus.Bitcoin

theorem size_eq {t k : ℕ} (hlo : 2 ^ k ≤ t) (hhi : t < 2 ^ (k + 1)) : Nat.size t = k + 1 :=
  le_antisymm (Nat.size_le.mpr hhi) (Nat.lt_size.mpr hlo)

theorem pow256 (s : ℕ) : (256 : ℕ) ^ s = 2 ^ (8 * s) := by rw [pow_mul]; norm_num

/-- If `t / 256^s = m` with a canonical mantissa `m ∈ [0x8000, 0x800000)`, then `GetCompact(t)`
encodes exactly `(m, s + 3)`. -/
theorem getCompact_of {t s m : ℕ} (hm : t / 256 ^ s = m) (hlo : 0x8000 ≤ m) (hhi : m < 0x800000) :
    getCompact t = m + 2 ^ 24 * (s + 3) := by
  have hpos : 0 < 256 ^ s := by positivity
  have ht1 : m * 256 ^ s ≤ t := by rw [← hm]; exact Nat.div_mul_le_self t _
  have ht2 : t < 256 ^ s * (m + 1) := by rw [← hm]; exact Nat.lt_mul_div_succ t hpos
  have hB := pow256 s
  unfold getCompact
  by_cases hbig : 0x10000 ≤ m
  · -- Three significant bytes: no normalization.
    have hsz : 8 * s + 16 < Nat.size t := Nat.lt_size.mpr (by
        calc 2 ^ (8 * s + 16) = 2 ^ 16 * 256 ^ s := by rw [hB, ← pow_add]; ring_nf
          _ ≤ m * 256 ^ s := Nat.mul_le_mul_right _ hbig
          _ ≤ t := ht1)
    have hsz2 : Nat.size t ≤ 8 * s + 23 := Nat.size_le.mpr (by
      calc t < 256 ^ s * (m + 1) := ht2
        _ ≤ 256 ^ s * 2 ^ 23 := Nat.mul_le_mul_left _ (by norm_num at hhi ⊢; omega)
        _ = 2 ^ (8 * s + 23) := by rw [hB, ← pow_add])
    have hbytes : (Nat.size t + 7) / 8 = s + 3 := by omega
    simp only [hbytes]
    have hc : (if s + 3 ≤ 3 then t * 256 ^ (3 - (s + 3)) else t / 256 ^ (s + 3 - 3)) = m := by
      split
      · have : s = 0 := by omega
        subst this; simp at hm ⊢; exact hm
      · rw [show s + 3 - 3 = s by omega, hm]
    rw [hc, if_neg (by omega)]
  · -- Two significant bytes: GetCompact shifts one byte less, then normalizes.
    have hsz : Nat.size t = 8 * s + 16 := by
      have := size_eq (t := t) (k := 8 * s + 15)
        (by calc 2 ^ (8 * s + 15) = 2 ^ 15 * 256 ^ s := by rw [hB, ← pow_add]; ring_nf
              _ ≤ m * 256 ^ s := Nat.mul_le_mul_right _ hlo
              _ ≤ t := ht1)
        (by calc t < 256 ^ s * (m + 1) := ht2
              _ ≤ 256 ^ s * 2 ^ 16 := Nat.mul_le_mul_left _ (by norm_num at hbig ⊢; omega)
              _ = 2 ^ (8 * s + 15 + 1) := by rw [hB, ← pow_add])
      omega
    have hbytes : (Nat.size t + 7) / 8 = s + 2 := by omega
    simp only [hbytes]
    -- c = t / 256^(s−1) (or t · 256^(1−s) for s ≤ 1) lies in [256·m, 256·m + 256).
    have hc : ∃ c, (if s + 2 ≤ 3 then t * 256 ^ (3 - (s + 2)) else t / 256 ^ (s + 2 - 3)) = c ∧
        c / 256 = m ∧ 2 ^ 23 ≤ c ∧ c < 2 ^ 24 := by
      have hm16 : m < 0x10000 := by omega
      split
      · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
        · simp only [pow_zero, Nat.div_one] at hm
          subst hm
          refine ⟨t * 256 ^ (3 - (0 + 2)), rfl, ?_, ?_, ?_⟩ <;> norm_num <;> omega
        · refine ⟨t * 256 ^ (3 - (1 + 2)), rfl, ?_, ?_, ?_⟩ <;> norm_num at hm ht1 ht2 ⊢ <;> omega
      · obtain ⟨u, rfl⟩ : ∃ u, s = u + 1 := ⟨s - 1, by omega⟩
        rw [show u + 1 + 2 - 3 = u by omega]
        refine ⟨t / 256 ^ u, rfl, ?_, ?_, ?_⟩
        · rw [Nat.div_div_eq_div_mul, ← pow_succ, hm]
        · rw [Nat.le_div_iff_mul_le (by positivity)]
          calc 2 ^ 23 * 256 ^ u ≤ m * 256 * 256 ^ u := Nat.mul_le_mul_right _ (by omega)
            _ = m * 256 ^ (u + 1) := by rw [pow_succ]; ring
            _ ≤ t := ht1
        · rw [Nat.div_lt_iff_lt_mul (by positivity)]
          calc t < 256 ^ (u + 1) * (m + 1) := ht2
            _ ≤ 256 ^ (u + 1) * 2 ^ 16 := Nat.mul_le_mul_left _ (by omega)
            _ = 2 ^ 24 * 256 ^ u := by rw [pow_succ]; ring
    obtain ⟨c, hceq, hcm, hc1, hc2⟩ := hc
    rw [hceq, if_pos (by omega), hcm]

/-- `GetCompact(powLimit) = 0x1d00ffff`. -/
theorem getCompact_powLimit : getCompact powLimit = 0x1d00ffff := by
  rw [getCompact_of (s := 26) (m := 0xffff) (by norm_num [powLimit]) (by norm_num) (by norm_num)]
  norm_num

/-- The new target's mantissa at the new exponent `sp + dd − 1` is a single quotient with divisor
`1209600 · 256^dd` (the circuit's `dd = d + 1 ∈ {0, 1, 2}`). -/
theorem quot_shift (P0 sp dd : ℕ) (hdd : dd ≤ 2) (h1 : 1 ≤ sp + dd) :
    P0 * 256 ^ sp / 1209600 / 256 ^ (sp + dd - 1) = 256 * P0 / (1209600 * 256 ^ dd) := by
  rw [Nat.div_div_eq_div_mul]
  rcases (by omega : dd = 0 ∨ dd = 1 ∨ dd = 2) with rfl | rfl | rfl
  · obtain ⟨u, rfl⟩ : ∃ u, sp = u + 1 := ⟨sp - 1, by omega⟩
    rw [show u + 1 + 0 - 1 = u by omega, pow_succ, pow_zero, mul_one,
      show P0 * (256 ^ u * 256) = 256 * P0 * 256 ^ u by ring, Nat.mul_div_mul_right _ _ (by positivity)]
  · rw [show sp + 1 - 1 = sp by omega, Nat.mul_div_mul_right _ _ (by positivity), pow_one,
      show 1209600 * 256 = 256 * 1209600 by norm_num, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 256)]
  · rw [show sp + 2 - 1 = sp + 1 by omega, pow_succ,
      show 1209600 * (256 ^ sp * 256) = 1209600 * 256 * 256 ^ sp by ring,
      Nat.mul_div_mul_right _ _ (by positivity),
      show (256 : ℕ) ^ 2 = 256 * 256 by norm_num, show 1209600 * (256 * 256) = 256 * (1209600 * 256) by ring,
      Nat.mul_div_mul_left _ _ (by norm_num : 0 < 256)]

/-- `CalculateNextWorkRequired` with the previous target's exponent and mantissa exposed. -/
theorem nextWork_eq {prevN mantp sp span : ℕ} {prevTime pst : ℤ} (hsize : prevN / 2 ^ 24 = sp + 3)
    (hword : prevN % 2 ^ 23 = mantp)
    (hspan : (max 302400 (min 4838400 (prevTime - pst))).toNat = span) :
    nextWork prevN prevTime pst = getCompact (min (mantp * span * 256 ^ sp / 1209600) powLimit) := by
  unfold nextWork compactValue targetTimespan
  simp only [hsize, hword, hspan]
  congr 2
  split
  · have : sp = 0 := by omega
    subst this; simp
  · rw [show sp + 3 - 3 = sp by omega]; ring_nf

/-- Division branch: the circuit's quotient is the encoding `GetNextWorkRequired` produces. -/
theorem nextWork_noncap {prevN mantp sp span P0 m dd sOwn : ℕ} {prevTime pst : ℤ}
    (hsize : prevN / 2 ^ 24 = sp + 3) (hword : prevN % 2 ^ 23 = mantp)
    (hspan : (max 302400 (min 4838400 (prevTime - pst))).toNat = span) (hP0 : P0 = mantp * span)
    (hdd : dd ≤ 2) (h1 : 1 ≤ sp + dd) (hs : sOwn = sp + dd - 1)
    (hq : m = 256 * P0 / (1209600 * 256 ^ dd)) (hcanon : 0x8000 ≤ m) (hlt : m < 2 ^ 23)
    (hlim : (m + 1) * 256 ^ sOwn ≤ 2 ^ 224) :
    nextWork prevN prevTime pst = m + 2 ^ 24 * (sOwn + 3) := by
  rw [nextWork_eq hsize hword hspan]
  set T := mantp * span * 256 ^ sp / 1209600
  have hT : T / 256 ^ sOwn = m := by
    rw [hs, hq, ← quot_shift P0 sp dd hdd h1, hP0]
  have hTlt : T < 2 ^ 224 := by
    have := Nat.lt_mul_div_succ T (show 0 < 256 ^ sOwn by positivity)
    rw [hT] at this
    calc T < 256 ^ sOwn * (m + 1) := this
      _ = (m + 1) * 256 ^ sOwn := by ring
      _ ≤ 2 ^ 224 := hlim
  rw [min_eq_left (by unfold powLimit; omega)]
  exact getCompact_of hT hcanon (by norm_num; omega)

/-- Cap branch: when the scaled target reaches 2^224, `GetNextWorkRequired` yields powLimit's
encoding `0x1d00ffff`. -/
theorem nextWork_cap {prevN mantp sp span P0 : ℕ} {prevTime pst : ℤ}
    (hsize : prevN / 2 ^ 24 = sp + 3) (hword : prevN % 2 ^ 23 = mantp)
    (hspan : (max 302400 (min 4838400 (prevTime - pst))).toNat = span) (hP0 : P0 = mantp * span)
    (hcap : 1209600 * 256 ^ 28 ≤ P0 * 256 ^ sp) :
    nextWork prevN prevTime pst = 0x1d00ffff := by
  rw [nextWork_eq hsize hword hspan, ← getCompact_powLimit]
  congr 1
  apply min_eq_right
  have : 256 ^ 28 ≤ mantp * span * 256 ^ sp / 1209600 := by
    rw [Nat.le_div_iff_mul_le (by norm_num), ← hP0]; linarith
  unfold powLimit
  calc 2 ^ 224 - 1 ≤ 256 ^ 28 := by norm_num
    _ ≤ _ := this

end BitcoinConsensus.Bitcoin
