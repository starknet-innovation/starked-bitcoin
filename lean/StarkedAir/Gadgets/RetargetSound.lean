/-
Soundness of the difficulty-retarget constraints (header chain v3b): at every header whose
height is a positive multiple of 2016, nBits equals Bitcoin Core's `GetNextWorkRequired`
(mainnet) applied to the predecessor's nBits, the predecessor's time and the period start.
-/
import StarkedAir.Gadgets.StateSound
import StarkedAir.Spec.RetargetMath

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-- Little-endian numeric value of a field held as a raw (big-endian) header word. -/
def leN (w : Word) : ℕ :=
  (w.toNat / 2 ^ 24) % 256 + 256 * ((w.toNat / 2 ^ 16) % 256) + 65536 * ((w.toNat / 2 ^ 8) % 256) +
    2 ^ 24 * (w.toNat % 256)

theorem nBitsOf_eq (hw : ℕ → Word) : nBitsOf hw = leN (hw 18) := rfl
theorem timeOf_eq (hw : ℕ → Word) : timeOf hw = leN (hw 17) := rfl

/-- The predecessor values a header's retarget uses. -/
def prevNB (pub : ℕ → F) (main : ℕ → ℕ → F) (j : ℕ) : Word :=
  if j = 0 then pubWord pub 34 else headerWord main (j - 1) 18
def prevTime (pub : ℕ → F) (main : ℕ → ℕ → F) (j : ℕ) : Word :=
  if j = 0 then pubWord pub 44 else headerWord main (j - 1) 17
def prevPst (pub : ℕ → F) (main : ℕ → ℕ → F) (j : ℕ) : Word :=
  if j = 0 then pubWord pub 36 else pstAt main (j - 1)

section Copy

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem copy_sat {h : ℕ} (hh : h ≤ 1) :
    ∀ c ∈ copyFam h, c.eval (2 ^ logSize) preCols pub main (256 * j + 220) = 0 :=
  fun c hc => hsat _ (by omega) c (by
    show c ∈ constraints
    simp only [constraints, List.mem_append]
    left; right
    exact List.mem_flatMap.mpr ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp, hc⟩)

theorem ev_copySel :
    copySelNF.eval (2 ^ logSize) preCols pub main (256 * j + 220) = (if j = 0 then 0 else 1) ∧
    copySelF.eval (2 ^ logSize) preCols pub main (256 * j + 220) = (if j = 0 then 1 else 0) := by
  have hr : 256 * j + 220 < 2 ^ logSize := by omega
  have hp : (pre PREV).eval (2 ^ logSize) preCols pub main (256 * j + 220) = 1 := by
    rw [eval_oneRow (show preCols.getD PREV (.periodic [0]) = oneRow 220 from rfl) hr,
      show (256 * j + 220) % 256 = 220 by omega]; simp
  have hf : (pre FIRST).eval (2 ^ logSize) preCols pub main (256 * j + 220) = if j = 0 then 1 else 0 := by
    rw [eval_first hr]; by_cases h0 : j = 0 <;> simp [h0] <;> omega
  unfold copySelNF copySelF
  rw [eval_mul', eval_mul', hp, eval_sub', eval_cst, hf]
  by_cases h0 : j = 0 <;> simp [h0]

/-- A copy-family limb pair, switched on, pins the word at row 220. -/
theorem copy_word {S : Expr} {X : ℕ} {rhs : ℕ → Expr} (Y : Word)
    (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h) (rhs h)) ∈ copyFam h)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + 220) = 1) (hX : X + 32 ≤ 96)
    (hrhs : ∀ h ≤ 1, (rhs h).eval (2 ^ logSize) preCols pub main (256 * j + 220) = ((half16 Y h : ℕ) : F)) :
    word main X (256 * j + 220) = Y := by
  have hr : 256 * j + 220 < 2 ^ logSize := by omega
  have e : ∀ h ≤ 1, ((half16 (word main X (256 * j + 220)) h : ℕ) : F) = ((half16 Y h : ℕ) : F) := fun h hh => by
    have := copy_sat hsat hj hh _ (hmem h hh)
    rw [eval_mul', hS, one_mul, eval_sub', eval_limb (wrap_zero hr) (bits (chainSat_of hsat) hr hX) hh,
      hrhs h hh] at this
    exact sub_eq_zero.mp this
  exact word_of_halves (e 0 (by norm_num)) (e 1 (by norm_num))

theorem copy_pub {S : Expr} {X b : ℕ} (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h) (.pub (b + h))) ∈ copyFam h)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + 220) = 1) (hX : X + 32 ≤ 96) :
    word main X (256 * j + 220) = pubWord pub b := by
  have hr : 256 * j + 220 < 2 ^ logSize := by omega
  have e : ∀ h ≤ 1, ((half16 (word main X (256 * j + 220)) h : ℕ) : F) = pub (b + h) := fun h hh => by
    have := copy_sat hsat hj hh _ (hmem h hh)
    rw [eval_mul', hS, one_mul, eval_sub', eval_limb (wrap_zero hr) (bits (chainSat_of hsat) hr hX) hh] at this
    exact sub_eq_zero.mp this
  exact word_of_pubs (by simpa using e 0 (by norm_num)) (e 1 (by norm_num))

/-- Row 220 holds the predecessor's nBits, time and period-start time. -/
theorem copy_facts :
    word main A (256 * j + 220) = prevNB pub main j ∧ word main E (256 * j + 220) = prevTime pub main j ∧
    word main W (256 * j + 220) = prevPst pub main j := by
  have hr : 256 * j + 220 < 2 ^ logSize := by omega
  obtain ⟨hnf, hf⟩ := ev_copySel hsat hj
  have lim := fun (X : ℕ) (k : ℕ) (hX : X + 32 ≤ 96) (hk : k ≤ 256 * j + 220) (h : ℕ) (hh : h ≤ 1) =>
    eval_limb (pc := preCols) (pub := pub) (wrap_back (k := k) hk hr)
      (bits (chainSat_of hsat) (by omega) hX) (half := h) hh
  unfold prevNB prevTime prevPst
  by_cases h0 : j = 0
  · simp only [h0, if_true] at hf ⊢
    subst h0
    exact ⟨copy_pub hsat hj (S := copySelF) (fun h _ => by simp [copyFam]) hf (by decide),
      copy_pub hsat hj (S := copySelF) (fun h _ => by simp [copyFam]) hf (by decide),
      copy_pub hsat hj (S := copySelF) (fun h _ => by simp [copyFam]) hf (by decide)⟩
  · simp only [h0, if_false] at hnf ⊢
    refine ⟨?_, ?_, ?_⟩
    · simp only [headerWord, show ¬ (18 < 16) by norm_num, if_false]
      exact copy_word hsat hj _ (S := copySelNF) (rhs := fun h => limb W h (-398))
        (fun h _ => by simp [copyFam]) hnf (by decide) (fun h hh => by
          have := lim W 398 (by decide) (by omega) h hh
          simp only [Nat.cast_ofNat] at this
          rwa [show 256 * j + 220 - 398 = 256 * (j - 1) + 76 + (18 - 16) by omega] at this)
    · simp only [headerWord, show ¬ (17 < 16) by norm_num, if_false]
      exact copy_word hsat hj _ (S := copySelNF) (rhs := fun h => limb W h (-399))
        (fun h _ => by simp [copyFam]) hnf (by decide) (fun h hh => by
          have := lim W 399 (by decide) (by omega) h hh
          simp only [Nat.cast_ofNat] at this
          rwa [show 256 * j + 220 - 399 = 256 * (j - 1) + 76 + (17 - 16) by omega] at this)
    · unfold pstAt
      exact copy_word hsat hj _ (S := copySelNF) (rhs := fun h => limb E h (-258))
        (fun h _ => by simp [copyFam]) hnf (by decide) (fun h hh => by
          have := lim E 258 (by decide) (by omega) h hh
          simp only [Nat.cast_ofNat] at this
          rwa [show 256 * j + 220 - 258 = 256 * (j - 1) + 218 by omega] at this)

end Copy

/-! ## Evaluation helpers at arbitrary rows -/

section Ev
variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ}

theorem ev_bit {c rr : ℕ} {off : ℤ} (hw : wrap n r off = rr) (hb : (main c rr).val ≤ 1) :
    (col c off).eval n pc pub main r = ((bit main c rr).toNat : F) := by
  rw [eval_col, hw]; exact eq_bit hb

theorem ev_bitsR {base lo k rr : ℕ} {off : ℤ} (hw : wrap n r off = rr)
    (hb : ∀ i < k, (main (base + lo + i) rr).val ≤ 1) :
    (bitsR base lo k off).eval n pc pub main r = ((ofBits (fun i => bit main (base + lo + i) rr) k : ℕ) : F) :=
  eval_sumPow_bits _ _ k (fun i hi => ev_bit hw (hb i hi))

/-- A big-endian byte of a word held in bit columns. -/
theorem ev_beByte {base i rr : ℕ} {off : ℤ} (hi : i < 4) (hw : wrap n r off = rr)
    (hb : ∀ k < 32, (main (base + k) rr).val ≤ 1) :
    (beByte base i off).eval n pc pub main r =
      (((word main base rr).toNat / 2 ^ (8 * (3 - i)) % 256 : ℕ) : F) := by
  unfold beByte
  rw [ev_bitsR hw (fun k hk => by rw [Nat.add_assoc]; exact hb _ (by omega)), ← ofBits_byte]
  congr 1
  exact ofBits_congr (fun k hk => by rw [Nat.add_assoc]; exact (word_getLsbD _ _ (by omega)).symm)

/-- A window of `k` bits starting at `lo` of a word held in bit columns. -/
theorem ev_window {base lo k rr : ℕ} {off : ℤ} (hk : lo + k ≤ 32) (hw : wrap n r off = rr)
    (hb : ∀ i < 32, (main (base + i) rr).val ≤ 1) :
    (bitsR base lo k off).eval n pc pub main r = (((word main base rr).toNat / 2 ^ lo % 2 ^ k : ℕ) : F) := by
  rw [ev_bitsR hw (fun i hi => by rw [Nat.add_assoc]; exact hb _ (by omega)), ← ofBits_window]
  congr 1
  exact ofBits_congr (fun i hi => by rw [Nat.add_assoc]; exact (word_getLsbD _ _ (by omega)).symm)

end Ev

/-! ## Facts at the retarget row (221) -/

section Rt

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem rt_sat : ∀ c ∈ retargetCs, c.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 0 :=
  fun c hc => hsat _ (by omega) c (by
    show c ∈ constraints; simp only [constraints, List.mem_append]; right; exact hc)

theorem ev_rtSel : rtSel.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 1 := by
  show (pre RT).eval _ _ _ _ _ = 1
  rw [eval_oneRow (show preCols.getD RT (.periodic [0]) = oneRow 221 from rfl) (by omega),
    show (256 * j + 221) % 256 = 221 by omega]; simp

/-- Booleanity of bit columns at any row of this header. -/
theorem bA {base rr : ℕ} (hrr : rr < 2 ^ logSize) (hbase : base + 32 ≤ 96) :
    ∀ k < 32, (main (base + k) rr).val ≤ 1 := bits (chainSat_of hsat) hrr hbase

theorem rtBase_sat : ∀ c ∈ rtBase, c.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 0 :=
  fun c hc => rt_sat hsat hj c (by simp only [retargetCs, List.mem_append]; tauto)

theorem ev_wbit {i : ℕ} (hi : i < 32) :
    (col (W + i)).eval (2 ^ logSize) preCols pub main (256 * j + 221) = ((bit main (W + i) (256 * j + 221)).toNat : F) :=
  ev_bit (wrap_zero (by omega)) (bA hsat hj (by omega) (by decide) i hi)

theorem ev_ohSum (f : ℕ → ℕ) :
    ((List.range 27).foldl (fun acc s => Expr.add acc (.mul (cst (f s)) (ohP s))) (cst 0)).eval
      (2 ^ logSize) preCols pub main (256 * j + 221) =
      ∑ s ∈ Finset.range 27, ((f s : ℕ) : F) * ((bit main (A + s) (256 * j + 221)).toNat : F) := by
  rw [eval_foldl_list _ (fun s => .mul (cst (f s)) (ohP s)), eval_cst, Nat.cast_zero, zero_add, list_range_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [eval_mul', eval_cst]; unfold ohP bitR
  rw [ev_bit (wrap_zero (by omega)) (bA hsat hj (by omega) (by decide) s (by simp at hs; omega))]

theorem ev_ohSum1 :
    ohSum.eval (2 ^ logSize) preCols pub main (256 * j + 221) =
      ∑ s ∈ Finset.range 27, ((bit main (A + s) (256 * j + 221)).toNat : F) := by
  unfold ohSum
  rw [eval_foldl_list _ ohP, eval_cst, Nat.cast_zero, zero_add, list_range_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  unfold ohP bitR
  rw [ev_bit (wrap_zero (by omega)) (bA hsat hj (by omega) (by decide) s (by simp at hs; omega))]

omit hsat hj in
theorem wrapN {N r k : ℕ} (hk : k ≤ r) (hr : r < N) : wrap N r (-(k : ℤ)) = r - k := wrap_back hk hr

/-- At a positive multiple of 2016: `rt` is on and the previous exponent is one-hot decoded. -/
theorem rt_core (hm : heightAt main j % 2016 = 0) (hpos : 0 < heightAt main j) :
    bit main W (256 * j + 221) = true ∧
    ∃ sp < 27, (∀ s < 27, s ≠ sp → bit main (A + s) (256 * j + 221) = false) ∧
      bit main (A + sp) (256 * j + 221) = true ∧ (prevNB pub main j).toNat % 256 = sp + 3 := by
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  obtain ⟨-, hflag, -, -, -, -, hq⟩ := state_row hsat (j := j) hj
  have hfb : bit main W (256 * j + 218) = true := hflag.mpr hm
  set Q := ofBits (fun i => bit main (A + i) (256 * j + 218 + 1)) 20
  have hQ1 : 1 ≤ Q := by omega
  have hQlt := ofBits_lt (fun i => bit main (A + i) (256 * j + 218 + 1)) 20
  have hall := rtBase_sat hsat hj
  simp only [rtBase, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hall
  obtain ⟨e1, -, e3, e4, e5, -⟩ := hall
  have hsel := ev_rtSel hsat hj
  have w3 : wrap (2 ^ logSize) r (-3) = 256 * j + 218 := by
    have := wrapN (N := 2 ^ logSize) (k := 3) (show 3 ≤ r by omega) hr; simp only [Nat.cast_ofNat] at this
    rw [this]; omega
  have w2 : wrap (2 ^ logSize) r (-2) = 256 * j + 218 + 1 := by
    have := wrapN (N := 2 ^ logSize) (k := 2) (show 2 ≤ r by omega) hr; simp only [Nat.cast_ofNat] at this
    rw [this]; omega
  have w1 : wrap (2 ^ logSize) r (-1) = 256 * j + 220 := by
    have := wrapN (N := 2 ^ logSize) (k := 1) (show 1 ≤ r by omega) hr; simp only [Nat.cast_one] at this
    rw [this]; omega
  have hflagE : flagAt.eval (2 ^ logSize) preCols pub main r = 1 := by
    unfold flagAt
    rw [ev_bit (c := W) w3 (by simpa using bA hsat hj (rr := 256 * j + 218) (by omega) (by decide) 0 (by norm_num)), hfb]
    simp
  have hqE : qAt.eval (2 ^ logSize) preCols pub main r = (Q : F) := by
    unfold qAt
    rw [eval_sumPow_bits _ (fun i => bit main (A + i) (256 * j + 218 + 1)) 20 (fun i hi =>
      ev_bit w2 (bA hsat hj (by omega) (by decide) i (by omega)))]
  have hnz := ev_wbit hsat hj (i := 1) (by norm_num)
  have hrt := ev_wbit hsat hj (i := 0) (by norm_num)
  -- nz = 1 because q ≥ 1.
  unfold nzE wctl bitR at e3
  rw [eval_mul', eval_mul', hsel, one_mul, eval_sub', eval_cst, hnz, hqE] at e3
  have hnz1 : bit main (W + 1) r = true := by
    cases h : bit main (W + 1) r
    · rw [h] at e3; simp at e3
      have : Q = 0 := natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by simpa using e3)
      omega
    · rfl
  -- rt = flag · nz = 1.
  unfold rtE nzE wctl bitR at e1
  rw [eval_mul', hsel, one_mul, eval_sub', eval_mul', hflagE, hnz, hnz1, hrt] at e1
  have hrt1 : bit main (W + 0) r = true := by
    cases h : bit main (W + 0) r
    · rw [h] at e1; simp at e1
    · rfl
  -- one-hot previous exponent.
  unfold rtE wctl bitR at e4
  · rw [eval_mul', hsel, one_mul, eval_sub', ev_ohSum1 hsat hj, hrt, hrt1] at e4
    have hsum : ∑ s ∈ Finset.range 27, (bit main (A + s) r).toNat = 1 := by
      have hle : ∑ s ∈ Finset.range 27, (bit main (A + s) r).toNat ≤ 27 := by
        calc _ ≤ ∑ s ∈ Finset.range 27, 1 := Finset.sum_le_sum (fun s _ => Bool.toNat_le _)
          _ = 27 := by simp
      apply natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P])
      push_cast; simpa using sub_eq_zero.mp e4
    obtain ⟨sp, hsp, hg, hu⟩ := onehot_of_sum hsum
    refine ⟨hrt1, sp, hsp, hu, hg, ?_⟩
    -- exponent: prevExp − 3 = Σ s·oh_s = sp.
    have hw : ∑ s ∈ Finset.range 27, ((s : ℕ) : F) * ((bit main (A + s) r).toNat : F) = (sp : F) := by
      rw [Finset.sum_congr rfl (fun s _ => mul_comm _ _)]; exact sum_onehot hsp hg hu (fun s => (s : F))
    unfold ohWeighted rtE wctl bitR at e5
    rw [eval_mul', hsel, one_mul, eval_sub', eval_mul', hrt, hrt1, ev_ohSum hsat hj (fun s => s), hw,
      eval_sub', eval_cst] at e5
    unfold prevExp at e5
    rw [ev_beByte (by norm_num) w1 (bA hsat hj (by omega) (by decide)), (copy_facts hsat hj).1] at e5
    simp only [Bool.toNat_true, Nat.cast_one, one_mul, show 8 * (3 - 3) = 0 by rfl, pow_zero, Nat.div_one] at e5
    have hb : (prevNB pub main j).toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
    exact natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by
      push_cast; linear_combination e5)

/-- Low/high 16-bit limbs of the little-endian numeric value of a raw word. -/
def tl (w : Word) (h : ℕ) : ℕ :=
  w.toNat / 2 ^ (8 * (3 - 2 * h)) % 256 + 256 * (w.toNat / 2 ^ (8 * (3 - (2 * h + 1))) % 256)

omit hsat hj in
theorem leN_tl (w : Word) : leN w = tl w 0 + 65536 * tl w 1 := by
  unfold leN tl; norm_num; ring

omit hsat hj in
theorem tl_lt (w : Word) (h : ℕ) : tl w h < 65536 := by
  unfold tl; have := Nat.mod_lt (w.toNat / 2 ^ (8 * (3 - 2 * h))) (show 0 < 256 by norm_num)
  have := Nat.mod_lt (w.toNat / 2 ^ (8 * (3 - (2 * h + 1)))) (show 0 < 256 by norm_num); omega

theorem ev_timeLimb {X : ℕ} (hX : X + 32 ≤ 96) {h : ℕ} (hh : h ≤ 1) :
    (timeLimb X h (-1)).eval (2 ^ logSize) preCols pub main (256 * j + 221) =
      ((tl (word main X (256 * j + 220)) h : ℕ) : F) := by
  have hr : 256 * j + 221 < 2 ^ logSize := by omega
  have w1 : wrap (2 ^ logSize) (256 * j + 221) (-1) = 256 * j + 220 := by
    have := wrapN (N := 2 ^ logSize) (k := 1) (show 1 ≤ 256 * j + 221 by omega) hr
    simp only [Nat.cast_one] at this; rw [this]; omega
  unfold timeLimb
  rw [eval_add', eval_mul', eval_cst, ev_beByte (by omega) w1 (bA hsat hj (by omega) hX),
    ev_beByte (by omega) w1 (bA hsat hj (by omega) hX)]
  unfold tl; push_cast; ring

/-- The span is Core's clamped timespan. -/
theorem rt_span (hm : heightAt main j % 2016 = 0) (hpos : 0 < heightAt main j) :
    (max 302400 (min 4838400 ((leN (prevTime pub main j) : ℤ) - leN (prevPst pub main j)))).toNat =
      ofBits (fun i => bit main (E + 0 + i) (256 * j + 221)) 23 := by
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  have hr1 : r + 1 < 2 ^ logSize := by omega
  obtain ⟨hrt1, -⟩ := rt_core hsat hj hm hpos
  obtain ⟨-, hcT, hcP⟩ := copy_facts hsat hj
  have hall := rtBase_sat hsat hj
  simp only [rtBase, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hall
  obtain ⟨-, -, -, -, -, e6, eM1, eM2, eM3, eM4, eL1, eL2, eL3, eH1, eH2, eH3⟩ := hall
  have hsel := ev_rtSel hsat hj
  have w0 : wrap (2 ^ logSize) r 0 = r := wrap_zero hr
  have w1' : wrap (2 ^ logSize) r 1 = r + 1 := wrap_one hr1
  have bW0 := bA hsat hj (rr := r) hr (base := W) (by decide)
  have bE0 := bA hsat hj (rr := r) hr (base := E) (by decide)
  have bA1 := bA hsat hj (rr := r + 1) hr1 (base := A) (by decide)
  have bE1 := bA hsat hj (rr := r + 1) hr1 (base := E) (by decide)
  have bW1 := bA hsat hj (rr := r + 1) hr1 (base := W) (by decide)
  have flag := fun (i : ℕ) (hi : i < 32) => ev_wbit hsat hj (i := i) hi
  set lo := bit main (W + 2) r
  set mid := bit main (W + 3) r
  set hi := bit main (W + 4) r
  set kp := bit main (W + 9) r
  set kn := bit main (W + 10) r
  set span := ofBits (fun i => bit main (E + 0 + i) r) 23
  set sLo := ofBits (fun i => bit main (E + 0 + i) r) 16
  set sHi := ofBits (fun i => bit main (E + 16 + i) r) 7
  have hspanE : spanE.eval (2 ^ logSize) preCols pub main r = (span : F) :=
    ev_bitsR w0 (fun i hi => by rw [Nat.add_assoc]; exact bE0 _ (by omega))
  have hsLo : spanLo.eval (2 ^ logSize) preCols pub main r = (sLo : F) :=
    ev_bitsR w0 (fun i hi => by rw [Nat.add_assoc]; exact bE0 _ (by omega))
  have hsHi : spanHi.eval (2 ^ logSize) preCols pub main r = (sHi : F) :=
    ev_bitsR w0 (fun i hi => by rw [Nat.add_assoc]; exact bE0 _ (by omega))
  have hsplit : span = sLo + 65536 * sHi := by
    have e := ofBits_add (fun i => bit main (E + 0 + i) r) 16 7
    simp only [show (16 + 7 : ℕ) = 23 from rfl] at e
    show ofBits (fun i => bit main (E + 0 + i) r) 23 = _
    rw [e]
    have : ofBits (fun i => bit main (E + 0 + (16 + i)) r) 7 = sHi :=
      ofBits_congr (fun i hi => by rw [show E + 0 + (16 + i) = E + 16 + i by omega])
    rw [this]; norm_num; rfl
  have spanLt := ofBits_lt (fun i => bit main (E + 0 + i) r) 23
  have sLoLt := ofBits_lt (fun i => bit main (E + 0 + i) r) 16
  have sHiLt := ofBits_lt (fun i => bit main (E + 16 + i) r) 7
  set tP := word main E (256 * j + 220)
  set pS := word main W (256 * j + 220)
  have tT0 := ev_timeLimb hsat hj (X := E) (by decide) (h := 0) (by norm_num)
  have tT1 := ev_timeLimb hsat hj (X := E) (by decide) (h := 1) (by norm_num)
  have tP0 := ev_timeLimb hsat hj (X := W) (by decide) (h := 0) (by norm_num)
  have tP1 := ev_timeLimb hsat hj (X := W) (by decide) (h := 1) (by norm_num)
  have l1 := tl_lt tP 0; have l2 := tl_lt tP 1; have l3 := tl_lt pS 0; have l4 := tl_lt pS 1
  -- Exactly one branch.
  unfold loE midE' hiE rtE wctl bitR at e6
  rw [eval_mul', hsel, one_mul, eval_sub', eval_add', eval_add', flag 2 (by norm_num), flag 3 (by norm_num),
    flag 4 (by norm_num), flag 0 (by norm_num), show bit main (W + 0) r = true by simpa using hrt1] at e6
  have hbr : lo.toNat + mid.toNat + hi.toNat = 1 := by
    have := Bool.toNat_le lo; have := Bool.toNat_le mid; have := Bool.toNat_le hi
    exact natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by push_cast; simpa using sub_eq_zero.mp e6)
  rw [← hcT, ← hcP, leN_tl, leN_tl]
  -- Common evaluations.
  have cv : (col CE_LO 1).eval (2 ^ logSize) preCols pub main r = ((bit main CE_LO (r + 1)).toNat : F) :=
    ev_bit w1' (bool_val (sha_sat (chainSat_of hsat)) hr1 (Or.inr ⟨by decide, by decide⟩))
  have v32v : (col CA_LO 1).eval (2 ^ logSize) preCols pub main r = ((bit main CA_LO (r + 1)).toNat : F) :=
    ev_bit w1' (bool_val (sha_sat (chainSat_of hsat)) hr1 (Or.inr ⟨by decide, by decide⟩))
  have vlo : (bitsR W 0 16 1).eval (2 ^ logSize) preCols pub main r =
      ((ofBits (fun i => bit main (W + 0 + i) (r + 1)) 16 : ℕ) : F) :=
    ev_bitsR w1' (fun i hi => by rw [Nat.add_assoc]; exact bW1 _ (by omega))
  have vhi : (bitsR W 16 16 1).eval (2 ^ logSize) preCols pub main r =
      ((ofBits (fun i => bit main (W + 16 + i) (r + 1)) 16 : ℕ) : F) :=
    ev_bitsR w1' (fun i hi => by rw [Nat.add_assoc]; exact bW1 _ (by omega))
  have u1v : (bitsR A 0 23 1).eval (2 ^ logSize) preCols pub main r =
      ((ofBits (fun i => bit main (A + 0 + i) (r + 1)) 23 : ℕ) : F) :=
    ev_bitsR w1' (fun i hi => by rw [Nat.add_assoc]; exact bA1 _ (by omega))
  have u2v : (bitsR E 0 23 1).eval (2 ^ logSize) preCols pub main r =
      ((ofBits (fun i => bit main (E + 0 + i) (r + 1)) 23 : ℕ) : F) :=
    ev_bitsR w1' (fun i hi => by rw [Nat.add_assoc]; exact bE1 _ (by omega))
  have vloLt := ofBits_lt (fun i => bit main (W + 0 + i) (r + 1)) 16
  have vhiLt := ofBits_lt (fun i => bit main (W + 16 + i) (r + 1)) 16
  have cb := Bool.toNat_le (bit main CE_LO (r + 1))
  have v32b := Bool.toNat_le (bit main CA_LO (r + 1))
  have kpb := Bool.toNat_le kp
  have knb := Bool.toNat_le kn
  have u1Lt := ofBits_lt (fun i => bit main (A + 0 + i) (r + 1)) 23
  have u2Lt := ofBits_lt (fun i => bit main (E + 0 + i) (r + 1)) 23
  simp only [midE', loE, hiE, kpE, knE, wctl, bitR] at eM1 eM2 eM3 eM4 eL1 eL2 eL3 eH1 eH2 eH3
  rcases (by have := Bool.toNat_le lo; have := Bool.toNat_le mid; have := Bool.toNat_le hi; omega :
      (lo.toNat = 0 ∧ mid.toNat = 1 ∧ hi.toNat = 0) ∨ (lo.toNat = 1 ∧ mid.toNat = 0 ∧ hi.toNat = 0) ∨
      (lo.toNat = 0 ∧ mid.toNat = 0 ∧ hi.toNat = 1)) with ⟨_, hmid, _⟩ | ⟨hlo, _, _⟩ | ⟨_, _, hhi⟩
  · -- mid: prevTime = pst + span with span in range.
    have m1 : (mid.toNat : F) = 1 := by rw [hmid]; simp
    rw [eval_mul', eval_mul', hsel, flag 3 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      eval_mul', tP0, tT0, hsLo, cv] at eM1
    try simp only [eval_cst] at eM1
    rw [eval_mul', eval_mul', hsel, flag 3 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      tP1, tT1, hsHi, cv] at eM2
    try simp only [eval_cst] at eM2
    rw [eval_mul', eval_mul', hsel, flag 3 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_sub',
      hspanE, u1v] at eM3
    try simp only [eval_cst] at eM3
    rw [eval_mul', eval_mul', hsel, flag 3 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_sub',
      hspanE, u2v] at eM4
    try simp only [eval_cst] at eM4
    have n1 : tl pS 0 + sLo = tl tP 0 + 65536 * (bit main CE_LO (r + 1)).toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eM1 ⊢; linear_combination eM1)
    have n2 : tl pS 1 + sHi + (bit main CE_LO (r + 1)).toNat = tl tP 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eM2 ⊢; linear_combination eM2)
    have n3 : span = 302400 + ofBits (fun i => bit main (A + 0 + i) (r + 1)) 23 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eM3 ⊢; linear_combination eM3)
    have n4 : span + ofBits (fun i => bit main (E + 0 + i) (r + 1)) 23 = 4838400 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eM4 ⊢; linear_combination -eM4)
    have hdiff : ((tl tP 0 + 65536 * tl tP 1 : ℕ) : ℤ) - ((tl pS 0 + 65536 * tl pS 1 : ℕ) : ℤ) = span := by
      push_cast; omega
    rw [hdiff, min_eq_right (by omega), max_eq_right (by omega)]; simp
  · -- lo: prevTime − pst ≤ 302399, span = 302400.
    have m1 : (lo.toNat : F) = 1 := by rw [hlo]; simp
    rw [eval_mul', eval_mul', hsel, flag 2 (by norm_num), m1, one_mul, one_mul, eval_sub', hspanE] at eL1
    try simp only [eval_cst] at eL1
    rw [eval_mul', eval_mul', hsel, flag 2 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      eval_add', eval_add', eval_mul', eval_mul', tP0, tT0, vlo,
      flag 9 (by norm_num), flag 10 (by norm_num)] at eL2
    simp only [eval_cst] at eL2
    rw [eval_mul', eval_mul', hsel, flag 2 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      eval_add', eval_add', eval_add', eval_mul', tP1, tT1, vhi, v32v,
      flag 9 (by norm_num), flag 10 (by norm_num)] at eL3
    simp only [eval_cst] at eL3
    have n1 : span = 302400 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by norm_num)) (by push_cast at eL1 ⊢; linear_combination eL1)
    have n2 : tl pS 0 + 302399 % 65536 + 65536 * kn.toNat =
        tl tP 0 + ofBits (fun i => bit main (W + 0 + i) (r + 1)) 16 + 65536 * kp.toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eL2 ⊢; linear_combination eL2)
    have n3 : tl pS 1 + 302399 / 65536 + kp.toNat =
        tl tP 1 + ofBits (fun i => bit main (W + 16 + i) (r + 1)) 16 + 65536 * (bit main CA_LO (r + 1)).toNat + kn.toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eL3 ⊢; linear_combination eL3)
    have hdiff : ((tl tP 0 + 65536 * tl tP 1 : ℕ) : ℤ) - ((tl pS 0 + 65536 * tl pS 1 : ℕ) : ℤ) ≤ 302399 := by
      push_cast; omega
    rw [min_eq_right (by omega), max_eq_left (by omega), n1]; rfl
  · -- hi: prevTime − pst ≥ 4838401, span = 4838400.
    have m1 : (hi.toNat : F) = 1 := by rw [hhi]; simp
    rw [eval_mul', eval_mul', hsel, flag 4 (by norm_num), m1, one_mul, one_mul, eval_sub', hspanE] at eH1
    try simp only [eval_cst] at eH1
    rw [eval_mul', eval_mul', hsel, flag 4 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      eval_add', eval_add', eval_mul', eval_mul', tP0, tT0, vlo,
      flag 9 (by norm_num), flag 10 (by norm_num)] at eH2
    simp only [eval_cst] at eH2
    rw [eval_mul', eval_mul', hsel, flag 4 (by norm_num), m1, one_mul, one_mul, eval_sub', eval_add', eval_add',
      eval_add', eval_add', eval_add', eval_mul', tP1, tT1, vhi, v32v,
      flag 9 (by norm_num), flag 10 (by norm_num)] at eH3
    simp only [eval_cst] at eH3
    have n1 : span = 4838400 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by norm_num)) (by push_cast at eH1 ⊢; linear_combination eH1)
    have n2 : tl pS 0 + 4838401 % 65536 + ofBits (fun i => bit main (W + 0 + i) (r + 1)) 16 + 65536 * kn.toNat =
        tl tP 0 + 65536 * kp.toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eH2 ⊢; linear_combination eH2)
    have n3 : tl pS 1 + 4838401 / 65536 + ofBits (fun i => bit main (W + 16 + i) (r + 1)) 16 +
        65536 * (bit main CA_LO (r + 1)).toNat + kp.toNat = tl tP 1 + kn.toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eH3 ⊢; linear_combination eH3)
    have hdiff : 4838401 ≤ ((tl tP 0 + 65536 * tl tP 1 : ℕ) : ℤ) - ((tl pS 0 + 65536 * tl pS 1 : ℕ) : ℤ) := by
      push_cast; omega
    rw [min_eq_left (by omega), max_eq_right (by omega), n1]; rfl

set_option maxHeartbeats 1600000 in
/-- The retarget row's product: `P0 = mant_prev · span`, with everything read from words. -/
theorem rt_p0 :
    let pa := (word main A (256 * j + 223)).toNat
    let pe := (word main E (256 * j + 223)).toNat
    pa + 2 ^ 32 * (pe % 2 ^ 16) =
      (leN (prevNB pub main j) % 2 ^ 23) * ((word main E (256 * j + 221)).toNat % 2 ^ 23) := by
  intro pa pe
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  have hr2 : r + 2 < 2 ^ logSize := by omega
  have hr3 : r + 3 < 2 ^ logSize := by omega
  have hsel := ev_rtSel hsat hj
  have w0 : wrap (2 ^ logSize) r 0 = r := wrap_zero hr
  have wm1 : wrap (2 ^ logSize) r (-1) = 256 * j + 220 := by
    have := wrapN (N := 2 ^ logSize) (k := 1) (show 1 ≤ r by omega) hr; simp only [Nat.cast_one] at this
    rw [this]; omega
  have w2 : wrap (2 ^ logSize) r 2 = 256 * j + 223 := by
    rw [wrap_eq (by omega) (by omega)]; omega
  have w3 : wrap (2 ^ logSize) r 3 = 256 * j + 224 := by
    rw [wrap_eq (by omega) (by omega)]; omega
  have bAm1 := bA hsat hj (rr := 256 * j + 220) (by omega) (base := A) (by decide)
  have bE0 := bA hsat hj (rr := r) hr (base := E) (by decide)
  have bA2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := A) (by decide)
  have bE2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := E) (by decide)
  have bA3 := bA hsat hj (rr := 256 * j + 224) (by omega) (base := A) (by decide)
  have bE3 := bA hsat hj (rr := 256 * j + 224) (by omega) (base := E) (by decide)
  set wv := (word main A (256 * j + 220)).toNat
  set sv := (word main E r).toNat
  set ma := (word main A (256 * j + 224)).toNat
  set me := (word main E (256 * j + 224)).toNat
  -- Operand and result digits.
  have ea : ∀ i < 3, (prevMant i).eval (2 ^ logSize) preCols pub main r =
      ((if i = 0 then wv / 2 ^ 24 % 2 ^ 8 else if i = 1 then wv / 2 ^ 16 % 2 ^ 8 else wv / 2 ^ 8 % 2 ^ 7 : ℕ) : F) := by
    intro i hi
    interval_cases i
    · exact ev_window (by norm_num) wm1 bAm1
    · exact ev_window (by norm_num) wm1 bAm1
    · exact ev_window (by norm_num) wm1 bAm1
  have eb : ∀ i < 3, (spanByte i).eval (2 ^ logSize) preCols pub main r =
      ((if i = 0 then sv / 2 ^ 0 % 2 ^ 8 else if i = 1 then sv / 2 ^ 8 % 2 ^ 8 else sv / 2 ^ 16 % 2 ^ 7 : ℕ) : F) := by
    intro i hi
    interval_cases i
    · exact ev_window (by norm_num) w0 bE0
    · exact ev_window (by norm_num) w0 bE0
    · exact ev_window (by norm_num) w0 bE0
  have ep : ∀ k < 6, (p0Byte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then pa / 2 ^ (8 * k) % 2 ^ 8 else pe / 2 ^ (8 * (k - 4)) % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    all_goals first
      | exact ev_window (by norm_num) w2 bA2
      | exact ev_window (by norm_num) w2 bE2
  have em : ∀ k < 5, (mcE k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 3 then ma / 2 ^ (10 * k) % 2 ^ 10 else me / 2 ^ (10 * (k - 3)) % 2 ^ 10 : ℕ) : F) := by
    intro k hk
    interval_cases k
    all_goals first
      | exact ev_window (by norm_num) w3 bA3
      | exact ev_window (by norm_num) w3 bE3
  -- Column equations.
  have col : ∀ k < 6, (p0Col k).eval (2 ^ logSize) preCols pub main r = 0 := fun k hk =>
    rt_sat hsat hj _ (by
      unfold retargetCs
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))))
  have c0 := col 0 (by norm_num); have c1 := col 1 (by norm_num); have c2 := col 2 (by norm_num)
  have c3 := col 3 (by norm_num); have c4 := col 4 (by norm_num); have c5 := col 5 (by norm_num)
  let f := fun i j => Expr.mul (prevMant i) (spanByte j)
  have s0 : sumCol 0 f 3 3 = (cst 0).add (f 0 0) := rfl
  have s1 : sumCol 1 f 3 3 = ((cst 0).add (f 0 1)).add (f 1 0) := rfl
  have s2 : sumCol 2 f 3 3 = (((cst 0).add (f 0 2)).add (f 1 1)).add (f 2 0) := rfl
  have s3 : sumCol 3 f 3 3 = ((cst 0).add (f 1 2)).add (f 2 1) := rfl
  have s4 : sumCol 4 f 3 3 = (cst 0).add (f 2 2) := rfl
  have s5 : sumCol 5 f 3 3 = cst 0 := rfl
  have ea0 := ea 0 (by norm_num); have ea1 := ea 1 (by norm_num); have ea2 := ea 2 (by norm_num)
  have eb0 := eb 0 (by norm_num); have eb1 := eb 1 (by norm_num); have eb2 := eb 2 (by norm_num)
  have ep0 := ep 0 (by norm_num); have ep1 := ep 1 (by norm_num); have ep2 := ep 2 (by norm_num)
  have ep3 := ep 3 (by norm_num); have ep4 := ep 4 (by norm_num); have ep5 := ep 5 (by norm_num)
  have em0 := em 0 (by norm_num); have em1 := em 1 (by norm_num); have em2 := em 2 (by norm_num)
  have em3 := em 3 (by norm_num); have em4 := em 4 (by norm_num)
  have hsel' : Expr.eval (2 ^ logSize) preCols pub main r rtSel = 1 := hsel
  simp only [Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, pow_zero,
    Nat.div_one] at ea0 ea1 ea2 eb0 eb1 eb2 ep0 ep1 ep2 ep3 ep4 ep5 em0 em1 em2 em3 em4
  simp only [p0Col, s0, s1, s2, s3, s4, s5, f, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceSub,
    Nat.reduceAdd, eval_mul', eval_sub', eval_add', eval_cst, hsel', one_mul, ea0, ea1, ea2, eb0, eb1, eb2, ep0, ep1, ep2, ep3, ep4, ep5,
    em0, em1, em2, em3, em4, Nat.cast_zero, zero_add, add_zero] at c0 c1 c2 c3 c4 c5
  -- Digit bounds.
  have bnd : ∀ x m : ℕ, x % 2 ^ m < 2 ^ m := fun x m => Nat.mod_lt _ (by positivity)
  have hwv : wv < 2 ^ 32 := (word main A (256 * j + 220)).isLt
  have hsv : sv < 2 ^ 32 := (word main E r).isLt
  have hpa : pa < 2 ^ 32 := (word main A (256 * j + 223)).isLt
  have hpe : pe < 2 ^ 32 := (word main E (256 * j + 223)).isLt
  have hma : ma < 2 ^ 32 := (word main A (256 * j + 224)).isLt
  have hme : me < 2 ^ 32 := (word main E (256 * j + 224)).isLt
  set a0 := wv / 2 ^ 24 % 2 ^ 8 with ha0; set a1 := wv / 2 ^ 16 % 2 ^ 8 with ha1; set a2 := wv / 2 ^ 8 % 2 ^ 7 with ha2
  set b0 := sv % 2 ^ 8 with hb0; set b1 := sv / 2 ^ 8 % 2 ^ 8 with hb1; set b2 := sv / 2 ^ 16 % 2 ^ 7 with hb2
  set p0 := pa % 2 ^ 8 with hp0; set p1 := pa / 2 ^ 8 % 2 ^ 8 with hp1; set p2 := pa / 2 ^ 16 % 2 ^ 8 with hp2; set p3 := pa / 2 ^ 24 % 2 ^ 8 with hp3
  set p4 := pe % 2 ^ 8 with hp4; set p5 := pe / 2 ^ 8 % 2 ^ 8 with hp5
  set m0 := ma % 2 ^ 10 with hm0; set m1 := ma / 2 ^ 10 % 2 ^ 10 with hm1; set m2 := ma / 2 ^ 20 % 2 ^ 10 with hm2
  set m3 := me % 2 ^ 10 with hm3; set m4 := me / 2 ^ 10 % 2 ^ 10 with hm4
  have la0 : a0 < 256 := bnd _ 8; have la1 : a1 < 256 := bnd _ 8; have la2 : a2 < 128 := bnd _ 7
  have lb0 : b0 < 256 := bnd _ 8; have lb1 : b1 < 256 := bnd _ 8; have lb2 : b2 < 128 := bnd _ 7
  have lp0 : p0 < 256 := bnd _ 8; have lp1 : p1 < 256 := bnd _ 8; have lp2 : p2 < 256 := bnd _ 8
  have lp3 : p3 < 256 := bnd _ 8; have lp4 : p4 < 256 := bnd _ 8; have lp5 : p5 < 256 := bnd _ 8
  have lm0 : m0 < 1024 := bnd _ 10; have lm1 : m1 < 1024 := bnd _ 10; have lm2 : m2 < 1024 := bnd _ 10
  have lm3 : m3 < 1024 := bnd _ 10; have lm4 : m4 < 1024 := bnd _ 10
  have q1 : a0 * b0 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q2 : a0 * b1 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q3 : a1 * b0 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q4 : a0 * b2 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q5 : a1 * b1 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q6 : a2 * b0 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q7 : a1 * b2 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q8 : a2 * b1 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have q9 : a2 * b2 ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have n0 : a0 * b0 = p0 + 256 * m0 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c0 ⊢; linear_combination c0)
  have n1 : a0 * b1 + a1 * b0 + m0 = p1 + 256 * m1 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c1 ⊢; linear_combination c1)
  have n2 : a0 * b2 + a1 * b1 + a2 * b0 + m1 = p2 + 256 * m2 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c2 ⊢; linear_combination c2)
  have n3 : a1 * b2 + a2 * b1 + m2 = p3 + 256 * m3 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c3 ⊢; linear_combination c3)
  have n4 : a2 * b2 + m3 = p4 + 256 * m4 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c4 ⊢; linear_combination c4)
  have n5 : m4 = p5 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at c5 ⊢; linear_combination c5)
  have hwvd : (prevNB pub main j).toNat = wv := by rw [← (copy_facts hsat hj).1]
  clear_value pa pe wv sv ma me a0 a1 a2 b0 b1 b2 p0 p1 p2 p3 p4 p5 m0 m1 m2 m3 m4
  have dpa : pa = p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 := by
    rw [hp0, hp1, hp2, hp3]
    exact (fun x : ℕ => (by omega : x < 2 ^ 32 → x = x % 2 ^ 8 + 256 * (x / 2 ^ 8 % 2 ^ 8) +
      65536 * (x / 2 ^ 16 % 2 ^ 8) + 2 ^ 24 * (x / 2 ^ 24 % 2 ^ 8))) pa hpa
  have dpe : pe % 2 ^ 16 = p4 + 256 * p5 := by
    rw [hp4, hp5]; exact (fun x : ℕ => (by omega : x % 2 ^ 16 = x % 2 ^ 8 + 256 * (x / 2 ^ 8 % 2 ^ 8))) pe
  have dm : leN (prevNB pub main j) % 2 ^ 23 = a0 + 256 * a1 + 65536 * a2 := by
    unfold leN; rw [hwvd, ha0, ha1, ha2]
    exact (fun x : ℕ => (by omega : (x / 2 ^ 24 % 256 + 256 * (x / 2 ^ 16 % 256) + 65536 * (x / 2 ^ 8 % 256) +
      2 ^ 24 * (x % 256)) % 2 ^ 23 = x / 2 ^ 24 % 2 ^ 8 + 256 * (x / 2 ^ 16 % 2 ^ 8) + 65536 * (x / 2 ^ 8 % 2 ^ 7))) wv
  have ds : sv % 2 ^ 23 = b0 + 256 * b1 + 65536 * b2 := by
    rw [hb0, hb1, hb2]
    exact (fun x : ℕ => (by omega : x % 2 ^ 23 = x % 2 ^ 8 + 256 * (x / 2 ^ 8 % 2 ^ 8) + 65536 * (x / 2 ^ 16 % 2 ^ 7))) sv
  rw [dpa, dpe, dm, ds]
  have : ((p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 + 2 ^ 32 * (p4 + 256 * p5) : ℕ) : ℤ) =
      (((a0 + 256 * a1 + 65536 * a2) * (b0 + 256 * b1 + 65536 * b2) : ℕ) : ℤ) := by
    have z0 : ((a0 * b0 : ℕ) : ℤ) = p0 + 256 * m0 := by exact_mod_cast n0
    have z1 : ((a0 * b1 + a1 * b0 + m0 : ℕ) : ℤ) = p1 + 256 * m1 := by exact_mod_cast n1
    have z2 : ((a0 * b2 + a1 * b1 + a2 * b0 + m1 : ℕ) : ℤ) = p2 + 256 * m2 := by exact_mod_cast n2
    have z3 : ((a1 * b2 + a2 * b1 + m2 : ℕ) : ℤ) = p3 + 256 * m3 := by exact_mod_cast n3
    have z4 : ((a2 * b2 + m3 : ℕ) : ℤ) = p4 + 256 * m4 := by exact_mod_cast n4
    have z5 : ((m4 : ℕ) : ℤ) = p5 := by exact_mod_cast n5
    push_cast at z0 z1 z2 z3 z4 z5 ⊢
    linear_combination -z0 - 256 * z1 - 65536 * z2 - 2 ^ 24 * z3 - 2 ^ 32 * z4 - 2 ^ 40 * z5
  exact_mod_cast this

omit hsat in
theorem w143 : wrap (2 ^ logSize) (256 * j + 221) (-143) = 256 * j + 78 := by
  have := wrapN (N := 2 ^ logSize) (k := 143) (show 143 ≤ 256 * j + 221 by omega) (by omega)
  simp only [Nat.cast_ofNat] at this; rw [this]; omega

omit hsat in
theorem wfwd {k : ℕ} (hk : k ≤ 7) : wrap (2 ^ logSize) (256 * j + 221) (k : ℤ) = 256 * j + 221 + k := by
  rw [wrap_eq (by omega) (by omega)]; omega

/-- The header's own mantissa (header word 18, row 78) seen from row 221. -/
theorem ev_ownMantE : ownMantE.eval (2 ^ logSize) preCols pub main (256 * j + 221) =
    ((mantNat (headerWord main j 18) : ℕ) : F) := by
  have hy : headerWord main j 18 = word main W (256 * j + 78) := by simp [headerWord]
  have hb := bA hsat hj (rr := 256 * j + 78) (by omega) (base := W) (by decide)
  unfold ownMantE ownMant
  simp only [show (0 : ℕ) < 2 from by norm_num, show (1 : ℕ) < 2 from by norm_num,
    show ¬ ((2 : ℕ) < 2) from by norm_num, if_true, if_false]
  rw [eval_add', eval_add', eval_mul', eval_mul', eval_cst, eval_cst,
    ev_beByte (by norm_num) (w143 hj) hb, ev_beByte (by norm_num) (w143 hj) hb,
    ev_window (by norm_num) (w143 hj) hb, ← hy]
  unfold mantNat; push_cast; norm_num

/-- The header's own exponent one-hot (row 216) seen from row 221. -/
theorem ev_ownOh : ownOhWeighted.eval (2 ^ logSize) preCols pub main (256 * j + 221) =
    ∑ s ∈ Finset.range 27, ((s : ℕ) : F) * ((bit main (A + s) (256 * j + 216)).toNat : F) := by
  have w5 : wrap (2 ^ logSize) (256 * j + 221) (-5) = 256 * j + 216 := by
    have := wrapN (N := 2 ^ logSize) (k := 5) (show 5 ≤ 256 * j + 221 by omega) (by omega)
    simp only [Nat.cast_ofNat] at this; rw [this]; omega
  unfold ownOhWeighted
  rw [eval_foldl_list _ (fun s => .mul (cst s) (col (A + s) (-5))), eval_cst, Nat.cast_zero, zero_add,
    list_range_sum]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [eval_mul', eval_cst, ev_bit w5 (bA hsat hj (by omega) (by decide) s (by simp at hs; omega))]

theorem ev_dflag {k : ℕ} (hk : k < 3) :
    (dE' k).eval (2 ^ logSize) preCols pub main (256 * j + 221) =
      ((bit main (W + (5 + k)) (256 * j + 221)).toNat : F) :=
  ev_wbit hsat hj (i := 5 + k) (by omega)

theorem dHead_sat : ∀ c ∈ dHead, c.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 0 :=
  fun c hc => rt_sat hsat hj c (by
    unfold retargetCs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ hc)))))

/-- Division branch (no cap): exactly one `d` flag `dd`, the exponent steps by `dd − 1`, and the
new mantissa is canonical. -/
theorem rt_dhead (hm : heightAt main j % 2016 = 0) (hpos : 0 < heightAt main j)
    (hcap : bit main (W + 8) (256 * j + 221) = false) :
    ∃ dd ≤ 2, (∀ k < 3, bit main (W + (5 + k)) (256 * j + 221) = decide (k = dd)) ∧
      (headerWord main j 18).toNat % 256 + 1 = (prevNB pub main j).toNat % 256 + dd ∧
      0x8000 ≤ mantNat (headerWord main j 18) := by
  set r := 256 * j + 221
  obtain ⟨hrt1, sp, hsp, hu, hg, hpe⟩ := rt_core hsat hj hm hpos
  obtain ⟨-, s0, hs0, hg0, hu0, hexp, -, -, -⟩ := header_pow_ex hsat hj
  have hsel := ev_rtSel hsat hj
  have hd := dHead_sat hsat hj
  simp only [dHead, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hd
  obtain ⟨e1, e2, e3⟩ := hd
  have f0 := ev_dflag hsat hj (k := 0) (by norm_num)
  have f1 := ev_dflag hsat hj (k := 1) (by norm_num)
  have f2 := ev_dflag hsat hj (k := 2) (by norm_num)
  have hc := ev_wbit hsat hj (i := 8) (by norm_num)
  have hr0 := ev_wbit hsat hj (i := 0) (by norm_num)
  set g := fun k => bit main (W + (5 + k)) r
  -- (1) exactly one d flag.
  unfold dAny capE rtE wctl bitR at e1
  rw [eval_mul', hsel, one_mul, eval_sub', eval_add', eval_add', eval_add', f0, f1, f2, hc, hcap, hr0] at e1
  simp only [Nat.add_zero] at e1; rw [hrt1] at e1
  have hsum : ∑ k ∈ Finset.range 3, (g k).toNat = 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := Bool.toNat_le (g 0); have := Bool.toNat_le (g 1); have := Bool.toNat_le (g 2)
    apply natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P])
    push_cast; simp only [Bool.toNat_false, Bool.toNat_true, Nat.cast_zero, Nat.cast_one, add_zero] at e1
    linear_combination e1
  obtain ⟨dd, hdd, hgd, hud⟩ := onehot_of_sum hsum
  have hflags : ∀ k < 3, g k = decide (k = dd) := fun k hk => by
    by_cases h : k = dd
    · subst h; simpa using hgd
    · simpa [h] using hud k hk h
  have hany : dAny.eval (2 ^ logSize) preCols pub main r = 1 := by
    unfold dAny; rw [eval_add', eval_add', f0, f1, f2]
    have h0 := hflags 0 (by norm_num); have h1 := hflags 1 (by norm_num); have h2 := hflags 2 (by norm_num)
    simp only [g] at h0 h1 h2
    rw [h0, h1, h2]
    interval_cases dd <;> simp
  refine ⟨dd, by omega, hflags, ?_, ?_⟩
  · -- (2) s_own − s_prev = d.
    have hw : ∑ s ∈ Finset.range 27, ((s : ℕ) : F) * ((bit main (A + s) r).toNat : F) = (sp : F) := by
      rw [Finset.sum_congr rfl (fun s _ => mul_comm _ _)]; exact sum_onehot hsp hg hu (fun s => (s : F))
    have hw0 : ∑ s ∈ Finset.range 27, ((s : ℕ) : F) * ((bit main (A + s) (256 * j + 216)).toNat : F) = (s0 : F) := by
      rw [Finset.sum_congr rfl (fun s _ => mul_comm _ _)]; exact sum_onehot hs0 hg0 hu0 (fun s => (s : F))
    unfold ohWeighted at e2
    rw [eval_mul', eval_mul', hsel, one_mul, hany, one_mul, eval_sub', eval_sub', eval_sub', ev_ownOh hsat hj, hw0,
      ev_ohSum hsat hj (fun s => s), hw, f0, f2] at e2
    have := hflags 0 (by norm_num); have := hflags 2 (by norm_num)
    simp only [g] at this
    have key : s0 + (g 0).toNat = sp + (g 2).toNat := by
      have := Bool.toNat_le (g 0); have := Bool.toNat_le (g 2)
      apply natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
      push_cast; linear_combination e2
    rw [hflags 0 (by norm_num), hflags 2 (by norm_num)] at key
    interval_cases dd <;> simp at key <;> omega
  · -- (3) canonical mantissa.
    have hb6 := bA hsat hj (rr := r + 6) (by omega) (base := E) (by decide)
    have w6 : wrap (2 ^ logSize) r 6 = r + 6 := by rw [wrap_eq (by omega) (by omega)]; omega
    rw [eval_mul', eval_mul', hsel, one_mul, hany, one_mul, eval_sub', eval_sub', ev_ownMantE hsat hj, eval_cst,
      ev_window (by norm_num) w6 hb6] at e3
    have hlt := Nat.mod_lt ((word main E (r + 6)).toNat / 2 ^ 0) (show 0 < 2 ^ 23 by norm_num)
    have hml : mantNat (headerWord main j 18) < 2 ^ 23 := by unfold mantNat; omega
    have : mantNat (headerWord main j 18) = (word main E (r + 6)).toNat / 2 ^ 0 % 2 ^ 23 + 0x8000 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination e3)
    omega

end Rt

/-- `leN` in 16-bit limbs. -/
theorem leN_limbs (w : Word) :
    leN w = ((w.toNat / 2 ^ 24) % 256 + 256 * ((w.toNat / 2 ^ 16) % 256)) +
      65536 * ((w.toNat / 2 ^ 8) % 256 + 256 * (w.toNat % 256)) := by
  unfold leN; ring

end StarkedAir.HeaderChain
