/-
Soundness of the median-time-past constraints (header chain v4, `Mtp.lean`).

For every header `j` of a satisfying trace, with `T_i = winAt main j i` (`i = 1..11`):
- the window is the predecessors' times: `T_1 = prevTime`, `T_{i+1}(j) = T_i(j − 1)`, and on
  the first header `T_{i+1} = pubWord pub (48 + 2(i − 1))` (`mtp_window`);
- at least 6 of the `T_i` are strictly below the header's own time (`mtp_count`);
- the last header's `T_1..T_10` are public outputs `68..87` (`mtp_out`);
- hence, when the window is the real predecessors' times padded with the genesis sentinel,
  the header satisfies Bitcoin Core's median-time-past rule (`mtp_core`).
-/
import StarkedAir.Gadgets.RetargetDiv
import StarkedAir.Spec.MtpMath

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-- Window slot `i` (1..11) of header `j`: the raw time word held in `a` at row `228 + i`. -/
def winAt (main : ℕ → ℕ → F) (j i : ℕ) : Word := word main A (256 * j + 228 + i)

section Mtp

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem mtp_sat {c : Expr} (hc : c ∈ mtpCs) {q : ℕ} (hq : q < 256) :
    c.eval (2 ^ logSize) preCols pub main (256 * j + q) = 0 :=
  hsat _ (by omega) c (by show c ∈ constraints; simp only [constraints, List.mem_append]; tauto)

omit hsat in
theorem ev_sel {k q : ℕ} (hk : k < 12) (hq : q < 256) :
    (pre (MTP0 + k)).eval (2 ^ logSize) preCols pub main (256 * j + q) = if q = 229 + k then 1 else 0 := by
  rw [eval_oneRow (i := MTP0 + k) (row := 229 + k) (by interval_cases k <;> rfl) (by omega),
    show (256 * j + q) % 256 = q by omega]

omit hsat in
theorem ev_slotSel {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 11) :
    (slotSel i).eval (2 ^ logSize) preCols pub main (256 * j + 228 + i) = 1 := by
  unfold slotSel
  rw [show 256 * j + 228 + i = 256 * j + (228 + i) by omega, ev_sel hj (by omega) (by omega)]
  simp; omega

omit hsat in
theorem ev_region {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 11) :
    mtpRegion.eval (2 ^ logSize) preCols pub main (256 * j + 228 + i) = 1 := by
  unfold mtpRegion
  rw [eval_foldl_list _ (fun k => pre (MTP0 + k)), eval_cst, Nat.cast_zero, zero_add, list_range_sum,
    Finset.sum_eq_single (i - 1)]
  · rw [show 256 * j + 228 + i = 256 * j + (228 + i) by omega, ev_sel hj (by omega) (by omega)]; simp; omega
  · intro k hk hne
    rw [show 256 * j + 228 + i = 256 * j + (228 + i) by omega, ev_sel hj (by simp at hk; omega) (by omega)]
    simp; omega
  · intro h; simp at h; omega

omit hsat in
theorem ev_firstAt {q : ℕ} (hq : q < 256) :
    (pre FIRST).eval (2 ^ logSize) preCols pub main (256 * j + q) = if j = 0 then 1 else 0 := by
  rw [eval_first (by omega)]
  by_cases h0 : j = 0 <;> simp [h0] <;> omega

/-- A row of `mtpCs` of the form `S · (limb X h − R h)` (both halves) with `S = 1` pins word `X`. -/
theorem mtp_word {S : Expr} {X q : ℕ} {R : ℕ → Expr} (Y : Word)
    (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h) (R h)) ∈ mtpCs) (hq : q < 256) (hX : X + 32 ≤ 96)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + q) = 1)
    (hR : ∀ h ≤ 1, (R h).eval (2 ^ logSize) preCols pub main (256 * j + q) = ((half16 Y h : ℕ) : F)) :
    word main X (256 * j + q) = Y := by
  have hr : 256 * j + q < 2 ^ logSize := by omega
  have e : ∀ h ≤ 1, ((half16 (word main X (256 * j + q)) h : ℕ) : F) = ((half16 Y h : ℕ) : F) := fun h hh => by
    have := mtp_sat hsat hj (hmem h hh) hq
    rw [eval_mul', hS, one_mul, eval_sub', eval_limb (wrap_zero hr) (bits (chainSat_of hsat) hr hX) hh,
      hR h hh] at this
    exact sub_eq_zero.mp this
  exact word_of_halves (e 0 (by norm_num)) (e 1 (by norm_num))

theorem mem_ownTime {c : Expr} {h : ℕ} (hh : h ≤ 1) (hc : c ∈ ownTime h) : c ∈ mtpCs := by
  unfold mtpCs
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp,
    List.mem_append_left _ (List.mem_append_left _ hc)⟩)

theorem mem_window {c : Expr} {h : ℕ} (hh : h ≤ 1) (hc : c ∈ window h) : c ∈ mtpCs := by
  unfold mtpCs
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp,
    List.mem_append_left _ (List.mem_append_right _ hc)⟩)

/-- Every slot row holds the header's own time in `w`. -/
theorem mtp_ownTime {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 11) :
    word main W (256 * j + 228 + i) = headerWord main j 17 := by
  induction i with
  | zero => omega
  | succ i ih =>
    have hr : 256 * j + 228 + (i + 1) < 2 ^ logSize := by omega
    rw [show 256 * j + 228 + (i + 1) = 256 * j + (229 + i) by omega]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · apply mtp_word hsat hj (S := slotSel 1) (R := fun h => limb W h (-152)) _
        (fun h hh => mem_ownTime hsat hj hh (List.mem_cons_self ..)) (by omega) (by decide)
        (by simpa using ev_slotSel hj (i := 1) (by norm_num) (by norm_num))
      intro h hh
      have := eval_limb (pc := preCols) (pub := pub) (base := W) (half := h)
        (wrap_back (n' := 2 ^ logSize) (k := 152) (show 152 ≤ 256 * j + (229 + 0) by omega) (by omega))
        (bits (chainSat_of hsat) (by omega) (by decide)) hh
      simp only [Nat.cast_ofNat] at this
      rw [this, show 256 * j + (229 + 0) - 152 = 256 * j + 76 + (17 - 16) by omega]
      simp [headerWord]
    · apply mtp_word hsat hj (S := slotSel (i + 1)) (R := fun h => limb W h (-1)) _
        (fun h hh => mem_ownTime hsat hj hh (List.mem_cons_of_mem _ (List.mem_map.mpr
          ⟨i - 1, List.mem_range.mpr (by omega), by simp [show i - 1 + 2 = i + 1 by omega]⟩)))
        (by omega) (by decide)
        (by rw [show 256 * j + (229 + i) = 256 * j + 228 + (i + 1) by omega]; exact ev_slotSel hj (by omega) (by omega))
      intro h hh
      have := eval_limb (pc := preCols) (pub := pub) (base := W) (half := h)
        (wrap_back (n' := 2 ^ logSize) (k := 1) (show 1 ≤ 256 * j + (229 + i) by omega) (by omega))
        (bits (chainSat_of hsat) (by omega) (by decide)) hh
      simp only [Nat.cast_one] at this
      rw [this, show 256 * j + (229 + i) - 1 = 256 * j + 228 + i by omega, ih (by omega) (by omega)]

/-- The window: `T_1` is the predecessor's time; later slots shift down from the predecessor,
or come from public inputs `48..67` on the first header. -/
theorem mtp_window :
    winAt main j 1 = prevTime pub main j ∧
    ∀ i, 1 ≤ i → i ≤ 10 → winAt main j (i + 1) =
      if j = 0 then pubWord pub (48 + 2 * (i - 1)) else winAt main (j - 1) i := by
  have hr0 : 256 * j + 220 < 2 ^ logSize := by omega
  refine ⟨?_, fun i hi1 hi => ?_⟩
  · unfold winAt
    rw [← (copy_facts hsat hj).2.1]
    apply mtp_word hsat hj (q := 229) (S := slotSel 1) (R := fun h => limb E h (-9)) _
      (fun h hh => mem_window hsat hj hh (List.mem_cons_self ..)) (by norm_num) (by decide)
      (by simpa using ev_slotSel hj (i := 1) (by norm_num) (by norm_num))
    intro h hh
    have := eval_limb (pc := preCols) (pub := pub) (base := E) (half := h)
      (wrap_back (n' := 2 ^ logSize) (k := 9) (show 9 ≤ 256 * j + 229 by omega) (by omega))
      (bits (chainSat_of hsat) hr0 (by decide)) hh
    simp only [Nat.cast_ofNat] at this
    rw [this, show 256 * j + 229 - 9 = 256 * j + 220 by omega]
  · unfold winAt
    rw [show 256 * j + 228 + (i + 1) = 256 * j + (229 + i) by omega]
    have hs : (slotSel (i - 1 + 2)).eval (2 ^ logSize) preCols pub main (256 * j + (229 + i)) = 1 := by
      rw [show i - 1 + 2 = i + 1 by omega, show 256 * j + (229 + i) = 256 * j + 228 + (i + 1) by omega]
      exact ev_slotSel hj (by omega) (by omega)
    have hf := ev_firstAt (pub := pub) (main := main) hj (q := 229 + i) (by omega)
    by_cases h0 : j = 0
    · simp only [h0, if_true] at hf ⊢
      subst h0
      have e : ∀ h ≤ 1, ((half16 (word main A (256 * 0 + (229 + i))) h : ℕ) : F) = pub (48 + 2 * (i - 1) + h) :=
        fun h hh => by
          have := mtp_sat hsat hj (c := Expr.mul (.mul (slotSel (i - 1 + 2)) (pre FIRST))
              (.sub (limb A h) (.pub (48 + 2 * (i - 1) + h))))
            (mem_window hsat hj hh (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
              ⟨i - 1, List.mem_range.mpr (by omega), List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)⟩)))
            (q := 229 + i) (by omega)
          rw [eval_mul', eval_mul', hs, hf, one_mul, one_mul, eval_sub',
            eval_limb (wrap_zero (by omega)) (bits (chainSat_of hsat) (by omega) (by decide)) hh] at this
          exact sub_eq_zero.mp this
      exact word_of_pubs (by simpa using e 0 (by norm_num)) (e 1 (by norm_num))
    · simp only [h0, if_false] at hf ⊢
      apply mtp_word hsat hj (S := .mul (slotSel (i - 1 + 2)) notFirst) (R := fun h => limb A h (-257)) _
        (fun h hh => mem_window hsat hj hh (List.mem_cons_of_mem _ (List.mem_flatMap.mpr
          ⟨i - 1, List.mem_range.mpr (by omega), List.mem_cons_self ..⟩))) (by omega) (by decide)
        (by unfold notFirst; rw [eval_mul', hs, eval_sub', eval_cst, hf]; simp)
      intro h hh
      have := eval_limb (pc := preCols) (pub := pub) (base := A) (half := h)
        (wrap_back (n' := 2 ^ logSize) (k := 257) (show 257 ≤ 256 * j + (229 + i) by omega) (by omega))
        (bits (chainSat_of hsat) (by omega) (by decide)) hh
      simp only [Nat.cast_ofNat] at this
      rw [this, show 256 * j + (229 + i) - 257 = 256 * (j - 1) + 228 + i by omega]


theorem ev_tl0 {X rr : ℕ} (hrr : rr < 2 ^ logSize) (hX : X + 32 ≤ 96) {h : ℕ} (hh : h ≤ 1) :
    (timeLimb X h 0).eval (2 ^ logSize) preCols pub main rr = ((tl (word main X rr) h : ℕ) : F) := by
  unfold timeLimb
  rw [eval_add', eval_mul', eval_cst, ev_beByte (by omega) (wrap_zero hrr) (bits (chainSat_of hsat) hrr hX),
    ev_beByte (by omega) (wrap_zero hrr) (bits (chainSat_of hsat) hrr hX)]
  unfold tl; push_cast; ring

/-- Each slot's flag is exactly "the window time is below the header's own time". -/
theorem mtp_cmp {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 11) :
    bit main 108 (256 * j + 228 + i) = decide (leN (winAt main j i) < leN (headerWord main j 17)) := by
  set rr := 256 * j + 228 + i
  have hr : rr < 2 ^ logSize := by omega
  have hq : 228 + i < 256 := by omega
  have hrow : rr = 256 * j + (228 + i) := by omega
  have cLo := mtp_sat hsat hj (c := cmpLo) (by unfold mtpCs; simp) hq
  have cHi := mtp_sat hsat hj (c := cmpHi) (by unfold mtpCs; simp) hq
  rw [← hrow] at cLo cHi
  have hreg : mtpRegion.eval (2 ^ logSize) preCols pub main rr = 1 := ev_region hj hi1 hi
  have hbool : ∀ c, 108 ≤ c → c < 124 → (main c rr).val ≤ 1 :=
    fun c h1 h2 => bool_val (sha_sat (chainSat_of hsat)) hr (Or.inr ⟨h1, h2⟩)
  have eb : bE.eval (2 ^ logSize) preCols pub main rr = ((bit main 108 rr).toNat : F) :=
    ev_bit (wrap_zero hr) (hbool 108 (by norm_num) (by norm_num))
  have ec : cE.eval (2 ^ logSize) preCols pub main rr = ((bit main 109 rr).toNat : F) :=
    ev_bit (wrap_zero hr) (hbool 109 (by norm_num) (by norm_num))
  have bE' := bA hsat hj (rr := rr) hr (base := E) (by decide)
  have ed : ∀ h ≤ 1, (dLimb h).eval (2 ^ logSize) preCols pub main rr =
      (((word main E rr).toNat / 2 ^ (16 * h) % 2 ^ 16 : ℕ) : F) :=
    fun h hh => ev_window (by omega) (wrap_zero hr) bE'
  have hown := mtp_ownTime hsat hj hi1 hi
  set T := winAt main j i
  set t := headerWord main j 17
  have eT : ∀ h ≤ 1, (timeLimb A h 0).eval (2 ^ logSize) preCols pub main rr = ((tl T h : ℕ) : F) :=
    fun h hh => ev_tl0 hsat hj hr (by decide) hh
  have et : ∀ h ≤ 1, (timeLimb W h 0).eval (2 ^ logSize) preCols pub main rr = ((tl t h : ℕ) : F) :=
    fun h hh => by rw [ev_tl0 hsat hj hr (by decide) hh, hown]
  have eT0 := eT 0 (by norm_num); have eT1 := eT 1 (by norm_num)
  have et0 := et 0 (by norm_num); have et1 := et 1 (by norm_num)
  have ed0 := ed 0 (by norm_num); have ed1 := ed 1 (by norm_num)
  unfold cmpLo at cLo; unfold cmpHi at cHi
  simp only [eval_mul', eval_sub', eval_add', eval_cst, hreg, eb, ec, eT0, eT1, et0, et1, ed0, ed1, one_mul]
    at cLo cHi
  have hT := leN_tl T; have ht := leN_tl t
  have lT0 := tl_lt T 0; have lT1 := tl_lt T 1; have lt0 := tl_lt t 0; have lt1 := tl_lt t 1
  have ld0 := Nat.mod_lt ((word main E rr).toNat / 2 ^ (16 * 0)) (show 0 < 2 ^ 16 by norm_num)
  have ld1 := Nat.mod_lt ((word main E rr).toNat / 2 ^ (16 * 1)) (show 0 < 2 ^ 16 by norm_num)
  have lc := Bool.toNat_le (bit main 109 rr)
  set d0 := (word main E rr).toNat / 2 ^ (16 * 0) % 2 ^ 16
  set d1 := (word main E rr).toNat / 2 ^ (16 * 1) % 2 ^ 16
  set c := (bit main 109 rr).toNat
  cases hb : bit main 108 rr
  · simp only [hb, Bool.toNat_false, Nat.cast_zero, zero_mul, zero_add, sub_zero, one_mul] at cLo cHi
    have n0 : tl t 0 + d0 = tl T 0 + 65536 * c :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cLo)
    have n1 : tl t 1 + d1 + c = tl T 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cHi)
    symm; simp only [decide_eq_false_iff_not, not_lt]; omega
  · simp only [hb, Bool.toNat_true, Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at cLo cHi
    have n0 : tl T 0 + 1 + d0 = tl t 0 + 65536 * c :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cLo)
    have n1 : tl T 1 + d1 + c = tl t 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cHi)
    symm; simp only [decide_eq_true_eq]; omega

/-- **Median time past.** At least 6 of a header's 11 window times are strictly below its own
time. -/
theorem mtp_count :
    6 ≤ ((Finset.range 11).filter (fun k => leN (winAt main j (k + 1)) < leN (headerWord main j 17))).card := by
  have hr : 256 * j + 240 < 2 ^ logSize := by omega
  have cc := mtp_sat hsat hj (c := countC) (by unfold mtpCs; simp) (q := 240) (by norm_num)
  have hbool : ∀ rr, rr < 2 ^ logSize → (main 108 rr).val ≤ 1 :=
    fun rr h => bool_val (sha_sat (chainSat_of hsat)) h (Or.inr ⟨by norm_num, by norm_num⟩)
  have esum : ∀ k ∈ Finset.range 11, (col 108 (-((11 - k : ℕ) : ℤ))).eval (2 ^ logSize) preCols pub main
      (256 * j + 240) = ((decide (leN (winAt main j (k + 1)) < leN (headerWord main j 17))).toNat : F) := by
    intro k hk
    simp only [Finset.mem_range] at hk
    rw [ev_bit (wrap_back (show 11 - k ≤ 256 * j + 240 by omega) hr) (hbool _ (by omega)),
      show 256 * j + 240 - (11 - k) = 256 * j + 228 + (k + 1) by omega, mtp_cmp hsat hj (by omega) (by omega)]
  have hbA := bA hsat hj (rr := 256 * j + 240) hr (base := A) (by decide)
  unfold countC at cc
  rw [show MTPC = MTP0 + 11 from rfl, eval_mul', ev_sel hj (k := 11) (by norm_num) (by norm_num), if_pos rfl,
    one_mul, eval_sub', eval_sub',
    eval_foldl_list _ (fun k => col 108 (-((11 - k : ℕ) : ℤ))), eval_cst, Nat.cast_zero, zero_add,
    list_range_sum, Finset.sum_congr rfl esum, eval_cst, ev_window (by norm_num) (wrap_zero hr) hbA] at cc
  rw [Finset.card_filter]
  set S := ∑ k ∈ Finset.range 11, if leN (winAt main j (k + 1)) < leN (headerWord main j 17) then 1 else 0
  have hS : (∑ k ∈ Finset.range 11, ((decide (leN (winAt main j (k + 1)) < leN (headerWord main j 17))).toNat : F))
      = ((S : ℕ) : F) := by
    rw [Nat.cast_sum]; refine Finset.sum_congr rfl (fun k _ => ?_)
    by_cases h : leN (winAt main j (k + 1)) < leN (headerWord main j 17) <;> simp [h]
  have hSle : S ≤ 11 := by
    calc S ≤ ∑ k ∈ Finset.range 11, 1 := Finset.sum_le_sum (fun k _ => by split <;> omega)
      _ = 11 := by simp
  rw [hS] at cc
  have hr8 := Nat.mod_lt ((word main A (256 * j + 240)).toNat / 2 ^ 0) (show 0 < 2 ^ 3 by norm_num)
  have : S = 6 + (word main A (256 * j + 240)).toNat / 2 ^ 0 % 2 ^ 3 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cc)
  omega


theorem mem_windowOut {c : Expr} {h : ℕ} (hh : h ≤ 1) (hc : c ∈ windowOut h) : c ∈ mtpCs := by
  unfold mtpCs
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp,
    List.mem_append_right _ hc⟩)

/-- The last header's window slots 1..10 are public outputs `68..87`. -/
theorem mtp_out (hlast : 2 ^ logSize = 256 * (j + 1)) {k : ℕ} (hk : k < 10) :
    winAt main j (k + 1) = pubWord pub (68 + 2 * k) := by
  unfold winAt
  rw [show 256 * j + 228 + (k + 1) = 256 * j + (229 + k) by omega]
  have hs : (slotSel (k + 1)).eval (2 ^ logSize) preCols pub main (256 * j + (229 + k)) = 1 := by
    rw [show 256 * j + (229 + k) = 256 * j + 228 + (k + 1) by omega]; exact ev_slotSel hj (by omega) (by omega)
  have hl : (pre LAST).eval (2 ^ logSize) preCols pub main (256 * j + (229 + k)) = 1 := by
    rw [eval_last (by omega)]; simp; omega
  have e : ∀ h ≤ 1, ((half16 (word main A (256 * j + (229 + k))) h : ℕ) : F) = pub (68 + 2 * k + h) :=
    fun h hh => by
      have := mtp_sat hsat hj (c := Expr.mul (.mul (slotSel (k + 1)) (pre LAST))
          (.sub (limb A h) (.pub (68 + 2 * k + h))))
        (mem_windowOut hsat hj hh (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)) (q := 229 + k) (by omega)
      rw [eval_mul', eval_mul', hs, hl, one_mul, one_mul, eval_sub',
        eval_limb (wrap_zero (by omega)) (bits (chainSat_of hsat) (by omega) (by decide)) hh] at this
      exact sub_eq_zero.mp this
  exact word_of_pubs (by simpa using e 0 (by norm_num)) (e 1 (by norm_num))


omit hsat hj in
theorem leN_lt (w : Word) : leN w < 2 ^ 32 := by
  have := w.isLt; unfold leN; omega

/-- **Median time past, in Core's terms.** If header `j`'s window is its real predecessors'
times (newest first, at most 11 used) padded with the genesis sentinel, the header passes
Bitcoin Core's `GetMedianTimePast` check. Establishing the window's form along a chain is
the job of the top-level theorem (roadmap `HC-TOP`), via `mtp_window`. -/
theorem mtp_core (real : List ℕ)
    (hwin : (List.range 11).map (fun k => leN (winAt main j (k + 1))) = (real ++ sentinel).take 11) :
    mtpOk (timeOf (headerWord main j)) real = true := by
  rw [timeOf_eq]
  apply sentinel_sound (leN_lt _) real
  rw [← hwin, List.countP_map]
  have h := mtp_count hsat hj
  rw [Finset.card_filter] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  simp only [List.range_succ, List.range_zero, List.nil_append, List.countP_append, List.countP_cons,
    List.countP_nil, Function.comp, decide_eq_true_eq] at ⊢
  simp only [Nat.reduceAdd, zero_add] at h ⊢
  omega

end Mtp

end StarkedAir.HeaderChain
