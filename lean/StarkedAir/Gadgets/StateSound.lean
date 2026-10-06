/-
Soundness of the header chain's state constraints (`HeaderChain.stateCs`, v3a): heights count
up from the public start height, `nBits` only changes at heights divisible by 2016, and the
period-start time resets exactly at those heights.
-/
import StarkedAir.Gadgets.PowSound

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-- Height of header `j` (row 218, `a` word). -/
def heightAt (main : ℕ → ℕ → F) (j : ℕ) : ℕ := (word main A (256 * j + 218)).toNat

/-- Period-start time of header `j` (row 218, `e` word; raw header-word-17 form). -/
def pstAt (main : ℕ → ℕ → F) (j : ℕ) : Word := word main E (256 * j + 218)

/-- Two limbs agreeing in the field make equal words. -/
theorem word_of_halves {x y : Word} (h0 : ((half16 x 0 : ℕ) : F) = ((half16 y 0 : ℕ) : F))
    (h1 : ((half16 x 1 : ℕ) : F) = ((half16 y 1 : ℕ) : F)) : x = y :=
  half16_inj (natCast_inj_of_lt (lt_P_of (by have := half16_lt x 0; omega)) (lt_P_of (by have := half16_lt y 0; omega)) h0)
    (natCast_inj_of_lt (lt_P_of (by have := half16_lt x 1; omega)) (lt_P_of (by have := half16_lt y 1; omega)) h1)

/-- Two limbs matching public inputs `b`, `b+1` make the word `pubWord pub b`. -/
theorem word_of_pubs {x : Word} {pub : ℕ → F} {b : ℕ} (h0 : ((half16 x 0 : ℕ) : F) = pub b)
    (h1 : ((half16 x 1 : ℕ) : F) = pub (b + 1)) : x = pubWord pub b := by
  have v : ∀ h ≤ 1, half16 x h = (pub (b + h)).val := fun h hh => by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · rw [Nat.add_zero, ← h0, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_P_of (by have := half16_lt x 0; omega))]
    · rw [← h1, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_P_of (by have := half16_lt x 1; omega))]
  have k0 := v 0 (by norm_num); have k1 := v 1 (by norm_num)
  simp only [Nat.add_zero] at k0
  have l0 := half16_lt x 0; have l1 := half16_lt x 1
  apply BitVec.eq_of_toNat_eq
  rw [half16_split, pubWord, BitVec.toNat_ofNat, ← k0, ← k1, Nat.mod_eq_of_lt (by omega)]

section State

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem state_sat : ∀ c ∈ stateCs, c.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 0 :=
  fun c hc => hsat _ (by omega) c (by show c ∈ constraints; simp only [constraints, List.mem_append]; tauto)

theorem fam_sat {h : ℕ} (hh : h ≤ 1) :
    ∀ c ∈ stateFam h, c.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 0 :=
  fun c hc => state_sat hsat hj c (List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp, hc⟩))

theorem hrow : 256 * j + 218 < 2 ^ logSize := by omega

theorem ev_stateSel : stateSel.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1 := by
  show (pre STATE).eval _ _ _ _ _ = 1
  rw [eval_oneRow (show preCols.getD STATE (.periodic [0]) = oneRow 218 from rfl) (hrow hsat hj),
    show (256 * j + 218) % 256 = 218 by omega]; simp

theorem ev_first : (pre FIRST).eval (2 ^ logSize) preCols pub main (256 * j + 218) =
    if j = 0 then 1 else 0 := by
  rw [eval_first (hrow hsat hj)]
  by_cases h0 : j = 0 <;> simp [h0] <;> omega

theorem ev_bitcol {base i : ℕ} (hbase : base + 32 ≤ 96) (hi : i < 32) {off : ℤ} {rr : ℕ}
    (hw : wrap (2 ^ logSize) (256 * j + 218) off = rr) (hrr : rr < 2 ^ logSize) :
    (col (base + i) off).eval (2 ^ logSize) preCols pub main (256 * j + 218) =
      ((bit main (base + i) rr).toNat : F) := by
  rw [eval_col, hw]; exact eq_bit (bits (chainSat_of hsat) hrr hbase i hi)

theorem ev_bitsAt {base k : ℕ} (hbase : base + 32 ≤ 96) (hk : k ≤ 32) {off : ℤ} {rr : ℕ}
    (hw : wrap (2 ^ logSize) (256 * j + 218) off = rr) (hrr : rr < 2 ^ logSize) :
    (bitsAt base k off).eval (2 ^ logSize) preCols pub main (256 * j + 218) =
      ((ofBits (fun i => bit main (base + i) rr) k : ℕ) : F) :=
  eval_sumPow_bits _ _ k (fun i hi => ev_bitcol hsat hj hbase (by omega) hw hrr)

/-- Facts read off the base state constraints at header `j`'s state row. -/
theorem state_row :
    heightAt main j < 2 ^ 30 ∧
    (bit main W (256 * j + 218) = true ↔ heightAt main j % 2016 = 0) ∧
    (bit main (W + 23) (256 * j + 218) = true ↔ (j ≠ 0 ∧ heightAt main j % 2016 ≠ 0)) ∧
    (bit main (W + 24) (256 * j + 218) = true ↔ (j = 0 ∧ heightAt main j % 2016 ≠ 0)) ∧
    (1 ≤ j → heightAt main j = heightAt main (j - 1) + 1) ∧
    (j = 0 → heightAt main j = (pubWord pub 32).toNat) := by
  set r := 256 * j + 218
  have hr : r < 2 ^ logSize := hrow hsat hj
  have hr1 : r + 1 < 2 ^ logSize := by omega
  have hcs := chainSat_of hsat
  have w0 : wrap (2 ^ logSize) r 0 = r := wrap_zero hr
  have w1 : wrap (2 ^ logSize) r 1 = r + 1 := wrap_one hr1
  have hsel := ev_stateSel hsat hj
  have hfirst := ev_first hsat hj
  have hb : ∀ c ∈ stateBase, c.eval (2 ^ logSize) preCols pub main r = 0 :=
    fun c hc => state_sat hsat hj c (List.mem_append_left _ hc)
  simp only [stateBase, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hb
  obtain ⟨e30, e31, eLo, eHi, eF0, eF1, eDec, eRem, eFl, eNf, eG, eG2⟩ := hb
  -- Bits used below.
  have bitv : ∀ base, base + 32 ≤ 96 → ∀ i < 32, (col (base + i)).eval (2 ^ logSize) preCols pub main r =
      ((bit main (base + i) r).toNat : F) := fun base hb i hi => ev_bitcol hsat hj hb hi w0 hr
  have fl : flagE.eval (2 ^ logSize) preCols pub main r = ((bit main W r).toNat : F) := by
    unfold flagE; have := bitv W (by decide) 0 (by norm_num); simpa using this
  have gv : gE.eval (2 ^ logSize) preCols pub main r = ((bit main (W + 23) r).toNat : F) :=
    bitv W (by decide) 23 (by norm_num)
  have g2v : g2E.eval (2 ^ logSize) preCols pub main r = ((bit main (W + 24) r).toNat : F) :=
    bitv W (by decide) 24 (by norm_num)
  have cv : hCarryE.eval (2 ^ logSize) preCols pub main r = ((bit main CA_LO r).toNat : F) := by
    unfold hCarryE; rw [eval_col, w0]
    exact eq_bit (bool_val (sha_sat hcs) hr (Or.inr ⟨by decide, by decide⟩))
  -- Height bits 30, 31 are zero.
  rw [eval_mul', hsel, one_mul, bitv A (by decide) 30 (by norm_num)] at e30
  rw [eval_mul', hsel, one_mul, bitv A (by decide) 31 (by norm_num)] at e31
  have b30 : bit main (A + 30) r = false := by cases h : bit main (A + 30) r <;> simp_all
  have b31 : bit main (A + 31) r = false := by cases h : bit main (A + 31) r <;> simp_all
  have hH : heightAt main j = ofBits (fun i => bit main (A + i) r) 30 := by
    unfold heightAt
    have e := ofBits_add (fun i => (word main A r).getLsbD i) 30 2
    simp only [show (30 + 2 : ℕ) = 32 from rfl] at e
    rw [toNat_eq_ofBits, e]
    have : ofBits (fun i => (word main A r).getLsbD (30 + i)) 2 = 0 := by
      simp only [ofBits, word_getLsbD _ _ (show 30 + 0 < 32 by norm_num), word_getLsbD _ _ (show 30 + 1 < 32 by norm_num)]
      simp [← Nat.add_assoc, b30, b31]
    rw [this, Nat.mul_zero, Nat.add_zero]
    exact ofBits_congr (fun i hi => word_getLsbD _ _ (by omega))
  have hHlt : heightAt main j < 2 ^ 30 := hH ▸ ofBits_lt _ 30
  -- Decomposition height = 2016·q + rem with rem ≤ 2015.
  set Q := ofBits (fun i => bit main (A + i) (r + 1)) 20
  set R := ofBits (fun i => bit main (W + 1 + i) r) 11
  set M := ofBits (fun i => bit main (W + 12 + i) r) 11
  set X := ofBits (fun i => bit main (E + i) (r + 1)) 11
  have hQ : qE.eval (2 ^ logSize) preCols pub main r = (Q : F) := ev_bitsAt hsat hj (by decide) (by norm_num) w1 hr1
  have hR : remE.eval (2 ^ logSize) preCols pub main r = (R : F) := by
    unfold remE bitsAt
    exact eval_sumPow_bits _ _ 11 (fun i hi => by rw [Nat.add_assoc]; exact bitv W (by decide) _ (by omega))
  have hM : remM1E.eval (2 ^ logSize) preCols pub main r = (M : F) := by
    unfold remM1E bitsAt
    exact eval_sumPow_bits _ _ 11 (fun i hi => by rw [Nat.add_assoc]; exact bitv W (by decide) _ (by omega))
  have hX : remCompE.eval (2 ^ logSize) preCols pub main r = (X : F) := ev_bitsAt hsat hj (by decide) (by norm_num) w1 hr1
  have hHe : heightE.eval (2 ^ logSize) preCols pub main r = (heightAt main j : F) := by
    rw [hH]; exact ev_bitsAt hsat hj (by decide) (by norm_num) w0 hr
  have Qlt := ofBits_lt (fun i => bit main (A + i) (r + 1)) 20
  have Rlt := ofBits_lt (fun i => bit main (W + 1 + i) r) 11
  have Mlt := ofBits_lt (fun i => bit main (W + 12 + i) r) 11
  have Xlt := ofBits_lt (fun i => bit main (E + i) (r + 1)) 11
  rw [eval_mul', hsel, one_mul, eval_sub', eval_add', eval_mul', eval_cst, hHe, hQ, hR] at eDec
  have hdec : heightAt main j = 2016 * Q + R :=
    natCast_inj_of_lt (lt_P_of (by omega)) (show 2016 * Q + R < P by norm_num [P]; omega)
      (by push_cast at eDec ⊢; linear_combination eDec)
  rw [eval_mul', hsel, one_mul, eval_sub', eval_add', eval_cst, hR, hX] at eRem
  have hrem : R + X = 2015 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast at eRem ⊢; linear_combination -eRem)
  have hmod : heightAt main j % 2016 = R := by omega
  -- flag ↔ rem = 0.
  rw [eval_mul', eval_mul', hsel, one_mul, fl, hR] at eFl
  rw [eval_mul', eval_mul', hsel, one_mul, eval_sub', eval_cst, fl, eval_sub', eval_sub', eval_cst, hR, hM] at eNf
  have hflag : bit main W r = true ↔ R = 0 := by
    constructor
    · intro h; rw [h] at eFl; simp at eFl
      exact natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by simpa using eFl)
    · intro h0
      by_contra hf
      have hf' : bit main W r = false := by simpa using hf
      rw [hf'] at eNf; simp at eNf
      have : R = M + 1 := natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
        (by push_cast; linear_combination eNf)
      omega
  -- g, g2.
  unfold notFirst at eG
  rw [eval_mul', hsel, one_mul, eval_sub', gv, eval_mul', eval_sub', eval_cst, hfirst, eval_sub', eval_cst, fl] at eG
  rw [eval_mul', hsel, one_mul, eval_sub', g2v, eval_mul', hfirst, eval_sub', eval_cst, fl] at eG2
  have hg : bit main (W + 23) r = true ↔ (j ≠ 0 ∧ heightAt main j % 2016 ≠ 0) := by
    rw [hmod]
    by_cases h0 : j = 0 <;> by_cases hR : R = 0 <;> cases hb1 : bit main W r <;>
      cases hb2 : bit main (W + 23) r <;> simp_all <;> norm_num at eG
  have hg2 : bit main (W + 24) r = true ↔ (j = 0 ∧ heightAt main j % 2016 ≠ 0) := by
    rw [hmod]
    by_cases h0 : j = 0 <;> by_cases hR : R = 0 <;> cases hb1 : bit main W r <;>
      cases hb2 : bit main (W + 24) r <;> simp_all <;> norm_num at eG2
  refine ⟨hHlt, by rw [hmod]; exact hflag, hg, hg2, fun hj1 => ?_, fun hj0 => ?_⟩
  · -- height increments.
    have hfz : (pre FIRST).eval (2 ^ logSize) preCols pub main r = 0 := by rw [hfirst]; simp; omega
    have hlo := eval_limb (pc := preCols) (pub := pub) (r := r) (wrap_back (k := 256) (by omega) hr)
      (bits hcs (r := r - 256) (by omega) (base := A) (by decide)) (half := 0) (by norm_num)
    have hhi := eval_limb (pc := preCols) (pub := pub) (r := r) (wrap_back (k := 256) (by omega) hr)
      (bits hcs (r := r - 256) (by omega) (base := A) (by decide)) (half := 1) (by norm_num)
    have clo := eval_limb (pc := preCols) (pub := pub) w0 (bits hcs hr (base := A) (by decide)) (half := 0) (by norm_num)
    have chi := eval_limb (pc := preCols) (pub := pub) w0 (bits hcs hr (base := A) (by decide)) (half := 1) (by norm_num)
    simp only [Nat.cast_ofNat] at hlo hhi
    rw [eval_mul', eval_mul', hsel, one_mul] at eLo eHi
    unfold notFirst at eLo eHi
    rw [eval_sub', eval_cst, hfz, eval_sub', eval_add', eval_add', eval_mul', eval_cst, eval_cst, hlo, clo, cv] at eLo
    rw [eval_sub', eval_cst, hfz, eval_sub', eval_add', hhi, chi, cv] at eHi
    simp only [Nat.cast_one, sub_zero, one_mul] at eLo eHi
    have cb := Bool.toNat_le (bit main CA_LO r)
    have l0 := half16_lt (word main A (r - 256)) 0; have l1 := half16_lt (word main A (r - 256)) 1
    have m0 := half16_lt (word main A r) 0; have m1 := half16_lt (word main A r) 1
    have nlo : half16 (word main A (r - 256)) 0 + 1 = half16 (word main A r) 0 + 65536 * (bit main CA_LO r).toNat :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination eLo)
    have nhi : half16 (word main A (r - 256)) 1 + (bit main CA_LO r).toNat = half16 (word main A r) 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination eHi)
    unfold heightAt
    rw [show 256 * (j - 1) + 218 = r - 256 by omega, half16_split (word main A r),
      half16_split (word main A (r - 256))]
    omega
  · -- first height is public.
    have hf1 : (pre FIRST).eval (2 ^ logSize) preCols pub main r = 1 := by rw [hfirst]; simp [hj0]
    have clo := eval_limb (pc := preCols) (pub := pub) w0 (bits hcs hr (base := A) (by decide)) (half := 0) (by norm_num)
    have chi := eval_limb (pc := preCols) (pub := pub) w0 (bits hcs hr (base := A) (by decide)) (half := 1) (by norm_num)
    rw [eval_mul', eval_mul', hsel, one_mul, hf1, one_mul, eval_sub'] at eF0 eF1
    simp only [Expr.eval] at eF0 eF1
    rw [clo] at eF0; rw [chi] at eF1
    unfold heightAt
    rw [word_of_pubs (sub_eq_zero.mp eF0) (sub_eq_zero.mp eF1)]

/-- A switched-on member of a limb-pair family pins a word. -/
theorem fam_word {S : Expr} {X : ℕ} {off : ℤ} {rhs : ℕ → Expr} {rr : ℕ} (Y : Word)
    (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h off) (rhs h)) ∈ stateFam h)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1)
    (hw : wrap (2 ^ logSize) (256 * j + 218) off = rr) (hrr : rr < 2 ^ logSize) (hX : X + 32 ≤ 96)
    (hrhs : ∀ h ≤ 1, (rhs h).eval (2 ^ logSize) preCols pub main (256 * j + 218) = ((half16 Y h : ℕ) : F)) :
    word main X rr = Y :=
  eqLimbs_word Y (fun c hc => by
      simp only [eqLimbs, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      exact fam_sat hsat hj (by rcases hh with rfl | rfl <;> norm_num) _ (hmem h (by rcases hh with rfl | rfl <;> norm_num)))
    hS hw (bits (chainSat_of hsat) hrr hX) hrhs

theorem fam_pub_off {S : Expr} {X b rr : ℕ} {off : ℤ}
    (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h off) (.pub (b + h))) ∈ stateFam h)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1)
    (hw : wrap (2 ^ logSize) (256 * j + 218) off = rr) (hrr : rr < 2 ^ logSize) (hX : X + 32 ≤ 96) :
    word main X rr = pubWord pub b := by
  have hb := bits (chainSat_of hsat) hrr hX
  have e : ∀ h ≤ 1, ((half16 (word main X rr) h : ℕ) : F) = pub (b + h) := fun h hh => by
    have := fam_sat hsat hj hh _ (hmem h hh)
    rw [eval_mul', hS, one_mul, eval_sub', eval_limb hw hb hh] at this
    exact sub_eq_zero.mp this
  exact word_of_pubs (by simpa using e 0 (by norm_num)) (e 1 (by norm_num))

theorem fam_pub {S : Expr} {X b : ℕ} (hmem : ∀ h ≤ 1, Expr.mul S (.sub (limb X h 0) (.pub (b + h))) ∈ stateFam h)
    (hS : S.eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1) (hX : X + 32 ≤ 96) :
    word main X (256 * j + 218) = pubWord pub b :=
  eqLimbs_pub (fun c hc => by
      simp only [eqLimbs, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      exact fam_sat hsat hj (by rcases hh with rfl | rfl <;> norm_num) _ (hmem h (by rcases hh with rfl | rfl <;> norm_num)))
    hS (hrow hsat hj) rfl (bits (chainSat_of hsat) (hrow hsat hj) hX)

theorem ev_selBit {k : ℕ} (hk : k < 32) (hb : bit main (W + k) (256 * j + 218) = true) :
    (Expr.mul stateSel (col (W + k))).eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1 := by
  rw [eval_mul', ev_stateSel hsat hj, one_mul, ev_bitcol hsat hj (by decide) hk (wrap_zero (hrow hsat hj)) (hrow hsat hj), hb]
  simp

/-- `nBits` only changes at heights divisible by 2016. -/
theorem nbits_fact (hm : heightAt main j % 2016 ≠ 0) :
    headerWord main j 18 = if j = 0 then pubWord pub 34 else headerWord main (j - 1) 18 := by
  obtain ⟨-, -, hg, hg2, -, -⟩ := state_row hsat hj
  have hr := hrow hsat hj
  have hw : wrap (2 ^ logSize) (256 * j + 218) (-140) = 256 * j + 218 - 140 := by
    rw [show (-140 : ℤ) = -((140 : ℕ) : ℤ) by norm_num, wrap_back (by omega) hr]
  simp only [headerWord, show ¬ (18 < 16) by norm_num, if_false]
  rw [show 256 * j + 76 + (18 - 16) = 256 * j + 218 - 140 by omega]
  by_cases h0 : j = 0
  · simp only [h0, if_true]
    have := fam_pub_off hsat hj (S := .mul stateSel g2E) (X := W) (b := 34) (off := -140)
      (fun h _ => by simp [stateFam, nbitsFirst]) (ev_selBit hsat hj (by norm_num) (hg2.mpr ⟨h0, hm⟩))
      hw (by omega) (by decide)
    simpa [h0] using this
  · simp only [h0, if_false]
    rw [show 256 * (j - 1) + 76 + (18 - 16) = 256 * j + 218 - 396 by omega]
    have hw' : wrap (2 ^ logSize) (256 * j + 218) (-396) = 256 * j + 218 - 396 := by
      rw [show (-396 : ℤ) = -((396 : ℕ) : ℤ) by norm_num, wrap_back (by omega) hr]
    exact fam_word hsat hj _ (S := .mul stateSel gE) (X := W) (off := -140) (rhs := fun h => limb W h (-396))
      (fun h _ => by simp [stateFam, nbitsLink]) (ev_selBit hsat hj (by norm_num) (hg.mpr ⟨h0, hm⟩))
      hw (by omega) (by decide)
      (fun h hh => eval_limb hw' (bits (chainSat_of hsat) (by omega) (by decide)) hh)

/-- The period-start time resets at a boundary and is otherwise inherited. -/
theorem pst_fact :
    pstAt main j = if heightAt main j % 2016 = 0 then headerWord main j 17
      else if j = 0 then pubWord pub 36 else pstAt main (j - 1) := by
  obtain ⟨-, hf, hg, hg2, -, -⟩ := state_row hsat hj
  have hr := hrow hsat hj
  unfold pstAt
  by_cases hm : heightAt main j % 2016 = 0
  · simp only [hm, if_true, headerWord, show (17 < 16) = False by norm_num, if_false]
    have hw : wrap (2 ^ logSize) (256 * j + 218) (-141) = 256 * j + 76 + (17 - 16) := by
      rw [show (-141 : ℤ) = -((141 : ℕ) : ℤ) by norm_num, wrap_back (by omega) hr]; omega
    have hwE : wrap (2 ^ logSize) (256 * j + 218) 0 = 256 * j + 218 := wrap_zero hr
    exact fam_word hsat hj _ (S := .mul stateSel flagE) (X := E) (off := 0) (rhs := fun h => limb W h (-141))
      (fun h _ => by simp [stateFam, pstReset]) (by
        have := ev_selBit hsat hj (k := 0) (by norm_num) (by simpa using hf.mpr hm)
        simpa [flagE] using this)
      hwE hr (by decide)
      (fun h hh => eval_limb hw (bits (chainSat_of hsat) (by omega) (by decide)) hh)
  · simp only [hm, if_false]
    by_cases h0 : j = 0
    · simp only [h0, if_true]
      have := fam_pub hsat hj (S := .mul stateSel g2E) (X := E) (b := 36)
        (fun h _ => by simp [stateFam, pstFirst]) (ev_selBit hsat hj (by norm_num) (hg2.mpr ⟨h0, hm⟩)) (by decide)
      simpa [h0] using this
    · simp only [h0, if_false]
      have hw' : wrap (2 ^ logSize) (256 * j + 218) (-256) = 256 * (j - 1) + 218 := by
        rw [show (-256 : ℤ) = -((256 : ℕ) : ℤ) by norm_num, wrap_back (by omega) hr]; omega
      exact fam_word hsat hj _ (S := .mul stateSel gE) (X := E) (off := 0) (rhs := fun h => limb E h (-256))
        (fun h _ => by simp [stateFam, pstCarry]) (ev_selBit hsat hj (by norm_num) (hg.mpr ⟨h0, hm⟩))
        (wrap_zero hr) hr (by decide)
        (fun h hh => eval_limb hw' (bits (chainSat_of hsat) (by omega) (by decide)) hh)

/-- The last header's state is public. -/
theorem out_fact (hlast : 256 * (j + 1) = 2 ^ logSize) :
    heightAt main j = (pubWord pub 38).toNat ∧ headerWord main j 18 = pubWord pub 40 ∧
      pstAt main j = pubWord pub 42 := by
  have hr := hrow hsat hj
  have hS : (Expr.mul stateSel (pre LAST)).eval (2 ^ logSize) preCols pub main (256 * j + 218) = 1 := by
    rw [eval_mul', ev_stateSel hsat hj, one_mul, eval_last hr, if_pos (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold heightAt
    rw [fam_pub hsat hj (S := .mul stateSel (pre LAST)) (X := A) (b := 38)
      (fun h _ => by simp [stateFam, outHeight]) hS (by decide)]
  · simp only [headerWord, show ¬ (18 < 16) by norm_num, if_false]
    have hw : wrap (2 ^ logSize) (256 * j + 218) (-140) = 256 * j + 76 + (18 - 16) := by
      rw [show (-140 : ℤ) = -((140 : ℕ) : ℤ) by norm_num, wrap_back (by omega) hr]; omega
    exact fam_pub_off hsat hj (S := .mul stateSel (pre LAST)) (X := W) (b := 40) (off := -140)
      (fun h _ => by simp [stateFam, outNBits]) hS hw (by omega) (by decide)
  · exact fam_pub hsat hj (S := .mul stateSel (pre LAST)) (X := E) (b := 42)
      (fun h _ => by simp [stateFam, outPst]) hS (by decide)

end State

/-- **Chain state soundness (v3a).** In a satisfying trace with `H = 2^logSize / 256` headers:
heights count up by one from the public start height (and stay below 2^30); `nBits` equals
the predecessor's (or the public predecessor value) whenever the height is not divisible by
2016; the period-start time resets to the header's own time exactly at those heights and is
otherwise inherited; and the last header's height, nBits and period-start time are public. -/
theorem state_sound {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : air.Satisfied logSize pub main) (hlog : 8 ≤ logSize) :
    let H := 2 ^ logSize / 256
    (∀ j < H, heightAt main j < 2 ^ 30) ∧
    heightAt main 0 = (pubWord pub 32).toNat ∧
    (∀ j < H, 1 ≤ j → heightAt main j = heightAt main (j - 1) + 1) ∧
    (∀ j < H, heightAt main j % 2016 ≠ 0 →
      headerWord main j 18 = if j = 0 then pubWord pub 34 else headerWord main (j - 1) 18) ∧
    (∀ j < H, pstAt main j = if heightAt main j % 2016 = 0 then headerWord main j 17
      else if j = 0 then pubWord pub 36 else pstAt main (j - 1)) ∧
    (heightAt main (H - 1) = (pubWord pub 38).toNat ∧ headerWord main (H - 1) 18 = pubWord pub 40 ∧
      pstAt main (H - 1) = pubWord pub 42) := by
  intro H
  have hN : 2 ^ logSize = 256 * H := by
    have : 2 ^ logSize = 2 ^ 8 * 2 ^ (logSize - 8) := by rw [← pow_add]; congr 1; omega
    simp only [H, this]; norm_num
  have hH : 1 ≤ H := by
    have : 1 ≤ 2 ^ (logSize - 8) := Nat.one_le_two_pow
    have h2 : 2 ^ logSize = 2 ^ 8 * 2 ^ (logSize - 8) := by rw [← pow_add]; congr 1; omega
    omega
  refine ⟨fun j hj => (state_row hsat (j := j) (by omega)).1,
    (state_row hsat (j := 0) (by omega)).2.2.2.2.2 rfl,
    fun j hj hj1 => (state_row hsat (j := j) (by omega)).2.2.2.2.1 hj1,
    fun j hj hm => nbits_fact hsat (by omega) hm,
    fun j hj => pst_fact hsat (by omega),
    out_fact hsat (by omega) (by omega)⟩

end StarkedAir.HeaderChain
