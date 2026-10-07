/-
Soundness of the retarget division and cap branches (header chain v3b).
-/
import StarkedAir.Gadgets.RetargetSound

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

section Div

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem ev_byD {dd : ℕ} (hdd : dd ≤ 2)
    (hfl : ∀ k < 3, bit main (W + (5 + k)) (256 * j + 221) = decide (k = dd)) (f : ℕ → Expr) :
    (byD f).eval (2 ^ logSize) preCols pub main (256 * j + 221) =
      (f dd).eval (2 ^ logSize) preCols pub main (256 * j + 221) := by
  unfold byD
  rw [eval_add', eval_add', eval_mul', eval_mul', eval_mul', ev_dflag hsat hj (k := 0) (by norm_num),
    ev_dflag hsat hj (k := 1) (by norm_num), ev_dflag hsat hj (k := 2) (by norm_num),
    hfl 0 (by norm_num), hfl 1 (by norm_num), hfl 2 (by norm_num)]
  interval_cases dd <;> simp

theorem ev_dAny {dd : ℕ} (hdd : dd ≤ 2)
    (hfl : ∀ k < 3, bit main (W + (5 + k)) (256 * j + 221) = decide (k = dd)) :
    dAny.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 1 := by
  unfold dAny
  rw [eval_add', eval_add', ev_dflag hsat hj (k := 0) (by norm_num),
    ev_dflag hsat hj (k := 1) (by norm_num), ev_dflag hsat hj (k := 2) (by norm_num),
    hfl 0 (by norm_num), hfl 1 (by norm_num), hfl 2 (by norm_num)]
  interval_cases dd <;> simp

omit hsat hj in
theorem divBytes_le (dd i : ℕ) : (divBytes dd).getD i 0 ≤ 255 := by
  rcases dd with _ | _ | dd <;> rcases i with _ | _ | _ | _ | _ | i <;> simp [divBytes]

omit hsat hj in
theorem divM1Bytes_le (dd i : ℕ) : (divM1Bytes dd).getD i 0 ≤ 255 := by
  rcases dd with _ | _ | dd <;> rcases i with _ | _ | _ | _ | _ | i <;> simp [divM1Bytes]

omit hsat hj in
theorem divBytes_val {dd : ℕ} (hdd : dd ≤ 2) :
    (divBytes dd).getD 0 0 + 256 * (divBytes dd).getD 1 0 + 65536 * (divBytes dd).getD 2 0 +
      2 ^ 24 * (divBytes dd).getD 3 0 + 2 ^ 32 * (divBytes dd).getD 4 0 = 1209600 * 256 ^ dd := by
  interval_cases dd <;> simp [divBytes]

omit hsat hj in
theorem divM1Bytes_val {dd : ℕ} (hdd : dd ≤ 2) :
    (divM1Bytes dd).getD 0 0 + 256 * (divM1Bytes dd).getD 1 0 + 65536 * (divM1Bytes dd).getD 2 0 +
      2 ^ 24 * (divM1Bytes dd).getD 3 0 + 2 ^ 32 * (divM1Bytes dd).getD 4 0 + 1 = 1209600 * 256 ^ dd := by
  interval_cases dd <;> simp [divM1Bytes]

omit hsat hj in
theorem leN_div24 (w : Word) : leN w / 2 ^ 24 = w.toNat % 256 := by
  have := w.isLt; unfold leN; omega

omit hsat hj in
theorem leN_split (w : Word) (hs : w.toNat / 2 ^ 8 % 256 < 128) :
    leN w = mantNat w + 2 ^ 24 * (w.toNat % 256) := by
  unfold leN mantNat; omega

omit hsat hj in
theorem lim_ok {m s : ℕ} (hs : s < 27) (hm : m < 2 ^ 23) (h26 : s = 26 → m < 65536) :
    (m + 1) * 256 ^ s ≤ 2 ^ 224 := by
  rcases (by omega : s = 26 ∨ s ≤ 25) with rfl | hle
  · calc (m + 1) * 256 ^ 26 ≤ 2 ^ 16 * 256 ^ 26 := Nat.mul_le_mul_right _ (by have := h26 rfl; omega)
      _ = 2 ^ 224 := by norm_num
  · calc (m + 1) * 256 ^ s ≤ 2 ^ 23 * 256 ^ 25 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) hle)
      _ ≤ 2 ^ 224 := by norm_num

omit hsat hj in
theorem digits4 (x : ℕ) (hx : x < 2 ^ 32) : x = x % 2 ^ 8 + 256 * (x / 2 ^ 8 % 2 ^ 8) +
    65536 * (x / 2 ^ 16 % 2 ^ 8) + 2 ^ 24 * (x / 2 ^ 24 % 2 ^ 8) := by omega

omit hsat hj in
theorem digits2 (x : ℕ) : x % 2 ^ 16 = x % 2 ^ 8 + 256 * (x / 2 ^ 8 % 2 ^ 8) := by omega

omit hsat hj in
theorem divq_arith {D0 D1 D2 D3 D4 o0 o1 o2 q0 q1 q2 q3 q4 k0 k1 k2 k3 k4 k5 k6 p0 p1 p2 p3 p4 p5 : ℕ}
    (n0 : D0 * o0 + q0 = 256 * k0)
    (n1 : D0 * o1 + D1 * o0 + q1 + k0 = p0 + 256 * k1)
    (n2 : D0 * o2 + D1 * o1 + D2 * o0 + q2 + k1 = p1 + 256 * k2)
    (n3 : D1 * o2 + D2 * o1 + D3 * o0 + q3 + k2 = p2 + 256 * k3)
    (n4 : D2 * o2 + D3 * o1 + D4 * o0 + q4 + k3 = p3 + 256 * k4)
    (n5 : D3 * o2 + D4 * o1 + k4 = p4 + 256 * k5)
    (n6 : D4 * o2 + k5 = p5 + 256 * k6) (n7 : k6 = 0) :
    (D0 + 256 * D1 + 65536 * D2 + 2 ^ 24 * D3 + 2 ^ 32 * D4) * (o0 + 256 * o1 + 65536 * o2) +
      (q0 + 256 * q1 + 65536 * q2 + 2 ^ 24 * q3 + 2 ^ 32 * q4) =
      256 * (p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 + 2 ^ 32 * (p4 + 256 * p5)) := by
  subst n7
  zify at n0 n1 n2 n3 n4 n5 n6 ⊢
  linear_combination n0 + 256 * n1 + 65536 * n2 + 2 ^ 24 * n3 + 2 ^ 32 * n4 + 2 ^ 40 * n5 + 2 ^ 48 * n6

set_option maxHeartbeats 1600000 in
/-- Division columns: `divisor · mant' + ρ = 256 · P0`, with `ρ` read from row 225. -/
theorem rt_divq {dd : ℕ} (hdd : dd ≤ 2)
    (hfl : ∀ k < 3, bit main (W + (5 + k)) (256 * j + 221) = decide (k = dd)) :
    let pa := (word main A (256 * j + 223)).toNat
    let pe := (word main E (256 * j + 223)).toNat
    let ra := (word main A (256 * j + 225)).toNat
    let re := (word main E (256 * j + 225)).toNat
    1209600 * 256 ^ dd * mantNat (headerWord main j 18) + (ra + 2 ^ 32 * (re % 2 ^ 8)) =
      256 * (pa + 2 ^ 32 * (pe % 2 ^ 16)) := by
  intro pa pe ra re
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  have hy : headerWord main j 18 = word main W (256 * j + 78) := by simp [headerWord]
  have w2 : wrap (2 ^ logSize) r 2 = 256 * j + 223 := by rw [wrap_eq (by omega) (by omega)]; omega
  have w4 : wrap (2 ^ logSize) r 4 = 256 * j + 225 := by rw [wrap_eq (by omega) (by omega)]; omega
  have w5 : wrap (2 ^ logSize) r 5 = 256 * j + 226 := by rw [wrap_eq (by omega) (by omega)]; omega
  have bW78 := bA hsat hj (rr := 256 * j + 78) (by omega) (base := W) (by decide)
  have bA2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := A) (by decide)
  have bE2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := E) (by decide)
  have bA4 := bA hsat hj (rr := 256 * j + 225) (by omega) (base := A) (by decide)
  have bE4 := bA hsat hj (rr := 256 * j + 225) (by omega) (base := E) (by decide)
  have bE5 := bA hsat hj (rr := 256 * j + 226) (by omega) (base := E) (by decide)
  have bW5 := bA hsat hj (rr := 256 * j + 226) (by omega) (base := W) (by decide)
  have hsel : Expr.eval (2 ^ logSize) preCols pub main r rtSel = 1 := ev_rtSel hsat hj
  have hany : Expr.eval (2 ^ logSize) preCols pub main r dAny = 1 := ev_dAny hsat hj hdd hfl
  have hbyD : ∀ f, Expr.eval (2 ^ logSize) preCols pub main r (byD f) =
      Expr.eval (2 ^ logSize) preCols pub main r (f dd) := ev_byD hsat hj hdd hfl
  set yv := (word main W (256 * j + 78)).toNat
  set dv := (word main E (256 * j + 226)).toNat
  set dw := (word main W (256 * j + 226)).toNat
  have eo : ∀ i < 3, (ownMant i).eval (2 ^ logSize) preCols pub main r =
      ((if i = 0 then yv / 2 ^ 24 % 2 ^ 8 else if i = 1 then yv / 2 ^ 16 % 2 ^ 8 else yv / 2 ^ 8 % 2 ^ 7 : ℕ) : F) := by
    intro i hi
    interval_cases i
    · exact ev_window (by norm_num) (w143 hj) bW78
    · exact ev_window (by norm_num) (w143 hj) bW78
    · exact ev_window (by norm_num) (w143 hj) bW78
  have er : ∀ k < 8, (rhoByte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then ra / 2 ^ (8 * k) % 2 ^ 8 else if k = 4 then re / 2 ^ 0 % 2 ^ 8 else 0 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bE4
    · rw [show rhoByte 5 = cst 0 from rfl, eval_cst]; simp
    · rw [show rhoByte 6 = cst 0 from rfl, eval_cst]; simp
    · rw [show rhoByte 7 = cst 0 from rfl, eval_cst]; simp
  have ec : ∀ k < 7, (dcE k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then dv / 2 ^ (8 * k) % 2 ^ 8 else dw / 2 ^ (8 * (k - 4)) % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w5 bE5
    · exact ev_window (by norm_num) w5 bE5
    · exact ev_window (by norm_num) w5 bE5
    · exact ev_window (by norm_num) w5 bE5
    · exact ev_window (by norm_num) w5 bW5
    · exact ev_window (by norm_num) w5 bW5
    · exact ev_window (by norm_num) w5 bW5
  have ep : ∀ k < 7, (p0Byte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then pa / 2 ^ (8 * k) % 2 ^ 8 else if k < 6 then pe / 2 ^ (8 * (k - 4)) % 2 ^ 8 else 0 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bE2
    · exact ev_window (by norm_num) w2 bE2
    · rw [show p0Byte 6 = cst 0 from rfl, eval_cst]; simp
  have col : ∀ k < 8, (divCol k).eval (2 ^ logSize) preCols pub main r = 0 := fun k hk =>
    rt_sat hsat hj _ (by
      unfold retargetCs
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
  have c0 := col 0 (by norm_num); have c1 := col 1 (by norm_num); have c2 := col 2 (by norm_num)
  have c3 := col 3 (by norm_num); have c4 := col 4 (by norm_num); have c5 := col 5 (by norm_num)
  have c6 := col 6 (by norm_num); have c7 := col 7 (by norm_num)
  have s0 : ∀ g, sumCol 0 g 5 3 = (cst 0).add (g 0 0) := fun _ => rfl
  have s1 : ∀ g, sumCol 1 g 5 3 = ((cst 0).add (g 0 1)).add (g 1 0) := fun _ => rfl
  have s2 : ∀ g, sumCol 2 g 5 3 = (((cst 0).add (g 0 2)).add (g 1 1)).add (g 2 0) := fun _ => rfl
  have s3 : ∀ g, sumCol 3 g 5 3 = (((cst 0).add (g 1 2)).add (g 2 1)).add (g 3 0) := fun _ => rfl
  have s4 : ∀ g, sumCol 4 g 5 3 = (((cst 0).add (g 2 2)).add (g 3 1)).add (g 4 0) := fun _ => rfl
  have s5 : ∀ g, sumCol 5 g 5 3 = ((cst 0).add (g 3 2)).add (g 4 1) := fun _ => rfl
  have s6 : ∀ g, sumCol 6 g 5 3 = (cst 0).add (g 4 2) := fun _ => rfl
  have s7 : ∀ g, sumCol 7 g 5 3 = cst 0 := fun _ => rfl
  have eo0 := eo 0 (by norm_num); have eo1 := eo 1 (by norm_num); have eo2 := eo 2 (by norm_num)
  have er0 := er 0 (by norm_num); have er1 := er 1 (by norm_num); have er2 := er 2 (by norm_num)
  have er3 := er 3 (by norm_num); have er4 := er 4 (by norm_num); have er5 := er 5 (by norm_num)
  have er6 := er 6 (by norm_num); have er7 := er 7 (by norm_num)
  have ec0 := ec 0 (by norm_num); have ec1 := ec 1 (by norm_num); have ec2 := ec 2 (by norm_num)
  have ec3 := ec 3 (by norm_num); have ec4 := ec 4 (by norm_num); have ec5 := ec 5 (by norm_num)
  have ec6 := ec 6 (by norm_num)
  have ep0 := ep 0 (by norm_num); have ep1 := ep 1 (by norm_num); have ep2 := ep 2 (by norm_num)
  have ep3 := ep 3 (by norm_num); have ep4 := ep 4 (by norm_num); have ep5 := ep 5 (by norm_num)
  have ep6 := ep 6 (by norm_num)
  simp only [Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, pow_zero,
    Nat.div_one] at eo0 eo1 eo2 er0 er1 er2 er3 er4 er5 er6 er7 ec0 ec1 ec2 ec3 ec4 ec5 ec6 ep0 ep1 ep2 ep3 ep4 ep5 ep6
  simp only [divCol, hbyD, s0, s1, s2, s3, s4, s5, s6, s7, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte,
    Nat.reduceSub, eval_mul', eval_sub', eval_add', eval_cst, hsel, hany, one_mul, eo0, eo1, eo2,
    er0, er1, er2, er3, er4, er5, er6, er7, ec0, ec1, ec2, ec3, ec4, ec5, ec6, ep0, ep1, ep2, ep3, ep4, ep5, ep6,
    Nat.cast_zero, zero_add, add_zero, mul_one, zero_mul, mul_zero, sub_zero] at c0 c1 c2 c3 c4 c5 c6 c7
  -- Digits.
  have bnd : ∀ x m : ℕ, x % 2 ^ m < 2 ^ m := fun x m => Nat.mod_lt _ (by positivity)
  have hpa : pa < 2 ^ 32 := (word main A (256 * j + 223)).isLt
  have hra : ra < 2 ^ 32 := (word main A (256 * j + 225)).isLt
  have hyv : yv < 2 ^ 32 := (word main W (256 * j + 78)).isLt
  have hDb := divBytes_le dd
  have hval := divBytes_val hdd
  have hmant : mantNat (headerWord main j 18) = yv / 2 ^ 24 % 2 ^ 8 + 256 * (yv / 2 ^ 16 % 2 ^ 8) +
      65536 * (yv / 2 ^ 8 % 2 ^ 7) := by rw [hy]; unfold mantNat; rfl
  clear_value pa pe ra re yv dv dw
  set D0 := (divBytes dd).getD 0 0 with hD0; set D1 := (divBytes dd).getD 1 0 with hD1
  set D2 := (divBytes dd).getD 2 0 with hD2; set D3 := (divBytes dd).getD 3 0 with hD3
  set D4 := (divBytes dd).getD 4 0 with hD4
  have lD0 : D0 ≤ 255 := hDb 0; have lD1 : D1 ≤ 255 := hDb 1; have lD2 : D2 ≤ 255 := hDb 2
  have lD3 : D3 ≤ 255 := hDb 3; have lD4 : D4 ≤ 255 := hDb 4
  set o0 := yv / 2 ^ 24 % 2 ^ 8 with ho0; set o1 := yv / 2 ^ 16 % 2 ^ 8 with ho1
  set o2 := yv / 2 ^ 8 % 2 ^ 7 with ho2
  set q0 := ra % 2 ^ 8 with hq0; set q1 := ra / 2 ^ 8 % 2 ^ 8 with hq1
  set q2 := ra / 2 ^ 16 % 2 ^ 8 with hq2; set q3 := ra / 2 ^ 24 % 2 ^ 8 with hq3
  set q4 := re % 2 ^ 8 with hq4
  set k0 := dv % 2 ^ 8 with hk0; set k1 := dv / 2 ^ 8 % 2 ^ 8 with hk1
  set k2 := dv / 2 ^ 16 % 2 ^ 8 with hk2; set k3 := dv / 2 ^ 24 % 2 ^ 8 with hk3
  set k4 := dw % 2 ^ 8 with hk4; set k5 := dw / 2 ^ 8 % 2 ^ 8 with hk5
  set k6 := dw / 2 ^ 16 % 2 ^ 8 with hk6
  set p0 := pa % 2 ^ 8 with hp0; set p1 := pa / 2 ^ 8 % 2 ^ 8 with hp1
  set p2 := pa / 2 ^ 16 % 2 ^ 8 with hp2; set p3 := pa / 2 ^ 24 % 2 ^ 8 with hp3
  set p4 := pe % 2 ^ 8 with hp4; set p5 := pe / 2 ^ 8 % 2 ^ 8 with hp5
  have lo0 : o0 < 256 := bnd _ 8; have lo1 : o1 < 256 := bnd _ 8; have lo2 : o2 < 128 := bnd _ 7
  have lq0 : q0 < 256 := bnd _ 8; have lq1 : q1 < 256 := bnd _ 8; have lq2 : q2 < 256 := bnd _ 8
  have lq3 : q3 < 256 := bnd _ 8; have lq4 : q4 < 256 := bnd _ 8
  have lk0 : k0 < 256 := bnd _ 8; have lk1 : k1 < 256 := bnd _ 8; have lk2 : k2 < 256 := bnd _ 8
  have lk3 : k3 < 256 := bnd _ 8; have lk4 : k4 < 256 := bnd _ 8; have lk5 : k5 < 256 := bnd _ 8
  have lk6 : k6 < 256 := bnd _ 8
  have lp0 : p0 < 256 := bnd _ 8; have lp1 : p1 < 256 := bnd _ 8; have lp2 : p2 < 256 := bnd _ 8
  have lp3 : p3 < 256 := bnd _ 8; have lp4 : p4 < 256 := bnd _ 8; have lp5 : p5 < 256 := bnd _ 8
  clear_value D0 D1 D2 D3 D4 o0 o1 o2 q0 q1 q2 q3 q4 k0 k1 k2 k3 k4 k5 k6 p0 p1 p2 p3 p4 p5
  have pr : ∀ a b : ℕ, a ≤ 255 → b < 256 → a * b ≤ 255 * 255 := fun a b ha hb =>
    Nat.mul_le_mul ha (by omega)
  have x00 := pr D0 o0 lD0 lo0; have x01 := pr D0 o1 lD0 lo1; have x02 := pr D0 o2 lD0 (lt_trans lo2 (by norm_num))
  have x10 := pr D1 o0 lD1 lo0; have x11 := pr D1 o1 lD1 lo1; have x12 := pr D1 o2 lD1 (lt_trans lo2 (by norm_num))
  have x20 := pr D2 o0 lD2 lo0; have x21 := pr D2 o1 lD2 lo1; have x22 := pr D2 o2 lD2 (lt_trans lo2 (by norm_num))
  have x30 := pr D3 o0 lD3 lo0; have x31 := pr D3 o1 lD3 lo1; have x32 := pr D3 o2 lD3 (lt_trans lo2 (by norm_num))
  have x40 := pr D4 o0 lD4 lo0; have x41 := pr D4 o1 lD4 lo1; have x42 := pr D4 o2 lD4 (lt_trans lo2 (by norm_num))
  have n0 : D0 * o0 + q0 = 256 * k0 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x00 lq0; omega)) (lt_P_of (by clear * - lk0; omega)) (by push_cast at c0 ⊢; linear_combination c0)
  have n1 : D0 * o1 + D1 * o0 + q1 + k0 = p0 + 256 * k1 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x01 x10 lq1 lk0; omega)) (lt_P_of (by clear * - lp0 lk1; omega)) (by push_cast at c1 ⊢; linear_combination c1)
  have n2 : D0 * o2 + D1 * o1 + D2 * o0 + q2 + k1 = p1 + 256 * k2 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x02 x11 x20 lq2 lk1; omega)) (lt_P_of (by clear * - lp1 lk2; omega)) (by push_cast at c2 ⊢; linear_combination c2)
  have n3 : D1 * o2 + D2 * o1 + D3 * o0 + q3 + k2 = p2 + 256 * k3 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x12 x21 x30 lq3 lk2; omega)) (lt_P_of (by clear * - lp2 lk3; omega)) (by push_cast at c3 ⊢; linear_combination c3)
  have n4 : D2 * o2 + D3 * o1 + D4 * o0 + q4 + k3 = p3 + 256 * k4 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x22 x31 x40 lq4 lk3; omega)) (lt_P_of (by clear * - lp3 lk4; omega)) (by push_cast at c4 ⊢; linear_combination c4)
  have n5 : D3 * o2 + D4 * o1 + k4 = p4 + 256 * k5 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x32 x41 lk4; omega)) (lt_P_of (by clear * - lp4 lk5; omega)) (by push_cast at c5 ⊢; linear_combination c5)
  have n6 : D4 * o2 + k5 = p5 + 256 * k6 :=
    natCast_inj_of_lt (lt_P_of (by clear * - x42 lk5; omega)) (lt_P_of (by clear * - lp5 lk6; omega)) (by push_cast at c6 ⊢; linear_combination c6)
  have n7 : k6 = 0 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lk6; omega)) (lt_P_of (by clear * - lk6; omega)) (by push_cast at c7 ⊢; linear_combination c7)
  have dpa : pa = p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 := by
    rw [hp0, hp1, hp2, hp3]; exact digits4 pa hpa
  have dra : ra = q0 + 256 * q1 + 65536 * q2 + 2 ^ 24 * q3 := by
    rw [hq0, hq1, hq2, hq3]; exact digits4 ra hra
  have dpe : pe % 2 ^ 16 = p4 + 256 * p5 := by rw [hp4, hp5]; exact digits2 pe
  rw [hmant, ← hval, dpa, dra, dpe]
  exact divq_arith n0 n1 n2 n3 n4 n5 n6 n7


omit hsat hj in
theorem rem_arith {q0 q1 q2 q3 q4 t0 t1 t2 t3 t4 s0 s1 s2 s3 M0 M1 M2 M3 M4 : ℕ}
    (n0 : q0 + t0 = M0 + 256 * s0) (n1 : q1 + t1 + s0 = M1 + 256 * s1)
    (n2 : q2 + t2 + s1 = M2 + 256 * s2) (n3 : q3 + t3 + s2 = M3 + 256 * s3) (n4 : q4 + t4 + s3 = M4) :
    (q0 + 256 * q1 + 65536 * q2 + 2 ^ 24 * q3 + 2 ^ 32 * q4) + (t0 + 256 * t1 + 65536 * t2 + 2 ^ 24 * t3 + 2 ^ 32 * t4) =
      M0 + 256 * M1 + 65536 * M2 + 2 ^ 24 * M3 + 2 ^ 32 * M4 := by
  omega

set_option maxHeartbeats 1600000 in
/-- Remainder columns: `ρ + σ = divisor − 1`, so `ρ < divisor`. -/
theorem rt_rem {dd : ℕ} (hdd : dd ≤ 2)
    (hfl : ∀ k < 3, bit main (W + (5 + k)) (256 * j + 221) = decide (k = dd)) :
    let ra := (word main A (256 * j + 225)).toNat
    let re := (word main E (256 * j + 225)).toNat
    let sw := (word main W (256 * j + 225)).toNat
    let sa := (word main A (256 * j + 226)).toNat
    (ra + 2 ^ 32 * (re % 2 ^ 8)) + (sw + 2 ^ 32 * (sa % 2 ^ 8)) + 1 = 1209600 * 256 ^ dd := by
  intro ra re sw sa
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  have w4 : wrap (2 ^ logSize) r 4 = 256 * j + 225 := by rw [wrap_eq (by omega) (by omega)]; omega
  have w5 : wrap (2 ^ logSize) r 5 = 256 * j + 226 := by rw [wrap_eq (by omega) (by omega)]; omega
  have w6 : wrap (2 ^ logSize) r 6 = 256 * j + 227 := by rw [wrap_eq (by omega) (by omega)]; omega
  have bA4 := bA hsat hj (rr := 256 * j + 225) (by omega) (base := A) (by decide)
  have bE4 := bA hsat hj (rr := 256 * j + 225) (by omega) (base := E) (by decide)
  have bW4 := bA hsat hj (rr := 256 * j + 225) (by omega) (base := W) (by decide)
  have bA5 := bA hsat hj (rr := 256 * j + 226) (by omega) (base := A) (by decide)
  have bA6 := bA hsat hj (rr := 256 * j + 227) (by omega) (base := A) (by decide)
  have hsel : Expr.eval (2 ^ logSize) preCols pub main r rtSel = 1 := ev_rtSel hsat hj
  have hany : Expr.eval (2 ^ logSize) preCols pub main r dAny = 1 := ev_dAny hsat hj hdd hfl
  have hbyD : ∀ f, Expr.eval (2 ^ logSize) preCols pub main r (byD f) =
      Expr.eval (2 ^ logSize) preCols pub main r (f dd) := ev_byD hsat hj hdd hfl
  set sc := (word main A (256 * j + 227)).toNat
  have er : ∀ k < 5, (rhoByte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then ra / 2 ^ (8 * k) % 2 ^ 8 else re / 2 ^ 0 % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bA4
    · exact ev_window (by norm_num) w4 bE4
  have es : ∀ k < 5, (sigByte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then sw / 2 ^ (8 * k) % 2 ^ 8 else sa / 2 ^ 0 % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w4 bW4
    · exact ev_window (by norm_num) w4 bW4
    · exact ev_window (by norm_num) w4 bW4
    · exact ev_window (by norm_num) w4 bW4
    · exact ev_window (by norm_num) w5 bA5
  have ek : ∀ k < 4, (scE k).eval (2 ^ logSize) preCols pub main r = ((sc / 2 ^ (2 * k) % 2 ^ 2 : ℕ) : F) :=
    fun k hk => ev_window (by omega) w6 bA6
  have col : ∀ k < 5, (remCol k).eval (2 ^ logSize) preCols pub main r = 0 := fun k hk =>
    rt_sat hsat hj _ (by
      unfold retargetCs
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
  have c0 := col 0 (by norm_num); have c1 := col 1 (by norm_num); have c2 := col 2 (by norm_num)
  have c3 := col 3 (by norm_num); have c4 := col 4 (by norm_num)
  have er0 := er 0 (by norm_num); have er1 := er 1 (by norm_num); have er2 := er 2 (by norm_num)
  have er3 := er 3 (by norm_num); have er4 := er 4 (by norm_num)
  have es0 := es 0 (by norm_num); have es1 := es 1 (by norm_num); have es2 := es 2 (by norm_num)
  have es3 := es 3 (by norm_num); have es4 := es 4 (by norm_num)
  have ek0 := ek 0 (by norm_num); have ek1 := ek 1 (by norm_num); have ek2 := ek 2 (by norm_num)
  have ek3 := ek 3 (by norm_num)
  simp only [Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, pow_zero,
    Nat.div_one] at er0 er1 er2 er3 er4 es0 es1 es2 es3 es4 ek0 ek1 ek2 ek3
  simp only [remCol, hbyD, Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, eval_mul', eval_sub',
    eval_add', eval_cst, hsel, hany, one_mul, er0, er1, er2, er3, er4, es0, es1, es2, es3, es4,
    ek0, ek1, ek2, ek3, Nat.cast_zero, add_zero] at c0 c1 c2 c3 c4
  have hra : ra < 2 ^ 32 := (word main A (256 * j + 225)).isLt
  have hsw : sw < 2 ^ 32 := (word main W (256 * j + 225)).isLt
  have hM := divM1Bytes_le dd
  have hval := divM1Bytes_val hdd
  clear_value ra re sw sa sc
  have bnd : ∀ x m : ℕ, x % 2 ^ m < 2 ^ m := fun x m => Nat.mod_lt _ (by positivity)
  set M0 := (divM1Bytes dd).getD 0 0 with hM0; set M1 := (divM1Bytes dd).getD 1 0 with hM1
  set M2 := (divM1Bytes dd).getD 2 0 with hM2; set M3 := (divM1Bytes dd).getD 3 0 with hM3
  set M4 := (divM1Bytes dd).getD 4 0 with hM4
  have lM0 : M0 ≤ 255 := hM 0; have lM1 : M1 ≤ 255 := hM 1; have lM2 : M2 ≤ 255 := hM 2
  have lM3 : M3 ≤ 255 := hM 3; have lM4 : M4 ≤ 255 := hM 4
  set q0 := ra % 2 ^ 8 with hq0; set q1 := ra / 2 ^ 8 % 2 ^ 8 with hq1
  set q2 := ra / 2 ^ 16 % 2 ^ 8 with hq2; set q3 := ra / 2 ^ 24 % 2 ^ 8 with hq3
  set q4 := re % 2 ^ 8 with hq4
  set t0 := sw % 2 ^ 8 with ht0; set t1 := sw / 2 ^ 8 % 2 ^ 8 with ht1
  set t2 := sw / 2 ^ 16 % 2 ^ 8 with ht2; set t3 := sw / 2 ^ 24 % 2 ^ 8 with ht3
  set t4 := sa % 2 ^ 8 with ht4
  set s0 := sc % 2 ^ 2 with hs0; set s1 := sc / 2 ^ 2 % 2 ^ 2 with hs1
  set s2 := sc / 2 ^ 4 % 2 ^ 2 with hs2; set s3 := sc / 2 ^ 6 % 2 ^ 2 with hs3
  have lq0 : q0 < 256 := bnd _ 8; have lq1 : q1 < 256 := bnd _ 8; have lq2 : q2 < 256 := bnd _ 8
  have lq3 : q3 < 256 := bnd _ 8; have lq4 : q4 < 256 := bnd _ 8
  have lt0 : t0 < 256 := bnd _ 8; have lt1 : t1 < 256 := bnd _ 8; have lt2 : t2 < 256 := bnd _ 8
  have lt3 : t3 < 256 := bnd _ 8; have lt4 : t4 < 256 := bnd _ 8
  have ls0 : s0 < 4 := bnd _ 2; have ls1 : s1 < 4 := bnd _ 2; have ls2 : s2 < 4 := bnd _ 2
  have ls3 : s3 < 4 := bnd _ 2
  clear_value M0 M1 M2 M3 M4 q0 q1 q2 q3 q4 t0 t1 t2 t3 t4 s0 s1 s2 s3
  have n0 : q0 + t0 = M0 + 256 * s0 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lq0 lt0; omega)) (lt_P_of (by clear * - lM0 ls0; omega))
      (by push_cast at c0 ⊢; linear_combination c0)
  have n1 : q1 + t1 + s0 = M1 + 256 * s1 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lq1 lt1 ls0; omega)) (lt_P_of (by clear * - lM1 ls1; omega))
      (by push_cast at c1 ⊢; linear_combination c1)
  have n2 : q2 + t2 + s1 = M2 + 256 * s2 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lq2 lt2 ls1; omega)) (lt_P_of (by clear * - lM2 ls2; omega))
      (by push_cast at c2 ⊢; linear_combination c2)
  have n3 : q3 + t3 + s2 = M3 + 256 * s3 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lq3 lt3 ls2; omega)) (lt_P_of (by clear * - lM3 ls3; omega))
      (by push_cast at c3 ⊢; linear_combination c3)
  have n4 : q4 + t4 + s3 = M4 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lq4 lt4 ls3; omega)) (lt_P_of (by clear * - lM4; omega))
      (by push_cast at c4 ⊢; linear_combination c4)
  have dra : ra = q0 + 256 * q1 + 65536 * q2 + 2 ^ 24 * q3 := by
    rw [hq0, hq1, hq2, hq3]; exact digits4 ra hra
  have dsw : sw = t0 + 256 * t1 + 65536 * t2 + 2 ^ 24 * t3 := by
    rw [ht0, ht1, ht2, ht3]; exact digits4 sw hsw
  rw [← hval, dra, dsw, ← rem_arith n0 n1 n2 n3 n4]

omit hsat hj in
theorem cap_arith {g25 g26 u0 u1 u2 u3 u4 u5 e0 e1 e2 e3 e4 p0 p1 p2 p3 p4 p5 : ℕ}
    (n0 : u0 = p0 + 256 * e0) (n1 : u1 + e0 = p1 + 256 * e1) (n2 : u2 + e1 = p2 + 256 * e2)
    (n3 : 117 * g26 + u3 + e2 = p3 + 256 * e3) (n4 : 117 * g25 + 18 * g26 + u4 + e3 = p4 + 256 * e4)
    (n5 : 18 * g25 + u5 + e4 = p5) :
    p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 + 2 ^ 32 * (p4 + 256 * p5) =
      1209600 * 2 ^ 24 * g25 + 1209600 * 2 ^ 16 * g26 +
        (u0 + 256 * u1 + 65536 * u2 + 2 ^ 24 * u3 + 2 ^ 32 * u4 + 2 ^ 40 * u5) := by
  omega

theorem capHead_sat : ∀ c ∈ capHead, c.eval (2 ^ logSize) preCols pub main (256 * j + 221) = 0 :=
  fun c hc => rt_sat hsat hj c (by
    unfold retargetCs
    exact List.mem_append_left _ (List.mem_append_right _ hc))

set_option maxHeartbeats 1600000 in
/-- Cap branch: the previous exponent is 28 or 29 (`s_prev ∈ {25, 26}`), the header's own
nBits word is `0x1d00ffff` (raw `0xffff001d`), and `P0 · 256^s_prev ≥ 1209600 · 256^28`. -/
theorem rt_cap (hm : heightAt main j % 2016 = 0) (hpos : 0 < heightAt main j)
    (hcap : bit main (W + 8) (256 * j + 221) = true) :
    let pa := (word main A (256 * j + 223)).toNat
    let pe := (word main E (256 * j + 223)).toNat
    ((prevNB pub main j).toNat % 256 = 28 ∨ (prevNB pub main j).toNat % 256 = 29) ∧
      (headerWord main j 18).toNat = 0xffff001d ∧
      1209600 * 256 ^ 28 ≤ (pa + 2 ^ 32 * (pe % 2 ^ 16)) * 256 ^ ((prevNB pub main j).toNat % 256 - 3) := by
  intro pa pe
  set r := 256 * j + 221
  have hr : r < 2 ^ logSize := by omega
  obtain ⟨-, sp, hsp, hu, hg, hpe⟩ := rt_core hsat hj hm hpos
  have hsel : Expr.eval (2 ^ logSize) preCols pub main r rtSel = 1 := ev_rtSel hsat hj
  have hc := ev_wbit hsat hj (i := 8) (by norm_num)
  have hcapE : Expr.eval (2 ^ logSize) preCols pub main r capE = 1 := by
    unfold capE wctl bitR; rw [hc, hcap]; simp
  have hoh : ∀ s < 27, Expr.eval (2 ^ logSize) preCols pub main r (ohP s) = ((bit main (A + s) r).toNat : F) :=
    fun s hs => by
      unfold ohP bitR
      exact ev_bit (wrap_zero hr) (bA hsat hj hr (by decide) s (by omega))
  have hb := bA hsat hj (rr := 256 * j + 78) (by omega) (base := W) (by decide)
  have hd := capHead_sat hsat hj
  simp only [capHead, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hd
  obtain ⟨e1, e2, e3⟩ := hd
  -- (1) s_prev ∈ {25, 26}.
  rw [eval_mul', eval_mul', hsel, hcapE, one_mul, one_mul, eval_sub', eval_add', hoh 25 (by norm_num),
    hoh 26 (by norm_num), eval_cst] at e1
  have h2526 : sp = 25 ∨ sp = 26 := by
    by_contra hne
    push_neg at hne
    rw [hu 25 (by norm_num) (fun h => hne.1 h.symm), hu 26 (by norm_num) (fun h => hne.2 h.symm)] at e1
    simp at e1
  -- (2) own nBits word.
  have hword : headerWord main j 18 = (0xffff001d : Word) := by
    have hy : headerWord main j 18 = word main W (256 * j + 78) := by simp [headerWord]
    rw [eval_mul', eval_mul', hsel, hcapE, one_mul, one_mul, eval_sub',
      eval_limb (w143 hj) hb (by norm_num), eval_cst] at e2 e3
    rw [hy]
    exact word_of_halves (by rw [sub_eq_zero.mp e2]; rfl) (by rw [sub_eq_zero.mp e3]; rfl)
  refine ⟨by omega, by rw [hword]; rfl, ?_⟩
  -- (3) P0 ≥ threshold, from the cap columns.
  rw [hpe, show sp + 3 - 3 = sp by omega]
  have w2 : wrap (2 ^ logSize) r 2 = 256 * j + 223 := by rw [wrap_eq (by omega) (by omega)]; omega
  have w7 : wrap (2 ^ logSize) r 7 = 256 * j + 228 := by rw [wrap_eq (by omega) (by omega)]; omega
  have bA2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := A) (by decide)
  have bE2 := bA hsat hj (rr := 256 * j + 223) (by omega) (base := E) (by decide)
  have bA7 := bA hsat hj (rr := 256 * j + 228) (by omega) (base := A) (by decide)
  have bE7 := bA hsat hj (rr := 256 * j + 228) (by omega) (base := E) (by decide)
  have bW7 := bA hsat hj (rr := 256 * j + 228) (by omega) (base := W) (by decide)
  set ta := (word main A (256 * j + 228)).toNat
  set te := (word main E (256 * j + 228)).toNat
  set cw := (word main W (256 * j + 228)).toNat
  have et : ∀ k < 6, (tauByte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then ta / 2 ^ (8 * k) % 2 ^ 8 else te / 2 ^ (8 * (k - 4)) % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w7 bA7
    · exact ev_window (by norm_num) w7 bA7
    · exact ev_window (by norm_num) w7 bA7
    · exact ev_window (by norm_num) w7 bA7
    · exact ev_window (by norm_num) w7 bE7
    · exact ev_window (by norm_num) w7 bE7
  have ecc : ∀ k < 5, (ccE k).eval (2 ^ logSize) preCols pub main r = ((cw / 2 ^ (4 * k) % 2 ^ 4 : ℕ) : F) :=
    fun k hk => ev_window (by omega) w7 bW7
  have ep : ∀ k < 6, (p0Byte k).eval (2 ^ logSize) preCols pub main r =
      ((if k < 4 then pa / 2 ^ (8 * k) % 2 ^ 8 else pe / 2 ^ (8 * (k - 4)) % 2 ^ 8 : ℕ) : F) := by
    intro k hk
    interval_cases k
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bA2
    · exact ev_window (by norm_num) w2 bE2
    · exact ev_window (by norm_num) w2 bE2
  have col : ∀ k < 6, (capCol k).eval (2 ^ logSize) preCols pub main r = 0 := fun k hk =>
    rt_sat hsat hj _ (by
      unfold retargetCs
      exact List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
  have c0 := col 0 (by norm_num); have c1 := col 1 (by norm_num); have c2 := col 2 (by norm_num)
  have c3 := col 3 (by norm_num); have c4 := col 4 (by norm_num); have c5 := col 5 (by norm_num)
  have et0 := et 0 (by norm_num); have et1 := et 1 (by norm_num); have et2 := et 2 (by norm_num)
  have et3 := et 3 (by norm_num); have et4 := et 4 (by norm_num); have et5 := et 5 (by norm_num)
  have ec0 := ecc 0 (by norm_num); have ec1 := ecc 1 (by norm_num); have ec2 := ecc 2 (by norm_num)
  have ec3 := ecc 3 (by norm_num); have ec4 := ecc 4 (by norm_num)
  have ep0 := ep 0 (by norm_num); have ep1 := ep 1 (by norm_num); have ep2 := ep 2 (by norm_num)
  have ep3 := ep 3 (by norm_num); have ep4 := ep 4 (by norm_num); have ep5 := ep 5 (by norm_num)
  have o25 := hoh 25 (by norm_num); have o26 := hoh 26 (by norm_num)
  simp only [Nat.reduceLT, ↓reduceIte, Nat.reduceMul, Nat.reduceSub, pow_zero, Nat.div_one]
    at et0 et1 et2 et3 et4 et5 ec0 ec1 ec2 ec3 ec4 ep0 ep1 ep2 ep3 ep4 ep5
  simp only [capCol, capThr25, capThr26, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
    Nat.reduceEqDiff, Nat.reduceLT, ↓reduceIte, Nat.reduceSub, eval_mul', eval_sub', eval_add', eval_cst, hsel,
    hcapE, one_mul, o25, o26, et0, et1, et2, et3, et4, et5, ec0, ec1, ec2, ec3, ec4, ep0, ep1, ep2, ep3, ep4, ep5,
    Nat.cast_zero, Nat.cast_ofNat, zero_add, add_zero, mul_zero] at c0 c1 c2 c3 c4 c5
  have hpa : pa < 2 ^ 32 := (word main A (256 * j + 223)).isLt
  have hta : ta < 2 ^ 32 := (word main A (256 * j + 228)).isLt
  have b25 := Bool.toNat_le (bit main (A + 25) r); have b26 := Bool.toNat_le (bit main (A + 26) r)
  set g25 := (bit main (A + 25) r).toNat with hg25
  set g26 := (bit main (A + 26) r).toNat with hg26
  have hgv : (sp = 25 → g25 = 1 ∧ g26 = 0) ∧ (sp = 26 → g25 = 0 ∧ g26 = 1) := by
    constructor
    · rintro rfl; rw [hg25, hg26, hg, hu 26 (by norm_num) (by norm_num)]; simp
    · rintro rfl; rw [hg25, hg26, hg, hu 25 (by norm_num) (by norm_num)]; simp
  clear_value pa pe ta te cw g25 g26
  have bnd : ∀ x m : ℕ, x % 2 ^ m < 2 ^ m := fun x m => Nat.mod_lt _ (by positivity)
  set u0 := ta % 2 ^ 8 with hu0; set u1 := ta / 2 ^ 8 % 2 ^ 8 with hu1
  set u2 := ta / 2 ^ 16 % 2 ^ 8 with hu2; set u3 := ta / 2 ^ 24 % 2 ^ 8 with hu3
  set u4 := te % 2 ^ 8 with hu4; set u5 := te / 2 ^ 8 % 2 ^ 8 with hu5
  set e0 := cw % 2 ^ 4 with he0; set e1' := cw / 2 ^ 4 % 2 ^ 4 with he1
  set e2' := cw / 2 ^ 8 % 2 ^ 4 with he2; set e3' := cw / 2 ^ 12 % 2 ^ 4 with he3
  set e4 := cw / 2 ^ 16 % 2 ^ 4 with he4
  set p0 := pa % 2 ^ 8 with hp0; set p1 := pa / 2 ^ 8 % 2 ^ 8 with hp1
  set p2 := pa / 2 ^ 16 % 2 ^ 8 with hp2; set p3 := pa / 2 ^ 24 % 2 ^ 8 with hp3
  set p4 := pe % 2 ^ 8 with hp4; set p5 := pe / 2 ^ 8 % 2 ^ 8 with hp5
  have lu0 : u0 < 256 := bnd _ 8; have lu1 : u1 < 256 := bnd _ 8; have lu2 : u2 < 256 := bnd _ 8
  have lu3 : u3 < 256 := bnd _ 8; have lu4 : u4 < 256 := bnd _ 8; have lu5 : u5 < 256 := bnd _ 8
  have le0 : e0 < 16 := bnd _ 4; have le1 : e1' < 16 := bnd _ 4; have le2 : e2' < 16 := bnd _ 4
  have le3 : e3' < 16 := bnd _ 4; have le4 : e4 < 16 := bnd _ 4
  have lp0 : p0 < 256 := bnd _ 8; have lp1 : p1 < 256 := bnd _ 8; have lp2 : p2 < 256 := bnd _ 8
  have lp3 : p3 < 256 := bnd _ 8; have lp4 : p4 < 256 := bnd _ 8; have lp5 : p5 < 256 := bnd _ 8
  clear_value u0 u1 u2 u3 u4 u5 e0 e1' e2' e3' e4 p0 p1 p2 p3 p4 p5
  have n0 : u0 = p0 + 256 * e0 :=
    natCast_inj_of_lt (lt_P_of (by clear * - lu0; omega)) (lt_P_of (by clear * - lp0 le0; omega))
      (by push_cast at c0 ⊢; linear_combination c0)
  have n1 : u1 + e0 = p1 + 256 * e1' :=
    natCast_inj_of_lt (lt_P_of (by clear * - lu1 le0; omega)) (lt_P_of (by clear * - lp1 le1; omega))
      (by push_cast at c1 ⊢; linear_combination c1)
  have n2 : u2 + e1' = p2 + 256 * e2' :=
    natCast_inj_of_lt (lt_P_of (by clear * - lu2 le1; omega)) (lt_P_of (by clear * - lp2 le2; omega))
      (by push_cast at c2 ⊢; linear_combination c2)
  have n3 : 117 * g26 + u3 + e2' = p3 + 256 * e3' :=
    natCast_inj_of_lt (lt_P_of (by clear * - b26 lu3 le2; omega)) (lt_P_of (by clear * - lp3 le3; omega))
      (by push_cast at c3 ⊢; linear_combination c3)
  have n4 : 117 * g25 + 18 * g26 + u4 + e3' = p4 + 256 * e4 :=
    natCast_inj_of_lt (lt_P_of (by clear * - b25 b26 lu4 le3; omega)) (lt_P_of (by clear * - lp4 le4; omega))
      (by push_cast at c4 ⊢; linear_combination c4)
  have n5 : 18 * g25 + u5 + e4 = p5 :=
    natCast_inj_of_lt (lt_P_of (by clear * - b25 lu5 le4; omega)) (lt_P_of (by clear * - lp5; omega))
      (by push_cast at c5 ⊢; linear_combination c5)
  have dpa : pa = p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 := by
    rw [hp0, hp1, hp2, hp3]; exact digits4 pa hpa
  have dpe : pe % 2 ^ 16 = p4 + 256 * p5 := by rw [hp4, hp5]; exact digits2 pe
  rw [dpa, dpe]
  have key := cap_arith n0 n1 n2 n3 n4 n5
  rcases h2526 with rfl | rfl
  · obtain ⟨h1, h0⟩ := hgv.1 rfl
    rw [h1, h0] at key
    have : 1209600 * 2 ^ 24 ≤ p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 + 2 ^ 32 * (p4 + 256 * p5) := by
      clear * - key; omega
    calc 1209600 * 256 ^ 28 = 1209600 * 2 ^ 24 * 256 ^ 25 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ this
  · obtain ⟨h0, h1⟩ := hgv.2 rfl
    rw [h1, h0] at key
    have : 1209600 * 2 ^ 16 ≤ p0 + 256 * p1 + 65536 * p2 + 2 ^ 24 * p3 + 2 ^ 32 * (p4 + 256 * p5) := by
      clear * - key; omega
    calc 1209600 * 256 ^ 28 = 1209600 * 2 ^ 16 * 256 ^ 26 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ this


/-- **Difficulty retarget (v3b).** At every header whose height is a positive multiple of 2016,
its nBits is Bitcoin Core's mainnet `GetNextWorkRequired` of the predecessor's nBits, the
predecessor's time and the period-start time. -/
theorem retarget_sound (hm : heightAt main j % 2016 = 0) (hpos : 0 < heightAt main j) :
    nBitsOf (headerWord main j) =
      nextWork (leN (prevNB pub main j)) (leN (prevTime pub main j)) (leN (prevPst pub main j)) := by
  set r := 256 * j + 221
  obtain ⟨-, sp, hsp, -, -, hpe⟩ := rt_core hsat hj hm hpos
  obtain ⟨-, s0, hs0, -, -, hexp, hlim26, -, hsign⟩ := header_pow_ex hsat hj
  have hsize : leN (prevNB pub main j) / 2 ^ 24 = sp + 3 := by rw [leN_div24, hpe]
  have hspan := rt_span hsat hj hm hpos
  have hspw : ofBits (fun i => bit main (E + 0 + i) r) 23 = (word main E r).toNat % 2 ^ 23 := by
    have := ofBits_window (word main E r) 0 23
    simp only [Nat.zero_add, pow_zero, Nat.div_one] at this
    rw [← this]
    exact ofBits_congr (fun i hi => by
      simp only [Nat.add_zero, Nat.zero_add]; exact (word_getLsbD _ _ (show i < 32 by omega)).symm)
  rw [hspw] at hspan
  have hP0 := rt_p0 hsat hj
  simp only at hP0
  set P0 := (word main A (256 * j + 223)).toNat + 2 ^ 32 * ((word main E (256 * j + 223)).toNat % 2 ^ 16)
    with hP0d
  set y := headerWord main j 18 with hyd
  have hnb : nBitsOf (headerWord main j) = leN y := rfl
  cases hc : bit main (W + 8) r
  · -- Division branch.
    obtain ⟨dd, hdd, hfl, hstep, hcanon⟩ := rt_dhead hsat hj hm hpos hc
    have hq := rt_divq hsat hj hdd hfl
    have hrm := rt_rem hsat hj hdd hfl
    simp only at hq hrm
    rw [← hyd] at hstep hcanon hq
    rw [← hP0d] at hq
    have hml : mantNat y < 2 ^ 23 := by unfold mantNat; omega
    have hdiv : mantNat y = 256 * P0 / (1209600 * 256 ^ dd) := by
      symm
      apply Nat.div_eq_of_lt_le
      · rw [mul_comm, ← hq]; exact Nat.le_add_right _ _
      · rw [← hq, add_mul, one_mul, mul_comm (mantNat y)]; omega
    rw [hnb, leN_split y hsign, hexp,
      nextWork_noncap hsize rfl hspan hP0 hdd (by omega) (sOwn := s0) (by omega) hdiv hcanon hml
        (lim_ok hs0 hml hlim26)]
  · -- Cap branch.
    obtain ⟨h2829, hword, hcap⟩ := rt_cap hsat hj hm hpos hc
    rw [← hP0d, hpe, show sp + 3 - 3 = sp by omega] at hcap
    rw [nextWork_cap hsize rfl hspan hP0 hcap, hnb]
    unfold leN; rw [hword]; norm_num

end Div

end StarkedAir.HeaderChain
