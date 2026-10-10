/-
**QM31 is a field (M3b).** Stwo's secure field: `CM31 = M31[i]/(i² + 1)`, `QM31 = CM31[u]/(u² − (2 + i))`.
Both polynomials are irreducible:
- `−1` is not a square mod `p = 2^31 − 1`, since `p ≡ 3 (mod 4)`;
- `2 + i` is not a square in CM31, else `5 = (a² + b²)²` would be a square mod `p`. Quadratic
  reciprocity rules that out: `(5/p) = (p/5) = (2/5) = −1`.

So both are fields (`AdjoinRoot`), and `toQ a b c d = (a + b i) + (c + d i) u` maps Stwo's coordinates in,
with the product rule the circuits use (`Circuit.Q`'s `Mul`).

This is what M3b's epoch argument needs: the LogUp bound (`LogUpSZ.logup_sz`) is over a field.
-/
import StarkedAir.IR
import StarkedAir.Circuit.Ops
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.SpecificDegree

namespace StarkedAir.Spec.QM31

open Polynomial

theorem P_mod4 : P % 4 = 3 := by unfold P; norm_num

theorem neg_one_not_square : ¬ IsSquare (-1 : F) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; simp [P_mod4]

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem five_not_square : ¬ IsSquare (5 : F) := by
  have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := 5) (q := P) (by norm_num) (by unfold P; norm_num)
  have h5 : ((P : ℕ) : ZMod 5) = 2 := by unfold P; decide
  have hP : (((5 : ℕ) : F)) = 5 := by norm_num
  rw [h5, hP] at h
  rw [← h]
  decide

/-- `X² + 1` over M31. -/
noncomputable def fI : F[X] := X ^ 2 + 1

theorem fI_natDegree : fI.natDegree = 2 := by unfold fI; compute_degree!

theorem fI_irreducible : Irreducible fI := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [fI_natDegree]) (by rw [fI_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [Polynomial.mem_roots (by intro h; have := fI_natDegree; rw [h] at this; simp at this)] at hx
  simp only [fI, IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx
  exact neg_one_not_square ⟨x, by linear_combination -hx⟩

instance : Fact (Irreducible fI) := ⟨fI_irreducible⟩

/-- CM31. -/
abbrev CM := AdjoinRoot fI

noncomputable def i : CM := AdjoinRoot.root fI

theorem i_sq : i ^ 2 = -1 := by
  have h : AdjoinRoot.mk fI (X ^ 2 + 1) = 0 := AdjoinRoot.mk_self
  simp only [map_add, map_pow, AdjoinRoot.mk_X, map_one] at h
  unfold i; linear_combination h

/-- Every element of CM31 is `a + b i`. -/
theorem cm_coords (y : CM) : ∃ a b : F, y = algebraMap F CM a + algebraMap F CM b * i := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  have hm : fI.Monic := by unfold fI; monicity!
  have e1 : AdjoinRoot.mk fI g = AdjoinRoot.mk fI (g %ₘ fI) := by
    rw [AdjoinRoot.mk_eq_mk]
    have := Polynomial.modByMonic_add_div g fI
    exact ⟨g /ₘ fI, by linear_combination -this⟩
  have hdeg : (g %ₘ fI).degree ≤ 1 := by
    have := Polynomial.degree_modByMonic_lt g hm
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, fI_natDegree] at this
    exact Order.le_of_lt_succ this
  refine ⟨(g %ₘ fI).coeff 0, (g %ₘ fI).coeff 1, ?_⟩
  conv_lhs => rw [e1, Polynomial.eq_X_add_C_of_degree_le_one hdeg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq, i]
  ring

theorem alg_inj : Function.Injective (algebraMap F CM) := (algebraMap F CM).injective

/-- `1, i` are independent over M31. -/
theorem cm_indep {a b : F} (h : algebraMap F CM a + algebraMap F CM b * i = 0) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · subst hb
    simp only [map_zero, zero_mul, add_zero] at h
    exact ⟨alg_inj (by rw [h, map_zero]), rfl⟩
  · exfalso
    have hi : i = algebraMap F CM (-a / b) := by
      have hb' : algebraMap F CM b ≠ 0 := fun e => hb (alg_inj (by rw [e, map_zero]))
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
    have h2 : algebraMap F CM ((-a / b) ^ 2) = algebraMap F CM (-1) := by
      rw [map_pow, ← hi, i_sq, map_neg, map_one]
    exact neg_one_not_square ⟨-a / b, by rw [← alg_inj h2]; ring⟩

/-- `2 + i` is not a square in CM31. -/
theorem two_i_not_square (y : CM) : y ^ 2 ≠ algebraMap F CM 2 + i := by
  intro hy
  obtain ⟨a, b, rfl⟩ := cm_coords y
  have e : algebraMap F CM (a ^ 2 - b ^ 2 - 2) + algebraMap F CM (2 * a * b - 1) * i = 0 := by
    have h2 : algebraMap F CM 2 = 2 := map_ofNat _ 2
    simp only [map_sub, map_pow, map_mul, map_ofNat, map_one]
    linear_combination hy - (algebraMap F CM b) ^ 2 * i_sq + h2
  obtain ⟨h1, h2⟩ := cm_indep e
  exact five_not_square ⟨a ^ 2 + b ^ 2, by linear_combination (-(a ^ 2 - b ^ 2) - 2) * h1 - (2 * a * b + 1) * h2⟩

/-- `X² − (2 + i)` over CM31. -/
noncomputable def fU : CM[X] := X ^ 2 - C (algebraMap F CM 2 + i)

theorem fU_natDegree : fU.natDegree = 2 := by unfold fU; compute_degree!

theorem fU_irreducible : Irreducible fU := by
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three (by rw [fU_natDegree]) (by rw [fU_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
  rw [Polynomial.mem_roots (by intro h; have := fU_natDegree; rw [h] at this; simp at this)] at hx
  simp only [fU, IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hx
  exact two_i_not_square x (by linear_combination hx)

instance : Fact (Irreducible fU) := ⟨fU_irreducible⟩

/-- **QM31**, a field. -/
abbrev QM := AdjoinRoot fU

noncomputable def u : QM := AdjoinRoot.root fU
noncomputable def I : QM := algebraMap CM QM i

theorem I_sq : I ^ 2 = -1 := by rw [I, ← map_pow, i_sq, map_neg, map_one]

theorem u_sq : u ^ 2 = 2 + I := by
  have h : AdjoinRoot.mk fU (X ^ 2 - C (algebraMap F CM 2 + i)) = 0 := AdjoinRoot.mk_self
  simp only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_add] at h
  rw [u, I]
  have : (AdjoinRoot.of fU) (algebraMap F CM 2) = 2 := by rw [map_ofNat, map_ofNat]
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination h + this

/-- M31 into QM31. -/
noncomputable def emb (x : F) : QM := algebraMap CM QM (algebraMap F CM x)

/-- Stwo's coordinates: `(a + b i) + (c + d i) u`. -/
noncomputable def toQ (x : Circuit.Q) : QM := emb x.a + emb x.b * I + (emb x.c + emb x.d * I) * u

@[simp] theorem emb_add (x y : F) : emb (x + y) = emb x + emb y := by simp [emb]
@[simp] theorem emb_sub (x y : F) : emb (x - y) = emb x - emb y := by simp [emb]
@[simp] theorem emb_mul (x y : F) : emb (x * y) = emb x * emb y := by simp [emb]
@[simp] theorem emb_zero : emb 0 = 0 := by simp [emb]
@[simp] theorem emb_one : emb 1 = 1 := by simp [emb]
@[simp] theorem emb_two : emb 2 = 2 := by simp [emb, map_ofNat]

theorem toQ_add (x y : Circuit.Q) : toQ (x + y) = toQ x + toQ y := by simp [toQ]; ring
theorem toQ_sub (x y : Circuit.Q) : toQ (x - y) = toQ x - toQ y := by simp [toQ]; ring

/-- **Stwo's product formula is QM31's product.** -/
theorem toQ_mul (x y : Circuit.Q) : toQ (x * y) = toQ x * toQ y := by
  show toQ ⟨_, _, _, _⟩ = _
  simp only [toQ, Circuit.Q.cmul, emb_add, emb_sub, emb_mul, emb_two, emb_one]
  linear_combination (-(emb x.c + emb x.d * I) * (emb y.c + emb y.d * I)) * u_sq +
    (-(emb x.b * emb y.b + (emb x.b * emb y.d + emb x.d * emb y.b) * u + emb x.d * emb y.d * (2 + I) +
      (emb x.c * emb y.d + emb x.d * emb y.c))) * I_sq

theorem emb_inj : Function.Injective emb := by
  intro x y h
  exact alg_inj ((algebraMap CM QM).injective h)

/-- Zero coordinates are the zero of QM31; nonzero `toQ` needs a nonzero coordinate. -/
theorem toQ_zero : toQ ⟨0, 0, 0, 0⟩ = 0 := by simp [toQ]

/-! ### Coordinates: `toQ` is a bijection -/

/-- Every element of QM31 is `A + C u` with `A, C` in CM31. -/
theorem qm_coords (y : QM) : ∃ A C : CM, y = algebraMap CM QM A + algebraMap CM QM C * u := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective y
  have hm : fU.Monic := by unfold fU; monicity!
  have e1 : AdjoinRoot.mk fU g = AdjoinRoot.mk fU (g %ₘ fU) := by
    rw [AdjoinRoot.mk_eq_mk]
    have := Polynomial.modByMonic_add_div g fU
    exact ⟨g /ₘ fU, by linear_combination -this⟩
  have hdeg : (g %ₘ fU).degree ≤ 1 := by
    have := Polynomial.degree_modByMonic_lt g hm
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, fU_natDegree] at this
    exact Order.le_of_lt_succ this
  refine ⟨(g %ₘ fU).coeff 0, (g %ₘ fU).coeff 1, ?_⟩
  conv_lhs => rw [e1, Polynomial.eq_X_add_C_of_degree_le_one hdeg]
  simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.algebraMap_eq, u]
  ring

/-- `1, u` are independent over CM31. -/
theorem qm_indep {A C : CM} (h : algebraMap CM QM A + algebraMap CM QM C * u = 0) : A = 0 ∧ C = 0 := by
  have hp : AdjoinRoot.mk fU (Polynomial.C A + Polynomial.C C * X) = 0 := by
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    exact h
  rw [AdjoinRoot.mk_eq_zero] at hp
  have hz : Polynomial.C A + Polynomial.C C * X = 0 := by
    apply Polynomial.eq_zero_of_dvd_of_natDegree_lt hp
    rw [fU_natDegree]
    calc (Polynomial.C A + Polynomial.C C * X).natDegree ≤ 1 := by compute_degree
      _ < 2 := by norm_num
  have h0 := congrArg (fun p => p.coeff 0) hz
  have h1 := congrArg (fun p => p.coeff 1) hz
  simp at h0 h1
  exact ⟨h0, h1⟩

theorem emb_eq (x : F) : emb x = algebraMap CM QM (algebraMap F CM x) := rfl

theorem toQ_eq (x : Circuit.Q) : toQ x = algebraMap CM QM (algebraMap F CM x.a + algebraMap F CM x.b * i) +
    algebraMap CM QM (algebraMap F CM x.c + algebraMap F CM x.d * i) * u := by
  simp only [toQ, emb, I, map_add, map_mul]

/-- **`toQ` is injective**: Stwo's four coordinates are unique. -/
theorem toQ_inj : Function.Injective toQ := by
  intro x y h
  have h0 : toQ (x - y) = 0 := by rw [toQ_sub, h, sub_self]
  rw [toQ_eq] at h0
  obtain ⟨hA, hC⟩ := qm_indep h0
  obtain ⟨ha, hb⟩ := cm_indep hA
  obtain ⟨hc, hd⟩ := cm_indep hC
  simp only [Circuit.Q.sub_a, Circuit.Q.sub_b, Circuit.Q.sub_c, Circuit.Q.sub_d, sub_eq_zero] at ha hb hc hd
  exact Circuit.Q.ext ha hb hc hd

/-- **`toQ` is surjective.** -/
theorem toQ_surj : Function.Surjective toQ := by
  intro y
  obtain ⟨A, C, rfl⟩ := qm_coords y
  obtain ⟨a, b, rfl⟩ := cm_coords A
  obtain ⟨c, d, rfl⟩ := cm_coords C
  exact ⟨⟨a, b, c, d⟩, by rw [toQ_eq]⟩

/-- The coordinates of a QM31 element (the inverse of `toQ`). -/
noncomputable def coordsOf (y : QM) : Circuit.Q := (toQ_surj y).choose

theorem toQ_coordsOf (y : QM) : toQ (coordsOf y) = y := (toQ_surj y).choose_spec

theorem coordsOf_toQ (x : Circuit.Q) : coordsOf (toQ x) = x := toQ_inj (toQ_coordsOf _)

end StarkedAir.Spec.QM31
