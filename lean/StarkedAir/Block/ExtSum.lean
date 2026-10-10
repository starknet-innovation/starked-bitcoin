/-
**A LogUp running sum against an external challenge (M3b, D-040).** The UTXO multiset argument spans many
block proofs, so its challenge `(α, z)` cannot be each proof's own Fiat–Shamir draw: it is public (QM31,
four public inputs each), and each proof outputs its partial sum.

QM31 values are four M31 expressions (`QE`, Stwo's coordinates `(a + b i) + (c + d i) u`), multiplied
with the circuit formula (`toQ_mul`). Per row:
- a tuple `t` (M31 columns);
- a multiplicity `m ∈ {−1, 0, 1}`;
- a fraction `f` with `(z − φ)·f = m`, where `φ = Σₖ αₖ tₖ` (the verifier sets `αₖ = αᵏ`), and
  `f = 0` when `m = 0`;
- an accumulator, `acc = acc_prev + f` (from 0).

The last row's accumulator is public. **`extsum_sound`**: the public sum is `Σ_r f_r`, and each `f_r` is
`m_r / (z − φ_r)` whenever `z ≠ φ_r`.

The test component `extsum_test` has three tuple columns; the coin-event component reuses the builders.
-/
import StarkedAir.Spec.QM31
import StarkedAir.Block.Fields

namespace StarkedAir.Block.ExtSum

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst wrap_back)
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub emb_zero emb_one emb_add emb_mul emb_sub)
open StarkedAir.Block.Fields (degE)

/-- A QM31 expression: four M31 expressions. -/
structure QE where
  a : Expr
  b : Expr
  c : Expr
  d : Expr

namespace QE

def base (e : Expr) : QE := ⟨e, cst 0, cst 0, cst 0⟩
def pubQ (i : ℕ) : QE := ⟨.pub i, .pub (i + 1), .pub (i + 2), .pub (i + 3)⟩
def colQ (c : ℕ) (off : ℤ := 0) : QE := ⟨col c off, col (c + 1) off, col (c + 2) off, col (c + 3) off⟩
def add (x y : QE) : QE := ⟨.add x.a y.a, .add x.b y.b, .add x.c y.c, .add x.d y.d⟩
def sub (x y : QE) : QE := ⟨.sub x.a y.a, .sub x.b y.b, .sub x.c y.c, .sub x.d y.d⟩
def cmulE (x0 x1 y0 y1 : Expr) : Expr × Expr := (.sub (.mul x0 y0) (.mul x1 y1), .add (.mul x0 y1) (.mul x1 y0))
/-- The circuit's QM31 product. -/
def mul (x y : QE) : QE :=
  let pr := cmulE x.a x.b y.a y.b
  let qs := cmulE x.c x.d y.c y.d
  let r := cmulE (cst 2) (cst 1) qs.1 qs.2
  let ps := cmulE x.a x.b y.c y.d
  let qr := cmulE x.c x.d y.a y.b
  ⟨.add pr.1 r.1, .add pr.2 r.2, .add ps.1 qr.1, .add ps.2 qr.2⟩
def coords (x : QE) : List Expr := [x.a, x.b, x.c, x.d]

/-- Evaluation, as circuit coordinates. -/
def ev (n : ℕ) (pre : List PreCol) (pub : ℕ → F) (M : ℕ → ℕ → F) (r : ℕ) (x : QE) : Circuit.Q :=
  ⟨x.a.eval n pre pub M r, x.b.eval n pre pub M r, x.c.eval n pre pub M r, x.d.eval n pre pub M r⟩

variable {n : ℕ} {pre : List PreCol} {pub : ℕ → F} {M : ℕ → ℕ → F} {r : ℕ}

theorem ev_add (x y : QE) : (x.add y).ev n pre pub M r = x.ev n pre pub M r + y.ev n pre pub M r := by
  ext <;> simp [ev, add, Expr.eval]
theorem ev_sub (x y : QE) : (x.sub y).ev n pre pub M r = x.ev n pre pub M r - y.ev n pre pub M r := by
  ext <;> simp [ev, sub, Expr.eval]
theorem ev_mul (x y : QE) : (x.mul y).ev n pre pub M r = x.ev n pre pub M r * y.ev n pre pub M r := by
  ext <;> simp [ev, mul, cmulE, Expr.eval, eval_cst, HMul.hMul, Mul.mul, Circuit.Q.cmul] <;> ring

theorem toQ_ev_base (e : Expr) : toQ ((base e).ev n pre pub M r) = emb (e.eval n pre pub M r) := by
  simp [toQ, ev, base, eval_cst]

/-- All four coordinates evaluate to zero: the value is zero in QM31. -/
theorem toQ_zero_of {x : QE} (h : ∀ e ∈ x.coords, e.eval n pre pub M r = 0) : toQ (x.ev n pre pub M r) = 0 := by
  simp only [coords, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at h
  simp [toQ, ev, h.1, h.2.1, h.2.2.1, h.2.2.2]

end QE

open QE

/-! ### The test component -/

def W : ℕ := 3
def TC (k : ℕ) : ℕ := k
def MC : ℕ := 3
def FC : ℕ := 4
def ACC : ℕ := 8
def N_MAIN : ℕ := 12

def PUB_Z : ℕ := 0
def PUB_ALPHA (k : ℕ) : ℕ := 4 + 4 * k
def PUB_S : ℕ := 16

def preCols : List PreCol := [.isFirst, .notLast]
def one : Expr := cst 1
def mE : Expr := col MC
def notFirst : Expr := .sub one (pre 0)
def isLast : Expr := .sub one (pre 1)

/-- `φ = Σₖ αₖ tₖ`. -/
def phi : QE := (List.range W).foldl (fun acc k => acc.add ((pubQ (PUB_ALPHA k)).mul (base (col (TC k))))) (base (cst 0))

def fracC : List Expr := (((pubQ PUB_Z).sub phi).mul (colQ FC) |>.sub (base mE)).coords
def zeroC : List Expr := (colQ FC).coords.map fun e => .mul (.sub one (.mul mE mE)) e
def accC : List Expr := ((colQ ACC).sub (((base notFirst).mul (colQ ACC (-1))).add (colQ FC))).coords
def lastC : List Expr := ((base isLast).mul ((colQ ACC).sub (pubQ PUB_S))).coords
def mC : Expr := .mul mE (.mul (.sub mE one) (.add mE one))

def constraints : List Expr := mC :: fracC ++ zeroC ++ accC ++ lastC

def air : Air := { name := "extsum_test", nMain := N_MAIN, pre := preCols, constraints := constraints }

#guard constraints.all (fun c => degE c ≤ 3)

/-! ### Soundness -/

section Sound

variable {L : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < 2 ^ L, ∀ c ∈ constraints, c.eval (2 ^ L) preCols pub M r = 0)
include hsat

/-- Row `r`'s fraction, accumulator, challenge and fingerprint in QM31. -/
noncomputable def fQ (M : ℕ → ℕ → F) (r : ℕ) : QM := toQ ⟨M FC r, M (FC + 1) r, M (FC + 2) r, M (FC + 3) r⟩
noncomputable def accQ (M : ℕ → ℕ → F) (r : ℕ) : QM := toQ ⟨M ACC r, M (ACC + 1) r, M (ACC + 2) r, M (ACC + 3) r⟩
noncomputable def pQ (pub : ℕ → F) (i : ℕ) : QM := toQ ⟨pub i, pub (i + 1), pub (i + 2), pub (i + 3)⟩
noncomputable def phiQ (pub : ℕ → F) (M : ℕ → ℕ → F) (r : ℕ) : QM :=
  ∑ k ∈ Finset.range W, pQ pub (PUB_ALPHA k) * emb (M (TC k) r)

omit hsat in
theorem ev_colQ {c r : ℕ} (hr : r < 2 ^ L) :
    toQ ((colQ c).ev (2 ^ L) preCols pub M r) = toQ ⟨M c r, M (c + 1) r, M (c + 2) r, M (c + 3) r⟩ := by
  simp [ev, colQ, eval_col, wrap_zero hr]

omit hsat in
theorem ev_pubQ {i r : ℕ} : toQ ((pubQ i).ev (2 ^ L) preCols pub M r) = pQ pub i := by
  simp [pQ, ev, pubQ, Expr.eval]

omit hsat in
theorem ev_phi {r : ℕ} (hr : r < 2 ^ L) : toQ (phi.ev (2 ^ L) preCols pub M r) = phiQ pub M r := by
  have e : phi = (((base (cst 0)).add ((pubQ (PUB_ALPHA 0)).mul (base (col (TC 0))))).add
      ((pubQ (PUB_ALPHA 1)).mul (base (col (TC 1))))).add ((pubQ (PUB_ALPHA 2)).mul (base (col (TC 2)))) := rfl
  rw [e, ev_add, ev_add, ev_add, ev_mul, ev_mul, ev_mul, toQ_add, toQ_add, toQ_add, toQ_mul, toQ_mul, toQ_mul,
    toQ_ev_base, toQ_ev_base, toQ_ev_base, toQ_ev_base, ev_pubQ, ev_pubQ, ev_pubQ]
  simp [phiQ, W, Finset.sum_range_succ, eval_col, wrap_zero hr, TC, eval_cst]

theorem coords_sat {x : QE} (hx : ∀ e ∈ x.coords, e ∈ constraints) {r : ℕ} (hr : r < 2 ^ L) :
    toQ (x.ev (2 ^ L) preCols pub M r) = 0 :=
  toQ_zero_of (fun e he => hsat r hr e (hx e he))

theorem frac_row {r : ℕ} (hr : r < 2 ^ L) :
    (pQ pub PUB_Z - phiQ pub M r) * fQ M r = emb (M MC r) := by
  have h := coords_sat hsat (x := (((pubQ PUB_Z).sub phi).mul (colQ FC)).sub (base mE))
    (fun e he => by simp [constraints, fracC, he]) hr
  rw [ev_sub, toQ_sub, ev_mul, toQ_mul, ev_sub, toQ_sub, ev_phi hr, ev_colQ hr, toQ_ev_base] at h
  simp only [mE, eval_col, wrap_zero hr] at h
  rw [ev_pubQ] at h
  unfold fQ; exact sub_eq_zero.mp h

theorem m_vals {r : ℕ} (hr : r < 2 ^ L) : M MC r = 0 ∨ M MC r = 1 ∨ M MC r = -1 := by
  have h := hsat r hr mC (by simp [constraints])
  simp only [mC, mE, one, Expr.eval, eval_col, eval_cst, wrap_zero hr, Nat.cast_one] at h
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · rcases mul_eq_zero.mp h1 with h2 | h3
    · exact Or.inr (Or.inl (sub_eq_zero.mp h2))
    · exact Or.inr (Or.inr (by linear_combination h3))

theorem zero_row {r : ℕ} (hr : r < 2 ^ L) (hm : M MC r = 0) : fQ M r = 0 := by
  have h : ∀ j < 4, M (FC + j) r = 0 := by
    intro j hj
    have hz : Expr.mul (.sub one (.mul mE mE)) (col (FC + j)) ∈ zeroC := by
      simp only [zeroC, colQ, coords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      interval_cases j <;> simp
    have := hsat r hr (.mul (.sub one (.mul mE mE)) (col (FC + j))) (by simp [constraints, hz])
    simpa [Expr.eval, eval_col, eval_cst, wrap_zero hr, mE, one, hm] using this
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num)
  simp only [Nat.add_zero] at h0
  simp [fQ, toQ, h0, h1, h2, h3]

theorem acc_row {r : ℕ} (hr : r < 2 ^ L) :
    accQ M r = (if r = 0 then 0 else accQ M (r - 1)) + fQ M r := by
  have h := coords_sat hsat (x := (colQ ACC).sub (((base notFirst).mul (colQ ACC (-1))).add (colQ FC)))
    (fun e he => by simp [constraints, accC, he]) hr
  rw [ev_sub, toQ_sub, ev_add, toQ_add, ev_mul, toQ_mul, toQ_ev_base, ev_colQ hr, ev_colQ hr] at h
  have hnf : notFirst.eval (2 ^ L) preCols pub M r = if r = 0 then 0 else 1 := by
    simp [notFirst, one, Expr.eval, eval_cst, preCols, PreCol.eval, StarkedAir.Sha256.pre, eval_col, wrap_zero hr]
    split_ifs <;> simp
  rw [hnf] at h
  unfold accQ fQ
  by_cases h0 : r = 0
  · rw [if_pos h0, emb_zero, zero_mul, zero_add] at h
    rw [if_pos h0, zero_add]; linear_combination h
  · rw [if_neg h0] at h ⊢
    have hp : toQ ((colQ ACC (-1)).ev (2 ^ L) preCols pub M r) =
        toQ ⟨M ACC (r - 1), M (ACC + 1) (r - 1), M (ACC + 2) (r - 1), M (ACC + 3) (r - 1)⟩ := by
      have hw : wrap (2 ^ L) r (-1) = r - 1 := by
        rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]
      simp [ev, colQ, eval_col, hw]
    rw [hp, emb_one, one_mul] at h
    linear_combination h

theorem acc_sum : ∀ r < 2 ^ L, accQ M r = ∑ q ∈ Finset.range (r + 1), fQ M q := by
  intro r
  induction r with
  | zero => intro hr; rw [acc_row hsat hr, if_pos rfl, zero_add]; simp
  | succ r ih =>
    intro hr
    rw [acc_row hsat hr, if_neg (by omega), show r + 1 - 1 = r by omega, ih (by omega), Finset.sum_range_succ _ (r + 1)]

/-- **The running sum is sound.** The public sum is the sum of the rows' fractions, and each row's fraction
is `m/(z − φ)` (zero when `m = 0`, and `m ∈ {−1, 0, 1}`). -/
theorem extsum_sound :
    pQ pub PUB_S = ∑ r ∈ Finset.range (2 ^ L), fQ M r ∧
    ∀ r < 2 ^ L, (M MC r = 0 ∨ M MC r = 1 ∨ M MC r = -1) ∧
      (pQ pub PUB_Z ≠ phiQ pub M r → fQ M r = emb (M MC r) / (pQ pub PUB_Z - phiQ pub M r)) := by
  have hn : 0 < 2 ^ L := by positivity
  refine ⟨?_, fun r hr => ⟨m_vals hsat hr, fun hne => ?_⟩⟩
  · have hl := hsat (2 ^ L - 1) (by omega)
    have h := coords_sat hsat (x := (base isLast).mul ((colQ ACC).sub (pubQ PUB_S)))
      (fun e he => by simp [constraints, lastC, he]) (show 2 ^ L - 1 < 2 ^ L by omega)
    rw [ev_mul, toQ_mul, toQ_ev_base, ev_sub, toQ_sub, ev_colQ (by omega)] at h
    have hil : isLast.eval (2 ^ L) preCols pub M (2 ^ L - 1) = 1 := by
      simp [isLast, one, Expr.eval, eval_cst, preCols, PreCol.eval, StarkedAir.Sha256.pre, eval_col,
        wrap_zero (show 2 ^ L - 1 < 2 ^ L by omega), show 2 ^ L - 1 + 1 = 2 ^ L by omega]
    rw [hil, emb_one, one_mul, ev_pubQ] at h
    have ha := acc_sum hsat (2 ^ L - 1) (by omega)
    rw [show 2 ^ L - 1 + 1 = 2 ^ L by omega] at ha
    unfold accQ at ha
    rw [← ha]; exact (sub_eq_zero.mp h).symm
  · have hf := frac_row hsat hr
    rw [eq_div_iff (sub_ne_zero.mpr hne), mul_comm, hf]

end Sound

end StarkedAir.Block.ExtSum
