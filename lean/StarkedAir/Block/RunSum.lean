/-
**The external-challenge running sum, for any column layout (M3b, D-040).** `ExtSum.lean` proves the
running sum for its test component's columns; the coin-event component uses the same constraint shapes
on its own columns (`Coin.fracC`, `zeroC`, `accC`, `lastC`). This file states the argument once, with
the fraction columns `fc`, the accumulator `acc`, the challenge and sum public inputs `pz`, `ps`, the
fingerprint `phi` and the multiplicity `m` as parameters.

**`runsum_sound`**: the public sum is `Σ_r f_r`; each row has `(z − φ_r)·f_r = m_r`, and `f_r = 0`
when `m_r = 0`. So `f_r = m_r/(z − φ_r)` whenever `z ≠ φ_r`.
-/
import StarkedAir.Block.ExtSum

namespace StarkedAir.Block.RunSum

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst wrap_back)
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub emb_zero emb_one emb_add emb_mul emb_sub)
open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

def preCols : List PreCol := [.isFirst, .notLast]
def one : Expr := cst 1
def notFirst : Expr := .sub one (pre 0)
def isLast : Expr := .sub one (pre 1)

def fracC (fc pz : ℕ) (phi : QE) (m : Expr) : List Expr := (((pubQ pz).sub phi).mul (colQ fc) |>.sub (base m)).coords
def zeroC (fc : ℕ) (m : Expr) : List Expr := (colQ fc).coords.map fun e => .mul (.sub one (.mul m m)) e
def accC (fc acc : ℕ) : List Expr := ((colQ acc).sub (((base notFirst).mul (colQ acc (-1))).add (colQ fc))).coords
def lastC (acc ps : ℕ) : List Expr := ((base isLast).mul ((colQ acc).sub (pubQ ps))).coords

/-- A QM31 of four columns at a row. -/
noncomputable def cQ (M : ℕ → ℕ → F) (c r : ℕ) : QM := toQ ⟨M c r, M (c + 1) r, M (c + 2) r, M (c + 3) r⟩
noncomputable def pQ (pub : ℕ → F) (i : ℕ) : QM := toQ ⟨pub i, pub (i + 1), pub (i + 2), pub (i + 3)⟩

section Sound

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {fc acc pz ps : ℕ} {phi : QE} {m : Expr}
  (hsat : ∀ r < n, ∀ c ∈ fracC fc pz phi m ++ zeroC fc m ++ accC fc acc ++ lastC acc ps,
    c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem ev_colQ {c r : ℕ} (hr : r < n) : toQ ((colQ c).ev n preCols pub M r) = cQ M c r := by
  simp [cQ, ev, colQ, eval_col, wrap_zero hr]

omit hsat in
theorem ev_pubQ {i r : ℕ} : toQ ((pubQ i).ev n preCols pub M r) = pQ pub i := by
  simp [pQ, ev, pubQ, Expr.eval]

theorem coords_sat {x : QE} (hx : ∀ e ∈ x.coords, e ∈ fracC fc pz phi m ++ zeroC fc m ++ accC fc acc ++ lastC acc ps)
    {r : ℕ} (hr : r < n) : toQ (x.ev n preCols pub M r) = 0 :=
  toQ_zero_of (fun e he => hsat r hr e (hx e he))

theorem frac_row {r : ℕ} (hr : r < n) :
    (pQ pub pz - toQ (phi.ev n preCols pub M r)) * cQ M fc r = emb (m.eval n preCols pub M r) := by
  have h := coords_sat hsat (x := (((pubQ pz).sub phi).mul (colQ fc)).sub (base m))
    (fun e he => by simp [fracC, he]) hr
  rw [ev_sub, toQ_sub, ev_mul, toQ_mul, ev_sub, toQ_sub, ev_colQ hr, toQ_ev_base, ev_pubQ] at h
  exact sub_eq_zero.mp h

theorem zero_row {r : ℕ} (hr : r < n) (hm : m.eval n preCols pub M r = 0) : cQ M fc r = 0 := by
  have h : ∀ j < 4, M (fc + j) r = 0 := by
    intro j hj
    have hz : Expr.mul (.sub one (.mul m m)) (col (fc + j)) ∈ zeroC fc m := by
      simp only [zeroC, colQ, coords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      interval_cases j <;> simp
    have := hsat r hr (.mul (.sub one (.mul m m)) (col (fc + j))) (by simp [hz])
    simpa [Expr.eval, eval_col, eval_cst, wrap_zero hr, one, hm] using this
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num)
  simp only [Nat.add_zero] at h0
  simp [cQ, toQ, h0, h1, h2, h3]

theorem acc_row {r : ℕ} (hr : r < n) : cQ M acc r = (if r = 0 then 0 else cQ M acc (r - 1)) + cQ M fc r := by
  have h := coords_sat hsat (x := (colQ acc).sub (((base notFirst).mul (colQ acc (-1))).add (colQ fc)))
    (fun e he => by simp [accC, he]) hr
  rw [ev_sub, toQ_sub, ev_add, toQ_add, ev_mul, toQ_mul, toQ_ev_base, ev_colQ hr, ev_colQ hr] at h
  have hnf : notFirst.eval n preCols pub M r = if r = 0 then 0 else 1 := by
    simp [notFirst, one, Expr.eval, eval_cst, preCols, PreCol.eval, StarkedAir.Sha256.pre, eval_col, wrap_zero hr]
    split_ifs <;> simp
  rw [hnf] at h
  by_cases h0 : r = 0
  · rw [if_pos h0, emb_zero, zero_mul, zero_add] at h
    rw [if_pos h0, zero_add]; linear_combination h
  · rw [if_neg h0] at h ⊢
    have hp : toQ ((colQ acc (-1)).ev n preCols pub M r) = cQ M acc (r - 1) := by
      have hw : wrap n r (-1) = r - 1 := by
        rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]
      simp [cQ, ev, colQ, eval_col, hw]
    rw [hp, emb_one, one_mul] at h
    linear_combination h

theorem acc_sum : ∀ r < n, cQ M acc r = ∑ q ∈ Finset.range (r + 1), cQ M fc q := by
  intro r
  induction r with
  | zero => intro hr; rw [acc_row hsat hr, if_pos rfl, zero_add]; simp
  | succ r ih =>
    intro hr
    rw [acc_row hsat hr, if_neg (by omega), show r + 1 - 1 = r by omega, ih (by omega), Finset.sum_range_succ _ (r + 1)]

/-- **The running sum is sound.** -/
theorem runsum_sound (hn : 0 < n) :
    pQ pub ps = ∑ r ∈ Finset.range n, cQ M fc r ∧
    ∀ r < n, (pQ pub pz - toQ (phi.ev n preCols pub M r)) * cQ M fc r = emb (m.eval n preCols pub M r) ∧
      (m.eval n preCols pub M r = 0 → cQ M fc r = 0) := by
  refine ⟨?_, fun r hr => ⟨frac_row hsat hr, zero_row hsat hr⟩⟩
  have hl : n - 1 < n := by omega
  have h := coords_sat hsat (x := (base isLast).mul ((colQ acc).sub (pubQ ps))) (fun e he => by simp [lastC, he]) hl
  rw [ev_mul, toQ_mul, toQ_ev_base, ev_sub, toQ_sub, ev_colQ hl] at h
  have hil : isLast.eval n preCols pub M (n - 1) = 1 := by
    simp [isLast, one, Expr.eval, eval_cst, preCols, PreCol.eval, StarkedAir.Sha256.pre, eval_col,
      wrap_zero hl, show n - 1 + 1 = n by omega]
  rw [hil, emb_one, one_mul, ev_pubQ] at h
  rw [← sub_eq_zero.mp h, acc_sum hsat (n - 1) hl, show n - 1 + 1 = n by omega]

end Sound

end StarkedAir.Block.RunSum
