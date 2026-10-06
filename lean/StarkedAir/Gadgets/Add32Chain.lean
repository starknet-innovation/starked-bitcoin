/-
Spike gadget: a chain of 32-bit additions, `x[r+1] = x[r] + y[r] mod 2^32`.

The definition mirrors `src/air/gadgets/add32_chain.zig` column for column.
The soundness theorem says that any trace satisfying the AIR encodes, through
its bit columns, words with
* `Z r = (X r + Y r) mod 2^32` on every row, and
* `X (r+1) = Z r` on every row but the last.
-/
import StarkedAir.IR

namespace StarkedAir.Add32Chain

open StarkedAir

def X : ℕ := 0
def Y : ℕ := 32
def Z : ℕ := 64
def cLo : ℕ := 96
def cHi : ℕ := 97

def bit (base k : ℕ) (off : ℤ) : Expr := .col .main (base + k) off

/-- `Σ_{j<k} 2^j · bit[base + 16·half + j]`, built exactly as the Zig builder does. -/
def limbAux (base half : ℕ) (off : ℤ) : ℕ → Expr
  | 0 => .const 0
  | k + 1 => .add (limbAux base half off k) (.mul (.const (2 ^ k)) (bit base (16 * half + k) off))

def limb (base half : ℕ) (off : ℤ) : Expr := limbAux base half off 16

def boolC (e : Expr) : Expr := .mul e (.sub e (.const 1))

def loC : Expr :=
  .sub (.sub (.add (limb X 0 0) (limb Y 0 0)) (limb Z 0 0)) (.mul (.const 65536) (.col .main cLo 0))

def hiC : Expr :=
  .sub (.sub (.add (.add (limb X 1 0) (limb Y 1 0)) (.col .main cLo 0)) (limb Z 1 0))
    (.mul (.const 65536) (.col .main cHi 0))

def chainC (half : ℕ) : Expr :=
  .mul (.col .pre 0 0) (.sub (limb X half 1) (limb Z half 0))

def constraints : List Expr :=
  (List.range 98).map (fun i => boolC (.col .main i 0)) ++ [loC, hiC, chainC 0, chainC 1]

def air : Air := { name := "add32_chain", nMain := 98, pre := [.notLast], constraints }

/-! ### Specification -/

/-- Natural value of limb `half` of the word at `base`, row `r`. -/
def limbNat (main : ℕ → ℕ → F) (base half r : ℕ) (k : ℕ := 16) : ℕ :=
  ∑ j ∈ Finset.range k, 2 ^ j * (main (base + (16 * half + j)) r).val

/-- The 32-bit word encoded at `base`, row `r`. -/
def word (main : ℕ → ℕ → F) (base r : ℕ) : ℕ :=
  limbNat main base 0 r + 2 ^ 16 * limbNat main base 1 r

/-! ### Soundness -/

section
variable {n : ℕ} {main : ℕ → ℕ → F}

theorem limbAux_eval (base half : ℕ) (off : ℤ) (r k : ℕ) :
    (limbAux base half off k).eval n [.notLast] main r =
      ((∑ j ∈ Finset.range k, 2 ^ j * (main (base + (16 * half + j)) (wrap n r off)).val : ℕ) : F) := by
  induction k with
  | zero => simp [limbAux, Expr.eval]
  | succ k ih =>
    simp only [limbAux, Expr.eval, ih, Finset.sum_range_succ, bit, ZMod.natCast_val,
      ZMod.cast_id', id, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem limbNat_lt {base half r : ℕ} (hb : ∀ j < 16, (main (base + (16 * half + j)) r).val ≤ 1) :
    limbNat main base half r < 2 ^ 16 := by
  unfold limbNat
  have key : ∀ k ≤ 16, ∑ j ∈ Finset.range k, 2 ^ j * (main (base + (16 * half + j)) r).val < 2 ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have h1 := ih (by omega)
      have h2 := hb k (by omega)
      have : 2 ^ k * (main (base + (16 * half + k)) r).val ≤ 2 ^ k :=
        by calc _ ≤ 2 ^ k * 1 := Nat.mul_le_mul_left _ h2
               _ = 2 ^ k := by ring
      omega
  exact key 16 le_rfl

end

theorem mem_bool {i : ℕ} (hi : i < 98) : boolC (.col .main i 0) ∈ constraints :=
  List.mem_append_left _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem P_gt : 2 ^ 20 < P := by norm_num [P]

/-- **Soundness of the add32-chain AIR.** -/
theorem sound {logSize : ℕ} {main : ℕ → ℕ → F} (h : air.Satisfied logSize main) :
    ∀ r < 2 ^ logSize,
      word main Z r = (word main X r + word main Y r) % 2 ^ 32 ∧
      (r + 1 < 2 ^ logSize → word main X (r + 1) = word main Z r) := by
  intro r hr
  set n := 2 ^ logSize with hn
  have ev : ∀ c ∈ constraints, c.eval n [.notLast] main r = 0 := fun c hc => h r hr c hc
  -- Every bit and carry column is boolean at every row < n.
  have bools : ∀ r' < n, ∀ i < 98, (main i r').val ≤ 1 := by
    intro r' hr' i hi
    have := h r' hr' _ (mem_bool hi)
    simp only [boolC, Expr.eval, air, wrap_zero (show r' < 2 ^ logSize from hr'),
      Nat.cast_one] at this
    exact val_le_one_of_bool this
  have limb_bound : ∀ r' < n, ∀ base half, base + 16 * half + 16 ≤ 98 →
      limbNat main base half r' < 2 ^ 16 := by
    intro r' hr' base half hle
    exact limbNat_lt (fun j hj => bools r' hr' _ (by omega))
  have limb_eval : ∀ base half (off : ℤ), (limb base half off).eval n [.notLast] main r =
      ((limbNat main base half (wrap n r off) : ℕ) : F) := by
    intro base half off; exact limbAux_eval base half off r 16
  have cLo_le := bools r hr cLo (by decide)
  have cHi_le := bools r hr cHi (by decide)
  have bX0 := limb_bound r hr X 0 (by decide)
  have bX1 := limb_bound r hr X 1 (by decide)
  have bY0 := limb_bound r hr Y 0 (by decide)
  have bY1 := limb_bound r hr Y 1 (by decide)
  have bZ0 := limb_bound r hr Z 0 (by decide)
  have bZ1 := limb_bound r hr Z 1 (by decide)
  have hP := P_gt
  -- Low limb: lo(x) + lo(y) = lo(z) + 2^16 c_lo over ℕ.
  have lo : limbNat main X 0 r + limbNat main Y 0 r =
      limbNat main Z 0 r + 65536 * (main cLo r).val := by
    have e := ev loC (by simp [constraints])
    simp only [loC, Expr.eval, limb_eval, wrap_zero hr] at e
    rw [sub_eq_zero, sub_eq_iff_eq_add] at e
    apply natCast_inj_of_lt (by omega) (by omega)
    push_cast at e ⊢
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at e ⊢
    linear_combination e
  have hi : limbNat main X 1 r + limbNat main Y 1 r + (main cLo r).val =
      limbNat main Z 1 r + 65536 * (main cHi r).val := by
    have e := ev hiC (by simp [constraints])
    simp only [hiC, Expr.eval, limb_eval, wrap_zero hr] at e
    rw [sub_eq_zero, sub_eq_iff_eq_add] at e
    apply natCast_inj_of_lt (by omega) (by omega)
    push_cast at e ⊢
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at e ⊢
    linear_combination e
  refine ⟨?_, fun hr1 => ?_⟩
  · unfold word; omega
  · -- Chaining: not_last = 1 here, so lo/hi of x@+1 equal those of z.
    have bX0' := limb_bound (r + 1) hr1 X 0 (by decide)
    have bX1' := limb_bound (r + 1) hr1 X 1 (by decide)
    have chain : ∀ half, half ≤ 1 → limbNat main X half (r + 1) = limbNat main Z half r := by
      intro half hh
      have e := ev (chainC half) (by rcases (by omega : half = 0 ∨ half = 1) with rfl | rfl <;> simp [constraints])
      simp only [chainC, Expr.eval, limb_eval, wrap_zero hr, wrap_one hr1, List.getD,
        PreCol.eval, hr1, if_true, one_mul, List.getElem?_cons_zero, Option.getD_some] at e
      have hb1 := limb_bound (r + 1) hr1 X half (by simp only [X]; omega)
      have hb2 := limb_bound r hr Z half (by simp only [Z]; omega)
      exact natCast_inj_of_lt (by omega) (by omega) (sub_eq_zero.mp e)
    unfold word; rw [chain 0 (by omega), chain 1 (by omega)]

end StarkedAir.Add32Chain
