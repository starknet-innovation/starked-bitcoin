/-
Canonical constraint IR (`starked-air-v1`): syntax and semantics.

Mirrors `src/air/ir.zig`. This file is the normative definition of what it
means for a trace to satisfy an AIR. The Zig verifier evaluates the same IR,
exported to JSON by `StarkedAir.Export`.

Semantics:
* The trace has `n = 2^logSize` rows. A column is a function `ℕ → F`, read
  only at rows `< n`.
* `col t i off` at row `r` reads column `i` of tree `t` at row
  `(r + off) mod n`. Wrap-around is real.
* Preprocessed columns are *defined by the AIR* (`PreCol`), never supplied
  by the prover. The Zig verifier enforces this by recomputing their
  commitment root.
* `pub i` is public input `i`. Its value is part of the statement and is
  bound into the Fiat–Shamir transcript.
* A trace satisfies the AIR (for given public inputs) iff every constraint
  evaluates to `0` at every row `r < n`.
-/
import Mathlib

namespace StarkedAir

/-- The Mersenne-31 prime. -/
def P : ℕ := 2 ^ 31 - 1

/-- 2^31 − 1 is a Mersenne prime; certified by the Lucas–Lehmer test. -/
theorem P_prime : Nat.Prime P :=
  show (mersenne 31).Prime from lucas_lehmer_sufficiency 31 (by norm_num) (by norm_num)

instance : Fact (Nat.Prime P) := ⟨P_prime⟩

abbrev F := ZMod P

inductive Tree where
  | pre
  | main
  deriving DecidableEq, Hashable, Repr

inductive Expr where
  | col (t : Tree) (i : ℕ) (off : ℤ)
  | const (v : ℕ)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  | neg (a : Expr)
  | pub (i : ℕ)
  deriving DecidableEq, Hashable, Repr

inductive PreCol where
  /-- `1` at row 0, else `0`. -/
  | isFirst
  /-- `0` at row `n-1`, else `1`. -/
  | notLast
  /-- `vals[r mod vals.length]`. -/
  | periodic (vals : List ℕ)
  /-- `1` on rows `r < k`, else `0`. -/
  | rowLt (k : ℕ)
  /-- `1` on the last `k` rows (`r + k ≥ n`), else `0`. -/
  | rowGeEnd (k : ℕ)
  deriving DecidableEq, BEq, Repr

structure Air where
  name : String
  nMain : ℕ
  pre : List PreCol
  constraints : List Expr

/-- Row `r + off` reduced cyclically modulo `n`. -/
def wrap (n r : ℕ) (off : ℤ) : ℕ := ((r + off) % (n : ℤ)).toNat

def PreCol.eval (n : ℕ) : PreCol → ℕ → F
  | .isFirst, r => if r = 0 then 1 else 0
  | .notLast, r => if r + 1 < n then 1 else 0
  | .periodic vs, r => ((vs.getD (r % vs.length) 0 : ℕ) : F)
  | .rowLt k, r => if r < k then 1 else 0
  | .rowGeEnd k, r => if n ≤ r + k then 1 else 0

/-- Value of an expression at row `r` of an `n`-row trace with public inputs `pub` and main
columns `main`. -/
def Expr.eval (n : ℕ) (pre : List PreCol) (pub : ℕ → F) (main : ℕ → ℕ → F) (r : ℕ) : Expr → F
  | .col .pre i off => (pre.getD i (.periodic [0])).eval n (wrap n r off)
  | .col .main i off => main i (wrap n r off)
  | .const v => (v : F)
  | .add a b => a.eval n pre pub main r + b.eval n pre pub main r
  | .sub a b => a.eval n pre pub main r - b.eval n pre pub main r
  | .mul a b => a.eval n pre pub main r * b.eval n pre pub main r
  | .neg a => -(a.eval n pre pub main r)
  | .pub i => pub i

def Air.Satisfied (air : Air) (logSize : ℕ) (pub : ℕ → F) (main : ℕ → ℕ → F) : Prop :=
  ∀ r < 2 ^ logSize, ∀ c ∈ air.constraints, c.eval (2 ^ logSize) air.pre pub main r = 0

/-! ### Basic lemmas used by gadget soundness proofs -/

theorem wrap_zero {n r : ℕ} (h : r < n) : wrap n r 0 = r := by
  unfold wrap
  have : ((r : ℤ) + 0) % (n : ℤ) = r := by
    rw [add_zero]; exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast h)
  rw [this]; simp

theorem wrap_one {n r : ℕ} (h : r + 1 < n) : wrap n r 1 = r + 1 := by
  unfold wrap
  have : ((r : ℤ) + 1) % (n : ℤ) = ((r + 1 : ℕ) : ℤ) := by
    push_cast; exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast h)
  rw [this]; simp

/-- Equal casts of naturals below `P` are equal naturals. -/
theorem natCast_inj_of_lt {a b : ℕ} (ha : a < P) (hb : b < P) (h : (a : F) = (b : F)) :
    a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `x(x-1) = 0` forces `x.val ∈ {0,1}`. -/
theorem val_le_one_of_bool {x : F} (h : x * (x - 1) = 0) : x.val ≤ 1 := by
  rcases mul_eq_zero.mp h with h0 | h1
  · simp [h0]
  · have : x = 1 := sub_eq_zero.mp h1
    subst this
    rw [ZMod.val_one]

end StarkedAir
