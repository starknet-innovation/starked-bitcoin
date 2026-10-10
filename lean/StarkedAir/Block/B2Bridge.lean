/-
**The Blake2s gadget inside the block component (M3a.6).** The block component's preprocessed columns
extend the gadget's 50, and the gadget's constraints read only those, so they evaluate the same: a
satisfied block component satisfies the gadget, and `compress_sound` applies to each aligned period.
-/
import StarkedAir.Block.B2s
import StarkedAir.Gadgets.Blake2sSound

namespace StarkedAir

/-- Every preprocessed column `e` reads is below `m`. -/
def Expr.preBelow (m : ℕ) : Expr → Bool
  | .col .pre i _ => decide (i < m)
  | .col .main _ _ => true
  | .const _ => true
  | .add a b | .sub a b | .mul a b => a.preBelow m && b.preBelow m
  | .neg a => a.preBelow m
  | .pub _ => true

theorem Expr.eval_pre_append {l1 l2 : List PreCol} (n : ℕ) (pub : ℕ → F) (main : ℕ → ℕ → F) (r : ℕ) :
    ∀ e : Expr, e.preBelow l1.length = true → e.eval n (l1 ++ l2) pub main r = e.eval n l1 pub main r
  | .col .pre i off, h => by
    simp only [Expr.preBelow, decide_eq_true_eq] at h
    simp only [Expr.eval]
    rw [List.getD_append _ _ _ _ h]
  | .col .main _ _, _ => rfl
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [Expr.preBelow, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pre_append n pub main r a h.1, Expr.eval_pre_append n pub main r b h.2]
  | .sub a b, h => by
    simp only [Expr.preBelow, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pre_append n pub main r a h.1, Expr.eval_pre_append n pub main r b h.2]
  | .mul a b, h => by
    simp only [Expr.preBelow, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pre_append n pub main r a h.1, Expr.eval_pre_append n pub main r b h.2]
  | .neg a, h => by
    simp only [Expr.preBelow] at h
    simp only [Expr.eval, Expr.eval_pre_append n pub main r a h]
  | .pub _, _ => rfl

end StarkedAir

namespace StarkedAir.Block.B2s

open StarkedAir

set_option maxRecDepth 100000 in
theorem gadget_pre : Blake2s.constraints.all (Expr.preBelow 50) = true := by decide

end StarkedAir.Block.B2s
