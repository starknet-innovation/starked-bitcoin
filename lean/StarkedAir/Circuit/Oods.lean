/-
**The shifted OODS points, Lean-first (VL-OODS).** The plain verifier samples a main column with mask
offset `off` at `oods + off·g_L`, where `g_L` generates the trace's subgroup of size `2^L`, and the
interaction tree's previous row at `oods − g_L`. `verifyPlain` builds each distinct offset's point
once: the shift's coordinates as constants, then stwo-zig's `addPoints`.

- **Spec:** the M31 circle group (`CP`, `cpAdd`, `cpMul`), stwo's generator `(2, 1268011823)` of
  order `2^31`, `traceGen L` (`= gen · 2^(31−L)`, stwo's `subgroup_gen(L)`), and `shiftPt L off`
  (`mulSigned`: a negative offset multiplies the conjugate).
- **Program:** `shiftP`: the two constants (Lean-computed `shiftPt L off`), then `addPoints`'s gates.
  `shift_sound`: the result is the circle sum of the OODS point and `shiftPt L off`, over QM31.
- **Table:** `shiftJson` exports, per log size and offset the leaf uses, the program; a Zig test checks
  the constants against stwo-zig's `mulSigned` and the gates against `addPoints`.
-/
import StarkedAir.Circuit.Channel
import StarkedAir.Circuit.Deep

namespace StarkedAir.Circuit.Oods

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

/-! ### The M31 circle group -/

/-- A point of the circle `x² + y² = 1` over M31. -/
structure CP where
  x : F
  y : F
  deriving DecidableEq

/-- The group law: `(x₀x₁ − y₀y₁, x₀y₁ + y₀x₁)`. -/
def cpAdd (p q : CP) : CP := ⟨p.x * q.x - p.y * q.y, p.x * q.y + p.y * q.x⟩

/-- The identity `(1, 0)`. -/
def cpZero : CP := ⟨1, 0⟩

/-- The conjugate (inverse) `(x, −y)`. -/
def cpConj (p : CP) : CP := ⟨p.x, -p.y⟩

/-- `k·p` by doubling, low bit first (stwo-zig's `CirclePoint.mul`). -/
def cpMul (p : CP) (k : ℕ) : CP :=
  if h : k = 0 then cpZero else
    let r := cpMul (cpAdd p p) (k / 2)
    if k % 2 = 1 then cpAdd p r else r
termination_by k
decreasing_by omega

/-- stwo's generator of the circle group over M31 (order `2^31`). -/
def gen : CP := ⟨2, 1268011823⟩

/-- The generator of the subgroup of size `2^L` (stwo's `subgroup_gen(L).to_point()`). -/
def traceGen (L : ℕ) : CP := cpMul gen (2 ^ (31 - L))

/-- `off·g_L` (stwo-zig's `mulSigned`). -/
def shiftPt (L : ℕ) (off : ℤ) : CP :=
  if 0 ≤ off then cpMul (traceGen L) off.toNat else cpMul (cpConj (traceGen L)) (-off).toNat

/-! ### The program -/

/-- The shift from register `n`: the constants `g = shiftPt L off`, then `addPoints(oods, g)`:
`x₀x₁`, `y₀y₁`, their difference, `x₀y₁`, `y₀x₁`, their sum. Result `(n + 4, n + 7)`. -/
def shiftP (n ox oy L : ℕ) (off : ℤ) : Out (ℕ × ℕ) :=
  let g := shiftPt L off
  ⟨[.const n g.x.val 0 0 0, .const (n + 1) g.y.val 0 0 0,
    .mul (n + 2) ox n, .mul (n + 3) oy (n + 1), .sub (n + 4) (n + 2) (n + 3),
    .mul (n + 5) ox (n + 1), .mul (n + 6) oy n, .add (n + 7) (n + 5) (n + 6)],
   (n + 4, n + 7), n + 8⟩

variable {ρ : ℕ → Q}

theorem lit_val (x : F) : toQ (lit x.val 0 0 0) = emb x := by
  rw [Composition.toQ_lit, ZMod.natCast_zmod_val]

/-- **The shifted point is sound.** Over QM31, the result is the circle sum of the OODS point
`(ox, oy)` and `shiftPt L off`. -/
theorem shift_sound {n ox oy L : ℕ} {off : ℤ} (h : Holds ρ (shiftP n ox oy L off).ops) :
    toQ (ρ (shiftP n ox oy L off).res.1) =
        toQ (ρ ox) * emb (shiftPt L off).x - toQ (ρ oy) * emb (shiftPt L off).y ∧
      toQ (ρ (shiftP n ox oy L off).res.2) =
        toQ (ρ ox) * emb (shiftPt L off).y + toQ (ρ oy) * emb (shiftPt L off).x := by
  have g : ∀ op ∈ (shiftP n ox oy L off).ops, op.holds ρ := h
  simp only [shiftP, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨cx, cy, m2, m3, s4, m5, m6, a7⟩ := g
  simp only [Op.holds] at *
  have ex : toQ (ρ n) = emb (shiftPt L off).x := by rw [cx, lit_val]
  have ey : toQ (ρ (n + 1)) = emb (shiftPt L off).y := by rw [cy, lit_val]
  simp only [shiftP]
  refine ⟨?_, ?_⟩
  · rw [s4, toQ_sub, m2, m3, toQ_mul, toQ_mul, ex, ey]
  · rw [a7, toQ_add, m5, m6, toQ_mul, toQ_mul, ex, ey]

/-! ### Spec checks -/

/-- The generator is on the circle, and `traceGen L` has order dividing `2^L` (checked for the leaf's
sizes by evaluation). -/
def onCircle (p : CP) : Bool := p.x * p.x + p.y * p.y == 1

#guard onCircle gen
#guard cpMul gen (2 ^ 31) == cpZero
#guard cpMul gen (2 ^ 30) != cpZero
#guard (List.range 21).all fun L => cpMul (traceGen L) (2 ^ L) == cpZero && onCircle (traceGen L)

/-! ### Export -/

/-- The exported shifts: one program per `(L, off)`, each `hook 0 → (ox, oy)` then `shiftP`. -/
def shiftJson (logs : List ℕ) (offs : List ℤ) : String :=
  let one := fun (L : ℕ) (off : ℤ) =>
    let o := shiftP 2 0 1 L off
    let ops := [Op.hook 0 [] [0, 1]] ++ o.ops
    s!"\{\"log\":{L},\"off\":{off},\"x\":{(shiftPt L off).x.val},\"y\":{(shiftPt L off).y.val},\"program\":\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{o.res.1},{o.res.2}]}}"
  let entries := logs.flatMap fun L => offs.map fun off => one L off
  s!"[{",".intercalate entries}]"

/-- The distinct nonzero main offsets of components, and `−1` (the interaction tree's previous row). -/
def leafOffsets (shapes : List Composition.PartShape) : List ℤ :=
  ((shapes.flatMap fun (s : Composition.PartShape) => s.offs.flatten) ++ [-1]).dedup.filter (· ≠ 0)

end StarkedAir.Circuit.Oods
