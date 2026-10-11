/-
**Glue circuits, Lean-first (CIRCUIT-GLUE).** The recursion circuits (leaf, node) are gate lists
over QM31 variables, built with stwo-zig's circuit builder. Their verifier parts stay trusted
(VERIFIER-LEAN, parked); the *glue* around them — public-input digests, the node's link checks,
key and tree root — is defined here as a program of ops, exported to JSON and replayed by
`src/recursion/glue.zig` into the same builder calls the hand-written code made (tested: the
replayed circuits have the same circuit hashes).

`Op.holds` is each op's meaning, i.e. what the gates the replay emits enforce
(`circuit.zig` `check`; guesses are constrained at finalization: M31 guesses by `x ⊙ 1 = x`, u16
guesses by `m31_to_u32(x) = x`). Constants are trusted to equal their values
(`finalize_constants`). Hooks are where the trusted verifier code runs; they constrain nothing
here.
-/
import StarkedAir.IR
import StarkedAir.Spec.Blake2s

namespace StarkedAir.Circuit

open StarkedAir

/-- A QM31 value: `(a + b·i) + (c + d·i)·u` with `i² = −1`, `u² = 2 + i`. -/
@[ext] structure Q where
  a : F
  b : F
  c : F
  d : F

namespace Q

instance : Add Q := ⟨fun x y => ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩⟩
instance : Sub Q := ⟨fun x y => ⟨x.a - y.a, x.b - y.b, x.c - y.c, x.d - y.d⟩⟩

/-- CM31 product `(x0 + x1 i)(y0 + y1 i)`. -/
def cmul (x0 x1 y0 y1 : F) : F × F := (x0 * y0 - x1 * y1, x0 * y1 + x1 * y0)

/-- QM31 product: `(p + q u)(r + s u) = pr + (2 + i) qs + (ps + qr) u`. -/
instance : Mul Q := ⟨fun x y =>
  let pr := cmul x.a x.b y.a y.b
  let qs := cmul x.c x.d y.c y.d
  let r := cmul 2 1 qs.1 qs.2
  let ps := cmul x.a x.b y.c y.d
  let qr := cmul x.c x.d y.a y.b
  ⟨pr.1 + r.1, pr.2 + r.2, ps.1 + qr.1, ps.2 + qr.2⟩⟩

@[simp] theorem add_a (x y : Q) : (x + y).a = x.a + y.a := rfl
@[simp] theorem add_b (x y : Q) : (x + y).b = x.b + y.b := rfl
@[simp] theorem add_c (x y : Q) : (x + y).c = x.c + y.c := rfl
@[simp] theorem add_d (x y : Q) : (x + y).d = x.d + y.d := rfl
@[simp] theorem sub_a (x y : Q) : (x - y).a = x.a - y.a := rfl
@[simp] theorem sub_b (x y : Q) : (x - y).b = x.b - y.b := rfl
@[simp] theorem sub_c (x y : Q) : (x - y).c = x.c - y.c := rfl
@[simp] theorem sub_d (x y : Q) : (x - y).d = x.d - y.d := rfl

/-- The base-field embedding `(x, 0, 0, 0)`. -/
def base (x : F) : Q := ⟨x, 0, 0, 0⟩

def IsBase (x : Q) : Prop := x.b = 0 ∧ x.c = 0 ∧ x.d = 0

/-- A `u32` wire: `(lo, hi, 0, 0)` with 16-bit limbs. -/
def IsU32 (x : Q) : Prop := x.a.val < 65536 ∧ x.b.val < 65536 ∧ x.c = 0 ∧ x.d = 0

/-- The word a `u32` wire holds. -/
def word (x : Q) : Spec.Blake2s.Word := BitVec.ofNat 32 (x.a.val + 65536 * x.b.val)

/-- The wire of a word. -/
def pack (w : Spec.Blake2s.Word) : Q := ⟨((w.toNat % 65536 : ℕ) : F), ((w.toNat / 65536 : ℕ) : F), 0, 0⟩

/-- `m31_to_u32`: `(x mod 2^16, x / 2^16, 0, 0)` of the base coordinate. -/
def m2u (x : Q) : Q := ⟨((x.a.val % 65536 : ℕ) : F), ((x.a.val / 65536 : ℕ) : F), 0, 0⟩

/-- A literal (four canonical coordinates), as exported. -/
def lit (a b c d : ℕ) : Q := ⟨a, b, c, d⟩

end Q

/-- Where a guessed value comes from (used by the replay only; semantics ignore it). -/
inductive Hint where
  | ext (k : ℕ)
  | reg (r : ℕ)
  | coord (j : ℕ) (h : Hint)
  | isEq (h : Hint) (k : ℕ)
  /-- Each coordinate's least significant bit (`pointwise_lsb`). -/
  | lsb (h : Hint)
  /-- Each coordinate's inverse, or 0 (`pointwise_inv_or_zero`). -/
  | invOrZero (h : Hint)

/-- One op. Registers are naturals; `o` is the defined register. -/
inductive Op where
  | const (o : ℕ) (a b c d : ℕ)
  | add (o x y : ℕ)
  | sub (o x y : ℕ)
  | mul (o x y : ℕ)
  | eq (x y : ℕ)
  | guessM31 (o : ℕ) (h : Hint)
  | guessU16 (o : ℕ) (h : Hint)
  /-- An unconstrained QM31 guess (the builder's `guess`). -/
  | guess (o : ℕ) (h : Hint)
  | m2u (o x : ℕ)
  /-- Outputs `o, o+1, o+2, o+3`. -/
  | blakeG (o a b c d f0 f1 : ℕ)
  | xor3 (o x y z : ℕ)
  /-- Host code (the trusted verifier) runs with `args` and defines `outs`. -/
  | hook (id : ℕ) (args outs : List ℕ)
  /-- The builder's variables 0 and 1 (gates around them are elided). -/
  | zero (o : ℕ)
  | one (o : ℕ)
  /-- `o = 1/x`: a guess with `x · o = 1` (the builder's `inv`). -/
  | inv (o x : ℕ)
  /-- `pointwiseMul`: coordinate-wise product. -/
  | pmul (o x y : ℕ)
  /-- `markAsUnused`: no constraint. -/
  | unused (x : ℕ)

open Q in
/-- **What an op enforces** on a register assignment `ρ`. -/
def Op.holds (ρ : ℕ → Q) : Op → Prop
  | .const o a b c d => ρ o = lit a b c d
  | .add o x y => ρ o = ρ x + ρ y
  | .sub o x y => ρ o = ρ x - ρ y
  | .mul o x y => ρ o = ρ x * ρ y
  | .eq x y => ρ x = ρ y
  | .guessM31 o _ => IsBase (ρ o)
  | .guessU16 o _ => IsBase (ρ o) ∧ (ρ o).a.val < 65536
  | .guess _ _ => True
  | .m2u o x => IsBase (ρ x) ∧ ρ o = Q.m2u (ρ x)
  | .blakeG o a b c d f0 f1 =>
    IsU32 (ρ a) ∧ IsU32 (ρ b) ∧ IsU32 (ρ c) ∧ IsU32 (ρ d) ∧ IsU32 (ρ f0) ∧ IsU32 (ρ f1) ∧
    let r := Spec.Blake2s.mix (word (ρ a)) (word (ρ b)) (word (ρ c)) (word (ρ d)) (word (ρ f0)) (word (ρ f1))
    ρ o = pack r.1 ∧ ρ (o + 1) = pack r.2.1 ∧ ρ (o + 2) = pack r.2.2.1 ∧ ρ (o + 3) = pack r.2.2.2
  | .xor3 o x y z => IsU32 (ρ x) ∧ IsU32 (ρ y) ∧ IsU32 (ρ z) ∧ ρ o = pack (word (ρ x) ^^^ word (ρ y) ^^^ word (ρ z))
  | .hook _ _ _ => True
  | .zero o => ρ o = lit 0 0 0 0
  | .one o => ρ o = lit 1 0 0 0
  | .inv o x => ρ x * ρ o = lit 1 0 0 0
  | .pmul o x y => ρ o = ⟨(ρ x).a * (ρ y).a, (ρ x).b * (ρ y).b, (ρ x).c * (ρ y).c, (ρ x).d * (ρ y).d⟩
  | .unused _ => True

def Holds (ρ : ℕ → Q) (ops : List Op) : Prop := ∀ op ∈ ops, op.holds ρ

theorem holds_append {ρ : ℕ → Q} {a b : List Op} : Holds ρ (a ++ b) ↔ Holds ρ a ∧ Holds ρ b := by
  simp [Holds, List.mem_append, or_imp, forall_and]

/-! ### JSON -/

def Hint.toJson : Hint → String
  | .ext k => s!"\{\"ext\":{k}}"
  | .reg r => s!"\{\"reg\":{r}}"
  | .coord j h => s!"\{\"coord\":[{j},{h.toJson}]}"
  | .isEq h k => s!"\{\"is_eq\":[{h.toJson},{k}]}"
  | .lsb h => s!"\{\"lsb\":{h.toJson}}"
  | .invOrZero h => s!"\{\"inv_or_zero\":{h.toJson}}"

def Op.toJson : Op → String
  | .const o a b c d => s!"[\"const\",{o},{a},{b},{c},{d}]"
  | .add o x y => s!"[\"add\",{o},{x},{y}]"
  | .sub o x y => s!"[\"sub\",{o},{x},{y}]"
  | .mul o x y => s!"[\"mul\",{o},{x},{y}]"
  | .eq x y => s!"[\"eq\",{x},{y}]"
  | .guessM31 o h => s!"[\"guess_m31\",{o},{h.toJson}]"
  | .guessU16 o h => s!"[\"guess_u16\",{o},{h.toJson}]"
  | .guess o h => s!"[\"guess\",{o},{h.toJson}]"
  | .m2u o x => s!"[\"m31_to_u32\",{o},{x}]"
  | .blakeG o a b c d f0 f1 => s!"[\"blake_g\",{o},{a},{b},{c},{d},{f0},{f1}]"
  | .xor3 o x y z => s!"[\"triple_xor\",{o},{x},{y},{z}]"
  | .hook id args outs =>
    s!"[\"hook\",{id},[{",".intercalate (args.map toString)}],[{",".intercalate (outs.map toString)}]]"
  | .zero o => s!"[\"zero\",{o}]"
  | .one o => s!"[\"one\",{o}]"
  | .inv o x => s!"[\"inv\",{o},{x}]"
  | .pmul o x y => s!"[\"pointwise_mul\",{o},{x},{y}]"
  | .unused x => s!"[\"unused\",{x}]"

/-- A glue program: its ops and its result registers. -/
structure Program where
  name : String
  ops : List Op
  results : List ℕ

def Program.toJson (p : Program) : String :=
  s!"\{\"schema\":\"starked-glue-v1\",\"name\":\"{p.name}\",\"ops\":[{",".intercalate (p.ops.map Op.toJson)}]" ++
    s!",\"results\":[{",".intercalate (p.results.map toString)}]}"

end StarkedAir.Circuit
