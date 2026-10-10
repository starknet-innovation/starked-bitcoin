/-
**The transcript order (VERIFIER-LEAN step 5).** The order of `verifyPlain`'s channel events, and the
Fiat–Shamir property it must have: every challenge is drawn after everything it must depend on has
been mixed. `verifyPlain` steps through the exported list (`PlainStatement.transcript`) next to each
channel call and refuses to build the circuit if its order differs.

- `elements_bound`: the lookup elements `(z, α)` are drawn after the FRI config, the preprocessed
  root, the statement and the main trace root.
- `coeff_bound`: the composition coefficient after the claimed sums and the interaction root.
- `oods_bound`: the OODS point after the composition root.
- `quotient_bound`: the DEEP coefficient after the OODS samples.
- `queries_bound`: the queries after the FRI commitments and the proof of work.

The FRI commitment and query selection are stwo-zig's (`friCommit`, `getQuerySelectionInputFromChannel`):
their own channel calls are part of the FRI protocol, whose soundness is assumed (`docs`
verifier-formalization.md, "Assumption").
-/
namespace StarkedAir.Circuit.Transcript

inductive Ev where
  | friConfig | pre | stmt | trace | elements | claimed | inter | coeff | comp | oods | samples | quotient
  | fri | pow | queries
deriving DecidableEq, Repr

/-- The events, with or without the lookup phase. -/
def events (lookups : Bool) : List Ev :=
  [.friConfig, .pre, .stmt, .trace] ++
    (if lookups then [.elements, .claimed, .inter] else []) ++
    [.coeff, .comp, .oods, .samples, .quotient, .fri, .pow, .queries]

/-- `a` occurs before `b` (both occur). -/
def Before (l : List Ev) (a b : Ev) : Prop := ∃ i j : Nat, i < j ∧ l[i]? = some a ∧ l[j]? = some b

instance (l : List Ev) (a b : Ev) : Decidable (Before l a b) :=
  decidable_of_iff (∃ i < l.length, ∃ j < l.length, i < j ∧ l[i]? = some a ∧ l[j]? = some b) (by
    constructor
    · rintro ⟨i, -, j, -, h⟩; exact ⟨i, j, h⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨i, (List.getElem?_eq_some_iff.mp hi).1, j, (List.getElem?_eq_some_iff.mp hj).1, hij, hi, hj⟩)

/-- Each event occurs once. -/
theorem nodup (b : Bool) : (events b).Nodup := by cases b <;> decide

theorem elements_bound : ∀ x ∈ [Ev.friConfig, .pre, .stmt, .trace], Before (events true) x .elements := by decide
theorem coeff_bound (b : Bool) : ∀ x ∈ [Ev.friConfig, .pre, .stmt, .trace], Before (events b) x .coeff := by
  cases b <;> decide
theorem coeff_bound_lookups : ∀ x ∈ [Ev.elements, .claimed, .inter], Before (events true) x .coeff := by decide
theorem oods_bound (b : Bool) : Before (events b) .comp .oods ∧ Before (events b) .coeff .oods := by cases b <;> decide
theorem quotient_bound (b : Bool) : Before (events b) .oods .samples ∧ Before (events b) .samples .quotient := by
  cases b <;> decide
theorem queries_bound (b : Bool) : Before (events b) .quotient .fri ∧ Before (events b) .fri .pow ∧
    Before (events b) .pow .queries := by cases b <;> decide

def Ev.name : Ev → String
  | .friConfig => "fri_config" | .pre => "pre" | .stmt => "stmt" | .trace => "trace"
  | .elements => "elements" | .claimed => "claimed" | .inter => "inter" | .coeff => "coeff"
  | .comp => "comp" | .oods => "oods" | .samples => "samples" | .quotient => "quotient"
  | .fri => "fri" | .pow => "pow" | .queries => "queries"

def json (lookups : Bool) : String :=
  s!"\{\"schema\":\"starked-transcript-v1\",\"events\":[{",".intercalate ((events lookups).map fun e => s!"\"{e.name}\"")}]}"

end StarkedAir.Circuit.Transcript
