/-
Export an `Air` to the canonical JSON consumed by `src/air/ir.zig`.

Expressions are emitted as a DAG in post-order (children before parents),
with structurally equal subexpressions shared. This export is a plain
printer of the very `Air` value the soundness theorems are about, so it
needs no separate correctness argument beyond being a faithful printer.
-/
import StarkedAir.IR
import Std.Data.HashMap

namespace StarkedAir

private structure EmitState where
  ids : Std.HashMap Expr ℕ := {}
  out : Array String := #[]

private def emit (e : Expr) : StateM EmitState ℕ := do
  if let some id := (← get).ids.get? e then return id
  let node ← match e with
    | .col t i off =>
      let tree := match t with | .pre => "preprocessed" | .main => "main"
      pure s!"\{\"col\":\{\"tree\":\"{tree}\",\"index\":{i},\"offset\":{off}}}"
    | .const v => pure s!"\{\"constant\":{v % P}}"
    | .add a b => do let a ← emit a; let b ← emit b; pure s!"\{\"add\":[{a},{b}]}"
    | .sub a b => do let a ← emit a; let b ← emit b; pure s!"\{\"sub\":[{a},{b}]}"
    | .mul a b => do let a ← emit a; let b ← emit b; pure s!"\{\"mul\":[{a},{b}]}"
    | .neg a => do let a ← emit a; pure s!"\{\"neg\":{a}}"
  let s ← get
  let id := s.out.size
  set { s with ids := s.ids.insert e id, out := s.out.push node }
  return id

private def preJson : PreCol → String
  | .isFirst => "{\"is_first\":{}}"
  | .notLast => "{\"not_last\":{}}"
  | .periodic vs => s!"\{\"periodic\":[{",".intercalate (vs.map toString)}]}"

def Air.toJson (air : Air) : String :=
  let (roots, st) := (air.constraints.mapM emit).run {}
  let join (xs : List String) := ",".intercalate xs
  "{\"schema\":\"starked-air-v0\"" ++
    s!",\"name\":\"{air.name}\"" ++
    s!",\"n_preprocessed\":{air.pre.length},\"n_main\":{air.nMain}" ++
    s!",\"preprocessed\":[{join (air.pre.map preJson)}]" ++
    s!",\"exprs\":[{join st.out.toList}]" ++
    s!",\"constraints\":[{join (roots.map toString)}]}"

end StarkedAir
