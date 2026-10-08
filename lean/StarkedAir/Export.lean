/-
Export an `Air` to the canonical JSON consumed by `src/air/ir.zig`.

The node array is `Air.toDag` (Dag.lean): expressions in post-order, structurally equal
subexpressions shared. `dag_correct` proves that this DAG evaluates, in any commutative ring, to
the AIR's constraints. This file only prints it.
-/
import StarkedAir.IR
import StarkedAir.Dag
import StarkedAir.Lookup

namespace StarkedAir

private def nodeJson : Node → String
  | .col t i off =>
    let tree := match t with | .pre => "preprocessed" | .main => "main"
    s!"\{\"col\":\{\"tree\":\"{tree}\",\"index\":{i},\"offset\":{off}}}"
  | .const v => s!"\{\"constant\":{v % P}}"
  | .add a b => s!"\{\"add\":[{a},{b}]}"
  | .sub a b => s!"\{\"sub\":[{a},{b}]}"
  | .mul a b => s!"\{\"mul\":[{a},{b}]}"
  | .neg a => s!"\{\"neg\":{a}}"
  | .pub i => s!"\{\"pub\":{i}}"

private def preJson : PreCol → String
  | .isFirst => "{\"is_first\":{}}"
  | .notLast => "{\"not_last\":{}}"
  | .periodic vs => s!"\{\"periodic\":[{",".intercalate (vs.map toString)}]}"
  | .rowLt k => s!"\{\"row_lt\":{k}}"
  | .rowGeEnd k => s!"\{\"row_ge_end\":{k}}"

/-- Number of public inputs referenced (max index + 1). -/
def Expr.nPub : Expr → ℕ
  | .pub i => i + 1
  | .add a b | .sub a b | .mul a b => max a.nPub b.nPub
  | .neg a => a.nPub
  | _ => 0

def Air.toJson (air : Air) : String :=
  let (nodes, roots) := air.toDag
  let join (xs : List String) := ",".intercalate xs
  "{\"schema\":\"starked-air-v1\"" ++
    s!",\"name\":\"{air.name}\"" ++
    s!",\"n_preprocessed\":{air.pre.length},\"n_main\":{air.nMain}" ++
    s!",\"n_pub\":{(air.constraints.map Expr.nPub).foldl max 0}" ++
    s!",\"preprocessed\":[{join (air.pre.map preJson)}]" ++
    s!",\"exprs\":[{join (nodes.toList.map nodeJson)}]" ++
    s!",\"constraints\":[{join (roots.map toString)}]}"

/-- A component with lookups (schema v2): constraints and lookup expressions share one DAG. -/
def Comp.toJson (c : Comp) : String :=
  let air := c.air
  let roots := air.constraints ++ c.lookups.flatMap fun l => l.mult :: l.vals
  let (ids, s) := emitAll roots {}
  let nc := air.constraints.length
  let rec lookupsJson : List Lookup → List ℕ → List String
    | [], _ => []
    | l :: ls, ids =>
      let k := l.vals.length + 1
      let mine := ids.take k
      s!"\{\"rel\":{l.rel},\"mult\":{mine.headD 0},\"vals\":[{",".intercalate ((mine.drop 1).map toString)}]}" ::
        lookupsJson ls (ids.drop k)
  let join (xs : List String) := ",".intercalate xs
  "{\"schema\":\"starked-air-v2\"" ++
    s!",\"name\":\"{air.name}\"" ++
    s!",\"n_preprocessed\":{air.pre.length},\"n_main\":{air.nMain}" ++
    s!",\"n_pub\":{(roots.map Expr.nPub).foldl max 0}" ++
    s!",\"preprocessed\":[{join (air.pre.map preJson)}]" ++
    s!",\"exprs\":[{join (s.out.toList.map nodeJson)}]" ++
    s!",\"constraints\":[{join ((ids.take nc).map toString)}]" ++
    s!",\"lookups\":[{join (lookupsJson c.lookups (ids.drop nc))}]}"

end StarkedAir
