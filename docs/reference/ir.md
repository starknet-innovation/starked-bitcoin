# Constraint IR (`starked-air-v1`)

Status: current · Updated: 2026-10-07 · Owner files: `lean/StarkedAir/IR.lean`,
`lean/StarkedAir/Export.lean`, `src/air/ir.zig`, `src/air/interp.zig`

The IR is the **single source of truth** for every AIR in this repo:

- AIRs are written in Lean as values of type `StarkedAir.Air`.
- Soundness is proven about those values.
- They are printed to `airs/*.json`.
- Zig parses the JSON, and the verifier evaluates it directly.
- No AIR is written by hand in Zig. Zig-side builders exist only in tests.

## Semantics

Both `IR.lean` (`Expr.eval`, `Air.Satisfied`) and `src/air/interp.zig`
implement these. The Lean definitions are normative.

- **Trace.** The trace has `n = 2^log_size` rows. Every column is a function
  from rows to M31 (`P = 2^31 − 1`).
- **Trees.** There are two: `preprocessed` (tree 0) and `main` (tree 1).
  There is no interaction (LogUp) tree yet.
- **`col{tree, index, offset}`.** At row `r` this reads column `index` at row
  `(r + offset) mod n`. Wrap-around is real. A constraint that must not wrap
  needs an explicit preprocessed selector.
- **`constant v`** is `v mod P`. **`add`, `sub`, `mul` and `neg`** are field
  operations.
- **`pub i`** is public input `i`. Public inputs are part of the statement and
  are mixed into Fiat–Shamir.
- **Satisfaction.** Every constraint evaluates to 0 at every row `r < n`.
- **Degree.** It must be ≤ 3, because the composition domain is
  `log_size + 1`. `component.zig` checks this.
- **Preprocessed columns** are defined by the AIR (`PreCol`), never supplied
  by the prover:

  | Kind | Value at row `r` |
  |---|---|
  | `is_first` | 1 if `r = 0`, else 0 |
  | `not_last` | 0 if `r = n−1`, else 1 |
  | `periodic [v₀…v_{k−1}]` | `v_{r mod k}` |
  | `row_lt k` | 1 if `r < k`, else 0 |
  | `row_ge_end k` | 1 if `r + k ≥ n`, else 0 |

  The verifier recomputes the preprocessed commitment and rejects a proof
  whose root differs (`PreprocessedRootMismatch`). Without this check a prover
  could switch selectors off; see stwo-zig#225 and
  [the spike report](../reports/2026-10-06-lean-first-spike.md).
- **Offsets on preprocessed columns** must be 0, because stwo-zig samples
  preprocessed columns only at the out-of-domain point.

## JSON format

`Air.toJson` in `Export.lean` emits:

```json
{ "schema": "starked-air-v1", "name": "header_chain_v3b",
  "n_preprocessed": 40, "n_main": 124, "n_pub": 48,
  "preprocessed": [ {"is_first":{}}, {"periodic":[0,1,…]}, {"row_lt":4}, … ],
  "exprs": [ {"col":{"tree":"main","index":3,"offset":-1}}, {"constant":7},
             {"add":[0,1]}, {"mul":[2,2]}, {"neg":4}, {"pub":12}, … ],
  "constraints": [ 5, 17, … ] }
```

- `exprs` is a DAG in post-order: children come before parents, and an
  integer is an index into `exprs`. Structurally equal subexpressions are
  emitted once, which also makes evaluation faster.
- `constraints` lists the root expression indices.
- The **AIR digest** (`ir.zig`) is a hash of the canonical form. The
  transcript binds it, so a proof is valid only for the exact constraint
  program it was made for.

## Regenerating `airs/*.json`

From `lean/`:

```sh
lake env lean --run Export.lean add32_chain     > ../airs/add32_chain.json
lake env lean --run Export.lean sha256_compress > ../airs/sha256_compress.json
lake env lean --run Export.lean header_chain    > ../airs/header_chain.json
lake env lean --run Export.lean probe_oracle    > ../airs/probe_oracle.json
```

- **Rule:** after any change to an AIR definition, regenerate its JSON and
  commit it with the Lean change.
- `zig build test` reads the committed JSON. A stale file means the tests are
  checking an old AIR.
- Drift check: run the same commands into a temp file and `cmp` against
  `airs/`. The check is listed in [status.md](../project/status.md).
- `probe_oracle` is not an AIR. It holds Lean-computed values of `Expr.eval`
  on a fixed random trace. The Zig test `interp.zig` "matches the Lean
  semantics" compares the interpreter against it (offsets −3…+5, every
  preprocessed kind, every operator).

## Lookups (`starked-air-v2`, IR-LOGUP)

- **Schema:** an AIR may carry `"lookups":[{"rel":R,"mult":id,"vals":[ids]}]`, whose
  expressions are nodes of the same DAG as the constraints. AIRs without lookups keep the v1
  bytes, so their digests are unchanged. Lean: `Comp` (`Lookup.lean`), exported by
  `Comp.toJson`.
- **Meaning:** at every row, a lookup emits `(R, vals)` with multiplicity `mult`. A *system* of
  components is satisfied when every AIR is and every relation balances
  (`System.Satisfied`). Tables emit with a multiplicity column; users emit with `−1`.
  `used_in_table` turns balance into membership.
- **Encoding (LogUp):** lookups are paired into batches. Each batch is a secure (QM31)
  interaction column: 4 limbs, holding cumulative sums. The last batch is also sampled at the
  previous row, and the last column is shifted by `claimed_sum / 2^log_size`. The denominator
  is `Σ eᵢ αⁱ − z` over `e = (rel, vals…)`; `(z, α)` are drawn after the main commitment. The
  formula is `component.logupConstraintValues`, and Lean proves it sound (`logup_sum`).
- **Proving:** `src/air/system.zig` proves several components in one STARK and checks that the
  claimed sums add to zero. `plain_verifier.zig` verifies the same proofs in-circuit.
- **Example:** `Testing/ByteLookup.lean` (`byte_table`, `byte_user`; theorem `user_bytes`).

## Trust boundary

| Link | How it is assured |
|---|---|
| Lean `Air` value → soundness theorem | Lean proof, standard axioms only |
| Lean `Air` → JSON | `Export.lean` is a plain printer (reviewed, not proven) |
| JSON → Zig `ir.Air` | Parser plus digest round-trip test |
| Zig `interp` ≡ Lean `Expr.eval` | Differential test against `probe_oracle` (not proven) |
| Zig `interp` inside Stwo | `component.zig` and `prove.zig`; Stwo soundness is assumed |
| LogUp constraints and claimed-sum check ⇒ fractions sum to zero | Lean `logup_sum` for the formula; the Zig implementations (native, in-circuit) are tested, not proven |
| Fractions sum to zero for random `(z, α)` ⇒ `Balanced` | LogUp soundness (Schwartz–Zippel over QM31), trusted with Stwo |

The full trust base is in [verification.md](verification.md).

## Known limits

- Single trace size: no lifting. All components of a system share one `log_size`; pad smaller
  components with inactive rows (selectors, multiplicity 0).
- Lookups have at most 32 values (`component.MAX_LOOKUP_VALS`); batch degrees must stay within 3.
- The verifier recomputes the preprocessed root in O(n). Production needs a
  verification key holding the roots per `(AIR, log_size)`.
