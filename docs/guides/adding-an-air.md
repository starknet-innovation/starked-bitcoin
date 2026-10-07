# Adding or changing an AIR

Status: current · Updated: 2026-10-07

Follow this sequence for every new AIR, every new AIR version (for example
header chain v4) and every constraint change. Steps 1–5 are one logical change.
A step is not done until its check passes.

## 1. Specify

- Write the property to enforce as a Lean spec in `lean/StarkedAir/Spec/`.
  Transcribe Bitcoin Core: name the Core function in the docstring.
- Add `#guard`s on real mainnet values.
- **Check:** `lake build StarkedAir.Spec.<File>`.

## 2. Design the layout

- Write the row/column plan in `docs/airs/<air>.md`, in a new version section
  (see the existing sections for the format). Include: which rows and columns,
  which selectors, the degree of each constraint, and why every equation holds
  over ℕ (no wrap mod P).
- Large features get a short design note first, in
  `docs/design/` (for example `consensus-rules.md`).

## 3. Define in Lean

- Add the constraints in `lean/StarkedAir/Gadgets/<Air>.lean`. Group them
  in named lists (`powCs`, `stateCs`, `retargetCs`, …), so proofs can refer
  to them by membership path.
- Bump `Air.name` (for example `header_chain_v4`).
- Regenerate the JSON (commands in [reference/ir.md](../reference/ir.md)).
- **Check:** `lake build` passes, the JSON is regenerated, and
  `zig build test` still parses it.

## 4. Witness and tests in Zig

- Extend the witness generator (`src/btc/*.zig` or `src/sha256/*.zig`).
- Add or extend tests:
  1. **Satisfies:** real data passes `firstViolation` against the
     Lean-exported JSON.
  2. **Tamper:** for each new constraint family, changing one cell is
     caught.
  3. **Refuses:** inputs that break the rule make the generator return an
     error.
  4. **Prove/verify:** a CPU round trip, when the AIR shape changed.
- Add a cheap independent reference implementation in Zig (like
  `retarget.nextWork`) and cross-check it on mainnet values.
- **Check:** `zig build test` is all green.

## 5. Commit the definition

Commit 1: `<AIR> vN: <feature>`. It contains the Lean definition, the JSON,
the Zig code, the tests and the layout doc. This commit can land before the
proof. In that case, record the AIR as "implemented, proof pending" in
[project/roadmap.md](../project/roadmap.md).

## 6. Prove soundness

- Put the proof in `lean/StarkedAir/Gadgets/<Air>Sound.lean`. Split it into
  new files when it passes about 600 lines or builds slowly.
- Follow the proof rules in [reference/lean.md](../reference/lean.md).
- State the main theorem in terms of the spec from step 1 only, not circuit
  internals.
- **Check:** `lake build` passes; `grep -rnE "\bsorry\b|native_decide|bv_decide" lean/StarkedAir`
  finds nothing; `#print axioms <theorem>` lists only
  `propext, Classical.choice, Quot.sound`.

## 7. Document and commit the proof

Commit 2: `Lean: prove <AIR> vN soundness (<theorem>)`. In the same commit,
update:

- `docs/airs/<air>.md`: the "Statement proven" paragraph and a proof
  outline;
- [reference/verification.md](../reference/verification.md): the proven table
  and any new cross-gadget dependencies;
- [reference/lean.md](../reference/lean.md): the file map and main-theorem
  table;
- the project-management files, as described in
  [project/README.md](../project/README.md).
