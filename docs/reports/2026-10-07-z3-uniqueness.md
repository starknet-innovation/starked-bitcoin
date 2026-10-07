# Z3 witness-uniqueness checks (FV-Z3, 2026-10-07)

**Verdict:** four gadget windows are proven unique by Z3, independently of the
Lean proofs: median-time-past comparison, height/boundary decomposition,
retarget clamp branch, and the PoW exponent one-hot. The SHA-256 round is out
of Z3's reach (timeout). It is covered by the Lean proof `compress_sound_air`.
A control query confirms the pipeline does report non-uniqueness.

## Question

For a window of rows: can two witnesses that satisfy every constraint and agree
on all input cells disagree on an output cell? `unsat` means the outputs are
determined by the inputs.

## Method

- **Tool:** `scripts/air_z3.py`. It reads `airs/header_chain.json` (v5)
  directly, without trusting the Lean semantics or proofs.
- **Encoding:** the docstring lists every encoding decision a reviewer must
  accept. In summary:
  - exact M31 arithmetic, as `poly = p·k` with interval-bounded `k`;
  - bit columns in {0,1}, justified by the global booleanity constraints;
  - preprocessed columns evaluated concretely (`log_size = 16`, header 1);
  - only the outputs' cone of influence is kept, plus optional dropping of
    SHA's per-row limb definitions. Dropping constraints only adds models, so
    `unsat` stays valid;
  - bit-vector encoding (`--bv`), with the width derived from interval bounds.
- **Command:** `.venv-fv/bin/python scripts/air_z3.py all --bv --timeout-ms 1800000`.
  Setup: `python3 -m venv .venv-fv && .venv-fv/bin/pip install z3-solver`
  (z3 5.1.0).
- **Machine:** Apple M4 Pro.

## Results

| Preset | Property | Verdict | Constraints/copy | Time |
|---|---|---|---|---|
| `mtp-slot` | MTP flag `b_i` is determined by `T_i` and `t` | unique | 36 | 24.5 s |
| `state-flag` | boundary flag, `rem` and `q` are determined by the height | unique | 73 | 133.6 s |
| `rt-clamp` | at a boundary (assumes `rt = 1`), clamp flags and span are determined by time and pst | unique | 107 | 545.7 s |
| `pow-onehot` | exponent one-hot is determined by nBits | unique | 60 | 40.4 s |
| `sha-round` | a round's `a`, `e` are determined by the previous state and `w` | **unknown** (timeout) | 88 | 1800 s |
| `control-free` | CONTROL: unconstrained carry cell 110 | not unique (expected) | 1 | 0.2 s |

## Notes

- The first `rt-clamp` attempt returned *not unique* because the clamp flags
  are free on non-boundary headers, where they are gated off. Not a defect:
  the preset now assumes `rt = 1`.
- The integer encoding timed out on every preset. The cone of influence plus
  bit-vectors is what made the checks tractable.
- These are per-window results. Cells outside the window are treated as
  inputs, so this does not replace the Lean whole-trace theorems.

## Follow-ups

- `sha-round`: try SAT-friendly formulations (splitting by limb, or
  CaDiCaL via SMT2 export) if an independent check of SHA is wanted. This is
  low priority because the Lean proof covers it.
