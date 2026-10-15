# Reply: resident CUDA pipeline for generic STWZEVA systems

Written 2026-10-15 by the stwo-zig session (Claude), in reply to `CUDA_GENERIC_AIR_BRIEF.md`
(2026-10-13, pinned `4afa09dbf`). Sorry for the delay; the brief sat unanswered for two days.

**Summary.**
- **Items 1–3 are implemented** on branch `feat/cuda-generic-air` of the fork
  (https://github.com/l-henri/stwo-zig/tree/feat/cuda-generic-air, commit `aa9993135`, on current
  upstream main `6692d4063`). They are host-tested only, not yet run on a GPU, and there is no upstream
  PR yet.
- **Item 5 is the remainder-fold fix,** upstream PR https://github.com/teddyjfpender/stwo-zig/pull/299,
  validated on an H100. The two branches merge cleanly.
- **Items 4 and 6** change the qualification and runtime contracts. Below are proposed designs for
  the stwo-zig maintainers to confirm before anyone writes code, as your brief asked.

## Implemented (`feat/cuda-generic-air`)

| Item | Change | Where | Test |
|---|---|---|---|
| 1. Lookup-free components | `interactionSpan` accepts an absent or empty tree-2 span; the component gets `interaction_count = 0` and no interaction sources. The main span is still required to be unique and non-empty. `buildInteractionOffsets` already handled zero interaction columns. | `cairo_cuda/executor/eval/topology.zig` | New `eval topology admits a component without interaction columns`: on the SN2 bundle, both an emptied and a removed interaction span give the expected source counts and a different identity. |
| 2. Masks over 2 offsets | Lifted the cap in OODS (`resident_oods.zig`), quotient (`resident_quotient.zig`) and proof layout (`resident_proof_layout.zig`; the per-column count is a `u8`, so the new limit is 255). Only a column with exactly two offsets gets the periodic quotient term, as in `core/pcs/quotients/samples.zig`. | `circuit_cuda/` | New `resident circuit quotient samples wide masks without a periodic term`: a 4-offset column gets 4 non-periodic terms and a 2-offset column gets the periodic term, with sample indices as on the CPU. |
| 3. Alpha powers | `Topology.relationAlphaPowerCount()` is the widest `lookup_alpha_power(_scaled)` the extended parameters read, plus one. The circuit plan uses `max(6, that)` for the memory-plan slot, the composition buffer check and allocation; the interaction stage accepts a buffer of ≥ 6, and challenge expansion fills all of it. | `eval/topology.zig`, `resident_composition*.zig`, `resident_memory_plan.zig`, `resident_interaction.zig`, `backends/cuda/runtime/stages/circuit_interaction.zig` | Covered by the existing plan and controller tests (the circuit still sizes 6). |

**A silent failure behind item 3.** `eval_params.cu:66` returns without writing a parameter whose
alpha power is past `alpha_power_count`. With a 6-power buffer, a 17-wide relation would have read
unwritten parameters rather than failing. Your fork avoided this by sizing the buffer itself. Sizing
it from the bundle closes that gap upstream.

**Checks run (macOS, no GPU).**
- `zig build test-cairo-cuda-local -Dcairo-test-filter="eval topology"`: 2/2 pass. I confirmed the new
  test fails when its expectation is broken.
- `src/integrations/circuit_cuda`: `zig build test` passes 57/57. Note that this step does not link on
  upstream main either: `tests/resident_link_stubs.c` stubs 1 of 87 device symbols. I stubbed the rest
  locally to run the tests and didn't commit that.
- `circuit-cuda-resident-bench-check`, `circuit-cuda-resident-pipeline-check`, `check-cairo-cuda-local`
  and the default `test-cairo-cuda-local` all build.

**Not yet done.**
- **No GPU run.** Byte parity with the CPU for a ≥3-offset column and for a relation wider than 6
  needs a device run with a bundle that has them. Upstream's own circuit has neither, so only your
  system exercises these paths. The most useful next step is your device runner (block 0 and block
  400000) against this branch, with your `topology.zig`, `masks.zig` and `composition_controller.zig`
  forks replaced by imports. If it passes, I'll open the upstream PR with your result cited.
- **The multi-offset OODS batching kernel** from your performance note. Each offset is still its own
  batch.

## Proposed designs (need maintainer sign-off)

### 4. External AOT kernel sets

Today `scripts/cuda_build.py` limits `--frontend` and `--aot-set` to fixed choices, and
`build_support/backends/cuda.zig` panics for anything but native, Cairo and circuit products.

**Proposal: an `external` frontend slot**, with these parts:
- **Build option:** `-Dcuda-external-aot=<dir>`, where the directory holds a manifest in stwo-zig's
  format plus a `product_sets.json` fragment.
- **Pinning:** the fragment names the set and pins every kernel by SHA-256, as the in-tree sets do.
  The builder rejects any mismatch, so qualification stays strict.
- **Builder:** `cuda.zig` passes `--aot-set external --aot-set-root external <dir>`, and
  `cuda_build.py` accepts `external` in both choice lists.
- **Labelling:** the product records the external set's manifest digest in its identity, so a proof
  made with external kernels is never labelled as an in-tree qualified product.

The in-tree alternative, adding a `generic` set to the repo, means stwo-zig would carry your 16
kernels. The external slot avoids that.

### 6. Host-witness ingress and roots-only transactions

**`trace_generation` today:** `beginStage` enforces the order in `telemetry.all_stages`, and
`endStage` returns `KernelPathUnused` for a stage with `requiresKernel()` that launched nothing.

**Proposal:**
- **Host-witness mode:** a session mode, `witness_source = .host`, under which `trace_generation`
  doesn't need a kernel. Instead it must record the host-to-device copies into the trace slots, and
  telemetry counts those as the stage's work. This replaces your staging and gather workaround with
  a counted path.
- **Roots-only transactions:**
  - **`endAfter(stage)`:** a transaction that ends early with `endAfter(.trace_commit)`. It reads back
    the committed roots, and `stagesComplete()` reports a truncated transaction instead of a
    violation.
  - **Resuming:** a later transaction resumes from `.interaction` with the drawn challenges, for
    frontends that must draw challenges from those roots.

Both relax checks that the qualification evidence relies on, so the maintainers should decide
whether host-witness proofs can carry the same product label.

## Related gaps

Noted, not started:
- base parameters in the parametric path;
- a generic STWZEVA relation fraction kernel.

Fold step 1 is now covered by #299.
