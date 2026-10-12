# GPU step 3: resident CUDA prover for the block system (2026-10-12)

Status: **design (M0) and host-checkable pieces (M2) done; no device run.** Parent: [gpu.md](gpu.md), step 3.
Code: `src/gpu/cuda/` (built only with `-Dcuda=true`). stwo-zig paths below are under
`third_party/stwo-zig/src/` at 4afa09dbf; `cc/` is `integrations/circuit_cuda/`. Nothing in stwo-zig is modified.

## Goal

A proof-owned CUDA session that produces **the same bytes** as `system.proveOpts` on the CPU
(`src/air/system.zig:351`), verified by `system.verifyExt`. It reuses stwo-zig's resident circuit-recursion
pipeline (`cc/resident_prover.zig:67`, `cc/resident_pipeline.zig:81`), which already runs our profile
(`proving_5a7c5ed`, Blake2sM31 channel, plain Blake2s Merkle, `PcsConfigV2`, lifted trees, 4 trees).

## Stage map

| Stage (cc/) | Verdict | Why / what changes |
|---|---|---|
| `geometry.zig` | **replace** (fill its struct) | `Geometry.init` is bound to the 11 circuit components (`geometry.zig:44-58`). `Geometry` is a plain struct, so `plan.geometry` fills it from our parts: per-component column logs for trees 0–2, 8 composition columns at L, FRI layers from `FriGeometry`. |
| `resident_commit.zig` | reuse | Cohorts are runs of equal height (≤ 96, `abi/stages/commitment.zig:5`); mixed heights lift shorter-first, as the CPU. Input form for trees 0–2: evaluations in storage (bit-reversed) order. |
| `transcript_prefix.zig`, `resident_transcript.zig` | **replace** | Different prefix (below). `transcript.DeviceSink` keeps the stage kernels (`backends/cuda/runtime/stages/transcript.zig`) and the tail calls `resident_fri`/`resident_decommit` make on a sink (`anytype`). |
| `air_aot.zig`, `resident_composition.zig` | **replace** | Pinned to the circuit bundle SHA (`air_aot.zig:84`) and N_COMPONENTS (`resident_composition.zig:42`). `catalog.zig` + `plan.compositionPlan` fill the same `Plan` struct from our catalog. |
| `cairo_cuda/executor/eval/topology.zig` | **fork** (one line) | `uniqueSpan` (`topology.zig:407`) rejects a component with no interaction columns; `block_anc` has no lookups. `topology.zig` (ours) accepts an empty span. |
| `resident_composition_controller.zig` | **adapt** (to do) | Generic, except `relation_alpha_powers.len != 6` (`:278`). Our widest tuple has 17 values, so we need α⁰…α¹⁷. |
| `resident_oods.zig`, `resident_quotient.zig`, `resident_proof_layout.zig` | **fork** (caps) | All three reject more than 2 mask offsets per column (`resident_oods.zig:75,80`, `resident_quotient.zig:61`, proof layout `count > 2`). Our AIRs read up to 23 rows (`block_sha`, `block_anc`; offsets −68…2816). The CPU PCS adds the periodic sample only for exactly two (`core/pcs/quotients/samples.zig:207`); `masks.zig` keeps that and lifts the cap, returning stwo-zig's own types. |
| `resident_fri.zig`, `resident_decommit.zig` | reuse | Generic over geometry and sink. Fold step 1: supported by code, **unqualified on a device**. |
| `resident_witness.zig`, `resident_interaction.zig` | **replace** | Circuit witness and LogUp producers. First version: host columns uploaded at ingress (below). |
| `resident_memory_plan.zig`, `resident_memory_binding.zig` | **adapt** (to do) | Slot ids are `kind·256 + ordinal` with one slot per column (`resident_memory_plan.zig:206`): our main tree has 1,210 columns. Circuit `values`/`interaction` slots go; statement words, claimed sums, z and α powers come in. |
| `resident_terminal_bundle.zig`, `resident_terminal_decode.zig`, `resident_terminal_capture.zig` | **adapt** (to do) | N_COMPONENTS claims and an interaction nonce (`resident_terminal_bundle.zig:54,70,76`). Ours: claims of the components with lookups (15), no interaction nonce. The decoder is generic over the layout type (`native_cuda/common/proof_decode.zig:24`). |
| `resident_pipeline.zig`, `resident_prover.zig` | **adapt** (to do) | Our stage order, our ingress, our decode to `system.Proof`. |

## Transcript

| Step | CPU (`system.proveOpts`) | Circuit (`cc/resident_pipeline.zig:94-118`) |
|---|---|---|
| 1 | FRI config (two felts) | channel salt, then FRI config |
| 2 | preprocessed root | preprocessed root |
| 3 | statement: `[n]`, per component `[log, digest₀..₇, n_pub]`, one `[p]` per public input (369 `mix_u32s` for the block system) | circuit hash, output claim |
| 4 | main root | base root |
| 5 | — | 20-bit interaction grind |
| 6 | draw (z, α) | draw (z, α) |
| 7 | claimed sums (one `mix_felts`) | claimed sums |
| 8 | interaction root | interaction root |
| tail | composition α, root, OODS point, sampled values, DEEP α, FRI roots/α's, last layer, query grind, queries | same |

The statement words are public: uploaded at ingress, mixed as slices (digest words are not M31, so no M31 validation).

## Witness and interaction (first device run)

The resident contract allows host writes only during ingress (`backends/cuda/runtime/context.zig:537`) and one proof read at the end (`telemetry.zig:253`). Host-built interaction columns need (z, α), which depend on the main root. Fastest credible path, in two transactions:
1. **Tx 1:** upload preprocessed and main evaluations, commit both on the device, read the two roots (the one allowed proof read).
2. **Host:** replay the prefix (`transcript.HostSink`), draw (z, α), build the interaction columns and claimed sums with today's multi-threaded code (`system.fractions`, `logup_columns.build`).
3. **Tx 2:** a full resident proof. Ingress uploads preprocessed, main and interaction evaluations, the statement words, claimed sums, z and α⁰…α^w. The device recommits trees 0–1 (cheap on a GPU) and draws (z, α) itself. The uploaded values are only consistent if the device draws the same (z, α); the verifier catches any mismatch.

Later: a device LogUp producer generated from the IR lookups. `relation_completion` (batch inverse and prefix sum) is generic; only the fraction producer is per-AIR. That removes tx 1.

## Public inputs

The CPU path bakes public inputs into the program as literals. Our lowering deduplicates equal constants (`stwzeva.ProgramBuilder.constant`), so the program shape depends on the values. New `PubMode.slots`: one `constant` instruction per public input, never shared. stwo-zig's parametric normaliser (`cairo_cuda/parametric_eval.zig:18`) turns every base literal into a session constant and erases the domain size. The kernel then depends on the AIR only: one kernel per AIR, for every statement and log size. The statement reaches the kernel through `args->base_params`, exactly as the circuit binds its literals (`resident_composition.zig`, `writeConstants`). Base `param`s (`lowerTemplate`) are not needed: the parametric path rejects them (`parametric_eval.zig:20`).

## AOT catalog

- `gpu/cuda_aot/`: 16 kernels (3.2 MiB of CUDA) and an `aot_manifest.json` in stwo-zig's product-set format.
- Cache key = `parametric.cacheKey(program identity, source identity, AIR digest)`, so changing an AIR changes only its own kernel.
- To build on a GPU host: `scripts/cuda_build.py --native-aot-root <root>` with a `product_sets.json`, plus `--aot-set-root`.
  - The script's `--frontend`/`--aot-set` choices are hard-coded (`scripts/cuda_build.py:56-64`), so it needs either an upstream entry for our set or a local AOT root that reuses the `circuit` names.

## Results so far (host only)

`zig build cuda-test -Dcuda=true -Doptimize=ReleaseFast` (no GPU):
- **Catalog invariance:** for all 16 AIRs, the normalised program identity and constant count are the same at logs 8/12/22 and for all-zero, all-one and random public inputs.
- **AOT kernels = interpreter:** the 16 catalog sources, built as host C++ (CUDA built-ins shimmed), equal our interpreter's composition at logs 6 and 9, with random traces, lookup elements and statements. The statement is bound only through `base_params` and wide trace offsets.
- **Drift:** the generated sources and manifest equal `gpu/cuda_aot/` byte for byte (`STARKED_CUDA_AOT_WRITE=1` regenerates).
- **Plans = CPU proof.** CPU proofs of block 0 are taken in the uniform profile (all components at log 11) and the tiered profile (logs 8–12, lifted to 13). For each, the resident plans reproduce the verifier's capture:
  - every tree's column sizes;
  - per-column OODS sample counts (4,837 samples);
  - the FRI layer count (11 and 12);
  - one placement per component (3,576 constraints).
- **Transcript = CPU.**
  - `HostSink` and the device sink run on a host model of the session, fed the proof's roots and values.
  - They reproduce the composition α, OODS point, DEEP α and query-grind nonce, and every raw query.

## Risks and open items

- **Fold step 1 is unqualified on CUDA**, and so is the packed-leaf FRI layout at fold 1 (`resident_decommit.zig` uses 4 rows per leaf). Only a device run settles it.
- **Memory at 2^22:** the resident arena size comes from the memory plan (to do). Every tree stays resident (sources, coefficients, 2× evaluations), so a uniform 2^22 block is far above one GPU; tiered sizes (D-045) are the realistic target.
- **Many OODS cohorts:** each extra mask offset of a column is its own cohort (`resident_oods.zig:107`), giving 4,837 samples. That is correct, but launch-heavy; batching by column is an optimisation.
- **Kernel size:** `block_coin` has 162 constants and `block_b2s` 10.9 k instructions. The parametric generator slices programs above 2,048 instructions, so neither is a blocker.
