# GPU step 3: resident CUDA prover for the block system (2026-10-12)

Status: **design (M0), build and linked device schedule (M1) and host-checkable pieces (M2) done; no device run.** Parent: [gpu.md](gpu.md), step 3.
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
| `resident_composition_controller.zig` | **fork** (one line) | Generic, except `relation_alpha_powers.len != 6` (`:278`). Our widest tuple has 17 values, so we need α⁰…α¹⁷ (`composition_controller.zig`). |
| `resident_oods.zig`, `resident_quotient.zig`, `resident_proof_layout.zig` | **fork** (caps) | All three reject more than 2 mask offsets per column (`resident_oods.zig:75,80`, `resident_quotient.zig:61`, proof layout `count > 2`). Our AIRs read up to 23 rows (`block_sha`, `block_anc`; offsets −68…2816). The CPU PCS adds the periodic sample only for exactly two (`core/pcs/quotients/samples.zig:207`); `masks.zig` keeps that and lifts the cap, returning stwo-zig's own types. |
| `resident_fri.zig`, `resident_decommit.zig` | reuse | Generic over geometry and sink. Fold step 1: supported by code, **unqualified on a device**. |
| `resident_witness.zig`, `resident_interaction.zig` | **replace** | Circuit witness and LogUp producers. First version: host columns uploaded at ingress (below). |
| `resident_memory_plan.zig`, `resident_memory_binding.zig` | **adapt** (`memory.zig`) | Slot ids were `kind·256 + ordinal` with one source slot per column (`resident_memory_plan.zig:206`); our main tree has 1,210 columns. Trace columns now land in place in each tree's coefficient buffer (the commit skips the copy, `resident_commit.zig:193`), so there are no source copies. The circuit `values`/`interaction` slots go; statement words, claimed sums, z and α powers come in. |
| `resident_terminal_bundle.zig`, `resident_terminal_decode.zig`, `resident_terminal_capture.zig` | **adapt** (`terminal.zig`) | N_COMPONENTS claims and an interaction nonce (`resident_terminal_bundle.zig:54,70,76`). Ours: claims of the components with lookups (15), no interaction nonce. The decoder is generic over the layout type (`native_cuda/common/proof_decode.zig:24`). |
| `resident_pipeline.zig`, `resident_prover.zig` | **adapt** (`pipeline.zig`, `prover.zig`) | Our stage order, our ingress (two passes, below), our decode to `system.Proof`. |

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
- Cache key = `parametric.cacheKey(program identity, source identity, Cairo authority)`: stwo-zig's build validator pins the authority. Changing an AIR changes only its own kernel.
- GPU-host build: a local AOT root that reuses the `circuit` names (see Running on a pod). The script's `--frontend`/`--aot-set` choices are hard-coded (`scripts/cuda_build.py:56-64`).

## Results so far (host only)

`zig build cuda-test -Dcuda=true -Doptimize=ReleaseFast` (no GPU; 8 tests, about 40 s):
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

`zig build cuda-check -Dcuda=true` builds `prover.prove` (both passes, the schedule and decode) without optimisation, so every device call is emitted, and links it against C stubs (stwo-zig's `test_stubs.c` and our `link_stubs.c`, 42 entry points). Nothing is executed.

- **Mutation check:** if the statement mixes are merged into fewer calls (same words), the transcript test fails.

**Arena sizes** (`arena_test.zig`; planned from (L, profile), bound on a host stand-in, accepted by the composition controller and the FRI plan; production profile):

| L | uniform | tiered | roots pass (uniform / tiered) |
|---|---|---|---|
| 20 | 23.2 GiB | 6.4 GiB | 17.1 / 5.1 GiB |
| 22 | 92.8 GiB | 25.6 GiB | 68.3 / 20.3 GiB |
| 23 | 185.6 GiB | 51.2 GiB | 136.6 / 40.6 GiB |

- About 97 % of the arena is the trace trees (coefficients plus 2× evaluations plus Merkle).
- A real 2^22 block fits an H100 80 GB tiered, and an H200 141 GB either way.
- 2^23 needs tiered sizes on an H100; uniform 2^23 needs streaming.

## What a first NVIDIA run needs

1. **AOT archive.** Build stwo-zig's native CUDA archive with our 16 kernels:
   - `scripts/cuda_build.py` with an AOT root whose `circuit_eval` set (or a new set) is `gpu/cuda_aot/`;
   - its `--frontend`/`--aot-set` choices are fixed, so either add an upstream entry or use a local root with the `circuit` names.
2. **Link.** Link `prover.zig` against the archive instead of the stubs: a `-Dcuda-native-archive` option, as `circuit_cuda/build.zig:204` does.
3. **Run a small block, check bytes.** Prove block 0 at the test profile.
   - Compare pass 1's roots with the CPU's, then the proof bytes with `system.proveOpts`, then `system.verifyExt`.
   - Expect to debug the composition and quotient first: our masks are wider than the circuit's, and fold step 1 is unqualified.
4. **Real blocks.** Tiered 2^22 and production PoW 26.

Estimate: 1–2 weeks with an H100 or H200, mostly steps 3–4. Later, device LogUp removes pass 1 (another 1–2 weeks).

## Running on a pod

**Build (`-Dcuda=true`).**
- `zig build cuda-archive-plan`: validates the archive selection without NVIDIA tools (passes on macOS).
  - It runs stwo-zig's `scripts/cuda_build.py --plan-only` on a local AOT root built by `build.zig`: frontend `circuit` = {`.`, `circuit_eval`}.
  - `.` is stwo-zig's native set, regenerated as its build does. `circuit_eval` is `gpu/cuda_aot/`.
  - Result: 64 AOT sources (48 native + our 16); cubins per SM.
- `gpu/cuda_aot/aot_manifest.json` uses stwo-zig's parametric Cairo-eval identity scheme, the only one its validator admits for 16 components. `catalog.json` maps kernels to AIRs.
- `zig build install <toolchain flags>` builds the real archive and links `zig-out/bin/cuda-prove` against it.
  - Toolchain flags: `-Dcuda-nvcc`, `-Dcuda-host-cxx`, `-Dcuda-host-runtime`, `-Dcuda-host-unwind-runtime`, `-Dcuda-ar`, `-Dcuda-home`, `-Dcuda-library-dir`, `-Dcuda-driver-dir`, `-Dcuda-arch`.
  - `-Dcuda-arch` defaults to `sm_80,sm_89,sm_90` and is also the list of SMs a session accepts.
  - Without `-Dcuda-nvcc`, `cuda-prove` links the C stubs: the CPU side and `--mock` work; the device fails at session open (`ExecutionProviderMismatch`).

**Runner (`src/gpu/cuda/runner.zig`).** Runs on one sample at one profile, in this order:
1. CPU proof.
2. Device pass 1: compares the preprocessed and main roots with the CPU's (first differing word).
3. Host LogUp.
4. Device pass 2.
5. Structured diff in production order, naming the stage behind the first difference: claims, roots 0–3, sampled values (tree/column/sample), FRI roots, last layer, nonce, openings.
6. Byte comparison, `verifyExt`, timings, and device counters (peak live bytes, H2D bytes, launches, AOT misses).

Big blocks use `--skip-cpu --cpu-sha <prefix> --cpu-len <bytes>`, or `--cpu-proof <file>`. Mid-proof device state cannot be read: the resident contract allows one read per transaction. The diff is the stage checkpoint.

**Scripts (`scripts/pod/`, image `runpod/pytorch:1.0.2-cu1281-torch280-ubuntu2404`).**
- `bootstrap.sh <commit>` (or `--tarball f`): installs the apt tools, Zig 0.15.2 (checksummed), source and submodule, then builds.
- `run.sh`: block 0 test uniform → tiered → production uniform → tiered, then 400000 tiered production against `cbcf7026134f9a71` / 1,131,354 B.
  - Logs and `nvidia-smi` memory samples go to `/workspace/logs`.
- `diag.sh`: device facts and a pass-1-only run.
- `CUDA_ARCH=sm_89` (etc.) builds one target only, which is faster.

## Pod runs (2026-10-13, RunPod L40S, sm_89, driver 580.178.04, nvcc 12.8.93)

| Step | Result |
|---|---|
| block 0, test profile, uniform (log 11) | byte-identical, verifies (`b03d4b8a…`, 121,905 B) |
| block 0, test profile, tiered (logs 8–12) | byte-identical, verifies (121,843 B) |
| block 0, production, uniform | byte-identical, verifies (681,480 B) |
| block 0, production, tiered | byte-identical, verifies (718,143 B) |
| **block 400000, production, tiered (L = 22)** | **sha256 `cbcf7026134f9a71…`, 1,131,354 B: equal to the saved CPU proof**, verifies |

**Block 400000 (production):**
- Wall time: 62 s. Of that, 54.7 s is host work: witness 9 s, plans and trace trees 12 s, CPU commit of trees 0–1 21 s, LogUp 8 s.
- Device proof: 4.2 s. Of that, ingress (host→device copy of 7.4 GB) takes 2.3 s; constraint evaluation 0.57 s; trace commit 0.27 s; the rest is under 0.1 s.
- Device peak: 25.6 GiB live (planned 25.61); 26.9 GB in `nvidia-smi`. Host peak RSS: 45.9 GB.

**Failures and fixes on the way:**
1. **`StageOrderViolation`.** The runtime runs every stage in order and requires kernel work in each; transforms are not allowed in `.trace_generation`. A roots-only device pass is therefore impossible.
   - Fix: the host computes the trace roots (`system.traceRoots`), and the device proof is one transaction.
   - Trees 0–2 are uploaded to staging and assembled in `.trace_generation` with stwo-zig's contiguous witness gather (a copy).
2. **FRI first-layer root differed;** every trace root and sampled value already matched. stwo packs four rows per FRI leaf only when a layer folds more than once. The circuit pipeline always packs.
   - Fix: `fri.zig`/`decommit.zig` (forks) use `leafLog(fold_step)`.
3. **One byte differed** (offset 245): the decoder filled the legacy `PcsConfig.lifting_log_size`, which the CPU leaves empty. Fix: it is cleared in `terminal.toSystemProof`.

**Next levers** (the device proof is now a small part of the wall time):
- device LogUp and the device main commit (remove the CPU commit and the host LogUp);
- device witness, or uploading only the natural-order columns (ingress is 2.3 s for 7.4 GB);
- a bigger or uniform block on an H100/H200.

## CuMetal (local Apple-GPU run): blocked

`~/Workshop/cuda-metal` is cloned at the pinned commit e88dd103 and not built. Three things block a local run:
- **Missing tools.** The build needs CMake and Apple's Metal toolchain (`xcrun metal`, `xcrun metallib`; cuda-metal README, lines 30–44). This Mac has only the Command Line Tools. Both are system-wide installs (Homebrew CMake, Xcode), so they wait for the owner.
- **No qualified path for our kernels.** stwo-zig qualifies CuMetal only for the Native wide-Fibonacci closure (`backends/cuda/cumetal/frontend_support.json`). There, Cairo evaluation is "unavailable" and circuit is not listed. Our schedule calls Cairo/circuit-family kernels (`stwo_cairo_eval_materialize_params_on`, addressed LDE and quotient buckets, `stwo_circuit_degree_verdict_on`), so even with the tools it would need stwo-zig CuMetal work.
- **Our Metal backend already covers local device checks.** Step 2 runs whole proofs on the Apple GPU, byte-identical to CPU. A CuMetal run would add a check of the CUDA sources only.

## Risks and open items

- **Fold step 1 is unqualified on CUDA**, and so is the packed-leaf FRI layout at fold 1 (`resident_decommit.zig` uses 4 rows per leaf). Only a device run settles it.
- **Pass 1 sends the trace twice:** pass 1 uploads the preprocessed and main trees, and pass 2 uploads them again (2^22 tiered: about 6 GB of host→device copies per pass). Device LogUp removes pass 1.
- **Unverified on a device:** the composition kernels, LDE, Merkle, OODS, quotient and FRI kernels are stwo-zig's. Our inputs to them are checked only for shape (plans equal the CPU proof's) and for transcript order, not numerically.
- **Many OODS cohorts:** each extra mask offset of a column is its own cohort (`resident_oods.zig:107`), giving 4,837 samples. That is correct, but launch-heavy; batching by column is an optimisation.
- **Kernel size:** `block_coin` has 162 constants and `block_b2s` 10.9 k instructions. The parametric generator slices programs above 2,048 instructions, so neither is a blocker.
