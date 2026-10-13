# GPU step 3: resident CUDA prover for the block system (2026-10-12)

Status: **byte-identical on L40S and H100 up to 2^23 tiered (2026-10-13), with device LogUp (default) and host LogUp (`--host-logup`).** Device witness for `block_sha`, `block_b2s` and tree 0 (default; `--host-witness` for A/B): host-checked, device run pending (§ Device witness). Parent: [gpu.md](gpu.md), step 3.
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
| `resident_commit.zig` | reuse | Cohorts are runs of equal height (≤ 96, `abi/stages/commitment.zig:5`); mixed heights lift shorter-first, as the CPU. Input form for trees 0–2: evaluations in storage (bit-reversed) order; trees 0–1 get there on the device (§ Natural upload). |
| `transcript_prefix.zig`, `resident_transcript.zig` | **replace** | Different prefix (below). `transcript.DeviceSink` keeps the stage kernels (`backends/cuda/runtime/stages/transcript.zig`) and the tail calls `resident_fri`/`resident_decommit` make on a sink (`anytype`). |
| `air_aot.zig`, `resident_composition.zig` | **replace** | Pinned to the circuit bundle SHA (`air_aot.zig:84`) and N_COMPONENTS (`resident_composition.zig:42`). `catalog.zig` + `plan.compositionPlan` fill the same `Plan` struct from our catalog. |
| `cairo_cuda/executor/eval/topology.zig` | **fork** (one line) | `uniqueSpan` (`topology.zig:407`) rejects a component with no interaction columns; `block_anc` has no lookups. `topology.zig` (ours) accepts an empty span. |
| `resident_composition_controller.zig` | **fork** (one line) | Generic, except `relation_alpha_powers.len != 6` (`:278`). Our widest tuple has 17 values, so we need α⁰…α¹⁷ (`composition_controller.zig`). |
| `resident_oods.zig`, `resident_quotient.zig`, `resident_proof_layout.zig` | **fork** (caps) | All three reject more than 2 mask offsets per column (`resident_oods.zig:75,80`, `resident_quotient.zig:61`, proof layout `count > 2`). Our AIRs read up to 23 rows (`block_sha`, `block_anc`; offsets −68…2816). The CPU PCS adds the periodic sample only for exactly two (`core/pcs/quotients/samples.zig:207`); `masks.zig` keeps that and lifts the cap, returning stwo-zig's own types. |
| `resident_fri.zig`, `resident_decommit.zig` | reuse | Generic over geometry and sink. Fold step 1: supported by code, **unqualified on a device**. |
| `resident_witness.zig` | **replace** | Circuit witness producer. Ours: `block_sha`, `block_b2s` and tree 0 generated in `.trace_generation` (`witness.zig`, § Device witness); the other columns built on the host and uploaded at ingress (below). |
| `resident_interaction.zig` | **replace** (`logup.zig`) | Its fraction producer is the circuit's 11 hand-written gates and its challenge expansion fixes 6 α powers. Ours: one generated kernel per AIR, the same generic `relation_completion` (§ Device LogUp). |
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

## Witness and interaction

The resident contract allows host writes only during ingress (`backends/cuda/runtime/context.zig:537`) and one proof read at the end (`telemetry.zig:253`). The trace (trees 0–1) is built on the host and uploaded at ingress, in natural row order, into staging slots, except the columns the device generates there in `.trace_generation` (§ Device witness); `.trace_generation` then reorders it into the commitments' buffers in storage order (§ Natural upload).

**Host LogUp (first version; `cuda-prove --host-logup`).** Host-built interaction columns need (z, α), which depend on the main root. The host computes the roots of trees 0–1 (`system.traceRoots`, a CPU commit), replays the prefix (`transcript.HostSink`), draws (z, α) and builds the interaction columns and claims (`system.interactionTrace`). Ingress uploads them with the trees; the device recommits trees 0–1, draws (z, α) itself and commits the uploaded tree 2. A different draw would be caught by the verifier. (The first plan was a roots-only device transaction; the runtime forbids it, see Pod runs.)

## Device LogUp (default, 2026-10-13)

Code: `src/gpu/cuda/logup.zig`; schedule in `pipeline.zig` (`.trace_generation`, `.trace_commit`). This follows `cc/resident_pipeline.zig:80-118`: inside `.trace_commit` the device commits tree 0, mixes, commits tree 1, draws (z, α), produces tree 2 and the claims, mixes the claims and commits tree 2. The runner no longer calls `system.traceRoots`, the host draw or `system.interactionTrace`, and tree 2 is not uploaded.

| Step | Where | What |
|---|---|---|
| sources | `.trace_generation` | The lookups read 551 of the 1,435 columns of trees 0–1. Right after the reorder (§ Natural upload) they are copied from the trees' coefficient buffers (storage order) into one compact slot (`logup_sources`, per component in kernel order) because the commitments interpolate trees 0–1 in place before the draw. Runs of adjacent columns are one device copy. |
| challenges | `.trace_commit` | `stwo_relation_expand_challenges_on` expands the drawn (z, α) into `relation_z` and α⁰…α¹⁷ (`relation_alpha_powers`, read later by the composition). The circuit wrapper fixes 6 powers; we call the ABI with 18. Both LogUp modes use it now (nothing is uploaded for z and α). |
| fractions | `.trace_commit` | One generated kernel per AIR with lookups (15; `block_anc` has none). One thread per storage row: every live lookup expression once (columns at their row offsets, constants, public inputs read from the statement words), then per batch `N = m₀·d₁ + m₁·d₀`, `D = d₀·d₁` with `d = rel + Σ vᵢ·αⁱ⁺¹ − z` (`system.Fractions.fill`, `component.denominator`). `N` goes to the batch's four tree-2 coefficient columns, `D` to a slab. A zero `D` sets the error flag (the CPU fails on it). |
| completion | `.trace_commit` | stwo-zig's generic `relation_completion` (`TraceCommitNative`): batch inverse of the slab, per-row running sum across batches, claimed sum of the last column, minus `claim · 2^-log`, and the coset-order inclusive scan of the last column — the semantics of `logup_columns.build`. Claims are written to `claims_mixed` (one per component with lookups) and copied into `claims_component` (zero for `block_anc`) for the composition. |
| commit | `.trace_commit` | Mix the claims, capture them, commit tree 2 from its coefficient buffer (in place, as before). |

**Row order.** Device trace columns are storage-order evaluations (bit-reversed circle domain). Storage row `s` is natural (coset-order) row `i` with `s = bitrev(circle(i))` (`natural` in `system.fractions`). A read at offset `o` is storage row `bitrev(circle((i + o) mod n))`; `(i + o) mod n` is a 32-bit wrap and a mask (n divides 2³²). The completion's scan uses the same map (`relation_coset_scan_row`).

**Memory** (`memory.zig`). New slots: `logup_sources` (`.trace_generation`–`.trace_commit`), pointer tables and completion geometry (ingress–`.trace_commit`, uploaded at ingress), completion scratch (`.trace_commit`). The denominator slab (tree-2 sized) borrows the head of tree 2's evaluation buffer, which is unused until tree 2 is committed right after the completion. Tree 2 has no staging slot. Planned arena (production profile): 2^22 tiered 26.4 GiB (25.6 with host LogUp), 2^23 tiered 52.8 GiB (51.2), 2^22 uniform 98.3 GiB (92.8). The 0.8–1.6 GiB tiered increase is the sources slot.

**AOT.** The kernels are `witness` entries of `gpu/cuda_aot/aot_manifest.json` under stwo-zig's native-authenticated identity (`sha256-source-and-contract-v1`: cache key from the source hash and a semantic contract naming the AIR digest and our argument list). The build admits only its listed ABI tags; we use `native_blake_exact_interaction_v1`, the only paired-LogUp-fraction tag. The tag is just an equality key between the manifest and the launch (`session.launchKernel`, `kernel.Kernel`); the argument contract is ours (8 arguments: `sources, outputs, pubs, powers, z, denominators, error, log_size`). `cuda-archive-plan`: 80 AOT sources (48 native + 16 constraint + 15 LogUp + 1 reorder).

## Natural upload (2026-10-13, branch `cuda/natural-upload`)

Before: the host permuted every column of trees 0–1 into storage order (`air/prove.zig toStorage`: natural row `i` → `bitrev(circle(i))`) and uploaded the copies. At 2^22 tiered on the M4 Pro that was 2.3–3.6 s of memory-bound scatter plus 0.6 s for the preprocessed columns, and a second host copy of the main tree.

Now (`prover.hostTraceTrees`, `pipeline.assembleTrace`, `reorder.zig`):

| Step | Where | What |
|---|---|---|
| host | `hostTraceTrees` | Tree 1: descriptors over the witness's own column slices (`Input.mains`), no copy. Tree 0: `system.preprocessedNatural` (natural order; `ir.PreCol.fill` by memset and period runs, all columns on all cores). Tree 2 (host LogUp only) stays the storage-order `system.interactionTrace`. |
| ingress | `uploadTree` | Unchanged: column `j` into its staging view (the commitment's cohort layout). |
| reorder | `.trace_generation` | Our kernel `starked_reorder_v1_*`, one launch per cohort of trees 0–1 (grid `(⌈2^log/256⌉, columns)`, at most 65,535 columns per launch): `storage[c·2^log + s] = natural[c·2^log + natural_row(s)]`, one thread per destination row (coalesced writes, gathered reads), staging → coefficient buffer, in place of the copy. A staged tree 2 (host LogUp) is a device copy per cohort. |
| LogUp sources | `.trace_generation` | `logup.Bound.gather` now reads the reordered coefficient buffers (storage order), so the fraction kernels are unchanged. |

The proof bytes cannot change: from the end of `.trace_generation` on, the device holds exactly what it held before. The arena is unchanged (same slots and lifetimes; 26.4 GiB at 2^22 tiered).

**AOT.** One fixed `witness` entry (`gpu/cuda_aot/witness_starked_reorder_*.cu`, last in the manifest), native-authenticated identity, ABI tag `native_m31_permutation_trace_v3` (a row permutation of M31 columns; the four-argument contract `natural, storage, log_size, columns` is ours and pinned by the semantic contract). As for LogUp, the tag is only an equality key between manifest and launch.

**Host checks** (`reorder_test.zig`, in `cuda-test`). The exact AOT source is built as host C++ and run over each launch's whole grid:
- it equals `toStorage` for cohorts of logs 0, 1, 2, 4, 7, 8, 9, 11, 12 and 16 with 1–7 columns, packed back to back (log 0 caught a bug: a one-row column maps row 0 to itself);
- the whole `.trace_generation` (`assembleTrace` through `reorder.Kernel.launch` and `logup.Bound.gather`, with a host session that runs the kernel at the launch's own grid and arguments) over an arena in host memory, bound with the real plans of block 0 uniform (2 launches) and tiered (18 launches): each of the 1,435 tree-0/1 columns equals the CPU prover's storage-order column, and the LogUp sources equal the storage-order columns they read.

**Host effect** (M4 Pro, block 400000 tiered 2^22, production, `cuda-prove --skip-cpu`, stops at session open):

| | before (0852bfd) | natural upload |
|---|---|---|
| "host trace trees" lap | 3.66 s | **0.15 s** |
| host trees | 1.0 GiB preprocessed + 5.4 GiB main, storage-order copies | 1.0 GiB preprocessed generated, 5.43 GiB main borrowed |
| peak memory footprint (`time -l`) | 14.07 GB | **7.16 GB** |

The saving in RSS is the main tree's storage copy: 5.4 GiB at 2^22, about 11 GiB at 2^23 (where the H100 runs reported 37 GB RSS, so expect about 25 GB). On the 18-vCPU H100 pod "plans/trees" was 16.9 s (2^22) and 30–35 s (2^23) before the parallel host commit 0852bfd; that pod is the place to measure the combined effect. The device adds one reorder launch per cohort of trees 0–1 (18 launches at block 0 tiered), a memory-bound gather over 6.4 GiB at 2^22: a few ms on an H100.

**Pinned host memory.** stwo-zig's ingress is `cudaMemcpyAsync` from pageable memory (`native/runtime/context.cu`, `stwo_exec_context_memcpy_h2d_async`), and the runtime has no host-register or pinned-staging API. Registering the witness ourselves (`cudaHostRegister`, about 13 GB at 2^23) would cost about what it saves: pinning runs at a few GB/s and ingress is 1.6 s for 12.9 GiB. It pays only if the witness generators allocate pinned memory from the start, or with an upstream double-buffered pinned upload. Not done.

## Device witness (2026-10-13, branch `cuda/device-witness`)

Code: `src/gpu/cuda/witness.zig` (kernels, inputs, plan, launches), `witness_test.zig`; `pipeline.assembleTrace` runs it first in `.trace_generation`. The device writes the largest columns into the staging slots in natural row order, exactly where ingress would have put the host's, so the reorder, the LogUp gather and every commitment are unchanged. No AIR or column definition changes.

| Kernel | Grid | Writes | Host generator it reproduces |
|---|---|---|---|
| `sha_words` | one thread per 72-row period (64 threads/block) | words `a, e, w` of every row into `witness_scratch` (3 words/row) | `sha256/witness.zig Words.place` (zero dummy past the plan) |
| `sha_columns` | one thread per row | `block_sha`'s 144 columns | `witness.columns` with `shaRole` (bits, Σ/σ/Ch/Maj limbs from cyclic neighbours, carries by role), `block/sha.zig Extra` (Meta columns, NILS/USEW/CHN/NNE, the mutation check's limb differences with row r − 8 and their M31 inverses, the ALLEQ chain on period rows 12–19) |
| `b2s` | one thread per row; recomputes its period's earlier G steps | `block_b2s`'s 312 columns | `hash/blake2s_air.zig fillPeriod` + `block/commit.zig B2sFill` |
| `pre` | one thread per (row, column); one launch per run of equal-log tree-0 columns | every preprocessed column | `ir.PreCol.at` (is_first, not_last, periodic, row_lt, row_ge_end) |

**Inputs** (`witness_inputs`, ingress → `.trace_generation`; `witness.Layout`): the SHA-256 K table followed by the per-period `Meta` (mid, blk, flags, lid, rid, ym; final, i.e. after `buildFull` sets `ym` from the coin counts), one compression (input state, block) per used period, the Blake2s σ table, one input per used Blake2s period (chaining value: `H0` or `chain[p−1]`, block, counter, last flag) plus the unused-period dummy, the preprocessed descriptors and periodic values, and the device address of every generated column (pointer tables, as the LogUp tables). 5.0 MiB at 2^22, 9.6 MiB at 2^23. `witness_scratch` (`.trace_generation` only) holds the SHA word trace: 48 / 96 MiB. The planned arena is unchanged (26.42 GiB at 2^22 tiered, 52.82 GiB at 2^23 tiered): both slots overlap buffers that are not live yet.

**Host** (`Input.witness`, `Prepared.initWitness`, `hostTraceTreesFor`): `buildFull` keeps the plan (`Built.sha_plan`) and the undo stream (`Built.undo`); with `skip_device_columns` it does not build the two components' columns. Tree 0 is not generated on the host. `uploadTree` skips the generated columns. `cuda-prove` uses the device witness unless `--host-witness` (or `--mock`), and skips the host columns when nothing on the host reads them (`--skip-cpu` or `--cpu-proof`, no `--host-logup`). Host LogUp needs every column on the host (its CPU roots and interaction trace), so there the host builds them all and the device still generates its own.

**AOT.** Four fixed `witness` entries (`gpu/cuda_aot/witness_starked_witness_{b2s,pre,sha_columns,sha_words}_*.cu`, after the reorder in the manifest), native-authenticated identity, ABI tag `native_indexed_recurrence_trace_v1` (a row-indexed trace; as for the reorder and LogUp tags, only an equality key between manifest and launch: the five-argument contract is ours and pinned by each semantic contract). No module globals: the K and σ tables travel in the inputs. `cuda-archive-plan`: 84 AOT sources (48 native + 16 constraint + 15 LogUp + 1 reorder + 4 witness).

**Host checks** (`witness_test.zig`, in `cuda-test`). The exact AOT sources are built as host C++ and each launch runs over its whole grid with its own argument array:
- generators = CPU: `witness.Bound.upload` + `generate` over host memory reproduce `buildFull`'s `block_sha` and `block_b2s` columns and `system.preprocessedNatural`, bit for bit: block 0 (uniform L 11, tiered L 12), 170, 91812 (tiered); with `STARKED_WITNESS_SAMPLES=2,4,5` also 91722, 91842, 91880; with `STARKED_WITNESS_LARGE=400000` block 400000 tiered at L 22 (SHA: 39,691 compressions at log 22, Blake2s: 3,213 blocks at log 20; 4.5 s on one core, 9.8 GB RSS). A flipped message word or Blake2s counter changes the output (the comparison is live);
- the whole `.trace_generation` (generators, reorder, LogUp gather) over a host-memory arena bound with block 0's real plans (uniform 6 launches, tiered 30), the host witness built with `skip_device_columns` and ingress through `prover.uploadTree`: all 1,435 tree-0/1 columns equal the CPU prover's storage-order columns (from a full build), and the LogUp sources the columns they read. Ingress for block 0: 6.0 MiB instead of 11.2 MiB (uniform).

**Host effect** (M4 Pro, production, tiered, `cuda-prove --skip-cpu`, stops at session open; `/usr/bin/time -l`):

| | 400000 (2^22) device witness | `--host-witness` | 970347 (2^23) device witness | `--host-witness` |
|---|---|---|---|---|
| "witness built" lap | **0.79 s** | 1.27 s | **1.55 s** | 2.94 s |
| host trees to upload | 0 + 1.96 GiB | 1.00 + 5.43 GiB | 0 + 3.92 GiB | 2.00 + 10.86 GiB |
| planned H2D | **2.00 GiB** | 6.46 GiB | **3.99 GiB** | 12.92 GiB |
| peak memory footprint | **2.30 GB** | 7.16 GB | **4.50 GB** | 14.21 GB |

Generated on the device: 4.47 GiB (2^22) / 8.94 GiB (2^23) of trees 0–1. Expected on the 16-vCPU H100 pod (witness 4× slower than the M4 Pro, ingress 1.4–4.1 s for 6.5–12.9 GiB): at 2^23 roughly 7–9 s less host witness and 1–3 s less ingress, against a few ms of kernels (a memory-bound 9 GiB write).

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

- **Device LogUp = CPU** (`logup_test.zig`). The 15 generated fraction kernels (the exact `gpu/cuda_aot` sources) are built as host C++ and run over what the device gets: the storage-order columns the plan gathers, the statement words, α⁰…α^w and z. A host model of stwo-zig's completion (`logup.hostComplete`: invert, running sum, claim, shift, coset-order scan, driven by the plan's completion geometry) finishes them. Every tree-2 column (444) and every claim equals `system.interactionTrace`: block 0 uniform (L 11) and tiered (logs 8–12), blocks 170, 91722, 91812, 91842, 91880 tiered (`STARKED_LOGUP_SAMPLES=1,2,3,4,5`), and block 400000 tiered at L = 22 (`STARKED_LOGUP_LARGE=400000`). A mutation (offset direction) fails it.
- **LogUp identities and arena:** kernel identities follow stwo-zig's native-authenticated scheme (and `cuda-archive-plan` validates the manifest with stwo-zig's own Python); the LogUp buffers bind in the 2^20–2^23 arenas and stwo-zig's checked `relation_completion.prepare` accepts them.

Not checked on the host: the completion kernels themselves (batch inverse groups, ragged reductions, block scans; stwo-zig's, used by its circuit pipeline), the d2d source copies, the kernels under nvcc, and the AOT bind of the new entries. The device run checks them.

`zig build cuda-check -Dcuda=true` builds `prover.prove` and `prover.proveHostLogup` (the schedule and decode) without optimisation, so every device call is emitted, and links it against C stubs (stwo-zig's `test_stubs.c` and our `link_stubs.c`, 45 entry points). Nothing is executed.

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
2. Host: plans, the natural-order trees 0–1 (main borrowed from the witness; `block_sha`, `block_b2s` and tree 0 generated on the device unless `--host-witness`), twiddles. With `--host-logup` also the CPU roots of trees 0–1 (compared with the CPU proof's), (z, α) and the interaction trace.
3. The device proof (one transaction; device LogUp unless `--host-logup`).
4. Structured diff in production order, naming the stage behind the first difference: claims, roots 0–3, sampled values (tree/column/sample), FRI roots, last layer, nonce, openings.
5. Byte comparison, `verifyExt`, timings, and device counters (peak live bytes, H2D bytes, launches, AOT misses).

Big blocks use `--skip-cpu --cpu-sha <prefix> --cpu-len <bytes>`, or `--cpu-proof <file>`. Mid-proof device state cannot be read: the resident contract allows one read per transaction. The diff is the stage checkpoint.

**Scripts (`scripts/pod/`, image `runpod/pytorch:1.0.2-cu1281-torch280-ubuntu2404`).**
- `bootstrap.sh <commit>` (or `--tarball f`): installs the apt tools, Zig 0.15.2 (checksummed), source and submodule, then builds.
- `run.sh`: block 0 test uniform → tiered → production uniform → tiered, then 400000 tiered production against `cbcf7026134f9a71` / 1,131,354 B. Single steps: `large-prod-tiered-hostlogup`, `large-prod-tiered-hostwitness`, `xl-970347`, `xl-970347-hostwitness`, `xl-774628`; `EXTRA=--host-witness` (or `--host-logup`) applies to any step.
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

**H100 NVL (RunPod, sm_90, 94 GB, 27 vCPUs, driver host CUDA 13.0, nvcc 12.8; 2026-10-13):**

| Step | Result | Wall | Device proof | Device peak | Host RSS |
|---|---|---|---|---|---|
| block 0, production, tiered | byte-identical, verifies | 1.5 s | | 0.9 GB | 0.4 GB |
| block 400000, production, tiered (L = 22) | `cbcf7026…` as on the L40S, verifies | 82 s | 4.8 s | 27.0 GB | 45.9 GB |
| **block 970347, production, tiered (L = 23)** | **byte-identical to the CPU proof** (`f6ff8ac953601dea…`, 1,184,413 B), verifies | 630 s incl. CPU proof | 5.5 s | 53.2 GB (51.20 GiB planned) | 90.7 GB |
| **block 774628, production, tiered (L = 23)** | **byte-identical to the CPU proof** (`c015e4b36600463a…`, 1,185,434 B), verifies | 682 s incl. CPU proof | 10.4 s (ingress 7.2 s) | 53.2 GB | 90.6 GB |

At 2^23 (block 970347) the host dominates even more on this 27-vCPU pod: witness 25 s, CPU proof (reference only) 394 s, plans and trace trees 38 s, **CPU commit of trees 0–1 123 s**, host LogUp 14 s. Device stages: ingress 2.9 s (14.75 GB), constraint evaluation 1.16 s, trace commit 0.49 s, the rest < 0.15 s each. The device itself scales about linearly (sum of stages after ingress, 2^22 → 2^23: 1.05 s → 1.9 s). Ingress varies between runs (2.9 s vs 7.2 s for the same size), so pinned host buffers are worth checking.

**Next levers** (the device proof is now a small part of the wall time):
- device LogUp and the device main commit: **done** (§ Device LogUp run);
- "plans, host trace trees, twiddles" (17 s at 2^22, 30–35 s at 2^23) and the witness (10 s / 20 s) are now the largest host steps;
- device witness, or uploading only the natural-order columns (ingress is 2.3 s for 7.4 GB);
- a uniform 2^22 block (92.8 GiB) on an H200; tiered 2^23 is done (above).

### Device LogUp run (H100 NVL, sm_90, 18 vCPUs, 2026-10-13)

All steps byte-identical and verified, first try. Time to proof (runner clock, before the optional `verifyExt`):

| Block | Device LogUp | Host LogUp (A/B, same pod) | Host RSS | Device peak | H2D |
|---|---|---|---|---|---|
| 0, four profiles | 1.1–1.3 s, identical | | 0.3 GB | 0.8 GB | |
| 400000 tiered (2^22) | **30.4 s** (witness 10.4, plans/trees 16.9, device 3.1) | 84.0 s (roots 39.0, LogUp 10.0) | 18.7 GB (45.9) | 27.9 GB | 6.46 GiB (7.37) |
| 970347 tiered (2^23) | **60.5 s** (witness 21.4, plans/trees 35.2, device 4.0) | ≈ 205 s (27-vCPU pod, earlier run) | 37.2 GB | 54.9 GB | 12.92 GiB |
| 774628 tiered (2^23) | **53.2 s** (witness 19.6, plans/trees 29.6, device 4.0) | ≈ 230 s (earlier run) | 37.1 GB | 54.9 GB | 12.92 GiB |

Device stages at 2^23: ingress 1.56 s, trace commit (now with commits 0–1, LogUp, commit 2) 0.52 s, constraint evaluation 1.15 s, OODS 0.15 s, the rest < 0.1 s. `verifyExt` adds 6 s (2^22) / 18 s (2^23).

### Natural upload + parallel host run (H100 NVL, sm_90, 16 vCPUs, 2026-10-13 evening)

All steps byte-identical and verified (block 0 ×4, 400000, A/B host LogUp, 970347, 774628). Time to proof:

| Block | Witness | Plans + trees + twiddles | Device proof | **Proof done** | Host RSS | Before (afternoon) |
|---|---|---|---|---|---|---|
| 400000 (2^22) | 8.3 s | 0.17 s | 3.3 s (ingress 1.36, reorder 0.017) | **11.8 s** | 12.0 GB | 30.4 s, 18.7 GB |
| 970347 (2^23) | 14.8 s | 0.39 s | 7.6 s (ingress 4.13, reorder 0.039) | **22.7 s** | 23.6 GB | 60.5 s, 37.2 GB |
| 774628 (2^23) | 15.5 s | 0.32 s | 5.1 s (ingress 2.31, reorder 0.039) | **20.8 s** | 23.6 GB | 53.2 s, 37.1 GB |

The witness is now the largest step. It is 4× slower on this pod than on the M4 Pro (8.3 s vs 2.0 s at 2^22): its remaining single-threaded parts (walk, fields, checks, coin) run on slower server cores. Ingress (pageable H2D, 6.5–12.9 GiB) is next: 1.4–4.1 s.

## CuMetal (local Apple-GPU run): blocked

`~/Workshop/cuda-metal` is cloned at the pinned commit e88dd103 and not built. Three things block a local run:
- **Missing tools.** The build needs CMake and Apple's Metal toolchain (`xcrun metal`, `xcrun metallib`; cuda-metal README, lines 30–44). This Mac has only the Command Line Tools. Both are system-wide installs (Homebrew CMake, Xcode), so they wait for the owner.
- **No qualified path for our kernels.** stwo-zig qualifies CuMetal only for the Native wide-Fibonacci closure (`backends/cuda/cumetal/frontend_support.json`). There, Cairo evaluation is "unavailable" and circuit is not listed. Our schedule calls Cairo/circuit-family kernels (`stwo_cairo_eval_materialize_params_on`, addressed LDE and quotient buckets, `stwo_circuit_degree_verdict_on`), so even with the tools it would need stwo-zig CuMetal work.
- **Our Metal backend already covers local device checks.** Step 2 runs whole proofs on the Apple GPU, byte-identical to CPU. A CuMetal run would add a check of the CUDA sources only.

## Risks and open items

- **Device witness, unverified on a device:** nvcc on the four generators, their AOT bind under `native_indexed_recurrence_trace_v1`, local-memory arrays in `b2s` (σ-indexed message words, G-step state) and `sha_words` (message schedule ring), the 64-bit pointer-table loads, and the scratch slot's placement. Host-checked bit for bit against the CPU generators and over the whole stage (§ Device witness). A difference would show up as a tree-0 or tree-1 root (`DIFF root of tree 0/1`).

- **Fold step 1 is unqualified on CUDA**, and so is the packed-leaf FRI layout at fold 1 (`resident_decommit.zig` uses 4 rows per leaf). Only a device run settles it.
- **Reorder kernel, unverified on a device:** nvcc on `starked_reorder_v1_*`, its AOT bind under `native_m31_permutation_trace_v3`, and kernel launches in `.trace_generation` (so far the runtime has run only copies there). Host-checked against `toStorage` and over the whole stage (§ Natural upload).
- **Device LogUp, unverified on a device:** the completion kernels, the source copies, nvcc on the generated kernels (`block_sha` has 1,585 live lookup values in one thread; expect register spills, not errors) and the AOT bind under the borrowed `native_blake_exact_interaction_v1` tag. The slab borrows tree 2's evaluation buffer: correct only while nothing writes it between the completion and tree 2's commit (true in our schedule).
- **Unverified on a device:** the composition kernels, LDE, Merkle, OODS, quotient and FRI kernels are stwo-zig's. Our inputs to them are checked only for shape (plans equal the CPU proof's) and for transcript order, not numerically.
- **Many OODS cohorts:** each extra mask offset of a column is its own cohort (`resident_oods.zig:107`), giving 4,837 samples. That is correct, but launch-heavy; batching by column is an optimisation.
- **Kernel size:** `block_coin` has 162 constants and `block_b2s` 10.9 k instructions. The parametric generator slices programs above 2,048 instructions, so neither is a blocker.
