# GPU step 3: resident CUDA prover for the block system (2026-10-12)

Status: **batch proving (`cuda-epoch`, one CUDA session) byte-identical on an H100, 2^23 tiered in 2.7 s per block (2026-10-15); byte-identical on L40S and H100 up to 2^23 tiered (2026-10-13), with device LogUp (default) and host LogUp (`--host-logup`).** Device witness for `block_sha`, `block_b2s`, `block_msg`, `block_walk`, `block_bytes` and tree 0 (default; `--host-witness` for A/B): validated on H100 (§ Device witness). Parent: [gpu.md](gpu.md), step 3.
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

### Phase 2: `block_msg`, `block_walk`, `block_bytes` (2026-10-15, branch `cuda/batch-witness`)

After phase 1 the host witness at 2^23 was walk (0.70 s on the M4 Pro), msg (0.42 s), fields (0.15 s) and small parts; walk and msg were also 2.8 of the 3.9 GiB still uploaded. Three more generators (`witness.zig`):

| Kernel | Grid | Inputs | Host reference |
|---|---|---|---|
| `msg` | one thread per row; binary search for its message | the block's bytes, 10 words per message (`msg.descriptors`: row, id, flags, tuple, data length, previous data length) | `msg.generate`, `setUses`, `merkle.addHeaderUses` |
| `walk` | one thread per row | the block's bytes, the sigop total and one 16-byte record per walked row (`walk.plan`: position, automaton state, remaining length, running sigops) | `walk.columns` |
| `bytes` | one thread per row | the block's bytes, the reads per position (`bytes.multiplicities`) | `bytes.generate` |

The sigop automaton is sequential per script, so the host keeps that pass (`walk.plan`, a tight loop with no field inversions) and the kernel expands each record into the 51 columns (the next state, the zero tests and their inverses). `walk.generate` is now `plan` + `columns`, and `msg.generate` collects its reads through `appendReads`: the CPU columns are unchanged (golden hashes). With `skip_device_columns`, `buildFull` leaves the three mains empty and keeps `Built.raw`, `msgs`, `walk_recs` and `byte_mults`.

Host checks (`witness_test.zig`): the kernels as host C++ equal the CPU columns of all five generated components for blocks 0 (uniform, tiered), 170, 91812, 91722, 91842, 91880 and 400000 (L 22); flipping a message id, a sigop sum or a byte multiplicity changes the output; `.trace_generation` over block 0's real plans equals the CPU storage order.

M4 Pro, production, tiered, `cuda-prove --skip-cpu` (stops at session open):

| | 400000 (2^22) phase 1 | phase 2 | 970347 (2^23) phase 1 | phase 2 |
|---|---|---|---|---|
| "witness built" lap | 0.79 s | **0.20 s** | 1.55 s | **0.40 s** |
| planned H2D | 2.00 GiB | **0.43 GiB** | 3.99 GiB | **0.85 GiB** |
| peak memory footprint | 2.30 GB | **0.62 GB** | 4.50 GB | **1.12 GB** |

**Device run** (H100 SXM 80 GB, sm_90, 8 vCPUs, 2026-10-15): every `run.sh` step byte-identical to the CPU proof and verified (block 0, four profiles), 400000 and both 2^23 blocks equal to their saved CPU proofs' hashes. Time to proof (runner clock):

| Block | Phase 1 (H100 PCIe, 2026-10-13) | Phase 2 | Host witness | H2D |
|---|---|---|---|---|
| 400000 (2^22) | 5.3 s | **1.95 s** | 0.41 s | 0.43 GiB |
| 970347 (2^23) | 11.0 s | **3.62 s** | 0.95 s | 0.85 GiB |
| 774628 (2^23) | 9.2 s | **3.13 s** | 0.60 s | 0.85 GiB |

Host RSS at 2^23: 10.9 GB (14.2 in phase 1).

## Batch proving: `cuda-epoch` (2026-10-15)

`cuda-epoch` (src/gpu/cuda/epoch.zig) is the GPU twin of `chainproof prove-epoch`: the same inputs (`<dir>/blocks`, `<dir>/undo` with `.ctx`, the headers and the chain proof), the same epoch challenge and the same files (`<dir>/proofs/<h>.sbblock`, `<dir>/set-<to>.bin`). The shared part is `src/block/epoch_run.zig`. One process proves every block of the epoch:

- per process: the AIRs, the AOT catalog, one `cuda.runtime.NativeRuntime` (the CUDA context and the AOT loader with its loaded functions stay open; each proof is a retained transaction, `prover.Input.runtime`), the twiddles per size, and the MMR over the headers folded once (`HT.Paths`);
- per block: the lean witness (five components and tree 0 on the device), the plans, the device proof, the file.

`HT.Paths` records the MMR fold once; each header's inclusion path is then a walk up the tree. Before, `bindWindow` folded all 970k leaves for each of the window's 12 headers, about 1 s per block in both provers. `Paths.proof` equals `inclusionProof` (test).

`--mock` proves on the CPU through the same code: over blocks 0..30 it writes the same bytes as `chainproof prove-epoch` (proofs and coin set), and `chainproof verify-epoch` accepts them. `--heights <file>` is a standalone run over listed blocks under the testing challenge (no coin set; not bound to an epoch): for measurements over a sample of the chain. `scripts/pod/epoch.sh` runs both on a pod.

**Batch proving run** (same pod, 2026-10-15). A retained session's per-proof arena stays reserved in the context's private pool (release threshold max), and the next proof's admission counts only driver-free memory, so on 80 GB a 2^23 proof failed after any large one. Batch proofs therefore use stwo-zig's prepared execution cache (`prepareExecution` + `openPreparedCachedRetained`, keyed on the placement; its admission counts pool-reusable memory and evicts LRU arenas), and `witness.Inputs.fixed_capacity` sizes the inputs slot by the components' log sizes so a size class has one plan.

- **Epoch 0..100**, production: 101 device proofs and the coin set byte-identical to `--mock` (CPU): 0.089 s per block on the device (0.415 s on the pod's CPU); a single `cuda-prove` process took about 0.8 s for such a block.
- **Sample** (`--heights`, 37 blocks: 3 per (L, profile) class from 2^11 to 2^21, 2 at 2^22 and 2^23, drawn from the survey with seed 15; production strength): all 37 verified on the host (`--verify`); the 27 up to 2^19 byte-identical to `--mock`. Mean time per block (witness, plans, device proof, file; one session):

| L (tiered unless noted) | blocks in the chain | s / block | of which device |
|---|---|---|---|
| 11 (uniform) | 86,958 | 0.119 | 0.101 |
| 12 – 16 | 87,898 | 0.092 – 0.118 | 0.077 – 0.098 |
| 17 | 29,309 | 0.142 | 0.114 |
| 18 | 43,593 | 0.177 | 0.140 |
| 19 | 50,045 | 0.261 | 0.199 |
| 20 | 76,633 | 0.412 | 0.308 |
| 21 | 65,919 | 0.747 | 0.537 |
| 22 | 293,931 | 1.413 | 1.030 |
| 23 | 236,765 | 2.661 | 1.938 |

Weighted by the survey (data/chain-sizes.csv), the whole chain's block proofs are about **325 H100-hours** (2^23: 175, 2^22: 115, the rest 35), against about 1,260 before (phase 1, one process per block, small-block times estimated). The GPU is busy about 70 % of the run; the rest is the host witness (0.7 s at 2^23 on these 8 vCPUs) and plans, which overlap nothing yet.

## Aggregation: `cuda-epoch-tree` (2026-10-21)

The epoch's recursion forest (docs/design/block-rec.md § The forest with wide nodes) on stwo-zig's resident
CUDA circuit prover, from `cuda-epoch`'s block proofs; `scripts/pod/prove_tree.sh` builds and runs it and
assembles the forest, and `scripts/pod/node_tree.sh` drives a run from the node. Gotchas:

- the `NativeRuntime` belongs to the thread that opened it; workers queue device proves to that thread;
- pass the circuit's preprocessed root (`Input.expected_preprocessed_root`, from the tree VK): the host
  hash was 3 s per proof;
- go level by level, so consecutive proofs share one circuit size.

Rehearsal: 11,432 proofs in 67 min on an H100 SXM, GPU about 60 % busy (more host workers next).

## Set pass: `cuda-set`, `cuda-set-tree` (2026-10-28, branch `gpu-set`; segments validated on an H200)

The coin-set pass ([set-pass.md](set-pass.md), step 6) on the same two provers: the segment system
(`block/set_seg.zig`, 12 components) on our resident prover, the set tree (`set_leaf_out` leaves,
`set_node_glue` nodes) on stwo-zig's resident circuit prover. Both drivers write exactly the files of
`chainproof prove-set` (`<work>/seg/<i>.sbseg`, `setvk.bin`, `pass.bin`), so `chainproof verify-set`
and `verify-chain --set-proofs` read them unchanged.

**Kernels.** `gpu/cuda_aot/` now holds both systems (`catalog.Product`): 25 constraint kernels (16
block + 9 set; `block_bytes`, `block_tables`, `block_fpwalk` are shared and listed once, with both
placements, because stwo-zig's build rejects a repeated cache key), 24 LogUp kernels (15 + 9), the
reorder and the 7 block witness generators. Manifest component indices are global, system-major (block
0–15, set 16–27); the Cairo parametric scheme does not bound them. `catalog.json` names the system.
The block entries' kernels and cache keys did not change (the diff only adds entries and the three
shared placements). `cuda-archive-plan`: 105 AOT sources (48 native + 57). After any change to the set
AIRs (Lean export), regenerate: `STARKED_CUDA_AOT_WRITE=1 zig build cuda-test -Dcuda=true
-Doptimize=ReleaseFast -Dtest-filter="drift check"`, then run the drift check without the variable.

**`cuda-set`** (`src/gpu/cuda/set.zig`, linked like `cuda-epoch`): cuts the file at `--logs` as
`provePass`, chains every segment's incoming state without witnesses (`set_seg.advance`, checked
against each witness's outgoing state), then `--jobs` workers build witnesses, plans and host trees while
the main thread proves (one runtime, the prepared-arena cache: one size for the whole pass). Host
witnesses only (`prover.Input.witness = null`): tree 0 and every main column are uploaded. The challenge
is a file (`chainproof set-challenge <epoch> <ch.bin>`, `set_tree.encodeChallenge`), copied to
`<work>/challenge.bin`. Options: `--cpu-check n` (CPU proof of the first and every n-th segment, byte
comparison; a mismatch keeps the device file as `.gpu` and stops), `--verify`, `--first n`, `--only
<list>`, `--mock` (CPU proofs through the same pipeline), `--stages` (per segment: H2D bytes and each device stage's time), `--host-only` (witness and plans only: host time
and memory). Existing segment files are skipped (resume).

**`cuda-set-tree`** (`src/gpu/cuda/set_tree_gpu.zig`, linked like `cuda-epoch-tree`; the shared GPU
part moved to `circuit_gpu.zig`): `setup` from segment 0 (`setvk.bin`, refused if one with other
contents is there), then `set_tree.tasks` level by level (leaves, then nodes by height; one padded
shape for all), one file per proof `<work>/stree/<lo>-<n>.sbproof` (resume), every proof checked against
the VK identity, verified natively and its digest compared with the native summary; `--cpu-check n`,
`--cpu-prover`. Then `pass.bin` (final state = the last segment's outgoing state, `set_tree.outState`)
and `verifyPass` under `<work>/challenge.bin` (or `--challenge`).

**Byte identity.** The device proof must equal `set_tree.proveSeg`'s (the CPU prover, `.compact`
storage: same bytes as the default). On the pod, `cuda-set --cpu-check 1 --first 1 --verify`
(`prove_set.sh check`) proves segment 0 both ways and compares the encoded files; full runs keep
`--cpu-check 500`. The tree side is `cuda-epoch-tree`'s, already byte-identical on an H100.

**Device memory** (`set_test.zig`, planned and bound on the host, production FRI; `set_mt` with 329 main columns):

| Logs (bytes, tables, pend, rec, fpwalk, b2w, b2c, tmsg, shac, lw, lc, mt) | Arena (device LogUp) | Host trees = H2D | Fits |
|---|---|---|---|
| production `23,8,6,16,22,21,23,23,23,22,23,23` | **152.9 GiB** | 43.0 GiB | B200 (180 GB) only; not H200 (141 GB) |
| halved `22,8,6,15,21,20,22,22,22,21,22,22` | 76.4 GiB | 21.5 GiB | H100 NVL 94 GB, H200; H100 80 GB (79.6 GiB) only just |
| quartered `21,8,6,14,20,19,21,21,21,20,21,21` | 38.2 GiB | 10.7 GiB | any 48 GB+ device |

The trees are 96 % of it (coefficients, two evaluation copies, Merkle). Halving the logs about doubles
the segment count (production: ~2,330 per set, [set-pass.md](set-pass.md) step 6; halved ~4,650,
quartered ~9,300, *est.*) and the tree's leaves, not the rows. `chainproof`'s `default_set_logs` is
unchanged (provisional); the runs pass `--logs` explicitly, and `prove-set`, `set-cut` and the VK take
the same list.

**Host checks** (`zig build cuda-test -Dcuda=true`; this Mac, no nvcc):
- the 12 set constraint kernels, built as host C++, equal the interpreter (logs 6 and 9, random traces
  and statements); invariance of the normal form over logs 8/12/22 and statements;
- a CPU proof of segment 0 of `set-170` (test logs `10,8,6,6,10,8,11,10,11,10,12,13`): the resident
  plans reproduce its shape (323/1,363/376/8 columns, 4,653 OODS samples, 13 FRI layers, 7,082
  constraints), the host channel and the device-sink model every challenge (3,012 statement mixes);
- its 12 LogUp kernels (host C++) and the completion model equal `system.interactionTrace` (376 tree-2
  columns, 12 claims); the host trees borrow the witness columns;
- the three arenas above plan and bind; drift check; `cuda-archive-plan` (stwo-zig's validator) accepts
  the 105-source selection; `cuda-check` links the device schedule.
- **Plumbing** (`scripts/test_cuda_set_mock.sh`, stub-linked binaries): `cuda-set --mock` +
  `cuda-set-tree --cpu-prover` write the same segment files, `setvk.bin` and `pass.bin` as `chainproof
  prove-set` (test chain, set after 8, epoch 4..8), `verify-set` accepts; set-170 under the testing
  challenge (25 segments, 49 tree proofs) verifies, and a run with a segment and a node removed resumes
  to the same `pass.bin`.

**Only a GPU settles:** nvcc on the 18 new kernels (`set_b2c`, `set_lc`, `set_mt` have 2,000–2,300
constraints each; expect register spills), their AOT bind, the device run at the set's shapes (masks up
to 10 offsets, −88…0), byte identity, the real arena peak and the times below.

**Time** (*est.*, from the block runs: device time ∝ arena; cuda-epoch 2^23 tiered, 51.2 GiB arena,
1.94 s on the device): ~5.8 s (production), ~2.9 s (halved), ~1.4 s (quartered) per segment, i.e. about
**3.7 H100-hours of device time per set** whatever the logs. The set's constraints are denser than the
block's (`set_b2c`/`set_lc`/`set_mt`), so composition may add to it. The tree: ~0.35–0.5 s per proof
(the block forest's 11,432 proofs in 67 min), ~1 h per set at halved logs. **The host witness is the
bottleneck:** it is single-threaded, ~10 s for one quartered segment on the M4 Pro (the padded `set-1000`
file, a lower bound; a loaded machine), so roughly 20 s halved and 40 s production, and 2–4× that on pod
cores; at ~30 GB of host memory per halved job, a 250 GB pod runs ~6–8 jobs, i.e. ~5–15 s per segment of
host time against ~3 s of device time. Levers: device witness generators for `set_b2c`/`set_lc`/`set_mt`
(Blake2s, as `block_b2s`) and `set_shac` (as `block_sha`), the bulk of the columns; or more pods' CPUs.

### Measured on an H200 (2026-10-28)

RunPod H200 SXM (secure, $5.29/h, 12 vCPU, 251 GB host), pod `73uw67ne4o1ed4`, ~1 h. Logs, the check
log and the 40 segment files are in `data/gpu-set-20261028/` on the Mac.

- **Build** (`prove_set.sh build`, `sm_90`): 18 min. nvcc took every new kernel.
- **Byte identity**: segment 0 of the set after 935,000 at halved logs: the device proof equals the CPU
  proof byte for byte and verifies (`SET CHECK OK`; the CPU proof took ~8 min and 93 GB RSS).
- **Throughput** (`cuda-set --first 40 --jobs 6`, an 8M-coin prefix of the same set, halved logs):
  **12.7 s per segment** wall clock; device 10.7 s per segment on average (6.3–18.4 s), host witness 29–42 s
  per job (six jobs keep up); peak device memory 79.1 GB, peak host RSS 137 GB; proofs ~1.22 MB each.
  The device time is ~4× the estimate above, so the GPU, not the host, bounds the pass.
- **A whole set** at halved logs: ~23,460 coins per segment, so ~7,000 segments for the 164M-coin sets,
  ~25 h of segments plus ~1.5 h of tree (*est.*), about $135 per set at $5.29/h.

Not yet run on a GPU: `cuda-set-tree` and a whole pass.

### Runbook (pod)

Image, bootstrap and `env.sh` as in § Running on a pod; the branch is not pushed, so ship a tarball.

```sh
# On the Mac (or the node): the source, and each pass's challenge (needs the epoch's forestk-<to>.bin
# and set files: run where they are).
scripts/pod/bundle.sh /tmp/sb-gpuset.tar.gz
zig-out/bin/chainproof set-challenge <dir>:945000:935001:<set-935000.bin> ch-945000.bin   # 935,000's pass under epoch 935,001..945,000
# copy the tarball, the challenge files and the set files to the pod ($DATA, container disk)

# On the pod:
NO_BUILD=1 bash scripts/pod/bootstrap.sh --tarball /root/sb-gpuset.tar.gz
cd /root/starked-bitcoin
CUDA_ARCH=sm_90 scripts/pod/prove_set.sh build           # cuda-set (our archive), cuda-set-tree (circuit archive), chainproof

# 1. One segment, device vs CPU, byte-identical and verified (stops on a mismatch):
L=22,8,6,15,21,20,22,22,22,21,22,22                      # halved: H100 NVL / H200 (80 GB H100: quartered, L=21,8,6,14,20,19,21,21,21,20,21,21)
scripts/pod/prove_set.sh check $DATA/set-935000.bin $DATA/ch-945000.bin $L
#    the CPU proof of a halved segment takes minutes and tens of GB (block 2^23: 394 s, ~90 GB RSS).
#    expect "segment 0: CPU proof byte-identical" and "== SET CHECK OK"; on a DIFF compare the files
#    (seg/0.sbseg vs seg/0.sbseg.gpu) and use cuda-prove's stage diff approach to localise.

# 2. A whole pass (segments, then tree and pass.bin, verified), detached and resumable:
nohup scripts/pod/prove_set.sh run s935000 $DATA/set-935000.bin $DATA/ch-945000.bin $L --jobs 6 > /dev/null 2>&1 &
tail -f $WORK/logs/s935000.seg.log                       # one line per segment; then s935000.tree.log
cat $WORK/logs/s935000.status                            # START / END, counts, VERIFIED line

# 3. Off the pod: $WORK/s935000/{setvk.bin,pass.bin} (and seg/ for membership proofs), then on the Mac
#    chainproof verify-set <work-dir> <dir>:945000:935001:<set-935000.bin> --unpinned
```

Before the full run, a few hundred segments (`cuda-set ... --first 300`) give the real per-segment host
and device times and the jobs count that keeps the GPU busy (`--host-only` measures the host alone).

## Public inputs

The CPU path bakes public inputs into the program as literals. Our lowering deduplicates equal constants (`stwzeva.ProgramBuilder.constant`), so the program shape depends on the values. New `PubMode.slots`: one `constant` instruction per public input, never shared. stwo-zig's parametric normaliser (`cairo_cuda/parametric_eval.zig:18`) turns every base literal into a session constant and erases the domain size. The kernel then depends on the AIR only: one kernel per AIR, for every statement and log size. The statement reaches the kernel through `args->base_params`, exactly as the circuit binds its literals (`resident_composition.zig`, `writeConstants`). Base `param`s (`lowerTemplate`) are not needed: the parametric path rejects them (`parametric_eval.zig:20`).

## AOT catalog

- `gpu/cuda_aot/`: 16 block kernels (3.2 MiB of CUDA; 25 constraint kernels with the set system's, § Set pass) and an `aot_manifest.json` in stwo-zig's product-set format.
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

**First rehearsal: 935,001–945,000** (2026-10-19; 10,000 blocks after Core's last assumeUTXO height).
- H100 SXM, `main` at f876665: the load ran out of host memory (244 GB of a 251 GB limit) before
  proving; fixed by bounded host memory (docs/design/block-data.md). A partial run (935,001–937,000)
  stopped at block 936,186: `InsufficientDeviceMemory`, one of 6 blocks in this epoch that need ~98 GiB.
- Split run, `main` at 9afd51e (the load now ~27 GB of host memory, 9 min):
  - H200 SXM, `--only` the 6 blocks: all L 22 uniform, 27 s each with `--verify` (witness 12 s, device
    4 s); peak device memory 99 GiB; all 6 accepted by `chainproof verify-block`. Its `set-945000.bin`
    equals `replay`'s (sha256 `881f50c5…`).
  - H100 SXM, `--skip` the 6: 2.45 s per block over 4,476 blocks (935,001–939,478); no block deferred.
    RunPod stopped and removed the container at 18:16 UTC ("container is unhealthy: dead"); the
    proofs copied to the Mac until 16:53 survive. Hence `prove_epoch.sh` / `follow.sh` below.
- Cost: $31.28 (H100 $8.48 and $19.41, H200 $3.40).

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
- An epoch run (2026-10-20, after the first rehearsal):
  - `env.sh` puts Zig (`$ZIG_DIR`), the source (`$SRC`) and the inputs (`$DATA`) on the container disk, at
    `/root`; `/workspace` can be NFS, which refuses `chown` and is slow for many small files. Outputs and
    logs go to `/workspace`. `-Dcuda-jobs` follows the cgroup quota (`cpu.max`), not `nproc`.
  - `xfer_epoch.sh <from> <to> <set-dir> <blocks-dir> <chain>` (on the Mac, `NODE_SSH`, `POD_SSH`): the
    previous set and the blocks with undo and ctx, node → Mac → pod in four zstd streams, then every
    file's sha256 against the node's. Nothing is written on the node.
  - `prove_epoch.sh <name> <from> <to> [--skip f | --only f]` (on the pod, under `nohup`): `cuda-epoch`
    with `--resume`, so a relaunch proves only the missing blocks. Proofs, the final set and the logs
    go to `/workspace/<name>` and `/workspace/logs`.
  - `follow.sh <name> <local-dir>` (on the Mac, `POD_SSH`): every 5 min copies the new proofs and logs
    off the pod. It exits 0 at the run's END, 3 when the pod misses two checks, 4 when `cuda-epoch` is
    gone without END, with a desktop notification. The persistent volume survives a container restart,
    not a host failure; the copies on the Mac survive both.

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

### Device witness run (H100 PCIe 80 GB, sm_90, 16 vCPUs, 2026-10-13 night)

All steps byte-identical and verified (block 0 ×4, 400000, A/B host witness, A/B host LogUp, 970347 + A/B, 774628). Time to proof (runner clock; `verifyExt` afterwards is optional):

| Block | Device witness | Host witness (A/B, same pod) | H2D | Host RSS |
|---|---|---|---|---|
| 400000 (2^22) | **5.3 s** (witness 3.2, device 2.0: ingress 0.30, trace generation 0.027) | 12.7 s | 2.00 GiB (6.46) | 7.2 GB (12.0) |
| 970347 (2^23) | **11.0 s** (witness 6.0, device 4.9: ingress 2.05, trace generation 0.085) | 32.2 s | 3.99 GiB (12.92) | 14.2 GB (23.7) |
| 774628 (2^23) | **9.2 s** (witness 5.6, device 3.5: ingress 0.70) | — | 3.99 GiB | 14.2 GB |

The host witness for the remaining components (fields, msg, walk, coin, …) is now the largest step (3–6 s). Ingress still varies run to run (0.7–2.1 s for the same 4 GiB). The optional self-check (`verifyExt`) takes 4.5 s / 17 s.

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
