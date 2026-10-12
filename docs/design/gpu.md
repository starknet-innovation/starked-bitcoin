# GPU proving: scope (2026-10-12)

Status: scoped; **step 1 (IR → STWZEVA, CPU parity) done**, see [Step 1 results](#step-1-results-2026-10-12);
**step 2 (Metal) done**, see [Step 2 results](#step-2-results-2026-10-12). Read from the vendored stwo-zig source (`third_party/stwo-zig`,
4afa09dbf), not its READMEs. Owner's direction: no CPU cloud spend now; scope the GPU route.

## What stwo-zig has

- **CUDA** (`src/backends/cuda`): a *resident* backend. A proof session owns device memory, kernels come
  from an authenticated ahead-of-time registry, and there is no CPU fallback. It is **not** a host-slice
  backend: `ProverEngine(CudaBackend)` (our `prove_rec.Engine`) cannot work.
  - Device kernels exist for every stage: LDE, Blake2s Merkle, transcript, LogUp batch-inverse/scan, OODS,
    DEEP quotients, FRI fold, PoW grind, decommit.
  - End-to-end integrations exist for native examples, Cairo (H200), and the recursion circuit
    (`integrations/circuit_cuda`, H100/H200).
  - `circuit_cuda` uses **our exact profile**: `proving_5a7c5ed`, Blake2sM31 channel, plain Blake2s Merkle,
    `PcsConfigV2`, lifted trees, `StarkProof(Plain)`. Its proofs are byte-identical to CPU ones, so our
    verifier, leaves and Lean statements would be unchanged.
  - Only fold step 4 with blowup 1 is qualified; we use fold step 1.
  - Linux and nvcc only (cubins); qualified on H100 SXM and H200. The products are staged and unreleased,
    pending requalification.
- **No generic AIR frontend on CUDA.** Constraints reach the GPU as hand-written kernels or as code
  generated from **STWZEVA/1** bytecode (`frontends/cairo/witness/eval_program.zig`).
  - STWZEVA has trace and preprocessed columns at row offsets, params, consts, field ops, extension ops
    and prefinalized LogUp.
  - `integrations/cairo_cuda/eval_codegen.zig` compiles it to CUDA, and the C and Metal generators also
    consume it.
  - `frontend_contract.zig` is an admission receipt, not a plug-in.
- **Metal** (`src/backends/metal`): `MetalCommitBackend` plugs into the generic `ProverEngine`.
  - LDE, Merkle, quotients, FRI and PoW run on the device; composition stays on the host unless a device
    stage is injected.
  - `integrations/circuit_metal` does that with a STWZEVA bundle and gives CPU-identical proofs.
  - It needs a pinned metallib minted with Xcode.

## Plan, if we go ahead

1. **IR → STWZEVA** (1–2 weeks): lower our Lean-exported JSON AIRs, including their LogUp layout, to
   STWZEVA. Check them with stwo-zig's CPU evaluator and C codegen; the CPU proofs must be byte-identical
   to today's.
2. **Metal composition** (~1 week): the `circuit_metal` pattern on an Apple Silicon Mac. Gives real
   speedups and shows where time goes, at no hardware cost.
3. **CUDA** (4–8 weeks plus H100/H200 time): generalise `circuit_cuda`'s resident pipeline (geometry,
   memory plan, witness ingress from host columns, interaction/LogUp kernels, composition controller,
   transcript, decode) from the 11 recursion components to any STWZEVA program. Add an AOT catalog and a
   `product_sets.json` entry, and CPU parity tests.

## Risks

- **Memory:** the main-tree LDE of ~1,200 columns at 2^24 rows is about 160 GB, more than an H200, so
  2^24 needs streaming or partial residency. Sizes 2^22–2^23 (most real blocks; the 4 MB sample is 2^23)
  look feasible: circuit_cuda planned 28 GB at 2^23.
- **Fold step 1** is unqualified on CUDA.
- **Kernel churn:** strict AOT pinning means every AIR change (e.g. `block_anc`) regenerates and re-pins
  kernels.
- **LogUp mapping:** confirmed (step 1): our pairs-of-lookups layout is STWZEVA's prefinalized layout.
- **Product status:** the CUDA products are staged, not released.
- The recursion leaves (8.3 M-variable circuits) are probably as costly as the block proofs and are
  already a `circuit_cuda`-shaped workload.

## Step 1 results (2026-10-12)

`src/air/stwzeva.zig` lowers an `ir.Air` and its lookups to a stwo-zig `composition_bundle.Component`
(one STWZEVA/1 program part). stwo-zig's `Program.parse` and `Bundle.parse` re-read every program and bundle,
checking the semantic hash and validating them. Nothing in `third_party/stwo-zig` was changed: our build
imports its Cairo frontend, C generator and Metal code generator by path.

### Evidence

All commands use `-Doptimize=ReleaseFast`.

| Check | Command | Result |
|---|---|---|
| (a) Composition parity, random traces and OODS points | `zig build test -Dtest-filter="stwzeva"` | header_chain, byte_table/user, block_reader and all 16 block AIRs: our interpreter equals stwo-zig's SIMD STWZEVA interpreter on the domain, and our STWZEVA point evaluator at the OODS point. stwo-zig's `RuntimeComponent` also agrees, except on block_coin (see gaps). |
| (a′) C code generator | same filter | stwo-zig's `bundle_main` turns `testdata/stwzeva/pubfree.bin` (7 AIRs without public inputs) into C at build time. The kernels equal the interpreter at logs 6 and 10. |
| (b) Byte-identical proofs | `zig build test -Dtest-filter="byte-identical"` | `system.proveWith(.stwzeva)` and `.stwzeva_native` give the same postcard bytes as `.interpreter`, and our verifier accepts them: **block_anc** at log 12 under the production profile (70 queries, PoW 26, blowup 1, fold 1; 175,953 B); the **byte LogUp system**; the **16-component block system on block 0** (log 11; 121,814 B). |
| Metal kernels on this Mac | `zig build metal-parity` (`METAL_PARITY_LOG=14` optional) | For header_chain and all 16 block AIRs, `cairo_metal/eval_codegen` generates MSL, the Metal runtime compiles it from source and dispatches it, and the result equals the interpreter. At log 14: header_chain 13.6 ms GPU vs 93 ms CPU interpreter; b2s 17.9 vs 79 ms. The first MSL compile takes up to 7.7 s (header_chain), then the OS shader cache serves it. |

A mutation (one sign in the lowering) makes both the parity test and the proof test fail.

### Mapping

| IR | STWZEVA |
|---|---|
| `col{main,i,off}` | `trace_col`, interaction 1, `a=i` local to the component's tree-1 span, `imm=off` |
| `col{pre,i,0}` | `trace_col`, interaction 0, `a=i`; `preprocessed_indices[i]` = global column |
| `const c`, `pub k` | base `constant` (public inputs become literals) |
| add/sub/mul/neg | base add/sub/mul/neg |
| constraint root | ext `secure_col(r,0,0,0)`, in IR order, then the LogUp batches |
| lookup tuple `(rel, vals)` | `const(rel) + Σ secure_col(vᵢ)·param(αⁱ⁺¹) − param(z)` |

- **Header:** flags `prefinalized_logup`; caps `ext_mul|prefinalized_logup`; `n_interactions=3`; `n_base_params=0`; `domain_log_size=reserved[0]=log`.
- **Bundle component:** `evaluation_log = log+1`. Denominators are `denominatorInverses(log, log+1)`. Spans are `{1: main}` and `{2: interaction}`; the interaction span is empty without lookups.
- **Mask:** stwo-zig derives a component's mask from the first appearance of each (column, offset) read. The lowering therefore reads every column once, in a prologue, in our mask order: main offsets ascending; on the interaction tree, −1 then 0.
- **Evaluator:** the composition is evaluated by stwo-zig. The mask geometry stays ours (`component.zig`).

### LogUp layout

- **"Prefinalized" is plain ext arithmetic.** It means the program reads interaction columns the host has already built and constrains them. STWZEVA has no LogUp opcode. Generating the interaction trace is outside STWZEVA.
- **Same scheme as stwo.** Our scheme (pairs, `logupConstraintValues`) is stwo's `finalize_logup_in_pairs`, which the Rust recorder emits (`tools/stwo-eval-program-abi/src/recording.rs`):
  - batch k < B−1: `(S_k − S_{k−1})·D − N`;
  - last batch: `(S_last − S_last[−1] − S_{B−2} + claimed_sum/2^log)·D − N`.
- **Ext params:** `[lookup_z, lookup_alpha_power 1..w, claimed_sum_scaled]`, resolved by `RuntimeComponent.extensionParameters`.
- **Composition:** `Σᵢ ext[rootᵢ]·rc[rc_base+i]`, then multiplied by `denominator_inverses[row >> log]`.
  - The `rc` are the accumulator's powers reversed (`orderedCoefficients`), so constraint i gets `α^(n−1−i)`: our order.
  - The OODS side is Horner `acc·α + c/Z(p)`.

### Gaps (no STWZEVA equivalent, or not yet handled)

1. **Public inputs.** STWZEVA has a base `param` opcode, but every consumer rejects it: the SIMD/C evaluators, the C writer and `RuntimeComponent` all require `n_base_params=0`. Literals therefore make one program per statement.
   - CUDA: the parametric normaliser (`circuit_cuda/air_aot.zig`) passes every base literal as a session constant, so this is fine.
   - C and Metal AOT: we need a kernel per statement, a parametric C/MSL path, or public inputs as `ExtSource.constant` (which costs QM31 arithmetic).
2. **Unread main columns (block_coin has 4).** Our proof gives them no sample. stwo-zig's program-derived mask geometry (`resident_geometry.componentOffsets`) rejects a span column that is never read. That geometry feeds `RuntimeComponent`, `sampleShape` and the resident CUDA/Metal pipelines. The proofs above still work only because our wrapper keeps our `maskPoints`.
   - Fix in Lean (drop the columns), or accept a proof-shape change (dummy reads).
3. **Preprocessed reads at offset ≠ 0:** unsupported, as in `component.zig`; no AIR uses them.
4. **Mixed sizes and lifting:** STWZEVA supports them (per-component `trace_log_size`, lifted reads); our system and mask do not yet.
5. **One part per component.** The largest programs are header_chain (15k instructions) and b2s (10.9k). Metal's device stage fuses and splits at 512–4096 instructions; we could emit several parts (`rc_base`), which the format already supports.

### What steps 2 and 3 need

- **Metal (step 2).**
  - `circuit_metal`'s device stage (`cairo_metal/composition_stage.zig`) loads kernels only from a metallib file whose digest it checks. The diagnostic `device()` accepts a pinned digest via `STWO_ZIG_COMPOSITION_METALLIB(_SHA256)`.
  - Producing that metallib needs the `stored_domain`/`bounded` MSL from `tools/cairo_metal_codegen/eval_source` and Xcode's `metal`/`metallib`. This Mac has only CommandLineTools: `xcrun --find metal` fails.
  - Alternative without Xcode: our own `device_stage.Device` that compiles MSL at runtime, as `metal-parity` does.
  - Either way, `system.prove` must pass `composition_stage` to `Engine.prove`, and run under `MetalCommitBackend`.
  - On-device interaction-trace generation is a separate piece.
- **CUDA (step 3).**
  - Feed `circuit_cuda`'s resident pipeline our bundle, generalised from the 11 circuit components (geometry, memory plan, ingress, composition controller).
  - Write a generic LogUp interaction kernel from the IR lookups (circuit's `resident_interaction` is circuit-specific).
  - Resolve gap 2 (unread columns) and gap 5 (part splitting).
  - Add the AOT catalog / `product_sets.json` entry and qualify fold step 1.

### Revised effort

| Step | Estimate |
|---|---|
| Step 1 | Done (≈1 day, not 1–2 weeks) |
| Step 2 (Metal composition in real proofs) | ≈1 week with a runtime-compiled `Device`; a few more days for the pinned-metallib route, which needs Xcode |
| Step 3 (CUDA) | 4–6 weeks plus H100/H200 time. The lowering risk is retired; the remainder is the resident pipeline and interaction kernels |

## Step 2 results (2026-10-12)

Whole block-system proofs now run on `rec.Engine(MetalCommitBackend)`, with composition on the device as well. They are **byte-identical** to the CPU proof and verify. No Xcode is needed.

### How it works

- **Device stage.** `src/gpu/metal_composition.zig` implements stwo-zig's `device_stage.Device`.
  - Kernels: generated by stwo-zig's `cairo_metal/eval_codegen` (eval-domain ABI) from the lowered programs, compiled at runtime (`Runtime.compileEvalLibrary`).
  - stwo-zig's `device_stage.Bound` keeps the accumulator protocol and evaluates any declined component on the host.
  - Each evaluation copies the component's committed columns into one reused resident arena, dispatches, and stores or adds the four coordinate planes.
- **Entry point.** `system.proveOpts(E, …, .{ .composition = .stwzeva, .device = mc.device(&parts) })`.
- **Compile cost.**
  - The first-ever pipeline build for the 16 block kernels took 75 s on this Mac.
  - After that, the stwo-zig runtime's MTLBinaryArchive disk cache (`~/Library/Caches`, `STWO_ZIG_METAL_CACHE_DIR`) and the OS shader cache bring it to 66–131 ms per process. Kernels are then cached in-process.
- **Public inputs (gap 1).**
  - Each AIR is lowered a second time as a template (`stwzeva.lowerTemplate`): public input k becomes base `param` k, which the Metal code generator reads from `args.base_params`.
  - So there is one kernel per AIR, compiled once; each proof only writes its public inputs into the arena. Measured: 16 compiles, then 0 new kernels for the next five blocks.
  - The host and CPU paths keep literal programs, because stwo-zig's CPU evaluators reject base params. Both compute the same field values, so the bytes are identical.
- **Program splitting (gap 5).** Not needed on Metal: the 15k-instruction header_chain and b2s kernels compile and run as single kernels.
- **Host-side speedup.** LogUp fraction generation (`system.fractions`) now runs multi-threaded: 2.2 s → 0.1 s at log 16. Before this, it was 72 % of the Metal proof.

### Evidence

Command: `zig build metal-prove -Doptimize=ReleaseFast` (production profile: 70 queries, PoW 26, blowup 1, fold 1).

- All six `checks.samples_small` blocks: CPU, Metal with host composition, and Metal with device composition give identical proof bytes.
- All 16 components run on the device, with no fallbacks; `verifyExt` accepts the proofs.

Per-mode runs (`METAL_PROVE_ONLY=cpu|metal`) are separate processes, so peak RSS is per mode. Block 170 is padded with `Opts.min_log`; production profile; proof hashes are equal across modes:

| log | CPU | Metal (device composition) | Peak RSS (CPU / Metal) |
|---|---|---|---|
| 12 (real size) | 3.7 s | 0.14 s | 0.36 GB (one process for both) |
| 14 | 7.95 s | 0.36 s | 0.63 / 0.96 GB |
| 16 | 6.3 s | 1.31 s | 2.2 / 3.4 GB |
| 17 | 9.5 s | 2.54 s | 4.3 / 6.1 GB |

- **PoW dominates the CPU column.** The CPU times include a 2²⁶ PoW grind on the CPU, which varies by seconds between runs. With PoW 10 at log 16 the times are 3.85 s (CPU) vs 1.31 s (Metal).
- **Metal phases at log 16:** main commit 0.39 s (including host storage conversion), interaction 0.1 + 0.07 s, STARK 0.27–0.44 s. The GPU composition itself is about 15–25 ms.
- **Memory:** the Metal path uses about 1.4× the CPU's memory, from the arena copies and resident trees.
- **samples_large (log 22) not run.** Peak RSS roughly doubles per log, which puts log 22 near 140 GB (CPU) and 190 GB (Metal). That is far beyond the ~12 GB budget, and beyond this machine.

### Recursion leaf (scoped, not run)

- **The swap is small.** `circuit_metal.Internal.prove` has the same signature as the `circuit_cpu.Internal.prove` that `leaf.proveCircuit` calls. Its device stage loads the in-tree, manifest-approved `vectors/circuit/official/circuit_air_composition_bounded.metallib`, so no Xcode is needed. Wiring takes two build dependencies (`stwo_circuit_metal_integration`, `stwo_cairo_metal_integration`) and one call site.
- **Not run: memory.** Block leaves are about 2²³-row circuits; the epoch run peaked at 40.7 GB, and the header leaf at 13.3 GB. That is over the shared-machine budget.

### Remaining gaps

- **Host-side work:** the interaction trace is built on the host; witness generation and main-column storage conversion are host-side too.
- **Copies:** the arena copy of each component's columns. A zero-copy binding of the committed buffers would remove it and the extra memory.
- **Template program trust:** the template program (public inputs as base params) is checked only through proof byte-identity. A direct template-vs-literal parity test is cheap to add.
- **Mixed sizes and lifting** are still unsupported.

### Step 3 (CUDA) notes, updated

- **Public inputs:** the template program (base params) is the natural CUDA input too. Alternatively, use the parametric literal normaliser.
- **Composition:** the device-stage pattern above maps directly onto `circuit_cuda`'s resident composition controller.
- **Biggest remaining items:**
  - a resident interaction kernel (fractions, then batch-inverse/prefix sum; CUDA already has LogUp batch-inverse/scan kernels);
  - device-side witness ingress;
  - memory: log 22 needs streaming or partial residency even on an H200.
- **Estimate:** unchanged, 4–6 weeks plus H100/H200 time.

## Memory (2026-10-12)

**Question:** where does a block proof's peak memory go, and what does it take to prove real blocks (traces of 2^21–2^24 rows)?

**How it was measured:**
- **Input:** block 170, padded with `Opts.min_log`; production profile; `zig build metal-prove` with `METAL_PROVE_ONLY`, so each prover runs in its own process.
- **Metric:** peak physical footprint, sampled every 5 ms. Phase markers come from `STWO_HOST_MEMORY_PROFILE=1`: ours in `system.proveOpts`, plus stwo-zig's own `core.*` and `pcs.*` stages.
- **Metal device memory:** Metal allocations are read from `MTLDevice.currentAllocatedSize`. A 1 GiB shared buffer that the CPU touches counts in both the footprint and the device allocations (tested). The true Metal total therefore lies between max(footprint, device) and their sum.
- **`maxrss` is not the metric.** Pages released with `MADV_FREE_REUSABLE` stay in `maxrss` until reclaimed, so `maxrss` overstates.

### Where it goes (measured)

Unit: one column at trace size, c = 4 B × 2^L. The block system has P = 225 preprocessed, M = 1,210 main and I = 444 interaction columns, 1,879 in total. Before the fixes, CPU at log 17 (c = 0.52 MB):

| Phase | Δ footprint | What it is |
|---|---|---|
| Witness built | 693 MB | M natural-order columns (634 MB) plus about 60 MB of generator intermediates |
| Preprocessed commit | +527 MB | Natural plus storage-order copies, coefficients plus 2× blown-up evaluations, Merkle tree (≈4.5 P) |
| Main storage order | +600 MB | A bit-reversed copy of the whole witness (M) |
| Main commit | +1,324 MB | Blown-up evaluations (2 M); the storage copy becomes the coefficients in place; Merkle layers (~2 %) |
| Interaction trace | +797 MB | Every component's fractions at once (32 B per batch-row = 2 c per interaction column), I columns, preprocessed regenerated |
| Interaction commit | +515 MB | 2 I evaluations plus tree |
| STARK | +50 MB | Composition (a QM31 at 2^(L+1)), its split, OODS/DEEP quotients, FRI layers: all small next to the trees |

- **Arena retention:** everything was kept until the end, because the prover allocated from the caller's arena.
- **CPU total:** ≈ 8.6 k c.
- **Metal before the fixes:** 7.3 GB footprint at log 17. Composition grew it by 3 GB, because every component's evaluations were copied into the arena and its shared pages were touched; that arena also kept all of stwo-zig's scratch.

### Fixes (in our code, byte-identical; `8fbfe3c`, `7245652`)

1. **`system.proveOpts` frees as it goes.** It works with a freeing thread-safe allocator (`smp_allocator`) and frees every intermediate when it dies. stwo-zig's composition, quotient and FRI scratch is released too. The proof is deep-copied into the caller's allocator.
2. **Fractions one component at a time,** evaluating only the expressions the lookups read.
3. **`Options.discard_mains`** (madvise) frees the witness in two steps: the 697 columns no lookup reads after storage conversion, the rest after each component's fractions.
4. **`Options.storage`** selects stwo-zig's existing commitment storage: `default` (coefficients + evaluations), `evaluations_only`, or `compact` (coefficients only, streaming commit, re-extended on demand). `component.zig` now reads coefficient-only columns.
5. **Metal:** the composition arena is freed when the stage closes.

Tests assert that every storage × composition mode gives identical bytes. All runs below had the same proof hash in every mode.

### Peak footprint after the fixes (measured, MB; Metal shows footprint / device)

| log | CPU default | CPU evals-only | CPU compact | Metal default | Metal compact |
|---|---|---|---|---|---|
| 15 | 785 (was 1,177) | 560 | 413 | 1,344 / 808 (was 2,576 footprint) | 1,171 / 320 |
| 16 | 1,517 (was 2,289) | 1,065 | 770 | 1,934 / 1,379 | 1,595 / 403 |
| 17 | 2,976 (was 4,507) | 2,072 | 1,482 | 3,174 / 2,679 (was 7,343) | 2,439 / 549 |
| 18 | 5,903 | 4,090 | 2,907 | 5,479 / 5,341 | 4,129 / 834 |

**Time at log 18:**
- CPU: compact 20.4 s vs default 19.8 s (similar).
- Metal: compact 8.9 s vs default 6.4 s. Under compact, the device stage re-extends columns on the host; a device-side expansion executor would remove that.

### Model, and projection to the real 16-component system

Peak ≈ k × 4 B × 2^L, where k counts column-copies alive at the peak. The fitted k matches the structure:

| Mode | k | Structure |
|---|---|---|
| Original | ≈ 8.6 k | (M witness + 3 M + 4.5 P + 2 I fractions + 3 I) |
| Default | ≈ 5.6 k | 3(P+M+I) |
| Evaluations-only | ≈ 3.9 k | 2(P+M+I) + witness overlap |
| Compact | ≈ 2.75 k | Witness M + storage M + P, at main commit |
| Metal default | ≈ 5.2 k footprint + 5.1 k device | Upper bound, double-counting shared pages |

Projected peak (modelled, dense data):

| L | Original | Default | Evals-only | Compact | Compact + (a1) | + lifting (c1, rough) |
|---|---|---|---|---|---|---|
| 21 | 72 GB | 47 GB | 33 GB | 23 GB | 18 GB | ~6–9 GB |
| 22 | 144 GB | 94 GB | 65 GB | 46 GB | 35 GB | ~12–18 GB |
| 23 | 289 GB | 188 GB | 131 GB | 92 GB | 70 GB | ~25–35 GB |
| 24 | 577 GB | 376 GB | 262 GB | 185 GB | 141 GB | ~50–70 GB |

**Comparison with the constraint check:** the large-block check (no proving) peaked at 8.5 GB at logs 22–23, below even one dense witness copy at 2^22 (1,210 × 4 B × 2^22 = 20 GB).
- Padded rows are left untouched or zero, and macOS compresses them.
- Proving cannot rely on that: blown-up evaluations are dense, and Linux has no compressor.
- The projections are therefore dense upper bounds.

### Reductions, ranked (estimated saving at 2^23)

**(a) Our code**
- Done: the five fixes above (default 289 → 188 GB; with `storage=compact` 92 GB).
- **(a1) Don't keep the witness and its storage copy together** (≈ −22 GB, medium):
  - generate witness columns in storage order with the prover's allocator and hand them to the commit, which consumes them;
  - recompute the 513 lookup-read columns per component from the committed coefficients when building fractions.
- **(a2) Make `compact` + `discard_mains` the block prover's default** (`proof_file.prove`). Same bytes, similar CPU time; owner's call.
- **(a3) Metal: zero-copy device composition** (stored-domain ABI on the committed buffers, `backendResidencyHandles`). This removes the arena (the largest component, ≈ 406 c ≈ 14 GB) and the touched shared pages. It is also what makes compact fast on Metal. Medium-high effort.

**(b) stwo-zig (described, not edited)**
- Device-side re-extension for compact storage. `Session.expansion` exists; Metal needs a host-free executor, and CUDA already has LDE kernels.
- Witness streaming into the commitment: `tiled_commit` exists; it needs a producer interface so the witness is never fully materialised (≈ −M, 40 GB at 2^23).
- Merkle layer retention is only ~3 % (all layers of 3 trees ≈ 96 c), so it is not worth pursuing.

**(c) Structural (owner review)**
- **(c1) Per-component sizes (lifting/mixed sizes).** Only sha, bytes, msg and b2s need the full height of a large block. fields (190 columns), coin (164), anc (125) and the others need far fewer rows. Rough estimate: 3× fewer cells.
  - stwo-zig supports lifted components (STWZEVA too).
  - Our system, mask geometry, in-circuit verifier and Lean statement do not yet.
  - Effort: large. Biggest lever.
- **(c2) Split large blocks across proofs** (tx ranges, with partial LogUp sums as the epoch does). Bounds L per proof, at the cost of more leaves. Large effort.
- **(c3) Streaming/partial residency on the GPU:** a CUDA concern, sized by the k above.
- **(c4) Config changes don't help:** blowup is already 1, and queries/PoW/fold don't affect memory. The profile is pinned anyway.

### Recommendation

- **H200 (141 GB), 2^23:**
  - compact residency (coefficients on device, re-extended per component and per quotient batch, ≈ 92 GB);
  - plus (a1) (≈ 70 GB);
  - witness generation streamed per component from the host.
  - Evaluations-only (131 GB) is too tight. 2^24 needs (c1) or (c2).
- **24–64 GB machine:**
  - with `compact` + `discard_mains` today: 2^21 (23 GB) fits a 32 GB machine and 2^22 (46 GB) a 64 GB one;
  - 24 GB needs (a1) for 2^21;
  - 2^23 needs (c1) per-component sizes (~25–35 GB), or (c2) splitting.
