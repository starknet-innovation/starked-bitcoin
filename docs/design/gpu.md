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
