# GPU proving: scope (2026-10-12)

Status: **scoping only**, nothing built. Read from the vendored stwo-zig source (`third_party/stwo-zig`,
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
- **LogUp mapping:** our IR's LogUp onto STWZEVA's prefinalized layout is unconfirmed.
- **Product status:** the CUDA products are staged, not released.
- The recursion leaves (8.3 M-variable circuits) are probably as costly as the block proofs and are
  already a `circuit_cuda`-shaped workload.
