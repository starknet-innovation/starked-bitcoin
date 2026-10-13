# Progress log

Append-only, newest first. One entry per work session; a session that spans
midnight goes under its start date. Never edit a past entry: write a
correction in a new one.

Template (copy it to the top):

```
## YYYY-MM-DD — <one-line summary>
Who: <person or agent (model)>
Roadmap: <IDs touched and their new status>
Done:
- <outcome, with commit hash>
Evidence:
- <commands run and their result: tests, lake build, #print axioms, benchmarks>
Problems / lessons:
- <what went wrong, how it was resolved, what to do differently>
Next: <the exact next step; must match status.md>
```

---

## 2026-10-13 (session 13, natural upload) — CUDA: trees 0–1 uploaded in natural order, reordered on the device (host-checked; device run pending)
Who: Claude (agent, Opus 5.5), worktree branch `cuda/natural-upload`
Roadmap: GPU step 3 (CUDA): host trace trees lever done on the host side; the pod run decides it
Done:
- fc579dd: `ir.PreCol.fill` (memset/period runs instead of per-row `at`), `ir.fillParallel`, `system.preprocessedNatural`; `genPreprocessed` uses them (every caller benefits).
- bbc8599: `src/gpu/cuda/reorder.zig`: one generated AOT kernel (`gpu/cuda_aot/witness_starked_reorder_*.cu`, native-authenticated, tag `native_m31_permutation_trace_v3`) moves each cohort of trees 0–1 from staging to the coefficient buffer in storage order in `.trace_generation` (`pipeline.assembleTrace`); the LogUp gather now reads the reordered buffers; a host-LogUp tree 2 is a device copy. `prover.hostTraceTrees`: tree 1 borrows the witness columns, tree 0 is generated in natural order. docs/design/gpu-cuda.md § Natural upload.
Evidence:
- `cuda-test`: new `reorder_test.zig`: the kernel's exact source as host C++ equals `toStorage` (logs 0–16, mixed cohorts; log 0 caught a bug), and the whole `.trace_generation` over block 0's real plans (uniform 2 launches, tiered 18) reproduces all 1,435 CPU storage-order columns and the LogUp sources. Drift, LogUp, arena (unchanged: 26.4 / 52.8 GiB) pass.
- `cuda-check`, `cuda-parity`, `cuda-archive-plan` (80 AOT sources: 48 + 16 + 15 + 1) pass; `zig build test -Doptimize=ReleaseFast` green: filters "ir: PreCol", "golden hashes", "block system" (30 min), then the full suite (37 min, 13.5 GB peak RSS).
- `cuda-prove --large 400000 --profile production --size tiered --skip-cpu` (M4 Pro, stub link): "host trace trees" 3.66 s → 0.15 s; peak footprint 14.07 GB → 7.16 GB (the main tree's 5.4 GiB storage copy is gone). `--host-logup` still runs its host steps.
Problems / lessons:
- Ingress H2D is pageable `cudaMemcpyAsync` and stwo-zig has no pinned/host-register API; registering 13 GB would cost about what it saves. Not done.
Next: pod run on this branch: `scripts/pod/run.sh` (block 0 ×4, 400000), `large-prod-tiered-hostlogup`, `xl-970347`, `xl-774628`; record host laps, RSS and the `.trace_generation` device time.

## 2026-10-13 (session 13, evening) — 2^23 block proved in ~21–23 s on one H100
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: GPU step 3 (CUDA): host side sped up; natural-order upload (merged from `cuda/natural-upload`)
Done:
- Parallel witness and storage reorder (0852bfd); natural-order upload with a device reorder kernel (bbc8599, fc579dd, merge 358eacd); D-046 tiered by default from 2^12 (bd0219e).
- H100 NVL pod (16 vCPUs, ~10 min, ≈ $0.55): every step byte-identical and verified. Time to proof: 400000 11.8 s (was 30.4 s), 970347 22.7 s (was 60.5 s), 774628 20.8 s (was 53.2 s). Host RSS at 2^23: 23.6 GB (was 37 GB). Details in docs/design/gpu-cuda.md.
Next: witness on server cores (8–15 s; single-threaded remainder), then ingress (pageable H2D, 1.4–4.1 s).

## 2026-10-13 (session 13, later) — Device LogUp validated on an H100: 2^23 block proved in about a minute
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: GPU step 3 (CUDA): device LogUp done (merged from `cuda/device-logup`)
Done:
- H100 NVL pod (RunPod, sm_90, 18 vCPUs, $3.19/hr, 14 min): with LogUp on the device, block 0 ×4 byte-identical; block 400000 tiered `cbcf7026…`; blocks 970347 `f6ff8ac9…` and 774628 `c015e4b3…` (tiered, L = 23) equal to the CPU proofs of the earlier H100 session. All verify. A/B with `--host-logup` also identical.
Evidence (time to proof, device LogUp vs host LogUp on the same pod):
- 400000 (2^22): 30.4 s vs 84.0 s; host RSS 18.7 GB vs 45.9 GB; h2d 6.46 vs 7.37 GiB.
- 970347 (2^23): 60.5 s (witness 21 s, plans and trace trees 35 s, device 4.0 s); 774628: 53.2 s. Host RSS 37 GB, device peak 52.8 GiB.
Problems / lessons:
- None on device: the generated LogUp kernels and stwo-zig's relation completion were right the first time, as the host check predicted.
Next: profile "plans, host trace trees, twiddles" (35 s at 2^23) and the witness (21 s); then the verifier self-check (18 s) is the largest remainder.

## 2026-10-13 — CUDA: device LogUp (host-checked; device run pending)
Who: Claude (agent, Opus 5.5), worktree branch `cuda/device-logup`
Roadmap: GPU step 3 (CUDA): device LogUp implemented and host-checked; the pod run decides it
Done:
- `src/gpu/cuda/logup.zig`: one generated fraction kernel per AIR with lookups (15, `gpu/cuda_aot/witness_starked_logup_*.cu`, stwo-zig's native-authenticated AOT identity), the plan (sources, tree-2 layout, completion geometry) and the device binding: sources gathered in `.trace_generation`; challenge expansion (18 α powers), fraction kernels, stwo-zig's `relation_completion` and the claim copy in `.trace_commit`. The denominator slab borrows tree 2's evaluation buffer.
- `pipeline.zig`/`prover.zig`/`memory.zig`: device LogUp is the default; `proveHostLogup` and `cuda-prove --host-logup` keep the first version for A/B; z and α powers are now always expanded on the device. `scripts/pod/run.sh`: `large-prod-tiered-hostlogup`, `EXTRA=...`.
- docs/design/gpu-cuda.md § Device LogUp.
Evidence:
- `zig build cuda-test -Dcuda=true -Doptimize=ReleaseFast`: all pass. New: the generated kernels (host C++) plus a completion model reproduce `system.interactionTrace` (444 columns, 15 claims, exact) for block 0 uniform/tiered; `STARKED_LOGUP_SAMPLES=1,2,3,4,5` (blocks 170–91880) and `STARKED_LOGUP_LARGE=400000` (L 22 tiered, 66 s, 6 GB RSS) also pass; an offset mutation fails. Arena: 2^22 tiered 26.4 GiB (25.6 host LogUp), 2^23 tiered 52.8 GiB.
- `zig build cuda-check -Dcuda=true`, `zig build cuda-archive-plan -Dcuda=true` (79 AOT sources: 48 + 16 + 15; stwo-zig's validator accepts the new entries), `zig build cuda-parity -Doptimize=ReleaseFast`, `zig build test -Doptimize=ReleaseFast`: pass (37 min, 8.3 GB peak RSS).
- `cuda-prove --small 0 --skip-cpu` (stub link): host steps run in both modes and stop at session open, as expected without a GPU.
Problems / lessons:
- stwo-zig's build admits AOT kernels only under its listed ABI tags; ours use `native_blake_exact_interaction_v1` (the paired-LogUp tag) with our own argument contract. Upstream ask: a generic external fraction-kernel schema.
- The commitments interpolate trees 0–1 in place, so the lookups' columns must be copied out before the draw (the `logup_sources` slot, +0.8 GiB at 2^22 tiered).
Next: pod run of `scripts/pod/run.sh` on this branch (block 0 four steps, block 400000 tiered), then the host-side witness and trace trees (12 s) as the next lever.

## 2026-10-13 (session 13) — CUDA prover on real GPUs: byte-identical from block 0 to 2^23
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: GPU step 3 (CUDA): device runs done (L40S, H100 NVL); device LogUp started (branch `cuda/device-logup`)
Done:
- L40S (RunPod, sm_89, 34.5 min, $0.64 billed): block 0 ×4 profiles and block 400000 tiered (2^22) byte-identical to the CPU, verified. Three device fixes (287ebe2, 7691c82, 4e52bdb, c2fd88b); pushed to main as daa311e.
- H100 NVL (RunPod, sm_90, 94 GB, $3.19/hr, ~36 min): block 0 tiered and block 400000 again identical; **blocks 970347 and 774628 (tiered, L = 23) byte-identical to CPU proofs made on the pod, verified.** Details in docs/design/gpu-cuda.md § Pod runs. Proofs kept in `data/store/gpu/` (gitignored).
- Pod scripts: the tarball bootstrap creates the one-commit repos the build identity needs; `run.sh large <height> <size>`; the source bundle drops stwo-zig's report evidence and notes (2.5 GB → 326 MB, upload 32 s).
Evidence:
- `cuda-prove` logs: sha256 970347 `f6ff8ac953601dea…` (1,184,413 B), 774628 `c015e4b36600463a…` (1,185,434 B), 400000 `cbcf7026134f9a71…` on both GPUs.
Problems / lessons:
- At 2^23 the device proof is 5.5 s of an 11-minute run; on a 27-vCPU pod the CPU commit of trees 0–1 alone takes 123–138 s. Device LogUp (removes it) is the next lever; host witness/plans next.
- Quote pod cost from RunPod billing, not from memory.
Next: device LogUp on `cuda/device-logup`, then one pod run to validate it.

## 2026-10-12 (session 12, night) — GPU step 3: resident CUDA prover ported (host-checked, no device run)
Who: Claude (agent, Opus 5.5), worktree branch `cuda/resident`
Roadmap: GPU step 3 (CUDA): M0 design, M1 build and linked schedule, M2 host checks done; M3 (CuMetal) blocked on tooling
Done:
- docs/design/gpu-cuda.md: stage-by-stage port of stwo-zig's resident circuit pipeline (2f54632).
- src/gpu/cuda: AOT catalog (one kernel per AIR, `gpu/cuda_aot/`), plans, transcript, memory, terminal, pipeline, two-pass prover; forks of stwo-zig's topology, OODS/quotient/layout and composition controller for empty spans, wide masks and 18 α powers (3ee987a, 85df3ec).
Evidence:
- `zig build cuda-test -Dcuda=true -Doptimize=ReleaseFast`: 8/8. AOT kernels (host C++) = interpreter; plans and transcript (host and device-sink model) reproduce CPU proofs of block 0, uniform and tiered; arena of 2^20/22/23 blocks plans and binds.
- `zig build cuda-check -Dcuda=true`: the whole device schedule links against C stubs.
- `zig build test -Dtest-filter=stwzeva` and `-Dtest-filter=byte-identical` (ReleaseFast): pass.
Problems / lessons:
- stwo-zig's circuit stages hard-code two mask offsets per column, six α powers and non-empty spans; ours need 23, 18 and an empty span (block_anc). Forked minimally; upstream changes listed in gpu-cuda.md.
- Host writes are ingress-only, so host LogUp needs a roots pass first.
Next: an NVIDIA host (owner decision): build the AOT archive with `gpu/cuda_aot/`, link `prover.zig`, prove block 0 and compare bytes.

## 2026-10-12 (session 11, night) — First real 2^22 block proved tiered; CUDA step 3 started
Who: Claude (agent, Opus 5.5) with a sub-agent (CUDA resident port, branch `cuda/resident`)
Roadmap: GPU-CODEGEN step 3 in progress; VL-FRI noted upstream (42653cf)
Done:
- Block 400000 (1,660 txs) proved at production strength (70 queries, PoW 26) in the tiered profile,
  CPU, compact + discard, and verified: L = 22, component logs {22,17,22,22,17,8,22,8,17,20,20,20,20,
  17,17,12}, 145 s, peak RSS 14.4 GB (estimate was ~17 GB), proof 1.13 MB, deterministic (same proof
  SHA-256 `cbcf7026134f9a71` on two runs). `METAL_PROVE_LARGE`/`METAL_PROVE_VERIFY` (5f1fdfd).
- CUDA step 3 item 1 (5f1fdfd): stwo-zig's CUDA codegen emits kernels for all 17 of our AIRs from the
  template programs (public inputs as base params); built as host C++ they equal the interpreter
  (`zig build cuda-parity`).
Evidence:
- `METAL_PROVE_LARGE=400000 METAL_PROVE_TIERED=1 METAL_PROVE_ONLY=cpu METAL_PROVE_DISCARD=1
  METAL_PROVE_VERIFY=1 METAL_PROVE_STORAGE=compact zig build metal-prove -Doptimize=ReleaseFast`.
- `zig build cuda-parity -Doptimize=ReleaseFast`: 17/17 kernels equal.
Next: production-strength recursion node measurement; CUDA resident port (sub-agent).

## 2026-10-12 (session 11, evening) — SHA at 2^24: Lean `SizeOk` replaces the L ≤ 23 cap
Who: Claude (agent, Opus 5.5)
Roadmap: D-045 follow-up (tiered blocks up to L = 24 covered by the Lean theorems)
Done:
- Why: a consensus-valid block of ~16k minimal segwit transactions needs ~14M SHA rows (estimate:
  ~12 compressions per tx × 72 rows), above 2^23. The cap was the lookup count bound 216·2^L < P.
- Lean: `SizeOk Ls` (Link.lean) = every hashed-system component ≤ 2^24 rows and `hashRows Ls < P`; it
  replaces `∀ i < 15, Ls i ≤ 23` in every block theorem. `SizeOk.of_le23` recovers the old case, so
  the uniform statements and all 100 `Compat.lean` statements are unchanged (only their proof terms
  route through it). `BlockPubOk'` and the forest/epoch conclusions use `SizeOk`. Two bounds tuned to
  2^23 were widened (CoinLink `coin_start_strict` 2^25 → 2^26; `coin_in_lex` tx index < 2^24).
- Zig: `bs.sizeOk` mirrors `SizeOk` (site counts tested equal to the AIRs' lookups); the block
  builder refuses uncovered sizes (`SizesNotCovered`) and the forest refuses uncovered size keys
  (`keyOk`). This also closes a pre-existing gap: the forest accepted a uniform L = 24 leaf that no
  theorem covered.
Evidence:
- `lake build` 8867 jobs; `lake build StarkedAir.Compat` 8856 jobs; `#print axioms` on `SizeOk.of_le23`,
  `BlockPubOk'.mtp`, `epoch_hyps_of_rng'`, `forest_epochV`, `epoch_systems_core`: standard three.
- Zig: SizeOk, sizesFor, block VK tests (incl. the golden key) pass; full suite 111 passed + 1 skipped (opt-in). 24 exported AIRs byte-identical. Tiered L = 24 site count ≈ 4.5·10⁸.
Problems / lessons:
- Not run: a real or synthetic 2^24 block (≈ 53 GB tiered compact; beyond the Mac).
Next: prove a real 2^22 block tiered; production-strength node measurement.

## 2026-10-12 (session 11, later) — Per-component trace sizes (D-045) merged; license; lean-consensus; S31
Who: Claude (agent, Opus 5.5) with sub-agents (prover track, Lean track, s31 evaluation)
Roadmap: D-045 implemented (uniform + tiered profiles); LICENSE done (Apache-2.0); memory (a1, a2) done
Done:
- Memory (a1, a2): witness released early, LogUp fractions per row, compact + discard as the block default
  (dca6dc6). 2^23 projected ≈ 97 GB uniform.
- D-045 prover (dd42720, 7f8fb95, 31855ee, 04cc5ee): mixed sizes via lifting; profiles uniform
  (byte-identical, golden hashes) and tiered (L ≥ 12); proof file v3; leaf and VKs per (L, profile).
  Tiered block 170 padded: 2.8x less memory, ~3x faster; tiered epoch 0–3 forest verified.
- D-045 Lean (cb123ee, fbfdfa0, cd30a5e, a73e13f): `Compat.lean` keeps 100 statements verbatim (2218
  definition pins); Block layer, circuit layer (`StarkSoundV`, `plain_soundV`, `starkSoundV_const`) and
  recursion layer (`tree_soundP`, `forest_epochV`) generalized. Interface docs on both sides; hook 2 keeps
  the counter convention (k-th call = k-th part), so composition exports stay byte-identical.
- LICENSE Apache-2.0 (1baf1f4); `lean-consensus/` standalone package + generator (370ecfa); main pushed
  (866ccc9..370ecfa); S31 issue https://github.com/teddyjfpender/s31/issues/9.
Evidence:
- After merging both tracks: `lake build` 8867 jobs, Compat 8856 jobs; exports block_coin, block_anc,
  composition_leaf, deep_leaf, statement_leaf byte-identical. Large-block test alone: 4 samples hold
  (peak 11 GB). Full suite: 110 passed, 1 skipped (the opt-in tiered real-block check), 35 min.
Problems / lessons:
- Proving recursion nodes peaked at 20.5 GB (two 70-query child proofs): the next memory bottleneck.
- The tiered leaf's mixed-size logic is Zig matched by inspection (as the uniform leaf's wiring is);
  `StarkSoundV` needs review against Stwo's lifting argument before external claims.
Next: prove a real L=22 block tiered (~17 GB est.); measure a production-strength node; decide tiered
as default for L ≥ 12; sha at 2^24 (Lean: < 1 day).

## 2026-10-12 (session 11, continued) — GPU steps 1–2, memory, VL-NODE, block_coin columns
Who: Claude (agent, Opus 5.5) with three sub-agents, on the owner's decisions of the day
Roadmap: VL-NODE done (D-044: our wiring proven here; stwo-zig's verifier upstream, briefed in
~/Workshop/stwo-zig/VERIFIER_FORMALIZATION_BRIEF.md); GPU steps 1–2 done; memory (a1) in progress
Done:
- GPU step 1 (3896f2e…7b467e1): IR → STWZEVA lowering; CPU proofs byte-identical. Step 2 (cee213e,
  a9d737e): block-system proofs on `Engine(MetalCommitBackend)` with GPU composition, byte-identical;
  block 170 3.7 s CPU → 0.14 s Metal. Memory (8fbfe3c, 7245652): freeing allocator, per-component
  LogUp, `discard_mains`, storage modes; 2^23 projected 289 → 188 GB (default), 92 GB (compact).
- block_coin's 4 unread `VAMT` columns removed (6414a09; vestigial since 185d30a).
- D-044 (58ff68f). VL-NODE (e51bc30, 60c5f70): node wiring Lean-first; `tree_sound`, `forest_epoch`,
  `htree_sound`, `header_root_sound` modulo the `Trust` structure's named hypotheses.
- Merged into m3a5: 427900c, 0c4fa18.
Evidence:
- Large-block test alone after the merges: 4 samples hold and balance (peak 11 GB). Full suite
  103/103 (37 min, peak 9.1 GB). `lake build` 8866 jobs; standard axioms for the node theorems.
- `zig build metal-prove`: all six small samples byte-identical CPU vs Metal, verified.
Problems / lessons:
- The `blockrec` and `block forest` test filters match no tests (a filter matching nothing still
  reports a pass); the end-to-end evidence is the epoch 0–3 forest run and the blockrec demo.
- The working branch is m3a5; `main` is the last push (147 commits behind).
Next: memory (a1) and compact-by-default (agent); then the per-component trace sizes plan (c1), owner
review first, acceptance: everything proven today stays proven.

## 2026-10-12 (session 11) — D-043 accepted; the previous MTP inside the block proof (option A)
Who: Claude (agent, Opus 5.5), on the owner's "D-043 part 3: Option A. No need to export the timestamps."
Roadmap: D-043 accepted and fully implemented; BLOCK-REC open item left: a shipped block VK
Done:
- `block_anc`, the block system's 16th component (7b04e43): the header chain's SHA256d, plumbing and
  linkage over 12 periods (11 predecessors, oldest first, then the block); period 11's hash = public
  25–40; the MTP limbs (public 3, 7) are the median (at most 5 times above, at most 5 below); a copy of
  `FIRST` read 2048 rows down forces ≥ 4096 rows with CSV; below CSV the limbs are 0. No lookups, no new
  preprocessed columns, times private. Witness `src/block/anc.zig`; ancestors of the CSV samples in
  `testdata/anc`; `chainproof` passes `PF.ancestors`.
- Lean (4e67e84): `AncSound.anc_sound` (via `chainSat`: the ancestry trace satisfies the header chain's
  base constraints for trace-read public inputs, so `header_hash`/`header_link` apply unchanged),
  `median_of_counts`; `BlockAnc.blockSys_sat`, `block_mtp`; `BlockPubOk` is the 16-component system,
  `BlockPubOk.mtp`; `blockSys_static`.
- GPU route scoped (docs/design/gpu.md): no generic-AIR CUDA path in stwo-zig; plan IR → STWZEVA, Metal
  composition, then a generic resident CUDA prover. The owner declined CPU cloud spend.
Evidence:
- `lake build` 8864 jobs; `#print axioms` standard for `anc_sound`, `block_mtp`, `BlockPubOk.mtp`,
  `blockSys_sat`, `blockSys_static`, `epoch_hyps_of_rng`.
- Full `zig build test -Doptimize=ReleaseFast`: 96/96 passed (35 min, peak 9.5 GB). Large-block test alone:
  4 samples (log 22–23) hold and balance, 26 min. Tampers (MTP ±1, broken ancestor, other block hash,
  nonzero limbs below CSV, 2048-row CSV trace) each rejected by their constraint; a CSV-era block (height
  500000) proves and verifies. Epoch 0–3 re-proved through the forest (`data/epoch-small-anc`): same set
  `ea4af14d…`; the leaf took 161 s (was 115 s).
Problems / lessons:
- The prover does not take preprocessed columns at an offset: the size guard reads a main-column copy.
- A component without lookups must export as a v1 AIR (`anc.air.toJson`).
- Debug-mode tests abort on forced invalid witnesses (M31 range asserts); run the suite in ReleaseFast.
- The epoch proofs on disk (0–170, 171–1000) are stale after the AIR change.
Next: owner — VL-FRI/VL-NODE trust boundaries; whether to re-prove 0–1000 locally; the GPU plan. Then a
shipped block VK.

## 2026-10-11/12 (session 10) — VL-ORACLE; BLOCK-REC built end to end at small scale
Who: Claude (agent, Opus 5.5), overnight on the owner's "keep going until 9am"
Roadmap: VL-ORACLE done; BLOCK-REC in progress; D-043 proposed
Done:
- VL-ORACLE (`zig build oracle`, acd5641): native-proof mutations, the native verifier and the circuit
  agree (0 disagreements). One apparent disagreement (the preprocessed root) was the circuit pinning
  that root as a statement constant; reclassified. An executable, not a test: stwo-zig logs an error
  on every native rejection, which fails Zig tests.
- BLOCK-REC: block leaf measured (aeb6f8b: 8.27 M variables, proved in 5.2 s, 858 KB); D-043 proposed
  (seed tree-shaped, hash binding per aligned subtree, MTP in the block proof, context in the leaf);
  Lean `rng_leaf`/`rng_node`/`epoch_hyps_of_rng` (83f2c35); leaf checks `checks_sound` (24a3743); seed
  v3 and the seed leaf (305d8c6); block leaf and node circuits, blocks 0–1 demo (d3d9f4c); `SumOk`,
  `sumOk_node`, `sumOk_leaf` (507d7c2); context `ctx_sound` (072b280); the epoch forest and its outer
  verifier (95f565d); `rng_forest`.
- Epochs 0–170 and 171–1000 re-proved and verified under seed v3 (sets unchanged).
Evidence:
- `lake build` 8859 jobs; `#print axioms` standard for every new theorem.
- Tests: leaf checks, seed leaf vs native, context at boundaries with tampers, `blockrec` demo (node
  digest = native join), epoch 0–3 through the forest verified, three tampers rejected.
Problems / lessons:
- A replacement range in `store.zig` swallowed code (restored from git, redone narrowly); an export name
  `block_ctx` collided with the block context AIR's JSON (restored, renamed `block_leaf_ctx`).
- Found while specifying: the previous-block MTP has no aggregator obligation (D-043 part 3).
- Epoch 0–170 through the recursion forest (5b23099): 5 trees, proved in 90 min (peak 17.7 GB), verified in
  0.6 s after the chain, same set `7105b60f…`. Exhaustive VL-ORACLE (8934134): 46,068 sites, 0
  disagreements. Full `zig build test` after the night's changes: 93/93 passed (29m50s, peak 13 GB).
- Lean, the coin theorem's hypotheses: `created_wfe_systems`, `spent_wfe`, `epoch_systems_wf` (WFE only for
  the sets; f108574, 4dbe410); `rec_starts`, `claim_is_record_at`, `ki_count`, **`claim_at_input`** (the
  events are functions of the committed data, D-041 in Lean; 8e6af52, 7181bf6); `created_nodup_of_txids`
  (fa86d67). `decodeSet` range checks (2086bb8). `forest_rng` (ea15018).
- Epoch 171–1000 through the forest: 11 trees, 830 leaves, proved in 7.2 h (01:55–09:05, peak footprint
  40.7 GB on the 24 GB Mac), `forest-1000.bin` 10.8 MB, verified in 1.4 s (the flat run: 63.8 s); same set,
  998 coins, `29a42ec2…` = Core's HASH_SERIALIZED.
Next: owner review of D-043 (MTP option A or B); then the MTP, a shipped block VK.

## 2026-10-11 (session 9) — VL-E2E: the plain verifier end to end
Who: Claude (agent, Opus 5.5), on the owner's roadmap amendments (VL table, D-042)
Roadmap: VL-E2E, VL-POW, VL-OODS done
Done:
- `lean/StarkedAir/Circuit/EndToEnd.lean`: `plain_sound` (composition and balance programs hold ⇒ under
  `StarkSound` the AIRs hold on extracted columns ⇒ with `SZGood`, `sys.SatisfiedExt`), `plain_leaf_valid`
  (header-chain leaf ⇒ `PubValidT`), `sz_good_bound`. Steps proven: `partTerms_eq`, `evalR_row`,
  `row_batch`, `comp_frac_sum` (via `logup_sum` and batch pairing), `fingerprint_poly`, `fracSum_sites`,
  `fracSum_ext`, `static_ext`.
- Docs: verifier-formalization.md (the theorem and its hypotheses), verification.md, roadmap, status.
Evidence:
- `lake build`: 8852 jobs OK. `#print axioms` for `plain_sound`, `plain_leaf_valid`, `sz_good_bound`:
  `propext, Classical.choice, Quot.sound`.
Problems / lessons:
- `SZGood` is stated for the columns `StarkSound` returns; its probability bound needs them to be the
  committed ones (fixed before `(α, z)`). That ordering is outside the logical statement; recorded as
  such rather than encoded.
- VL-POW: `Circuit/Pow.lean` (`powCheckP`, `powCheck_sound`, `Spec.powOk`); op `guess`, hints `lsb`,
  `inv_or_zero` (Lean `Ops.lean`, `glue.zig`); `LeanChannel.pow` replays it for n_bits 0/4/26.
- VL-OODS: `Circuit/Oods.lean` (circle group spec, `shiftP`, `shift_sound`, `#guard`s on generator
  orders); `ShiftTable`/`shiftPoint` in `plain_verifier.zig`; the leaf loads `airs/oods_shift_leaf.json`.
- Evidence for both: full `zig build test` with VL-POW (exit 0, 30 min, all rec-fuzz mutations
  rejected); then `-Dtest-filter` OODS, PoW, pinned mainnet VK, glue parity, leaf wrap: 6/6 passed;
  `#print axioms` standard for `powCheck_sound`, `shift_sound`; exported JSON regenerates byte-identically.
- Lesson: this repo's test filter is `-Dtest-filter=…`; `-- --test-filter` is ignored and runs the
  whole suite.
Next: VL-ORACLE (native-verifier oracle on the REC-FUZZ mutations); BLOCK-REC design per block-rec.md.

## 2026-10-11 (session 8) — M3b coin proof layers 4–5; challenge binding fixed (D-041)
Who: Claude (agent, Opus 5.5), continuing the owner's "M3b and everything not blocked by compute"
Roadmap: UTXO (M3b) in progress (coin proof layers 1–4 done, layer 5 in progress)
Done:
- Lean layer 4 (events): each coin row is its transaction's input or output, with its tuple the event's
  encoding; `coin_block_sum` (the public partial sum, by coin events).
- Lean layer 5 so far: `encE` and its injectivity (`encE_inj`), `phiOf_poly` (with `αₖ = αᵏ`; the
  implementation now uses powers), `coin_in_lex`, `block_claims`, `block_event_sum` (a block's partial
  sum as epoch events).
- **Soundness gap, found while stating the epoch theorem and fixed (D-041):** the LogUp and fingerprint
  bounds need every event fixed before the epoch challenge, but the final set was not in the seed, the
  initial set was bound by `hash_serialized` (no transaction index), and each input's claimed `CTX` was
  a free trace column. Fixes: the seed binds both sets' full encodings (c2c859d); undo records carry the
  creating-transaction index inside the committed stream, URec yields it and the coin row's `CTX` must
  equal it (013dc7e; Lean: `coin_urec`, `urec_bytes`, `coin_in_tuple`; 214 sites per row).
Evidence:
- `zig build test` filters: coin events (with new index-tamper and commitment checks), amounts, block
  commitment, epoch, block 170, block proof file, block system small and block-hash, block negative:
  pass. `lake build` clean, no `sorry`.
Problems / lessons:
- For any challenge-based argument, list every value behind a tuple and check it is fixed before the
  challenge; "the trace is committed" is not enough when the challenge is drawn before the trace.
- All epoch proofs made before D-041 are stale (seed tag v2, undo stream format).
- Later in the session: the epoch sum and balance (`epoch_balance`), the run (`epoch_coin_run`), the
  bridge to Core's coins (`run_map`, `decSer_ser`, `epoch_connect`), the per-transaction amounts and
  `ClaimsOK` (`Block/CoinClaims.lean`), and **`epoch_core`** (standard axioms).
- **Second D-041 gap, found while assembling the epoch and fixed:** URec's record lengths were free
  (records only had to tile the stream), so the claims' boundaries were a trace choice; records now
  commit a 2-byte length (`code ‖ index ‖ length ‖ serTxOut`), URec constrains `TL` to it. Large-block
  test passes after both AIR changes (21m45s); epochs 0–170 and 171–1000 re-proved under the first fix
  (same `hash_serialized` values) and being re-proved under the second.
Next: the wrapper instantiating `block_facts` over an epoch's block systems, and the remaining
hypotheses from `block_sound` (see utxo.md, layer 5, Open).

## 2026-10-10 (session 7) — VERIFIER-LEAN steps 4–5 done; M3b proofs; an amount-check soundness bug fixed
Who: Claude (agent, Opus 5.5), on the owner's "proceed with step 5 (channel and Merkle proven, FRI
soundness stated), then M3b and everything not blocked by compute"
Roadmap: VERIFIER-LEAN step 5 done (end-to-end composition theorem open); UTXO (M3b) in progress
Done:
- VERIFIER-LEAN: Merkle leaf hashing (ecd7fbf), the DEEP response list (185a271), Merkle paths
  (59fbbad), the channel and the transcript order (d0d975f), all Lean-first and in the leaf; FRI
  soundness stated as an assumption (verifier-formalization.md).
- `glue.parse` counted constants' coordinates as registers (n_regs up to ~2^31): fixed in d0d975f;
  leaf tests' peak memory 14 GB → 6 GB.
- M3b: the fingerprint's Schwartz–Zippel step (`epoch_sound_fp`, 04efc40); the coin component's
  row-level soundness (`CoinSound.lean`, f29bbfa) and running sum (`coin_runsum`, 86807b1).
- **Soundness bug, found by the coin proof and fixed:** the coin component's high comparators (`H1`:
  inputs ≤ `MAX_MONEY`, inputs ≥ outputs; `H2`: coinbase ≤ subsidy + fees) were four full bytes, up to
  2^32 > P, so their equations could wrap modulo P: a transaction could output more than its inputs,
  or a coinbase more than subsidy plus fees. Fixed as in the fields' value check: `H1C = 7 − H1 3` and
  `H2C = 7 − H2 3`, range-checked (high limbs < 2^27). Regression test: block 170 with the subsidy one
  satoshi lower and the wrapped comparator is rejected; with the bound's constraint alone removed, the
  same trace balances.
- **Core rule added:** the block's accumulated fees within `MAX_MONEY` (Core's
  `bad-txns-accumulated-fee-outofrange`), checked after each non-coinbase transaction (comparator 3).
  It also keeps the fee accumulator from wrapping, which the coinbase check relies on.
- Amounts at the natural-number level (`in_nat`, `out_nat`, `tend_nat`, `fee_acc`, `coinbase_nat`):
  given the byte ranges the lookups provide, every sum is exact (no wrap), inputs within `MAX_MONEY`,
  outputs at most inputs, the fees the sum of the transactions' fees, the coinbase at most subsidy
  plus fees.
Evidence:
- `zig build test` filters for the recursion set (20/20), channel/Merkle/transcript parity, block system
  small samples, coin events, amounts, epoch (6/6); `lake build` clean; `#print axioms` standard for
  every new theorem.
Problems / lessons:
- A shell command with a stray `cat > file` waited on stdin for 3.5 hours; check background jobs
  actually start.
- Running a Lean build next to the leaf tests OOM-killed the test; the real cause was the register
  count bug above.
- Epoch proofs made before the comparator fix (0–170, 0–1000) use the old coin AIR and are stale.
Next: the coin system links (lookups to the fields, SHA, undo records, fingerprints), the amounts at the
natural-number level, then the step to `connect_of_run`; epochs from a previous set; the sorted pass.

## 2026-10-10 (session 6) — M3a.5 BLK-CHECKS done and proven (`block_sound`)
Who: Claude (agent, Opus 5.5), on the owner's "go forward, finish M3"
Roadmap: BLOCK-AIR → M3a.5 done (M3a.6 next); BLOCK-DATA, UTXO, CATCHUP todo
Done:
- AIRs and witnesses for the checks: fields extension, `block_tables` (8-bit range and opcode
  table), `block_walk`, `block_ctx`, `block_wmerkle`; the nine-component system proves and verifies
  on small samples and satisfies and balances on large ones (b3969e6, cb4a0e6).
- Lean: per-transaction checks (`tx_values`, `tx_prevouts`, `tx_final`), the walker's total, the
  context facts, the witness tree (`wmerkle_sound`), totals, script multiset, commitment selection,
  coinbase structure, and the assembly **`block_sound`** (`Block/BlockSound.lean`): a satisfied system
  with `BlockPubs c pub` gives `checkBlock c raw = none`, given no repeated prevout (D-031).
- Soundness fix found by the proof: `prevMtp` was public as one value with private 16-bit limbs, so
  limbs for `prevMtp + P` also passed. Now two public limbs (`pub 3`, new `pub 7`); D-035 amended.
- D-035 amended: the range table is 8-bit (one shared trace size).
- `tx_final` takes `cutoff < 2^32` (was `2^31`), so header times need no hypothesis.
Evidence:
- `lake build`: green, 8809 jobs; no `sorry`, `native_decide` or `bv_decide`.
- `#print axioms block_sound` (and `merkle_sound`, `wmerkle_sound`, `fields_sound_gen`):
  `propext, Classical.choice, Quot.sound`.
- JSON drift: all 22 exported AIRs equal the Lean export.
- `zig build test`: see the commit that merges this work.
Problems / lessons:
- A single public value split into private limbs is not bound modulo P: either bound the limbs
  (range) or make the limbs public.
- `Setup` (a structure of the parsed block and grammar facts) kept the final assembly short.
- M3a.6 BLK-COMMIT, same session: D-038 (proposed) `C = blake2s(blake2s(raw) ++ blake2s(0x01 ++ undo))`;
  AIRs `block_undo`, `block_b2msg`, `block_b2s` (the proven gadget, chained); **`commit_sound`**
  (a77183f, 86df454). Found while proving: the outer period needed `OUTP·NIL = 0`.
- Memory: the 12-component system at `2^23` rows (774628, 3.96 MB) exceeds 24 GB in the in-memory
  check; that sample is now skipped by the large test.
- BLOCK-DATA, same session: block hash public, proven (`hash_pub`, a8f57fd); `.sbblock` files,
  `chainproof prove-block`/`verify-block`, `scripts/fetch_undo.py` (ba207e0). Block 170 proved and
  verified against the mainnet chain proof. Block 400000: witness checked (2²², 235 s); proving stopped
  for low memory.
- M3b design proposed (D-040, utxo.md); CATCHUP is a compute wall.
- Owner decisions (2026-10-10): D-035 amendments confirmed; D-038 amended to `C = blake2s(undo)`
  (built, 5014aeb); D-039 self-contained block files (built, 2d3efd9); D-040 approved (multiset, epochs at
  Core's assumeUTXO heights).
- M3b, same day: `run_of_balance`, `epoch_sound`, `connect_of_run`, QM31 field, `extsum_sound`,
  `seg_sound`, `rows_sound` (Lean); coin/undo-record/fingerprint components with amount rules; the
  15-component system proves on the samples; blocks 9+170 balance; epoch 0–170 verified from genesis
  (706083a).
Next: the in-circuit plain verifier proof (owner's request), then coin-component Lean links.

## 2026-10-09 (session 5) — M3a.5 design pass
Who: Claude (agent, Opus 5.5), on the owner's request
Roadmap: BLOCK-AIR → in progress (M3a.5 BLK-CHECKS designed, not started)
Done:
- Design: [block-data.md § M3a.5](../design/block-data.md#m3a5-blk-checks-design-approved-2026-10-10-d-035).
  - It flattens `checkBlock` into `BlockOK`.
  - It adds public inputs 2–6 for the context.
  - It adds four components: a range table, an opcode table, the sigop walker and `ctx`.
  - It extends the fields component with per-token checks.
  - The witness tree and commitment reuse the Merkle and SHA components.
- D-035 recorded as proposed.
- Duplicate inputs stay with M3b (D-031, already settled).
Next: owner review of D-035, then stage M3a.5a (`Spec/BlockFlat.lean`).

## 2026-10-09/10 (session 5) — PROOF-STORE done; trust reductions; M3a.5a
Who: Claude (agent, Opus 5.5), owner away 48 h with agreed priorities
Roadmap: PROOF-STORE done; REC-FUZZ done; SPEC-FUZZ done; MMR-LEAN done; LOGUP-SZ done;
LEAF-ONE-PROOF done; BLOCK-AIR: M3a.5a done (AIR stages parked)
Done:
- **M3a.5 design (D-035, proposed), then parked** on the owner's request.
- **PROOF-STORE (D-036):**
  - the `chainproof` CLI, the pinned VK and the frozen shape;
  - pinned requests (review finding 2), checkpoints, extension, the genesis leaf;
  - `prove_loop.sh` and `extend_tip.sh`.
- **Full chain saved and verified;** `T` equals the 2026-10-09 run and an independent recomputation.
  Extended to 970,733 in 334 s; the tip matches your node.
- **REC-FUZZ:** 102,013 mutations over three campaigns, all rejected by the circuit.
- **Spec vs Core** (header and block specs): about 860k cases, 0 mismatches. Constants checked
  against `chainparams.cpp`.
- **Lean:**
  - `Mmr.lean` (`mmr_inclusion`, `fold_eq_mmr`);
  - `RootChecks.lean` (genesis checks exported; `verifyRoot` reads them);
  - `LogUpSZ.lean` and `LogUpSZSystems.lean`;
  - `Spec/BlockFlat.lean` (`checkBlock_none_iff`, `walk_eq_sigOps`, ...).
- **AIR digests** bound to Lean's exact text (byte-identical re-serialization).
- **Scoping note:** proving Core's assumeUTXO `HASH_SERIALIZED`.
Evidence:
- `chainproof verify mainnet data/store/mainnet-0-970347.sbchain`: VERIFIED in 1.5 s;
  `mainnet-to-970734.sbchain`: VERIFIED.
- `#print axioms` gives standard axioms for every new theorem; the drift check (17 exports) is
  identical.
- Tests: `proof store`, `rec fuzz`, `header tree`, `genesis checks` and `re-serializes` all pass.
Problems / lessons:
- **Log-20 leaves peak at 34–37 GB on a 24 GB machine,** so the first two attempts swapped and were
  stopped. Measuring showed transient peaks, not a leak. Fixed with log-19 segments, bounded
  per-process steps, and one-proof leaves. Measure the footprint over time before calling a leak.
- **The Mac sleeps when no `caffeinate` holds it;** keep one running for long jobs.
- **`git add docs` swept in an untracked file** the owner had not approved. Add explicit paths.
Next: owner review (D-035, D-036, the review report, push). Then M3a.5b, or keep the proof fresh with
`extend_tip.sh`.

## 2026-10-09 (session 4) — M3a.4 done: the txid Merkle root is proven
Who: Claude (agent, Opus 5.5), on the owner's "go ahead"
Roadmap: BLOCK-AIR → in progress (M3a.4 BLK-MERKLE done for the txid tree; witness tree with M3a.5)
Done:
- Design and D-034: Merkle nodes are SHA messages (`NODE`/`NPAD` blocks); a Merkle component lays out the
  tree; the transaction count is public input 1.
- AIRs: `block_sha` gains node blocks and the CVE-2012-2459 mutation check; `block_merkle` (new);
  `block_fields` checks `VAL = pub 1` on row 0.
- Zig: `src/block/merkle.zig` (tree layout, SHA plan extension, witness). Tests:
  - the 5-component system proves on blocks 0, 170 and 91812;
  - blocks 481824 and 709632 (1,866 and 2,043 transactions) satisfy the SHA and Merkle constraints with
    the header's root;
  - rejected: a tampered root limb; a duplicated transaction (fails at the mutation check).
- Proofs moved to the 5-component system (`ShaSound`, `Link`, `HashSound`), plus `MerkleSound` and
  `MerkleLink`. Headline `merkle_sound`.
Evidence:
- `lake build` OK (8,773 jobs, no `sorry`). `#print axioms merkle_sound`: `propext`, `Classical.choice`,
  `Quot.sound`.
- `zig build test -Dtest-filter=block` and `-Dtest-filter="block merkle"` pass.
Problems / lessons:
- A positive-offset-free design (comparisons at `−8`) kept the prover unchanged.
- Lookups' degree limits shaped the AIR: `NNE`, `ZZ` and the `LEFT`/`RIGHT` columns keep every
  constraint at degree ≤ 3 and every value at degree 1.
Next: M3a.5 BLK-CHECKS design (including the witness tree and commitment).

## 2026-10-09 (session 3) — M3a.3 done: digests are txids, wtxids and the header hash
Who: Claude (agent, Opus 5.5)
Roadmap: BLOCK-AIR → in progress (M3a.3 BLK-SHA done)
Done:
- `digest_sha256d`, `HashSpec.sha256d_eq`, `TxIndex.lock_unique`, `mid_tuple`, `same_bytes`, `block_word`.
- Transaction ranges: `TxSplit.txT_split`, `tx_layout`, `tx_cols`, `tx_bytes`, `lock_tx`. FieldsSound's
  byte-read lemmas are now generic over a read oracle (`Reads` section). `Link.hash_read` and
  `hash_fields_read` supply the oracle for `hashSys`.
- `whole_data`, `whole_tx`, `split_pieces`, `split_tx`, `txs_rows`, `block_index`, and the headline
  `digest_tx`: the block parses as `b`, and each digest is `SHA256d(b.header)` or the `wtxid`/`txid` of
  `b.txs[TI]`.
Evidence:
- `lake build` OK (8,769 jobs, no `sorry`). `#print axioms` on every new theorem: `propext`, `Classical.choice`,
  `Quot.sound` only.
Problems / lessons:
- `unfold P` inside goals with `ZMod.val` makes `omega` fail with bogus counterexamples (recorded in
  reference/lean.md).
Next: M3a.4 BLK-MERKLE (Merkle component).

## 2026-10-09 (session 2) — M3a.3: message and SHA components built; component soundness proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: BLOCK-AIR → in progress (M3a.3 BLK-SHA: AIRs, witnesses, component proofs done; linking next)
Done:
- Fields yield each transaction's byte ranges (62f8838). `block_msg` (bf260ea) and `block_sha` (b7b0d3b)
  AIRs, witnesses and tests, plus negative tests (0c1f74d).
- SHA soundness `digest_sound` (37bc8ab..275fc02): a second hash's digest is SHA256d of its message's
  words, read block by block from the first block.
- Message soundness (c129f50..60968c0): `whole_msg`, `split_msg`, `pad_ok`, `pad_bytes`, `belongs`,
  `word_yield`, `len_yield`.
- `msg_pad`: a message's rows are `Spec.Block.pad` of its data bytes. Linking (`Block/Link.lean`):
  `sha_word`, `sha_len`, `msg_read`, `msg_tuple_linked`.
- Soundness fix (1fffa02): the length rows were checked only mod `P`, and a top length byte up to 255
  allowed `8 · len + P`. Bits 3..7 of that byte must now be clear; `top_lt` proves the bound.
- The owner's `bitcoind` node is reachable over SSH and an RPC tunnel. It is a data source only: the
  machine is too small to prove on. Credentials stay in `prove-any-chain/.env.local`, which is gitignored
  here.
Evidence:
- `lake build`: 8,763 jobs, OK. `#print axioms` on `digest_sound`, `whole_msg`, `split_msg`,
  `pad_bytes`, `word_yield`, `len_yield`, `belongs`, `msg_pad`, `sha_word`, `sha_len`, `msg_read`,
  `msg_tuple_linked`: only `propext`, `Classical.choice`, `Quot.sound`.
- `zig build test -Dtest-filter=block` passes (exit 0). (bytes, fields, msg, sha) proves and verifies
  on blocks 0, 170 and 91812. Txid digests reproduce the Merkle roots, including on segwit blocks
  481824 and 709632.
Problems / lessons:
- The prover rejects preprocessed columns read at a nonzero offset (`PreprocessedOffsetUnsupported`).
  Use an extra periodic indicator for the shifted row instead (`IS56`, `IS0`).
- Proving the length rows against the spec exposed the mod-`P` gap. Check for wrap-around whenever a
  constraint compares a multi-byte value.
Next: one message per id, then compose into "digest = `Spec.Block.sha256d` of the message"; the fields' tx
yield semantics (tuples are `serNoWit`/`serWit` ranges).

## 2026-10-09 — Full chain re-proven with the header tree
Who: Claude (agent, Opus 5.5)
Roadmap: HC-HASHTREE → done
Done:
- `spike chain 20 70 26`: 243 leaves, 242 nodes, root verified with the public-data VK; `T` equals the natively
  recomputed MMR root over 970,348 block hashes ([report](../reports/2026-10-09-full-chain-tree.md)).
Evidence:
- Log `data/chain_full_tree.log`: leaves 45,317 s, fold 5,098 s, verify 1.09 s, root proof 981,000 bytes.
Problems / lessons:
- Leaves cost about 2.5× the previous run: the segment proof now includes the tree component at the same row
  count (no lifting yet).
Next: M3a.3 BLK-SHA.

## 2026-10-08 (session 4) — M3a.1 and M3a.2 done and proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: BLOCK-AIR → in progress (M3a.1 BLK-BYTES, M3a.2 BLK-FIELDS done)
Done:
- M3a.1 block byte table: `bytes_rows`, `read_byte` (33e3237).
- M3a.2 grammar layer `toksBlock_parse` (b898e56); fields AIR, tokenizer and witness (310ab0d); AIR-layer proof
  through `fields_sound` (8bb66a9 … this commit).
- Soundness fix found while proving: bound the 5-byte CompactSize's top byte (95a05bc).
Evidence:
- `zig build -Dtest-filter=block -Doptimize=ReleaseFast test`: 11/11 (6 small samples prove and verify with the byte table;
  5 large ones satisfy the constraints; tampered rows and bytes rejected).
- `lake build` clean, no sorry; `#print axioms fields_sound`: propext, Classical.choice, Quot.sound; JSON drift: ok.
Problems / lessons:
- `set` abbreviations break rewrites against lemma outputs stated on the original terms; state lemmas
  over abstract `M`/`R` with hypotheses instead.
- `by` blocks inside applications elaborate before implicit naturals are unified; use `refine … ?_`.
- `unfold P` inside goals that mention `ZMod P` values creates distinct omega atoms; bound via `lt_P`.
Next: M3a.3 BLK-SHA; the full-chain run with the tree continues (see status).

## 2026-10-08 (session 3) — Prover race fixed; CIRCUIT-GLUE done
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: CIRCUIT-GLUE → done; PROOF-STORE proposed; HC-HASHTREE full run in progress
Done:
- Fixed an intermittent `ConstraintsNotSatisfied` in multi-component proofs (fdd5a03): two components evaluate
  concurrently and allocated from one arena; `system.prove` now wraps the allocator thread-safely.
- Glue defined in Lean, exported, replayed (15b6496); proofs: `blake2s_sound`, `node_sound`, `node_compose`, digests, key.
Evidence:
- Before the fix about 1 in 4-5 runs of `spike chain 16` failed (ReleaseSafe: integer overflow in the accumulator
  merge); after it, 10/10 pass.
- `glue parity` tests: leaf, and node in topology and value mode, gate-identical to the hand-written builders; the
  node proves and verifies.
- `lake build` clean, no sorry; `#print axioms` of the new theorems: propext, Classical.choice, Quot.sound.
Problems / lessons:
- The first full run with the tree died at start (the race); restarted at fdd5a03, running.
- A word-level Blake2s spec with the chaining value as a function evaluated exponentially (16^blocks); materialize lists.
Next: let the full-chain run finish and write its report; then M3a.1.

## 2026-10-08 (session 2) — IR-LOGUP, BLAKE2S, M3a spec, HC-HASHTREE built and proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: IR-LOGUP, BLAKE2S, BLOCK-SAMPLES, BLOCK-SPEC, BLOCK-AUDIT → done; HC-HASHTREE → built and proven, full-chain re-run todo
Done:
- Owner decisions D-027..D-033 (multi-component LogUp, spent-output slots, Blake2s commitments, duplicate inputs in M3b, header commitment = MMR).
- Private repo starknet-innovation/starked-bitcoin created; authors rewritten to the GitHub noreply address. Nothing pushed.
- IR-LOGUP (Lean semantics, system prover, in-circuit), BLAKE2S (`compress_sound_air`), block spec and serialization round trip.
- HC-HASHTREE: tree + header-v7 components and `tree_root_sound` (a2066db); leaf over the system with the root entry (bb1a9c0);
  Lean aggregation with `T` (b668b4e); node computes `T` in-circuit, MMR fold, VK sizes, inclusion proofs, native `T` check (this commit).
Evidence:
- `zig build -Dtest-filter=...`: leaf, node (T = perfect root over 32 hashes; node 229–328 s Debug), header tree (MMR, inclusion, blockHash) pass.
- `spike chain 12 3 10 data/headers.bin 53`: 4 segments (16+16+16+4), 3 nodes, root verified; `T` equals the native MMR root over 52 hashes.
- `lake build` clean; `#print axioms` for `pub_compose_T`, `leaf_valid_T`, `chain_from_genesis_T`: propext, Classical.choice, Quot.sound.
Problems / lessons:
- A first background chain run stopped silently after leaf 1 (exit status hidden by a pipe); the direct rerun completed. Not reproduced.
- 1-header segments have no tree node: the plan now uses ≥ 2-header segments and leaves an odd last header out.
Next: full-chain re-run with the tree (`spike chain 20 70 26 data/headers.bin`, about 8 h+), then M3a.1 (block AIR).

## 2026-10-08 — M1 and M2 done: full chain checked and proven to one root
Who: Claude (agent, Opus 5.5)
Roadmap: HC-FULLRUN, AGG, RECURSION, VK → done; IR-LOGUP → moved to M3; REC-STMT-EQ → partly done
Done:
- `fullrun 16 check`: heights 0..970,347, 0 failures; chainwork equals Core's (blockchair).
- `spike chain 20 70 26`: 243 leaves, 242 nodes, root verified; 8.2 h CPU wall.
- `leafIdentity`: the verifier derives leaf identities from public data; drivers use it.
Evidence: [report](../reports/2026-10-08-full-chain.md); `zig build test` 32/32.
Problems / lessons:
- The full run's VK used the leaf proofs' own hashes; fixed afterwards and checked at
  every leaf size used, but the 8 h run was not repeated.
Next: REC-FUZZ, then M3 after the owner's decisions (status.md, Needs owner).
## 2026-10-07 — M2: plain in-circuit verifier, leaf, node, aggregation (Lean + Zig); headers downloaded
Who: Claude (agent, Opus 5.5), with the owner (Q-MASK choice B)
Roadmap: REC-PROFILE, REC-COMPOSE, REC-MASK, REC-LEAF, REC-FOLD → done; AGG → in-progress (full-chain run); HC-FULLRUN → in-progress (check running)
Done:
- REC-PROFILE (ab8d1fc), REC-COMPOSE `segment_compose` (31e1db4), `dag_correct` (1c973bb).
- D-024 plain in-circuit verifier for multi-offset, no-LogUp proofs (089faee).
- REC-LEAF (0eb473a): leaf circuit, proved and verified natively.
- AGG-LEAN (d4b5714): `pub_compose`, `leaf_valid`, `chain_from_genesis`.
- REC-FOLD (2d89e67, D-025): node circuit with in-circuit `PubLink` and identity key.
- AGG (933b7a8, 9267084): fold driver, node identity from topology, `verifyRoot`, `spike chain`.
- All 970,348 mainnet headers (0..970347) downloaded and merged, every link checked.
Evidence:
- `zig build test`: 32/32. Lean builds; new theorems use standard axioms only.
- `spike agg 16 4 70 26`: 1,024 headers → one root proof (0.98 MB), verified in 0.23 s.
- `spike agg 20 2 70 26`: 8,192 headers; leaf 31–33 s + 33 s segment, node 24 s, 13.3 GB peak.
- `spike chain 12 3 10 … 40`: mixed leaf sizes and an odd carry; chainwork 40 × 0x100010001.
Problems / lessons:
- `verifyProofBytes` returns the verifier circuit's own output, not the proven circuit's
  digest; the proven digest is `request.output_digest`, bound by acceptance.
- Adding a package that a dependency already imports creates a duplicate module; use the
  dependency's re-export (`circuit_cpu.verify.Request`).
- Zero component sizes are not a valid padding target; start the fixpoint from a leaf's padded sizes.
Next: finish `spike chain 20 70 26 data/headers.bin` (data/chain_full.log) and `fullrun 16 check`
(data/fullrun_check.log); write the report; close M1 and M2.

## 2026-10-07 (session 4) — HC-V6 proven, Core audit, full-chain tooling; download running
Who: Claude (agent), with the owner
Roadmap: HC-V6, HC-AUDIT → done; HC-FULLRUN → in-progress. Decision D-022 (owner): defer GPU/H200.
Done:
- HC-V6 minimum block version (BIP34/66/65; heights verified in Core `chainparams.cpp`): spec,
  AIR v6, witness, real segment at 400000, `version_sound`, added to `SegmentValid` (f8dc841).
- HC-AUDIT against Core master: `SegmentValid` covers every mainnet header rule except
  `time-too-new` (verification.md § Coverage audit).
- `scripts/fetch_headers.py` (verified header download) and `spike fullrun` (2873f78).
  Heights 0..2047: check mode OK, Metal prove+verify OK, chaining OK, chainwork exact.
Evidence:
- `lake build` OK (8733 jobs); `#print axioms header_chain_sound` → standard axioms only.
- `zig build test`: 27/27.
Problems / lessons:
- Blockstream started returning 429 under 4 parallel workers; the fetcher now puts a failing
  source on cooldown and uses the other.
- An overclaiming test comment ("version 3 refused" may fail on PoW first) was corrected.
Next: when the download finishes, merge the chunks (`fetch_headers.py --merge data/chunk_{0,1,2,3}.bin`)
and run `spike fullrun 16 check data/headers.bin`; then `fullrun 18 metal` to measure the full-chain proving time.

## 2026-10-07 (session 3) — HC-V5, HC-TOP, BENCH-RAITO, FV-Z3; version rule found missing
Who: Claude (agent), with the owner
Roadmap: HC-V5, HC-TOP, BENCH-RAITO, FV-Z3 → done. New: HC-V6 (next), HC-AUDIT, HC-FULLRUN.
Decisions: D-020 (exact chainwork, owner), D-021 (s ≥ 16, agent).
Done:
- HC-V5 exact chainwork: definition 5199752, proof 79d2fde (`work_q`, `work_step`, `work_out`,
  built on the generic `carry_chain`/`shift_sum`/`cauchy`).
- HC-TOP: `Spec/Chain.lean` `SegmentValid` and `header_chain_sound` (9a6ea99).
- BENCH-RAITO: our SHA AIR is about 250× faster than Raito's Cairo SHA-256 under `scarb prove` (84a42fe).
- FV-Z3: `scripts/air_z3.py`. Four windows unique, SHA round unknown, control behaves (this commit).
Evidence:
- `lake build` OK (8731 jobs). No sorry/native_decide/bv_decide. `#print axioms header_chain_sound`
  → propext, Classical.choice, Quot.sound.
- `zig build test`: 26/26. JSON drift: in sync. Benchmarks and Z3 runs: see the reports.
Problems / lessons:
- **A consensus rule was missing.** Core rejects low block versions after BIP34/66/65
  ("bad-version"). I had wrongly recorded that version rules never matter. Found while answering
  the owner; now HC-V6, plus HC-AUDIT so that a line-by-line check of Core replaces memory.
- Z3: integer encoding hopeless at this size; cone of influence + bit-vectors made 4/5 tractable.
- Lean: `set` trap again (facts derived after `set` keep the unfolded form); derive first, set last.
Next: HC-V6 (version rule). Q-HEADERS is open for HC-FULLRUN.

## 2026-10-07 (session 2) — HC-V4 median time past: defined, tested, proven
Who: Claude (agent), with the owner
Roadmap: HC-V4 → done; HC-V5 → next. Owner decisions D-018 (counting) and D-019 (M1 before M2).
Done:
- Spec `mtpOk` (Core `GetMedianTimePast`) with `#guard`s, including mainnet height 101982 whose
  time is below two predecessors. Counting equivalence `mtpOk_iff_count` and `sentinel_sound` proven.
- v4 AIR (`Mtp.lean`, rows 229–240, 394 constraints, 52 preprocessed, 88 pubs), Zig witness,
  tests, real pre-history test data (6fa5376, c903ecb).
- Soundness (`MtpSound.lean`): `mtp_window`, `mtp_cmp`, `mtp_count`, `mtp_out`, `mtp_core`.
Evidence:
- `lake build`: OK, 8727 jobs. No sorry/native_decide/bv_decide. `#print axioms` on all 10 main
  theorems → `propext, Classical.choice, Quot.sound`.
- `zig build test`: 23/23 passed. JSON drift: all 4 files in sync.
- Python brute force (200k cases) and a Zig randomized test (100k) agree: the sentinel counting
  rule matches Core's sorted median (sound always, and complete for t > 0).
- Benchmark: 1024 headers at 2^18 rows, Metal, 70 queries/26-bit PoW: 3.65 s prove (≈ 280
  headers/s, down from ≈ 350), 0.13 s verify, 1.07 MB.
Problems / lessons:
- My first `#guard` had the median of 1..11 wrong; the guard caught it. Keep writing guards
  before the circuit.
- The Blockstream API rate-limited after the timestamp scans. Fetched the new test data from
  mempool.space (same Esplora API) and recorded the source.
- The doc-edit script aborted midway but the shell chain still committed. Fixed in c903ecb.
  Run edit scripts so a failure stops the commit (`&&`, assertions).
- `set` lesson again: facts obtained after `set x := e` mention `e`, not `x`; state them with
  the `set` name.
Next: HC-V5 (chainwork). Start with the design note in `docs/design/consensus-rules.md` § v5.

## 2026-10-07 — v3b retarget proven; docs and PM process
Who: Claude (agent), with the owner
Roadmap: HC-V3B → done (5e219bb); DOCS → done
Done:
- `retarget_sound` proven (5e219bb). The new file `RetargetDiv.lean` holds
  `rt_divq`, `rt_rem`, `rt_cap` and the final assembly. `header_pow_ex`
  exports the PoW row's exponent and powLimit facts.
- Documentation tree, README map and PM process (4df8c1e). The old docs
  moved to `docs/design`, `docs/airs` and `docs/reports`.
Evidence:
- `lake build`: all 8724 jobs OK. No `sorry`, `native_decide` or `bv_decide`.
  `#print axioms` on `retarget_sound`, `chain_sound_v2` and `state_sound` →
  `propext, Classical.choice, Quot.sound`.
- `zig build test`: green.
- JSON drift check: all four `airs/*.json` files match the Lean export.
Problems / lessons:
- A single proof took 47 minutes and hit the heartbeat limit. The causes:
  `omega` over a ~70-fact context (including `(by omega : …)` inside a term),
  let-bound `set` variables, and bounds stated about the unfolded expression.
  Fixed with `clear * -`, `clear_value` and top-level helper lemmas; the
  proof now takes 15 s. Bisecting with truncated copies of the module built
  in parallel found the culprit quickly. The rules are recorded in
  [reference/lean.md](../reference/lean.md).
- Retarget soundness depends on the PoW row's powLimit constraints. This is
  recorded in [verification.md](../reference/verification.md).
Next: HC-V4 (median time past). Start with the design section in
`docs/design/consensus-rules.md` and a layout plan in `docs/airs/header-chain.md`.

## 2026-10-06 — Repo bootstrap through header chain v3b (definition)
Who: Claude (agent), with the owner
Roadmap: SPIKE, STWO-225, SHA, IR-V1, HC-V1, HC-V2, HC-V3A → done; HC-V3B definition done
Done:
- Scaffold and Lean-first spike (9b95bb6); Zig↔Lean differential test (a0e54a5).
- Filed teddyjfpender/stwo-zig#225 (the verifier doesn't pin the
  preprocessed root; forgery reproduced).
- SHA-256 compression AIR (665b732) and its soundness proof (daae642,
  69ba59a, f18e90d).
- IR v1 (1e3a824). Header chain v1 (2fa7211, 69b2335), v2 (829a7e4,
  3323650), v3a (f9f7a95, 508cfd8), v3b definition and tests (b7ab5ce), and
  the retarget proof groundwork (0a808ce, f0297d8).
Evidence:
- The per-AIR docs list the tests, theorems and benchmarks.
Problems / lessons:
- A claim about stwo-zig's CUDA support taken from its README was wrong.
  Verify upstream claims in source code.
- `lake env lean` ignores `autoImplicit=false`; use `lake build`.
- `norm_num` cannot prove M31 prime; use Lucas–Lehmer.
Next: finish the v3b proof.
