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

## 2026-10-27 (session 23) — Coin-set pass step 3 done: the segment system's soundness
Who: Claude (agent, Opus 5.5), owner: "Go for it. Don't stop working until you need something from me."
Roadmap: coin-set pass (D-048) step 3 done; step 4 (the set tree) next
Done:
- f7caac7: soundness fix found in review. The compression components yielded their end token at row 0
  of the last block's period; the trace's last period can be cut short (2^L is not a multiple of 88 or
  72) and a cut period has no output rows, so the outgoing chaining value was free. The tokens are now on
  the period's last row (set_b2c P_FIN 3, set_shac row 71). JSON regenerated; segment tests pass.
- d3a8b5a, 0b6f809 and this commit: `SetPass.set_seg_sound` (lean/StarkedAir/SetPass/Sound.lean) and its
  parts: the system link (Link, LinkUse: uses −1/0, `link`, byte/range/pending reads), Facts (fingerprints,
  stream reads, compression words, end tokens), RecSound, B2wSound/B2cSound/B2Spec,
  TMsgSound/ShaCSound/ShaSpec, Fold. The component files were written by three parallel sub-agents
  (no pods); the link and composition by the main agent.
Evidence:
- `#print axioms StarkedAir.SetPass.set_seg_sound`: propext, Classical.choice, Quot.sound.
- `lake build` (full) passes; the AIR JSON drift check passes for all 32 AIRs (set_b2c and set_shac
  were regenerated in f7caac7; the existing block AIRs are byte-identical).
- `zig build test -Dtest-filter="set segments"` passes after f7caac7.
Problems / lessons:
- `unfold P; omega` splits `ZMod.val` atoms; use `Rec.P_big` (`2^30 < P`) with omega instead.
- The SHA-256 block count is carried as a field element: the verifier must check the final length is
  below 64·P bytes. The tree must check `EncIn`'s ranges on the first segment (the begin state meets them).
Next: the set tree (step 4): node circuit over segments with `linkChecks`/`combine`, root VK pinned.

## 2026-10-27 (session 22) — Coin-set pass step 3: the segment circuit (AIRs, witness, tests)
Who: Claude (agent, Opus 5.5), with the owner (push of 949cbe3 approved; "go ahead with the segment circuit"; the node's RunPod key kept)
Roadmap: coin-set pass (D-048) step 3, circuit half; the soundness proofs are next
Done:
- 949cbe3 pushed with approval.
- The segment system designed in docs/design/set-pass.md (§ The segment system): nine components, three reused unchanged (`block_bytes`, `block_tables`, `block_fpwalk`), six new in `lean/StarkedAir/SetPass/` (`set_pend`, `set_rec`, `set_b2w`, `set_b2c`, `set_tmsg`, `set_shac`), 550 public inputs. The pass's start (the count bytes) and end (the hash finalizations, `i = n`) are left to the verifier: both are pure functions of public values.
- One challenge per pass: the set after block 945,000 gets two passes (~+$15–20 *est.*), so `block_fpwalk` and the accumulator are reused with their proofs.
- `src/block/set_seg.zig`: the witnesses, `begin`/`finish`, the native state after a segment.
Evidence:
- `zig build test -Dtest-filter="set segments"`: every segment of the sets after blocks 170 (3 records each) and 1000 (40 each) satisfies every constraint and balances; the first segment of each proves and verifies; the chained states give `set_pass.run`'s digest, `hash_serialized`, count, amount, highest height and sum. Tampering any of 21 public values (each carried part, in and out) is rejected.
- Lean: `lake build` passes (the components' degree `#guard`s); the existing AIRs' JSON is unchanged.
Problems / lessons:
- Limits the circuit adds over the reader: `height < 2^24`, `len < 2^24` (a record must fit a segment), the amount below `2^96`, segments over 64 bytes. Real sets are far inside them; a file outside cannot be proved (completeness only).
Next: the Lean soundness theorem `set_seg_sound` (per component, then the system), then step 4 (the set tree).

---

## 2026-10-26 (session 21) — Epoch VKs pinned; verify-only header file; coin-set pass steps 1–2
Who: Claude (agent, Opus 5.5), with the owner (pin the circuits; shrink the header proof, option 1; the coin-set pass, D-048 "Ok on all 3"; pushes approved one by one)
Roadmap: BLOCK-REC epoch VKs pinned (D-047); PROOF-STORE compact file (D-049); coin-set pass designed and accepted (D-048), native model and Lean spec done
Done:
- b9d6504 pushed (session 20's work), then ec354e7 and 287b9a3 pushed on the owner's approval.
- ec354e7: tree, root and join VKs pinned in `vk/epoch/` and embedded in `chainproof`; the epoch verifiers accept only them (`--unpinned` for tests); `setup-vks` remakes them from public inputs (D-047).
- 287b9a3: the coin-set pass proposal (docs/design/set-pass.md) and its native model (`src/block/set_pass.zig`, `chainproof set-pass-model`).
- This commit: `.sbchain` root kind `compact` (the root proof without the peaks; `chainproof compact`; extension refuses it) (D-049); Lean `Spec/SetFile.lean` (the set file's parse, facts, the streamed pass, `pass_sound`, `pass_segments`, `encSet_inj`); D-048 recorded; the step-3 component survey in set-pass.md.
Evidence:
- `verify-chain` on the node with pinned VKs only: VERIFIED blocks 935,001–972,500, `hash_serialized 9f92d143…`. The stale tip root from 2026-10-23 (`tree972/epochroot-972500.bin`, made before 43bc5f9) is now rejected (`VkNotPinned`); the epoch stays proved by the chain proof, whose roots use the current circuit.
- `setup-vks` on the real forests (Mac, 80 s, 14.8 GB): every remade tree and join VK equals the pinned one; the remade root VK equals `root-16-prev.vk` (written while pinning).
- `chainproof compact` on `mainnet-to-972502.sbchain`: 13,768,372 → 986,168 bytes; `verify` 2.02 s → 0.13 s (Mac); the same tip, chainwork and `T` on the Mac and the node. `verify-chain` on the node with the compact file: VERIFIED, the same coin set; the header check 0.8 s.
- `set-pass-model` on the node's set after block 972,500 (7,154 segments): Core's `hash_serialized` and the epoch root's digest `77a0de28…`, 15 min, 3.8 MB.
- Lean: `lake build` passes; `#print axioms` on `pass_sound`, `pass_segments`, `encSet_inj`, `encSet_of_parseSet`, `parseSet_encSet`: standard only; `#guard`s against Python `hashlib` and `set-pass-model` on a two-coin file (a mutated guard fails the build).
- `zig build test -Doptimize=ReleaseFast`: 129/130 passed, 1 skipped (2,047 s).
Problems / lessons:
- Correction to session 20: `verify-chain`'s time is the set files, not the heads. Its "chain of epochs verified (2,009 s)" span reads each 14 GB set twice before the join proof is checked (`ER.loadInit`, `SF.scan`), and the balance after it reads them again; the whole run took 53 min on the node, the proofs a few seconds. The set pass removes those reads.
- The first pinned root VK was a stale file (pre-43bc5f9); `setup-vks` caught it. Remake a VK before pinning it.
- A test that borrows one decoded chain's peaks into another must not free them twice (segfault in the first run).
Next: coin-set pass step 3, the segment system (modified Blake2s and SHA-256 with carried state, the record parser, two-challenge fractions), small sets on the Mac.

---

## 2026-10-22 (session 20) — Epoch 945,001–972,500 proved to the tip; one proof per epoch; the two mainnet epochs joined into one proof
Who: Claude (agent, Opus 5.5), with the owner (scope: prove the tip epoch from the node overnight, build the epoch root and the epoch join, run the real join; no push)
Roadmap: BLOCK-REC epoch root built (one proof per epoch); epoch join built (one proof per chain of epochs); 935,001–972,500 proved as ONE proof and verified on the node
Done:
- bd7b0fd..1146363: the epoch root (Lean `epochRoot M prevV`, Zig program over M node-shaped roots, seed and challenge in-circuit, two-level output digest); `prove-epoch-root` / `verify-epoch-root`, `--set-digests` (a pod without the set files).
- 2145d55..b7eeb97: Lean soundness of the epoch root (`low31_sound`, `logOf_sound`, `links_sound`, `sums_sound`, `root_seed`, `root_challenge`, `root_sound`, `root_digest`, `root_children`, `rootK_epoch`).
- 43bc5f9..01e6a90: the epoch join (Lean `EpochJoin.lean`: base_prev, base_genesis, step); chain shapes (root shape R from both root variants at the largest child count, join shape J a fixpoint), chain VK `joinvk.bin`, chain file (every epoch's head and the last join's proof), `prove-chain` / `verify-chain`.
- efdaef9: `prove-chain` reads size keys from the forest and one block proof per key; `scripts/pod/node_join.sh` (a join on a pod, CPU build, cost cap).
- 5b9bd13, 83cda05, 0c23832: Lean `join_sound`, `EpochChainSound` (chain_sound, chain_cover, chain_verify) and the witness-style, non-vacuous `EpochChainW` (`chain_verifyW`).
- 5b46f78: `airs/epoch_root_16.json` (the no-prev 16-child root, needed by the root shape).
- 96a3763: `chainproof rebind-forest` (a forest's paths in a longer chain's header tree, each subtree's block-hash root checked against the new chain proof's root; no proof redone); `prove-chain` reuses a root file only when its head is this run's byte for byte.
Evidence:
- Tip epoch 945,001–972,500 (27,500 blocks) from the node: block proofs on an H100 (3 deferred blocks on an H200), final set equal to the pod's; tree and epoch root on an H100. `verify-epoch-wide` and `verify-epoch-root` on the node: VERIFIED, 164,539,066 coins, `hash_serialized 9f92d143…` (Core's).
- Mac: a 3-epoch chain (blocks 0..15) proved and verified as one proof, roots and joins at 2^22, ~4 s per join, ~527 KB; the prefix chain-8 verifies alone; rejected: a wrong prev set (`SetsDoNotLink`), a short proof for a long range (`WrongEpochs`), out-of-order epochs (`RootNotSetUp`), resealed tampers of nin/sum (`WrongDigest`), a hash root (`HashesNotTheChain`), a proof byte (`CircuitProofRejected`). A minimal dir (forest, tree VK, one proof per size key, set digests) gives the same VK. After 96a3763: blocks 4..15 as one chain proof, both roots reused.
- `zig build test -Doptimize=ReleaseFast`: 127/128 passed, 1 skipped (2,081 s).
- The real join (H100 pod, CPU, 224 cores): shapes R = 2^25, J = 2^22 (237 s); both roots proved at R (97 s, 99 s); the join 9.4 s; chain file 575,868 bytes; 7.5 min, 69.6 GB peak. `verify-chain` on the node: "VERIFIED blocks 935001..972500 as one chain proof: the coin set after block 972500 is 164539066 coins, hash_serialized 9f92d143…", both epochs balanced (the 945,000 set 165,215,167 coins).
- `#print axioms` on the new Lean theorems: standard axioms only.
- RunPod billing: 2026-10-22 $57.10 (block run $54.05), 2026-10-23 $29.12 (block run tail $9.39, H200 $5.86, tree and root $13.04, first join try $0.83), 2026-10-26 $1.82 (two join tries).
Problems / lessons:
- First join try: `EpochRootNotExported`. The root shape folds both variants at the largest child count; only the 16-child prev variant was exported. The Mac test used 3 children, where both exist. A test with the production child count would have caught it.
- Second try: `HashesNotTheChain`. The rehearsal epoch's forest held paths in the header tree of the chain file it was proved against. An epoch proved under an older chain file needs `rebind-forest` before a join under a newer one.
- The tip's own epoch root was not reused (it was proved at its natural shape, not the chain's R); re-proving it took 99 s.
- My watcher for the first try never ran ssh (zsh does not word-split `$N`); the failure sat unseen for three days. Watchers are now bash scripts.
- `verify-chain` on the node (16 GB, aarch64) took 33 min, most of it opening the heads and the joins' native replay; worth profiling.
- A Zig result-location alias (`x = .{ .f = g(&x) }`) gave `SetsDoNotLink`; compute into a const first.
Next: push `rec/epoch-root` (owner's approval); profile `verify-chain`; the coin-set pass (the set fingerprint and hash_serialized in-circuit).

---

## 2026-10-21 (session 19) — Rehearsal epoch verified flat, then aggregated on the GPU: 10,000 block proofs as 16 recursion trees
Who: Claude (agent, Opus 5.5), with the owner (scope: run the rest of the rehearsal from the node, verify it, build the GPU aggregation tree, push)
Roadmap: rehearsal 935,001–945,000 proved and verified (flat and through recursion); BLOCK-REC wide nodes and per-level shapes built, on the GPU
Done:
- d798305: `scripts/pod/node_run.sh` (an epoch run driven from the node: transfer, follow, final-set check, pod deletion, cost cap; `FOLLOW_ONLY` re-attaches after a node restart). The last 5,518 block proofs on an H100 from the node; final set equal to `replay`'s.
- e5fa2c5: `verify-epoch` caches each block shape's preprocessed root (`PF.PreRoots`); before, every 2^23 proof cost ~15 s and ~10 GB to verify.
- `rec/per-level` (bad788e..071e206): `src/recursion/block_tree.zig` (wide-node forest: leaves padded only to the leaf level, 8-wide nodes with the remainder arity at a subtree's top, node circuits per arity and child kind at one node size; tree VK, forest file, outer verifier, resumable `<dir>/tree`); `chainproof prove-epoch-wide` / `verify-epoch-wide`; `cuda-epoch-tree` (resident CUDA circuit prover, one runtime on its owner thread, host workers, cached preprocessed roots); leaves reuse the block proof's root per shape; pod scripts `prove_tree.sh`, `node_tree.sh`; Lean `TreeK.node a v` (node hash per arity and variant, `TrustK`/`TrustKW`).
Evidence:
- Flat: `verify-epoch --jobs 4` on the node (16 GB, temporary swap): 10,000 block proofs, 165,215,167 coins, `hash_serialized 5b2b0df7…`, 21 min, 14.4 GB.
- Mac, epoch 0..3 production: forest verified (same set as `verify-epoch`); a dropped coin (`ChallengeMismatch`), a size key (`LeafSizeNotSetUp`), a summary limb (`WrongDigest`) and a swapped root (`WrongCircuit`) rejected; a resumed run and `cuda-epoch-tree --cpu-prover` byte-identical.
- Shapes (`--shapes-only`, one block per class of the rehearsal): leaves 2^22, every node variant ≤ 2^24.
- H100 SXM (EU-NL-1): 11,432 circuit proofs in 67 min (10,000 leaves at 0.23 s of GPU each, 1,432 nodes), CPU cross-checks byte-identical, peak device 47.9 GB, host 58 GB; forest 9.1 MB. `verify-epoch-wide` on the node: 16 trees, the same 165,215,167 coins and `5b2b0df7…`, 0.5 GB peak (15 min, the two set scans). Pod billing $5.48 (+ $1.61 for two failed starts).
- `lake build` (8,873 jobs); `forestK_epochV`, `treeK_soundP`, `forestK_epochVW`: standard axioms.
Problems / lessons:
- `tar --exclude='.*'` excludes `.` itself: the first pod got no proofs (the node deleted it after a minute). Send files by name.
- stwo-zig's CUDA runtime belongs to the thread that opened it: device proves from worker threads fail (`InvalidState`). Workers queue jobs to that thread.
- The follower saw the forest's assembly (cuda-epoch-tree gone, no END yet) as a crash and relaunched once; `PROC` is now a pattern covering the assembly.
- The large-block tests need ReleaseFast: a Debug `zig build test` ran 8 h.
- The node was resized to 16 GB mid-run (it restarted); the driver re-attached with `FOLLOW_ONLY`.
Next: the root circuit over an epoch's trees (one proof per epoch, seed and challenge in-circuit), then the segmented final-set pass; more host workers (the GPU was ~60 % busy).

---

## 2026-10-19 (session 18) — First rehearsal (935,001–945,000): bounded host memory, split GPU runs, parallel verify-epoch
Who: Claude (agent, Opus 5.5), with the owner (scope: the rehearsal, the H200 for the 6 large blocks, ship the fixes)
Roadmap: rehearsal partly proved (4,476 + 6 of 10,000 blocks); epoch tooling hardened
Done:
- d8524de, 41cdeef: epochs in bounded host memory (`set_file.zig`; `epoch_run.load` streams the sets and
  keeps per block only its hash and commitment; `verify-epoch` streams both sets).
- 9afd51e: `cuda-epoch --only / --skip / --resume`; a block the device cannot hold is deferred to
  `<dir>/deferred-<to>.txt`.
- `verify-epoch --jobs` (block proofs checked on threads); scripts/pod `prove_epoch.sh`, `follow.sh`,
  `xfer_epoch.sh`, and `env.sh` / `bootstrap.sh` fixes (container disk for inputs, cgroup CPUs, retried
  submodule fetch).
Evidence:
- Bounded memory: proofs and sets byte-identical to the previous binary on 0..170, 171..1000 and
  `cuda-epoch --mock` 0..170; on the node, 935,001..945,000 loaded with `set-945000.bin` equal to
  `replay`'s; on the pods ~27 GB host memory for the 10,000-block load (was 244 GB and out of memory).
- `--only`/`--skip`/`--resume` with `--mock`: a split 0..20 run equals the single run.
- H200: the 6 large blocks proved and verified (`verify-block`), peak device memory 99 GiB; the set
  equals `replay`'s (sha256 `881f50c5…`). H100: 4,476 proofs, a sample of 57 verified.
- `verify-epoch --jobs`: same output as sequential on 0..170 and 171..1000; tampered and dropped sets,
  a corrupted and a missing proof rejected; 37.3 s → 5.9 s on 171..1000. `zig build test
  -Doptimize=ReleaseFast`: exit 0.
- `follow.sh` against a stand-in pod: exits 0 at END, 4 without the process, 3 when unreachable.
Problems / lessons:
- RunPod removed the H100's container at 18:16 UTC (host-side; "container is unhealthy: dead"). The
  run's log, measurements and the proofs after the last half-hourly copy were lost. Outputs now go to
  the persistent volume, and `follow.sh` copies every 5 min and alerts within two missed checks.
- Two pods pulling the same 33 GB through the Mac at once halve each other's transfer.
- My node-side watcher waited for a log line `prove-epoch` never prints, so the node proved on its CPU
  for 74 min after the load; kill on the set file's appearance, not on the log.
Next: finish the epoch: a new H100 with `--skip` the 6 blocks and the 4,476 proofs (`--resume`,
~3.75 h, ~$17), then `verify-epoch --jobs` over all 10,000 on the Mac.

## 2026-10-15 (session 17) — Full-chain data: `replay`; its coin sets equal Core's UTXO set at all four assumeUTXO heights
Who: Claude (agent, Opus 5.5), with the owner (scope: the 10k-block rehearsal, data first; node resized to 64 GB)
Roadmap: full-chain data preparation built and run to 970,000; rehearsal data ready (960,001–970,000)
Done:
- 3435d0f: `fetch_undo.py --ctx` reads the creating block by the prevout's height, batched (382 s -> 29 s for
  block 969000; same bytes on ten blocks). Still ~21 s per recent block: about 1 GB of JSON.
- c0cc5df, 859fa9f: `replay` (src/block/replay.zig, src/bin/replay.zig) and scripts/stream_blocks.py. Raw
  blocks in, in order, each checked against its pinned header, Merkle root (mutation rule) and witness
  commitment; per block the undo stream and `.ctx`, and coin sets in `prove-epoch`'s format. The coin
  table is rehashed in place every capacity/4 removals.
- 5b08f4d, f59cb81, 732b1ff: scripts/replay_run.sh (on the node, `/data/replay`, `-Dcpu=neoverse_v1`).
- docs/design/block-data.md § Full-chain data.
- The stwo-zig pin d34b26903 is fetchable now (stwo-zig pushed it; a fetch by SHA from the submodule URL works).
Evidence:
- 0–1000: undo, ctx, blocks, set-170, set-1000 byte-identical to the node-fetched and `prove-epoch`
  files, also resumed from set-170. 0–250,000 over the tunnel: BIP30 undo streams equal testdata/undo.
- Whole chain on the node: `hash_serialized` equals `chainparams.cpp` at 840,000 (`a2a5521b…`, 176,948,713
  coins), 880,000 (`dbd19098…`), 910,000 (`4daf8a17…`), 935,000 (`e4b90ef9…`). Window 960,001–970,000 and
  set-960000 (166,295,599 coins) written; 969000–969008 equal the RPC-fetched files.
- `zig build test -Doptimize=ReleaseFast`: exit 0.
Problems / lessons:
- A generic aarch64 build lacks the SHA-256 instructions: 10x slower on the Graviton.
- `std.HashMap` tombstones under churn slowed the pass tenfold past 700k (fixed: periodic `rehash`).
- The checkpoints went to ~/replay on the node's 30 GB root disk and filled it (`WriteFailed`). Freed at
  once (recomputable checkpoints deleted); bitcoind, whose data is on /data, stayed in sync. Moved to /data.
- `pkill -f <pattern>` over ssh matched the ssh command line itself and killed the session: kill by PID.
Next: the 10k-block rehearsal (`cuda-epoch --from 960001 set-960000.bin`, ~7.2 GPU-h by the survey; the host
needs ~100 GB RAM for the epoch's raws and sets), then `chainproof verify-epoch` on it.

## 2026-10-15 (session 16) — Block prover: device witness phase 2 and batch proving; full chain's block proofs ≈ 325 H100-hours
Who: Claude (agent, Opus 5.5), with the owner (scope: "1 and 3", merge + push when verified, GPU budget $30)
Roadmap: GPU step 3 (CUDA): device witness phase 2 done; batch proving (`cuda-epoch`) done
Done:
- 0dc1416: `cuda-prove` compiles again with `-Dcuda=true` on main's stwo-zig pin (d34b26903 added
  `FriLayer.rows_per_leaf_log`; the pod run on 2026-10-14 built only `cuda-widenode`).
- 78bf486: device witness for `block_msg`, `block_walk`, `block_bytes` (`witness.zig`; `walk.plan` +
  `walk.columns`, `msg.descriptors`, `bytes.multiplicities`). M4 Pro at 2^23: host witness 1.55 -> 0.42 s,
  planned H2D 3.99 -> 0.85 GiB, peak footprint 4.5 -> 1.1 GB.
- 5c52c2d, f268d9d: `cuda-epoch` (src/gpu/cuda/epoch.zig), the GPU twin of `chainproof prove-epoch` over
  the shared `src/block/epoch_run.zig`; one `NativeRuntime` per process; `--mock`, `--verify`,
  `--heights` (standalone sample, testing challenge). `HT.Paths`: the header MMR folded once (window
  paths were a full fold per header, about 1 s per block, in both provers).
- 17a5565, 598a53f: one prepared device arena per size class (`witness.Inputs.fixed_capacity`,
  `openPreparedCachedRetained`); the cached plan uses a process allocator.
- docs/design/gpu-cuda.md § Phase 2, § Batch proving.
Evidence:
- `cuda-test` filter "cuda witness": kernels = CPU for the five components on blocks 0, 170, 91722,
  91812, 91842, 91880, 400000 (L 22), mutations caught, fixed-capacity layout, `.trace_generation` = CPU.
- `cuda-epoch --mock` 0..30 = `chainproof prove-epoch` (bytes); `chainproof verify-epoch` VERIFIED.
- Pod `jj6cafaqpb7q2b` (H100 SXM 80 GB, secure, $3.99/hr, 8 vCPUs): `run.sh` all byte-identical;
  400000 1.95 s, 970347 3.62 s, 774628 3.13 s to proof (were 5.3 / 11.0 / 9.2 s); epoch 0..100 device =
  CPU (101 proofs + coin set), 0.089 s/block; 37-block sample: all verified, 27 (L <= 19) = CPU;
  2^23 2.66 s/block, 2^22 1.41 s/block in one session. Pod deleted, `list-pods` empty.
- `zig build test -Doptimize=ReleaseFast`: exit 0 on the final tree; `zig build cuda-test -Dcuda=true`
  (all host-checkable CUDA tests): exit 0.
Problems / lessons:
- A retained CUDA session keeps freed arenas in the context's pool and the per-proof admission counts
  only driver-free memory: a 2^23 proof failed after a 2^22 one. Use the prepared execution cache.
- The cached plan outlived the per-block arena allocator (`ArenaSlotMissing` on the second block).
- zsh does not word-split `$var`: run multi-word loops under `bash -c`.
- main's stwo-zig pin d34b26903 is on no stwo-zig branch on GitHub: a fresh clone cannot check out the
  submodule; pods use `bundle.sh` tarballs until it is pushed there.
- stwo-zig replies (archived in docs/reports, 2026-10-15): `liftExtract` follow-up (merged as
  `lift-extract-2`: (W) proven for b2msg, fpwalk, urec; `mainOffs` = the verifier's offsets; the first
  `hashSysW_of_hard` kept verbatim, the four-component form is `hashSysW_of_hard4`); CUDA generic AIR
  (items 1–3 on the fork branch `feat/cuda-generic-air`, host-tested; they ask for our device runner
  against it, with our topology/masks/controller forks replaced by imports).
Next: overlap the host witness of block i+1 with the device proof of block i (GPU busy ~70 %); a pod run
of `cuda-prove` against stwo-zig `feat/cuda-generic-air`; then the per-level recursion shapes.

## 2026-10-14 (session 15) — CUDA remainder-fold fix verified on an H200; per-level shapes at 1.0 s of GPU per block
Who: Claude (agent, Opus 5.5), with the owner (pod funding)
Roadmap: BLOCK-REC wide nodes on GPU: per-level shapes validated (leaves 2^21, 8-child node 2^24)
Done:
- Device test of stwo-zig's remainder-fold fix (pod `30qsgjojbt7f7h`, H200 SXM, $5.29/hr, ~30 min):
  every run verified and byte-identical to the CPU circuit prover (`docs/design/block-rec.md` § Wide nodes):
  short last rounds of 1, 2, 3; fold 1; and `cuda-widenode C` (8 leaves at 2^21 + node at 2^24: 8.0 s GPU).
- Merged `gpu/remainder` (448d504). main (`9bda446`) has the `RecCR` restatements.
- stwo-zig's `liftExtract` patch applied on branch `lift-extract` (3e507d5) with their reply in
  `docs/reports/`; not yet built here (the owner builds it).
Evidence:
- Pod logs: runs `widenode-A-164_1_2_4_fold_4_last_0_cpu`, `widenode-A-164_1_fold_1_cpu`,
  `widenode-C-164_cpunode`, all `BYTE-IDENTICAL`, exit 0. Pod deleted.
Problems / lessons:
- H100 SXM and NVL capacity vanished between the capacity read and the create; the H200 create only
  succeeded without the CUDA-version and disk constraints.
Next: per-level shapes in `block_forest.zig` and the outer verifier; cache the static preprocessed hash.

## 2026-10-14 (session 14) — `Collision` is vacuous; per-instance restatements (RecCR); stwo-zig remainder-fold fix staged for a device test
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: VL-NODE: tree/forest soundness restated with named collisions (RecCR); GPU per-level shapes await the device test
Done:
- `Collision` (BlockRec) and `Mmr.Collision` are provable by pigeonhole, so every `… ∨ Collision`
  conclusion was vacuous (flagged by the stwo-zig session, confirmed in Lean). New `Circuit/RecCR.lean`:
  `TrustW`/`TrustKW` (witness functions instead of `∃`, equivalent to `Trust` by choice), and the tree,
  forest, epoch, wide-tree and header theorems with `Collides ps` over explicit message pairs. `Spec/Mmr.lean`:
  `inclusion_soundC`, `mmr_inclusionC`. Old theorems and `Compat.lean` unchanged; module docs note the vacuity.
  `docs/design/verifier-formalization.md` § correction.
- stwo-zig's remainder-fold fix (`fix/cuda-fri-remainder-fold` aacbb85cb, cherry-picked onto our pin
  4afa09dbf as d34b26903 in the `starked-bitcoin-gpuwide` worktree, branch `gpu/remainder`): reviewed
  (per-layer leaf packing, as the CPU prover and native verifier decide). `cuda-widenode` gains `A --last`
  and `C` (per-level shapes: 8 leaves at their common natural size, the 8-child node at its own). Plan-only
  run: blocks 164.. at k = 1, 2, 4 give trace logs 21, 22, 23, so last rounds of 1, 2, 3.
Evidence:
- `lake build` (whole library incl. `Compat`) passes; `#print axioms` for `collision_true`, `tree_soundW`,
  `forest_epochW`, `forest_epochVW`, `forestK_epochVW`, `header_root_soundW`, `Trust.exists_w`:
  propext, Classical.choice, Quot.sound.
- Pod `q22wlc9916ekx8` (session 13): $2.37 billed.
Problems / lessons:
- A disjunction with an existential `Collision` is only meaningful if `Collision` is not a theorem;
  over unbounded messages it always is. Name the pairs instead.
- The device run is blocked: RunPod refused a new pod (account balance too low).
Next: fund RunPod, then on an H100: `widenode.sh run A 164 1 2 4 --fold 4 --last 0 --cpu`,
`run A 164 1 --cpu` (fold 1), `run C 164 --cpu-node`.

## 2026-10-14 (session 13, GPU wide node) — 8-child wide node proved on an H100, byte-identical to CPU; CUDA fold 1 fails
Who: Claude (agent, Opus 5.5), with the owner (pod)
Roadmap: BLOCK-REC wide nodes: GPU validated at 2^24 (fold 4); per-level shapes blocked on CUDA fold 1
Done:
- `cuda-widenode` (`src/gpu/cuda/widenode.zig`, branch `gpu/widenode`, not pushed):
  - A: a leaf or packed circuit at its natural size, any fold.
  - B: 8 GPU block leaves at the shared 2^24 shape, then the 8-child node over them on the GPU.
  - A device proof becomes a `leaf.CircuitProof` child: the verified-capture verifier proof, the
    request and the circuit hash.
- Pod scripts: `widenode.sh build|run`, `bundle.sh` (a source tarball for an unpushed branch, 160 MB),
  and `NO_BUILD=1 bootstrap.sh`.
Evidence:
- RunPod H100 SXM 80 GB, sm_90 ($3.99/hr, about 45 min). Logs were kept outside the repo.
- B, blocks 164–171 (mixed 2^11 uniform and 2^12 tiered):
  - 8 leaves at 4.6 s each and the node at 4.4 s on the GPU.
  - The node's digest equals `block_node_k.expected`'s.
  - All 9 proofs pass both native verifiers and are byte-identical to the CPU proofs (CPU about 40 s each).
  - 45.65 GiB device memory. Table in block-rec.md § Wide nodes.
- A, block 0, fold 1, 2^21: the GPU proof is rejected, `FRI verification failed: FirstLayerCommitmentInvalid`.
  At fold 4: 1.55 s (k = 1) and 1.42 s (k = 2), the same SHA-256 as the Mac CPU proofs.
- Mac: `zig build -Dcuda=true cuda-widenode` (stubs) and `--plan-only` for A and B work;
  `zig build test -Dtest-filter="wide node"` passes 3/3.
Problems / lessons:
- The CUDA circuit prover's fold 1 doesn't work (first FRI layer commitment), so per-level shapes on the
  GPU wait for stwo-zig.
- The circuit verifier also rejects any last layer other than 0 (seen on CPU), so remainder-fold proofs
  can't be children.
- Base: in the main checkout `main` is 3815dd5; 4ec348e is `pack-join`'s HEAD, which this branch is based on.
- `widenode.sh`: `ls -t` with no files lists the cwd; that cost one failed link on the pod (fixed, aa2d97c).
Next: report the fold-1 failure to stwo-zig; per-level shapes; forest over `TreeK`.

## 2026-10-14 (session 13, wide nodes) — Full survey in: sizes mix, so the width goes into the node; wide node in Lean and Zig
Who: Claude (agent, Opus 5.5), branch `pack-join`
Done:
- Pushed the packing spike to main (518032e). Brief for stwo-zig: `~/Workshop/stwo-zig/CUDA_FRI_REMAINDER_FOLD_BRIEF.md` (untracked).
- Collected the full survey (971,298 blocks) and wrote it into chain-survey.md:
  - 87 H200 blocks: 84 are 22 uniform, and **3 are 24 tiered** (367851, 367853, 836361);
  - 998 uniform fallbacks.
- **Packing k block proofs into one leaf doesn't work for mixed sizes.** The leaf circuit depends on the tuple of the blocks' (L, profile), and only 7,906 of 60,706 aligned 16-block groups are uniform. Packing only those gives 1.6 blocks per leaf.
- **Wide node** (`2^a` child circuit proofs per node):
  - Lean `Circuit/BlockNodeK.lean`: `blockNodeK`, `joinT_sound`, `nodeK_sound`, `treeK_sound`, `forestK_soundP`, `forestK_epochV`; standard axioms only.
  - JSON `airs/block_node_k{1..4}.json`.
  - Zig `recursion/block_node_k.zig`, plus `blockpack widenode|nodecost|shapes`.
Evidence:
- 2 children (blocks 0–1): output = native digest = the binary node's; proved and verified in 15.1 s (CPU).
- 4 children: blocks 0–3, and blocks 168–171 (mixed 2^11 uniform and 2^12 tiered leaves). Both satisfied, with the output equal to the native digest.
- Swapped children and a wrong child key are rejected.
- One in-circuit child verifier: 12.6 M vars at fold 1, 6.4 M at fold 4.
- Shape fixpoints: block-rec.md § Wide nodes. 8 children at fold 4 fit 2^24.
- `zig build test -Dtest-filter="wide node"` passes.
- Re-proved block proofs 0–171 into `data/epoch-pack` (220 s); the old `data/epoch` ones are stale.
Problems / lessons:
- My earlier "~61k leaves" assumed mixed-size packing. Check the size distribution before costing a leaf design.
- One shared shape pads every leaf to the node's 2^24 (8× a 2^21 leaf).
  - Per-level shapes fix this, but they need natural trace logs at fold 4, which only the CUDA prover's remainder-fold bug blocks.
  - Correction, same day: what I first logged as an in-circuit verifier panic at fold 4 was my own config (last layer 3); the in-circuit verifier asserts last layer 0. At last layer 0 with a remainder round, the CPU prover, the native verifier and the in-circuit verifier all work. A 2-child node at fold 4: 7.3 s, 521 KB, against 15.1 s and 981 KB at fold 1.
  - Alternatively, fold 1 on the CUDA circuit prover (untested).
Next: one GPU session (CUDA circuit fold 1 at 2^21; the 8-child node at 2^24, fold 4), then per-level shapes and the forest over `TreeK`.

## 2026-10-14 (session 13) — Survey merged; leaf packing on GPU: 16 blocks per circuit proof on an H200
Who: Claude (agent), with the owner
Done:
- Pushed m3a5 to main with the chain survey merged (f7da4ec). Owner: the ~50 undo-heavy blocks that need
  uniform 2²² go to an H200 (no third profile).
- Leaf-packing spike (b61e15f and after): `block_pack` (k block proofs in one circuit), `blockpack`,
  `cuda-pack` on stwo-zig's resident circuit prover, `scripts/pod/pack.sh`.
Evidence:
- H200 pod (~37 min, $5.29/hr): k = 1, 2, 4, 8, 16 byte-identical GPU vs CPU; k = 16 proved in 11.5 s
  (0.72 s per block), 101 GiB device. Table in block-rec.md § Leaf packing measured.
Problems / lessons:
- CUDA FRI with a last fold of 1 gives proofs that fail verification; pick the last-layer bound so
  every fold is 4 (stwo-zig only qualifies fold step 4).
- stwo-zig's circuit archive and ours both name a set `circuit_eval`: cuda-pack links stwo-zig's own.
Next: the packed leaf's join (summaries in-circuit, Lean statement), then a node over packed leaves on GPU.

## 2026-10-13 (session 13, device witness) — CUDA: block_sha, block_b2s and tree 0 generated on the device (host-checked; device run pending)
Who: Claude (agent, Opus 5.5), worktree branch `cuda/device-witness`
Roadmap: GPU step 3 (CUDA): device witness for the three largest column sets implemented and host-checked; the pod run decides it
Done:
- 043a068: `buildFull` keeps `Built.sha_plan` (compressions + final Meta) and `Built.undo`; `skip_device_columns` leaves `mains[sha]`, `mains[b2s]` empty.
- 14e9c6c: `src/gpu/cuda/witness.zig`: four fixed AOT witness kernels (`sha_words`, `sha_columns`, `b2s`, `pre`; tag `native_indexed_recurrence_trace_v1`) run first in `.trace_generation` and write the staging slots in natural order; ingress uploads only their inputs (`witness_inputs`, 5–10 MiB) and skips the generated columns; SHA word scratch slot (`.trace_generation`). Arena unchanged. `gpu/cuda_aot` regenerated (84 AOT sources).
- 0ef9c19: `cuda-prove` uses the device witness by default; `--host-witness` for A/B; lean host witness with `--skip-cpu`/`--cpu-proof` (not with `--host-logup`). `scripts/pod/run.sh`: `large-prod-tiered-hostwitness`, `xl-970347-hostwitness`. docs/design/gpu-cuda.md § Device witness.
Evidence:
- `cuda-test` (new `witness_test.zig`): the exact kernel sources as host C++ reproduce `block_sha` (144), `block_b2s` (312) and tree 0 bit for bit for blocks 0 (uniform, tiered), 170, 91812, 91722, 91842, 91880, and SHA + Blake2s for 400000 tiered at L 22; two input mutations are caught; the whole `.trace_generation` (generators + reorder + LogUp gather) over block 0's real plans (uniform, tiered) with a lean host witness equals the CPU storage-order trees 0–1 and LogUp sources. Drift, catalog parity, LogUp, reorder, arena tests pass.
- `cuda-check`, `cuda-parity`, `cuda-archive-plan` (84 sources) pass; `zig build test` filters "golden hashes", "block system", "block sha", "SHA-256 AIR", "Blake2s AIR", "block commitment" pass; full suite `zig build test -Doptimize=ReleaseFast` green (35.5 min, 11.4 GB peak RSS).
- `cuda-prove --skip-cpu --profile production --size tiered` (M4 Pro, stub link, stops at session open), device witness vs `--host-witness`: 400000 (2^22) witness 0.79 vs 1.27 s, planned H2D 2.00 vs 6.46 GiB, peak footprint 2.30 vs 7.16 GB; 970347 (2^23) 1.55 vs 2.94 s, 3.99 vs 12.92 GiB, 4.50 vs 14.21 GB.
Problems / lessons:
- None blocking. The kernels passed the host comparison the first time; the mutation check was added to make sure the comparison is live.
Next: pod run on this branch: `scripts/pod/run.sh` (block 0 ×4 against the CPU proof, 400000), `large-prod-tiered-hostwitness`, `xl-970347`, `xl-970347-hostwitness`, `xl-774628`; record the witness lap, ingress, `.trace_generation` time and host RSS.

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

## 2026-10-13 (session 13, night) — Device witness validated: 2^23 block proved in 9–11 s on one H100
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: GPU step 3 (CUDA): device witness phase 1 (SHA, BLAKE2s, preprocessed) merged from `cuda/device-witness`
Done:
- H100 PCIe pod (16 vCPUs, ~14 min, ≈ $0.66): every step byte-identical and verified, incl. A/B with `--host-witness` and `--host-logup`. Time to proof: 400000 5.3 s (12.7 s with the host witness on the same pod), 970347 11.0 s (32.2 s), 774628 9.2 s. H2D at 2^23: 3.99 GiB (12.92); host RSS 14.2 GB (23.7).
Next: the remaining host witness (3–6 s: fields, msg, walk, coin, …), ingress variance; aggregation on GPU (stwo-zig circuit pipeline spike).

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
