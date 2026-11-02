# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-02 (session 27: hygiene pass)
- **HEAD at last update:** 27fc228 (the `gpu-set` merge), plus the two commits of 2026-11-02 that follow it (the set VK pin, then this session log)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** SET-PASS (D-048, [set-pass.md](../design/set-pass.md)): one of the four real passes is
  still to prove. Everything is on `main` (27fc228 + this session's commits): `rec/epoch-root` and
  `gpu-set` are merged, the stale worktrees are gone, the set VK is pinned.

## State in one paragraph

The header chain from genesis to 972,502 is one proof (`data/store/mainnet-to-972502.sbchain`; compact
0.99 MB, D-049). Blocks 935,001–972,500 (two epochs) are ONE chain proof (`prove-chain`/`verify-chain`,
D-047 pinned VKs), verified on the node on 2026-10-26: 164,539,066 coins, `hash_serialized 9f92d143…` =
Core's. The coin-set pass (D-048) replaces the verifier's set files: three of its four passes are proved
on H200s and verified on the node (sets after 935,000 and 945,000 under epoch 1's challenge, 972,500
under epoch 2's). Membership (D-050) is built and proven (`set_root_sound`); 66 strkBTC-bridge coins
(13,689,057,287 sat under the 3-of-5 P2WSH) verify against the 972,500 pass. Lean: every project
theorem on standard axioms; trusted items in [verification.md](../reference/verification.md).

## Next step (concrete)

1. **The missing pass** (needs the owner's go, ≈ $55 on an H200): the set after 945,000 under epoch 2's
   challenge `ch-972500`. On the node: `/data/replay/setgpu/` has `ch-972500.bin`, the pod runbook is
   [gpu-cuda.md § Set pass](../design/gpu-cuda.md) (`scripts/pod/prove_set.sh run s945000-ch972500
   <set-945000.bin> <ch-972500.bin> …`). Then point `tree972/pass-945000` at the new pass and rerun
   `/data/replay/setgpu/final972.sh` (verify-set, set-member of the bridge coins, `verify-chain
   --set-proofs --members --witness-script`): expect VERIFIED for both epochs. Before that, change no AIR
   and nothing in the challenge derivation (the three existing passes would go stale).
2. Then: profile `verify-chain`; fold the balance check and the header root into the join (set-pass.md
   "later"); BLOCK-VK and SET-VK-SETUP from the backlog.

## In flight

- Nothing uncommitted after this session's commits. The node (`/data/replay`) holds the three passes
  (`setgpu/passes/s{935000,945000,972500}`, ~8 GB each), `bridge-972500.sbmember`, the chain files and the
  new binary `chainproof-setvk-pin` (built from this session's tree, aarch64).
- Branches `rec/epoch-root` (origin at 287b9a3…9fec17f…) and `gpu-set` are merged into `main` and kept
  locally until `main` is pushed; delete them after.

## Needs owner

- **Push `main`** (27fc228 and this session's commits; `origin/main` is at 06d7bf7): D-016.
- **The missing pass:** ≈ $55 of H200 time (see Next step 1).
- **Block VK pinning (BLOCK-VK):** `verify-block` still reads `blockvk.bin` from the prover's directory.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? Outward-facing.

## Verify the current state

Run from the repo root. All must pass before new work starts.

```sh
git status --short                      # expect: clean, or explained under "In flight"
zig build test -Doptimize=ReleaseFast --summary all 2>&1 | grep "tests passed"   # expect: all pass (about 45 min; large blocks are slow)
(cd lean && lake build)                 # expect: "Build completed successfully"
grep -rnE "\bsorry\b|native_decide|bv_decide" lean/StarkedAir   # expect: no matches

cat > /tmp/ax.lean <<'EOS'
import StarkedAir
open StarkedAir.HeaderChain StarkedAir.Spec.Bitcoin
#print axioms header_chain_sound
#print axioms StarkedAir.Sha256.compress_sound_air
#print axioms pub_compose
#print axioms chain_from_genesis
#print axioms StarkedAir.HeaderTree.chain_from_genesis_T
#print axioms StarkedAir.Circuit.node_compose
#print axioms StarkedAir.Block.Fields.fields_sound_gen
#print axioms StarkedAir.Block.merkle_sound
#print axioms StarkedAir.Block.wmerkle_sound
#print axioms StarkedAir.Block.block_sound
#print axioms StarkedAir.Block.commit_sound
#print axioms StarkedAir.Block.hash_pub
#print axioms StarkedAir.SetPass.set_seg_sound
#print axioms StarkedAir.SetPass.set_seg_root
#print axioms StarkedAir.SetPass.set_root_sound
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

scripts/check_air_drift.sh                 # expect: every airs/*.json "ok" (88 files, ~10 min; AIRs and circuit programs)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors outside data/ (it also scans the gitignored data/core-src, Core's own broken links)
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
