# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-03 (session 28: the fourth set pass; chain, sets and bridge coins verified together)
- **HEAD at last update:** 15e6705 (the 2026-11-02 docs commit) plus this session-log commit
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** SET-PASS (D-048) is complete. All four real passes are proved and verified with
  the pinned set VK, and on 2026-11-03 `verify-chain --set-proofs --members` on the node verified the
  chain proof, both epochs' balances and 66 strkBTC-bridge coins together, with no set file and every VK
  pinned. Everything is on `main`; `origin/main` is behind by this session's and the previous session's
  commits (push: owner, D-016).

## State in one paragraph

The header chain from genesis to 972,502 is one proof (`data/store/mainnet-to-972502.sbchain`; compact
0.99 MB, D-049). Blocks 935,001–972,500 (two epochs) are ONE chain proof (`prove-chain`/`verify-chain`,
D-047 pinned VKs): 164,539,066 coins after 972,500, `hash_serialized 9f92d143…` = Core's. The coin-set
pass (D-048) replaces the verifier's set files: the sets after 935,000 and 945,000 under epoch 1's
challenge and after 945,000 and 972,500 under epoch 2's are proved on H200s and verified under the pinned
`vk/epoch/set-l22.vk`. Membership (D-050) is proven (`set_root_sound`): the 66 bridge coins
(13,689,057,287 sat under the 3-of-5 P2WSH) are bound to the chain-proven set after 972,500. Lean:
every project theorem on standard axioms; trusted items in [verification.md](../reference/verification.md).

## Next step (concrete)

1. **Fold the balance check and the header root into the join** (set-pass.md "later"), so one root proof
   covers the chain, the blocks and the sets: start from `lean/StarkedAir/Circuit/EpochJoin.lean` and
   `src/recursion/epoch_join.zig` (the join already verifies epoch roots in-circuit; add the set-pass
   roots as children and the balance equations; the header root as one more child). New circuits mean
   new pinned VKs (reviewed commit, D-047).
2. Backlog items opened on 2026-11-02: BLOCK-VK (pin `blockvk.bin` like the epoch layers), SET-VK-SETUP
   (remake the set VK from public inputs). Then profile `verify-chain` on the node.
3. For the next set pass, decide the pod's data path first (log.md session 28): a pull from the node
   needs a credential on the pod; a push through the pod's exposed port runs at ~1 MB/s.

## In flight

- Nothing uncommitted. No pod is running (`list-pods` empty, 2026-11-03 08:50 UTC).
- The node (`/data/replay`) holds the four passes (`setgpu/passes/s935000`, `s945000` under epoch 1,
  `s945000c2` under epoch 2 with pass/VK/challenge only, `s972500`), `bridge-972500.sbmember`, the chain
  files, and the logs `setgpu/node945.log`, `verifyset945c2.log`, `final945c2.log`. The `s945000c2`
  segment files (~8 GB) were not fetched (they are only needed for membership proofs against that set).
- Branches `rec/epoch-root` and `gpu-set` are merged into `main` and kept until the push; delete after.

## Needs owner

- **Push `main`** (D-016): 27fc228 and the commits of 2026-11-02 and 2026-11-03.
- **Block VK pinning (BLOCK-VK):** `verify-block` still reads `blockvk.bin` from the prover's directory.
- **Data path for pods:** a deploy key for pods on the node (removed after each run) or another pull route.
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
