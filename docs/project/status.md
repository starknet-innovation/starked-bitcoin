# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-05 (session 30: SEAL-LEAN, the seal's soundness composed)
- **HEAD at last update:** d8b53cd (D-051 accepted, pushed) plus this session's commits
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** SEAL-LEAN done (2026-11-05): `seal_soundW` (`lean/StarkedAir/Circuit/ChainSealCompose.lean`)
  states what one accepted seal proof gives: a valid chain of epochs, per epoch the end and start sets as
  proven passes under the epoch's challenge with the balance, the finishes to `fin`/`prev` and the
  ranges, and the end facts; or a named Blake2s collision. Next: SEAL-T. This session's commits are not
  pushed (D-016).

## State in one paragraph

The header chain from genesis to 972,502 is one proof (`data/store/mainnet-to-972502.sbchain`; compact
0.99 MB, D-049). Blocks 935,001–972,500 (two epochs) are one chain proof (`prove-chain`/`verify-chain`,
D-047 pinned VKs), and their three boundary coin sets are four set-pass proofs (D-048, pinned
`vk/epoch/set-l22.vk`). The chain seal (D-051, [chain-seal.md](../design/chain-seal.md)) verifies the
last join and the four set roots in-circuit and checks there what `verify-chain --set-proofs` checked
natively: 164,539,066 coins after 972,500, 2,010,133,549,560,777 sat, Merkle root `f74e9573…`,
`hash_serialized 9f92d143…` = Core's, from Core's assumeUTXO set after 935,000. Membership (D-050) is
proven; the 66 bridge coins are bound to the proven set. Lean: every project theorem on standard axioms,
including the seal's composed statement (`seal_soundW`); trusted items in [verification.md](../reference/verification.md).

## Next step (concrete)

1. **SEAL-T** ([chain-seal.md § Next fold](../design/chain-seal.md#next-fold-the-header-root-and-t)):
   the header root as a child (`HeaderRec` opening, the genesis checks as constants), MMR inclusion per
   epoch child with sides from the bits of the position and the leaf count (`Spec/Mmr.lean` `sides`).
   Then extend `seal_soundW` (its hypotheses on `c` would come from the header root instead of the
   verifier).
2. Backlog: BLOCK-VK, SET-VK-SETUP, profile `verify-seal`/`verify-chain` on the node.

## In flight

- Nothing uncommitted after this session's commits; they are not pushed. No pod is running.
- Mainnet seal inputs and output on the Mac under `data/seal972/` (gitignored `data/`): `out/seal-972500.bin`,
  `out/sealvk.bin`, the chain file, the join and tree VKs, the four passes' `pass.bin`/`setvk.bin`. On the
  node: `join972b/out/{seal-972500.bin,sealvk.bin}`, the binary `chainproof-seal`, `setgpu/verifyseal972.log`.
- The test chain's five passes were re-proved (twelve logs); its seal is `data/test-chain/out/seal-15.bin`.

## Needs owner

- **Push `main`** (D-016): this session's SEAL-LEAN commits.
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
#print axioms StarkedAir.Circuit.ChainSeal.compressFinal_sound
#print axioms StarkedAir.Circuit.ChainSeal.checks_epoch
#print axioms StarkedAir.Circuit.ChainSeal.seal_digest
#print axioms StarkedAir.SetPass.set_root_soundW
#print axioms StarkedAir.Circuit.ChainSeal.seal_soundW
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

scripts/check_air_drift.sh                 # expect: every airs/*.json "ok" (90 files, ~10 min; AIRs and circuit programs)

# The mainnet seal (inputs under data/seal972/, see "In flight"), pinned VKs only:
zig-out/bin/chainproof verify-seal data/store/mainnet-q70-p26-l20.vk data/store/mainnet-to-972502.compact.sbchain data/seal972/out data/seal972/e945:945000:935001:none data/seal972/e972:972500:945001:none
# expect: "VERIFIED blocks 935001..972500 as one sealed proof: the coin set after block 972500 is 164539066 coins"
zig-out/bin/chainproof setup-seal-vk /tmp/sealvk data/seal972/out/chain-972500.bin vk/epoch/join-935001-972500.vk data/seal972/passes/s972500
# expect: "seal VK remade: trace 2^24 (…); it equals the pinned one"

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors outside data/ (it also scans the gitignored data/core-src, Core's own broken links)
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
