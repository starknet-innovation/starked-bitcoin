# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-07 (session 33: SEAL-T-LEAN)
- **HEAD at last update:** this session's commit (f42d5d5 and the next; not pushed)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** none in progress. SEAL-T (D-052, accepted 2026-11-09) is proved on mainnet, pinned,
  and its soundness is composed in Lean (`sealT_soundW`, `Circuit/ChainSealTCompose.lean`, standard axioms).

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

1. Optional: the test chain's SEAL-T proof (81.8 M variables, ~17 GB: more than the Mac has free; a pod).
2. Optional, Lean: discharge `MmrT` (HC-HASHTREE's shape binding) by carrying the tree shape through
   `htree_soundW` (`RecCR.lean`) and `fold_eq_mmr` (`Spec/Mmr.lean`).
3. Backlog: SET-VK-SETUP (needs one mainnet segment proof from the node), profile `verify-seal`/`verify-chain` on the node.

## In flight

- Nothing uncommitted after this session's commit. No pod is running.
- Mainnet seal inputs and outputs on the Mac under `data/seal972/` (gitignored `data/`): `out/` (D-051
  seal), `outT/` (SEAL-T seal, `sealvk.bin`, copies of the chain file and join VK), `outTamper/` (tamper
  scratch, deletable), the join and tree VKs, the four passes. On the node: the D-051 seal only.

## Needs owner

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
#print axioms StarkedAir.Circuit.ChainSeal.pathOps_sound
#print axioms StarkedAir.Circuit.ChainSeal.sealT_cpath
#print axioms StarkedAir.Circuit.ChainSeal.sealT_soundW
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

LAKE=~/.elan/bin/lake scripts/check_air_drift.sh   # expect: every airs/*.json "ok" (90 files, ~10 min; AIRs and circuit programs)

# The mainnet seal (inputs under data/seal972/, see "In flight"), pinned VKs only:
zig-out/bin/chainproof verify-seal data/store/mainnet-q70-p26-l20.vk data/store/mainnet-to-972502.compact.sbchain data/seal972/out data/seal972/e945:945000:935001:none data/seal972/e972:972500:945001:none
# expect: "VERIFIED blocks 935001..972500 as one sealed proof: the coin set after block 972500 is 164539066 coins"
zig-out/bin/chainproof setup-seal-vk /tmp/sealvk data/seal972/out/chain-972500.bin vk/epoch/join-935001-972500.vk data/seal972/passes/s972500
# expect: "seal VK remade: trace 2^24 (…); it equals the pinned one"
# SEAL-T (D-052), pinned VK, header chain in-circuit:
zig-out/bin/chainproof verify-seal data/store/mainnet-q70-p26-l20.vk data/store/mainnet-to-972502.compact.sbchain data/seal972/outT data/seal972/e945:945000:935001:none data/seal972/e972:972500:945001:none
# expect: "seal VK …: pinned (vk/epoch/sealt-935001-972500.vk)" and "VERIFIED blocks 935001..972500 as one sealed proof"
zig-out/bin/chainproof setup-seal-vk /tmp/sealvkT data/seal972/outT/chain-972500.bin vk/epoch/join-935001-972500.vk data/seal972/passes/s972500 --paths 32 data/store/mainnet-q70-p26-l20.vk
# expect: "seal VK remade: trace 2^24 (…); it equals the pinned one"

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors outside data/ (it also scans the gitignored data/core-src, Core's own broken links)
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
