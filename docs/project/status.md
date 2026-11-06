# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-06 (session 32: SEAL-T proved on mainnet, verified, VK pinned)
- **HEAD at last update:** 1fccc06 (pushed) plus this session's commit
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** SEAL-T-LEAN. SEAL-T (D-052, proposed) is proved on mainnet 935,001–972,500
  (`data/seal972/outT/seal-972500.bin`: 69.5 M variables, 2^24, 131 s, 14.3 GB, 631 KB), verified in
  0.2 s with the header root, genesis checks and block-hash paths in-circuit, its VK pinned
  (`vk/epoch/sealt-935001-972500.vk`) and remade by `setup-seal-vk --paths 32`. Its gadgets are proven
  (`Circuit/ChainSealTSound.lean`); their composition into the seal theorem is not.

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

1. **SEAL-T-LEAN:** in a new file `lean/StarkedAir/Circuit/ChainSealTCompose.lean`, state `sealT_soundW`:
   `seal_soundW`'s conclusion plus "every epoch child's block-hash root is the MMR subtree of the header
   chain at its position", from `sealT_cpath`/`sealT_gpath` (paths reach `T`), the header tree's trust record
   (`TrustK`-style for `hdrChild`'s digest) and `Spec.Mmr.mmr_inclusionC`. Child roots sit at level `k`, so
   a subtree version of `mmr_inclusionC` is needed first (`Spec/Mmr.lean`).
2. Optional: the test chain's SEAL-T proof (81.8 M variables, likely ~17 GB: more than the Mac has free).
3. Backlog: SET-VK-SETUP (needs one mainnet segment proof from the node), profile `verify-seal`/`verify-chain` on the node.

## In flight

- Nothing uncommitted after this session's commit. No pod is running.
- Mainnet seal inputs and outputs on the Mac under `data/seal972/` (gitignored `data/`): `out/` (D-051
  seal), `outT/` (SEAL-T seal, `sealvk.bin`, copies of the chain file and join VK), `outTamper/` (tamper
  scratch, deletable), the join and tree VKs, the four passes. On the node: the D-051 seal only.

## Needs owner

- **Review D-052** (SEAL-T, proposed): proved and pinned now; acceptance is the owner's.
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
