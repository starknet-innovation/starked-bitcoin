# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-11-24 (sessions 46 and 46b: what a run from genesis needs. A real time lock proved; ANC-PRE-CSV (D-060); the recursion delivers `epoch_systems_coreS`'s hypotheses (`Circuit/RecCtx.lean`); the `tight` size profile (D-061))
- **HEAD at last update:** this session's commit on branch `connect-rules` (after b319bfb, which is `main` and pushed)
- **Branches:** `main` = c83ddb1 (pushed): the AIRs of the published proofs. `connect-rules` (pushed to b95fe45; this session's commit is local): CONNECT-RULES steps 2–5, ANC-PRE-CSV, `tight`; its AIRs give other block VKs; merge it when the re-prove is made (or when the owner says).
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** WEB-MEMBER is live as an unannounced preview at https://starknet-innovation.github.io/starked-bitcoin/ (set file and index on Cloudflare R2, r2.dev URL; [web/README.md](../../web/README.md) "Live deployment"). Open: custom domain for the bucket, external review before announcing. TIP-ITER not started. NODE-BOOT step 1 done: `chainproof verify-snapshot` ([node-boot.md](../guides/node-boot.md)); Core's `dumptxoutset` at 972,500 VERIFIED against the seal on the node.
  SEAL-T (D-052, accepted) is proved on mainnet and the test chain, pinned, and composed in Lean
  (`sealT_soundW`) with the header tree's MMR shape now proven (`Circuit/HeaderShape.lean`).

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

**Owner's order (2026-11-19): A–D below come before items 0–3.**

A. CONNECT-RULES ([connect-rules.md](../design/connect-rules.md)), on branch `connect-rules`. Steps 1–5 are built, proven in Lean and device-checked. Session 46 added what a run from genesis needs (connect-rules.md, "After step 4"): three real time-locked blocks proved (test on block 947,544); `block_anc` from height 11 (D-060); `RecCR.forest_epochCW` (`lean/StarkedAir/Circuit/RecCtx.lean`): the recursion delivers every block hypothesis of `epoch_systems_coreS`. **Owner's direction (2026-11-23): the goal is a proof from genesis; no re-prove yet.** **Next step:** (1) TIERS-GEN: the needs of blocks 0–492,992 are in `data/survey/needs-0-492992.csv` (local; the node's run was killed there by its 16 GB). On them `tight` saves nothing from height 100,000 on (taken by 1–6 % of blocks): blocks before segwit want their own offsets. Get the needs of 492,993–935,000 on a machine with more memory (a CPU pod, as the replay of 945,001–972,500 was; owner's go, cost), then search profiles per era with `scripts/tier_search.py`. (2) done 2026-11-24 (log session 46b): on an H100 the 2^23 block takes 2.40 s under `tight` against 3.46 s under `tiered`, 34.9 GiB against 55.5; device proofs byte-identical to CPU after D-060. Open limits: SET-TIME (snapshot starts only), heights 0–10 (D-060), REC-CORE (one theorem from the seal to the rules).
B. SNAP-HASH: [snapshot-hash.md](../design/snapshot-hash.md) is drafted. The Delving follow-up, posted by the owner on 2026-11-20 (draft: `~/Workshop/prove-any-chain/delving-3070-reply3.md`: cost split, the SHA-256/Blake2s correction, the hash proposal). No circuit work before a reaction.
C. TIERS-2 (D-055, D-061): built. `tight` proves 39.1 % fewer cells than `tiered` on 935,001–972,500 and plans 34.9 GiB for a 2^23 block (tiered: 55.5). GPU-timed 2026-11-24 (31 % less device time on a 2^23 block). Open: the offsets on the whole chain (TIERS-GEN).
D. The proof run: the owner wants the run from genesis (2026-11-23), not started. Before it: TIERS-GEN, the GPU timing, a cost estimate for the owner, and the choice of epochs. Re-proving 935,001–972,500 alone would keep the snapshot limit of D-059 on time locks.

0. WEB-MEMBER: move the bucket to a custom domain (owner) and update `SET_URL`/`INDEX_URL`; external review before announcing. Upstream: fix stwo-zig `composition_aot_build.zig` (host codegen imports the target `stwo_core`), then move CI back to x86.
1. TIP-ITER ([roadmap.md](roadmap.md), "Now"): design the repeatable extension of the seal past 972,500:
   the header chain from `data/store/mainnet-to-972502.sbchain` (PROOF-STORE `--from`), new block proofs
   and an epoch from 972,501, rejoin (`prove-chain`), the next set pass, `prove-seal --paths 32`; estimate
   compute first (block proofs: [gpu-route] figures in [gpu-cuda.md](../design/gpu-cuda.md)).
2. NODE-BOOT step 2: a Core patch that loads a seal-attested snapshot (`validation.cpp` `PopulateAndValidateSnapshot` checks the hash against `chainparams` `m_assumeutxo_data`) and skips background validation (D-053, owner 2026-11-13); release after external review. STARKNET-PATH is backlog.
3. Backlog: SET-VK-SETUP, profile `verify-seal`/`verify-chain` on the node.

## In flight

- Nothing uncommitted after this session's commit except `AGENTS.md` (not the agent's change). No pod is running. The work tree is on branch `connect-rules`. Nothing is running on the node; `/data/replay/needsrun/` (the needs csv, logs) and `/data/replay/{replay-needs,needs_run.sh}` can be deleted.
- On the node: `/data/bitcoin/utxo-972500.dat` (Core snapshot, 9.4 GB), `~/snap/` (arm64 `chainproof`, seal inputs, `dump.sh`, `dump.log`); keep for NODE-BOOT step 2, delete after. Also in `~/snap/`: `survey`, `survey2`, `survey3`, `pack.py`, `needs.csv`, `bip68.csv`, `rules.csv`, `tlcheck.py`, `tlcheck.out` (sessions 39 and 40's measurements; can be deleted, `needs.csv` is the input of `scripts/tier_search.py`).
- Mainnet seal inputs and outputs on the Mac under `data/seal972/` (gitignored `data/`): `out/` (D-051
  seal), `outT/` (SEAL-T seal, `sealvk.bin`, copies of the chain file and join VK), `outTamper/` (tamper
  scratch, deletable), the join and tree VKs, the four passes. On the node: the D-051 seal only.

## Needs owner

- **D-060** ([decisions.md](decisions.md)): confirm the form of ANC-PRE-CSV: on from height 11, keyed on the public height; coins created at heights 0–10 keep time 0 (a security statement to check: harmless only because of the chain's timestamps); three `Compat.lean` statements restated. D-059 was confirmed by the owner on 2026-11-23 ("I'm ok with 1").
- **D-061**: the `tight` profile's offsets and rule. And the go for a CPU machine with 64 GB to finish the whole-chain needs (TIERS-GEN).
- **Push:** `connect-rules` is pushed up to a2e1454; the docs commit of session 46b is local.
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
#print axioms StarkedAir.HeaderTree.planTree_fill
#print axioms StarkedAir.Circuit.RecCR.htree_soundWS
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
