# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-12, overnight (VL table done but FRI/NODE decisions; BLOCK-REC built end to end at small scale)
- **HEAD at last update:** see `git log -1` (this file is committed with the work)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** BLOCK-AIR complete: M3a.5 (`block_sound`) and M3a.6 (`commit_sound`) done and
  proven (2026-10-10). Next: BLOCK-DATA. For the owner: D-035's amendments (8-bit range table; `prevMtp`
  as two public limbs, a soundness fix) and D-038 (the commitment format, proposed).

## State in one paragraph

The whole mainnet header chain is proven and **saved** as a file that verifies standalone and extends
at the tip:
- `data/store/mainnet-0-970347.sbchain` (12.8 MB), and `mainnet-to-970734.sbchain` after extension;
- the pinned VK is in `vk/`, and `chainproof verify mainnet <file>` checks it;
- `T` and the tip are checked against an independent recomputation and your node.

Lean proves the chain end to end at the public-input level (`chain_from_genesis_checked`), plus:
- the MMR inclusion and fold (`Spec/Mmr.lean`);
- LogUp's Schwartz–Zippel step (`LogUpSZ.lean`);
- the block rules as a conjunction (`Spec/BlockFlat.lean`);
- **`block_sound`**: a satisfied block system proves `checkBlock c raw = none` (Core's `CheckBlock`
  without PoW, and `ContextualCheckBlock`), given no repeated prevout (M3b's obligation, D-031);
- **`commit_sound`**: its public inputs 9–24 are `blake2s(blake2s(raw) ++ blake2s(undo))` (D-038).

The plain in-circuit verifier is mutation-fuzzed (102k mutations, all rejected). The specs are fuzzed
against Core's own C++ (about 860k cases, 0 mismatches).

## Next step (concrete)

**M3b (UTXO, D-040) is built and running at small scale.** The block system has 15 components (coin
events, undo records, segment fingerprints). `chainproof prove-epoch` / `verify-epoch` prove the coin set
after block N from genesis. Measured: blocks 0–170 proved in 209 s (production strength); the epoch
verifies to a 171-coin set of 850,000,000,000 sat; a tampered set is rejected.

Proven in Lean (standard axioms):
- **Spec:** `run_of_balance`, `epoch_sound`, `connect_of_run` (Core's coins view), QM31 is a finite field;
- **Components:** `extsum_sound`, `seg_sound`, `rows_sound` (undo records);
- **System:** `block_sound`, `commit_sound`, `hash_pub` still hold for the 15-component system
  (`L ≤ 23`, 216 lookup sites per row);
- **The coin component, end to end (2026-10-11):** `epoch_systems_core`: block systems at consecutive
  heights sharing the epoch's challenge, with a balanced public sum (outside the fingerprint and LogUp
  bad sets), connect as Core does from the initial view and end at exactly the final set; every block
  then passes Core's block checks (`epoch_block_valid`, D-031 from the run). Plan and lemma map in
  utxo.md, "The coin proof".

**Soundness fixes from the coin proof:** amount comparators could wrap mod P (2026-10-10); and D-041
(2026-10-11): the final set, the initial set's indices, each input's claimed creating transaction and the
undo records' boundaries were all chosen after the epoch challenge. Now the seed binds both sets'
encodings and the undo records commit their index and length. Epochs 0–170 and 171–1000 re-prove and
verify under the new protocol (same `hash_serialized`).

Not yet:
1. The coin theorem's hypotheses (updated 2026-10-12): `WFE` remains only for the initial and final sets
   (the verifier's decoded data; `decodeSet` checks the ranges) — created and spent events are proven
   (`epoch_systems_wf`); the events are **proven** functions of the committed data (`claim_at_input`, D-041
   in Lean); distinct created outpoints reduce to distinct txids (`created_nodup_of_txids`), which is the
   stated assumption (SHA256d collision resistance, BIP34/BIP30; utxo.md).
2. ~~The fingerprint's Schwartz–Zippel step~~ (done 2026-10-10).
3. The final sorted pass as a proof (`HASH_SERIALIZED` in-circuit). For now the verifier computes
   the final set's fractions and hash natively from an explicit, sorted coin list. Fine at height
   1,000; at a snapshot height that list is ~13 GB. Deprioritized (2026-10-11): a node using
   assumeUTXO already holds the snapshot file, so a verifier with it checks the set natively without
   trusting anyone; in-circuit only makes the proof succinct, and its cost is compute-bound at that
   scale anyway.
4. ~~Epochs that start from a previous set~~ (done 2026-10-11: `--from <a> <prev-set>`, the previous
   set's hash in the seed, `epoch_from_sound`; 0..170 then 171..1000 verify and match the genesis run's
   hash). The aggregator as a circuit (`BLOCK-REC`) is still to do.
5. **CATCHUP:** a compute wall. Full blocks need lifting or a larger machine, and the in-memory check
   of a 1 MB block already took ~14 GB before M3b's extra ~190 columns.

**Also scheduled (owner, 2026-10-11):** the remaining VERIFIER-LEAN work, as the
[VL table in the roadmap](roadmap.md#vl-the-in-circuit-plain-verifier-proven-verifier-lean):
VL-E2E, VL-POW, VL-OODS and VL-ORACLE are **done** (2026-10-11: `plain_sound`, `plain_leaf_valid`,
`powCheck_sound`, `shift_sound`, `zig build oracle`).

**BLOCK-REC (2026-10-12, overnight):** the block-proof aggregation runs end to end at small scale — block
leaves (the plain verifier over the 15-component block system, 8.3 M variables, 5 s to prove), block
nodes, an epoch as a forest of trees over the seed v3 decomposition, and an outer verifier
(`chainproof prove-epoch-tree` / `verify-epoch-tree`; epoch 0–3 verified, tampers rejected; **epoch 0–170
through 5 recursion trees: proved in 90 min, verified in 0.6 s, same coin set `7105b60f…`**); **epoch 171–1000 through 11 recursion trees: proved in 7.2 h on the 24 GB Mac (830 leaves, peak footprint 40.7 GB), proof 10.8 MB, verified in 1.4 s (vs 63.8 s for the 830 flat block proofs), same coin set: 998 coins, `hash_serialized 29a42ec2…` = Core's**. Lean: `SumOk`, `sumOk_leaf`, `sumOk_node`, `rng_forest`, the leaf's checks and context. Needs
the owner: **D-043** (proposed) — the seed v3 is implemented (forced by recursion), the previous-block
MTP (part 3) is not bound until the owner picks option A or B. VL-FRI and VL-NODE are trust-boundary decisions waiting on the owner. And **D-042** (owner): the hybrid UTXO tip tree is
scheduled as `UTXO-TREE`, the aggregator as `BLOCK-REC` — design in
[block-rec.md](../design/block-rec.md); freeze the block-proof interface before CATCHUP.

## In flight

- Nothing.

## Needs owner

- **Pushing:** `main` was pushed to the private repo starknet-innovation/starked-bitcoin on 2026-10-10, on the owner's go. Each later push still needs the owner's approval (D-016).
- **M3 node:** available (data source only; proving stays on the Mac). Credentials are in `prove-any-chain/.env.local`, never committed.
- **LICENSE:** none chosen.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? This is outward-facing.

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
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle byte_table byte_user blake2s_compress blake2s_tree header_chain_v7 node_glue leaf_glue block_bytes block_reader block_fields block_msg block_sha block_merkle block_tables block_walk block_ctx block_wmerkle block_undo block_b2msg block_b2s extsum_test genesis_checks; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
