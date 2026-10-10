# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-10 (owner away 48 h; agent working through the agreed priorities)
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

BLOCK-DATA is built (`hash_pub` proven; `chainproof prove-block` / `verify-block`; D-039 proposed).
Measured: block 170 proves in 0.6 s (544 KB) and verifies against the mainnet chain proof. Block
400000 (949 KB, 1,660 txs, undo 182 KB) builds a 2²² trace that satisfies all constraints in 235 s.
Proving it was stopped for low memory on the 24 GB Mac (the in-memory check already needed ~14 GB).

1. **Owner decisions:** D-035 amendments, D-038 (commitment format), D-039 (block proof file),
   **D-040 (M3b: multiset argument instead of a per-block tree, decides `Q-TREE`)**.
2. **M3b** after D-040: the coin-event component, `z` from the commitments' MMR, the final sorted pass
   (`HASH_SERIALIZED`).
3. **Memory/CATCHUP:** full blocks need lifting (per-component sizes) or a larger machine; catch-up
   from genesis needs a proving cluster, not this laptop ([utxo.md § Compute wall](../design/utxo.md)).

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
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle byte_table byte_user blake2s_compress blake2s_tree header_chain_v7 node_glue leaf_glue block_bytes block_reader block_fields block_msg block_sha block_merkle block_tables block_walk block_ctx block_wmerkle block_undo block_b2msg block_b2s genesis_checks; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
