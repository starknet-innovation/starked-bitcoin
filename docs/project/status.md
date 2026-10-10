# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-10 (owner away 48 h; agent working through the agreed priorities)
- **HEAD at last update:** see `git log -1` (this file is committed with the work)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** M3a.5 `BLK-CHECKS`: D-035 **approved** (2026-10-10); M3a.5a (spec) done, M3a.5b (per-transaction checks) next. PROOF-STORE done (D-036 confirmed).
  **parked** (owner); its spec stage M3a.5a is done (`Spec/BlockFlat.lean`).

## State in one paragraph

The whole mainnet header chain is proven and **saved** as a file that verifies standalone and extends
at the tip:
- `data/store/mainnet-0-970347.sbchain` (12.8 MB), and `mainnet-to-970734.sbchain` after extension;
- the pinned VK is in `vk/`, and `chainproof verify mainnet <file>` checks it;
- `T` and the tip are checked against an independent recomputation and your node.

Lean proves the chain end to end at the public-input level (`chain_from_genesis_checked`), plus:
- the MMR inclusion and fold (`Spec/Mmr.lean`);
- LogUp's Schwartz–Zippel step (`LogUpSZ.lean`);
- the block rules as a conjunction (`Spec/BlockFlat.lean`).

The plain in-circuit verifier is mutation-fuzzed (102k mutations, all rejected). The specs are fuzzed
against Core's own C++ (about 860k cases, 0 mismatches).

## Next step (concrete)

1. **M3a.5b, per-transaction checks** (D-035, approved 2026-10-10;
   [block-data.md § M3a.5](../design/block-data.md#m3a5-blk-checks-design-approved-2026-10-10-d-035)):
   - the 16-bit range table;
   - public inputs 2–6 (height, prevMtp, activation bits);
   - the fields-component extensions: values (`values_ok_iff`), non-empty outputs, non-null prevouts,
     finality, witness bytes `W`, `NSEG`, script spans and `totals`;
   - Lean: the per-transaction facts of `CtxFreeOK`/`CtxOK` (Spec/BlockFlat.lean).
2. **Keeping the proof fresh:** `tools/extend_tip.sh data/store/chainproof-run5 <latest .sbchain>`.
   About 5–6 min per 400 headers.
3. **M3b design input:** assumeUTXO compatibility is a goal (D-037), so `Q-TREE` must allow a
   traversal in Core's coin order.

Full account of the away session: [2026-10-10-away-session.md](../reports/2026-10-10-away-session.md).

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
zig build test --summary all 2>&1 | grep "tests passed"   # expect: 32/32 tests passed (about 16 min in Debug)
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
#print axioms StarkedAir.Block.Fields.fields_sound
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle byte_table byte_user blake2s_compress blake2s_tree header_chain_v7 node_glue leaf_glue block_bytes block_reader block_fields; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
