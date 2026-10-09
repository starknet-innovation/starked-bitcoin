# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-09
- **HEAD at last update:** 819f56e (plus this status commit)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** M3a.4 `BLK-MERKLE` next; M3a.3 `BLK-SHA` done (2026-10-09). HC-HASHTREE done (full chain re-proven 2026-10-09).

## State in one paragraph

All 970,348 mainnet headers are proven to one root (M1/M2, [report](../reports/2026-10-08-full-chain.md)),
before the header tree. Now each segment proves a (headers, Blake2s tree) system;
public inputs gain the tree root `T` (indices 108–123), nodes compute `T` in-circuit,
and the fold runs in MMR order, so the root's `T` is the MMR over all block hashes.
Lean proves it end to end at the public-input level (`chain_from_genesis_T`,
standard axioms only); the in-circuit verifiers and node code stay trusted
(verification.md). Tested end to end on 52 headers.

## Next step (concrete)

1. M3a.3 `BLK-SHA` is done and proven (`digest_tx`: each digest is a transaction's `wtxid`/`txid` or the
   hash of the block's first 80 bytes; see [airs/block.md](../airs/block.md)). `digest_tx` names the parsed block:
   `SHA256d(b.header)` and the `wtxid`/`txid` of `b.txs[TI]`. Next is M3a.4 `BLK-MERKLE`: the
   Merkle component (txid tree with the CVE-2012-2459 check, witness tree, witness commitment) per
   [block-data.md](../design/block-data.md).
2. Proposed: REC-FUZZ (differential fuzzing of the plain verifier).

## In flight

- Nothing.

## Needs owner

- **Push / remote:** private repo starknet-innovation/starked-bitcoin exists; nothing pushed. Wait for the owner's go.
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
