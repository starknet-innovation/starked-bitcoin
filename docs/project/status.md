# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-08
- **HEAD at last update:** 9cc5f7a (plus this status commit)
- **Current milestones:** M1 (`HC-FULLRUN`) and M2 (`AGG` full-chain run), both waiting on long runs.
- **Current item:** the two runs below.

## State in one paragraph

Segments are proven (`header_chain_sound`), wrapped into leaf circuit proofs,
and folded by our node circuit, which checks the chain link in-circuit (D-025).
`verifyRoot` checks the root against the node circuit identity, the expected
identity key and genesis. Lean proves the pub-level composition
(`leaf_valid`, `pub_compose`, `chain_from_genesis`). A 1,024- and an
8,192-header tree from genesis verify at production parameters. All 970,348
mainnet headers are in `data/headers.bin`.

## Next step (concrete)

1. **Full-chain completeness check:** `data/fullrun_check.log`
   (`spike fullrun 16 check data/headers.bin`). Every `FAIL` is a header the AIR
   cannot express: investigate each one.
2. **Whole chain to one root:** `data/chain_full.log`
   (`spike chain 20 70 26 data/headers.bin`, about 5.5 h on CPU). Success line:
   `chain ROOT VERIFIED`. Compare the printed tip with a public explorer
   (block 970347 hash; state words are SHA-256 state order) and the chainwork
   with `getblockheader … chainwork`.
3. Write the report (`docs/reports/`), then close M1 (`HC-FULLRUN`) and M2 (`AGG`).
   A separate `fullrun 20 metal` timing run is optional (the chain run proves every segment);
   the Metal plan and 10k sample are in [the sample report](../reports/2026-10-07-fullrun-sample.md).

## In flight

- `spike fullrun 16 check` and `spike chain 20 …` (background, started 2026-10-08).
  If a run dies, re-run the same command; neither resumes partially.

## Needs owner

- **Push / remote:** nothing has been pushed (D-016).
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
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
