# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-07
- **HEAD at last update:** 97dbca4 (plus this status-only commit)
- **Current milestone:** M1 (header chain, locally, formally verified)
- **Current item:** none in progress. **Next item: `HC-V4`** (median time past)

## State in one paragraph

The header-chain AIR (`header_chain_v3b`) enforces SHA256d, prev-hash
linkage, proof of work, the height/period state and the difficulty retarget.
Each of these is proven sound in Lean, with standard axioms only (see
[verification.md](../reference/verification.md)). Not yet enforced: median
time past (HC-V4) and chainwork (HC-V5). Proving runs locally on CPU and
Metal at about 350 headers/s. No recursion yet, so a proof covers one segment
of at most `2^logSize / 256` headers.

## Next step (concrete)

**HC-V4: median time past.** Follow
[guides/adding-an-air.md](../guides/adding-an-air.md):

1. **Spec.** In `lean/StarkedAir/Spec/Bitcoin.lean`, add `mtpOk`:
   `time_j > median(time_{j−1..j−11})`, matching Core's `GetMedianTimePast`
   for heights below 11 (fewer blocks; median index `k/2` of the sorted `k`).
   Add `#guard`s on mainnet values.
2. **Layout.** Plan it in `docs/airs/header-chain.md` (new v4 section),
   following `docs/design/consensus-rules.md` § v4:
   - count ≥ 6 of the previous 11 times strictly below `time_j`, each with a
     range-checked difference;
   - read earlier headers' time words at constant offsets (`−256·k + 77`);
   - the first 11 headers of a segment take earlier times from public inputs;
   - use free scratch rows 229–255.
3. Then follow steps 3–7 of the guide.

## In flight

Nothing. The working tree is clean after the docs commit, and no builds are
running.

## Needs owner

- **Push / remote:** nothing has been pushed (D-016). Should the repo get a
  remote, and should the commits be pushed?
- **LICENSE:** none chosen.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? This is
  outward-facing.
- **Priority check:** finish M1 (HC-V4, HC-V5, HC-TOP, BENCH-RAITO, FV-Z3)
  before starting M2 recursion and aggregation? This is the default
  assumption unless told otherwise.

## Verify the current state

Run these from the repo root. All must pass before new work starts.

```sh
git status --short                      # expect: clean, or explained under "In flight"
zig build test                          # expect: no output, exit 0
(cd lean && lake build)                 # expect: "Build completed successfully"
grep -rnE "\bsorry\b|native_decide|bv_decide" lean/StarkedAir   # expect: no matches

# Axioms of the main theorems (expect only propext, Classical.choice, Quot.sound)
cat > /tmp/ax.lean <<'EOF'
import StarkedAir
open StarkedAir.HeaderChain
#print axioms StarkedAir.Sha256.compress_sound_air
#print axioms chain_sound_v2
#print axioms state_sound
#print axioms retarget_sound
EOF
(cd lean && lake env lean /tmp/ax.lean)

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)
```
