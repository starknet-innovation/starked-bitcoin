# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-07
- **HEAD at last update:** the `FV-Z3` commit (follows 0c7f39c)
- **Current milestone:** M1. Finish M1 before M2 (D-019). Three items were added on 2026-10-07: HC-V6, HC-AUDIT, HC-FULLRUN.
- **Current item:** none in progress. **Next item: `HC-V6`** (minimum block version)

## State in one paragraph

`header_chain_sound` proves that any accepted segment satisfies `SegmentValid`
(`Spec/Chain.lean`):
- PoW, linkage and heights;
- nBits continuity and `GetNextWorkRequired`;
- median time past over real predecessors;
- exact chainwork and chaining outputs.

All of it uses standard axioms only (see
[verification.md](../reference/verification.md)). Z3 independently confirms
four gadgets. Speed: Metal 239 headers/s; CPU 154–358 headers/s, about 100×
Raito's Cairo hashing alone. **Known gap:** the minimum block version rule
(BIP34/66/65) is not enforced yet (HC-V6). The chain has been exercised on
mainnet heights 0–1023, 1973–2047 and 32181–32319 only (HC-FULLRUN).

## Next step (concrete)

**HC-V6: minimum block version.** Follow [guides/adding-an-air.md](../guides/adding-an-air.md):

1. **Spec.** In `Spec/Bitcoin.lean`, add `versionOk (height version : ℕ)` per Core
   `ContextualCheckBlockHeader`:
   - version ≥ 2 if height ≥ 227931;
   - ≥ 3 if height ≥ 363725;
   - ≥ 4 if height ≥ 388381.

   `nVersion` is a signed int32: header bytes 0..3, little-endian (raw word 0
   byte-swapped). Comparisons are signed, so a negative version is < 2. Add
   `#guard`s.
2. **Layout.** Use rows 254–255 (free). Range-check `height − 227931` etc. with
   flags, and require `version − k ≥ 0` (signed) when the flag is on. Add the
   rule to `SegmentValid`, and extend `header_chain_sound`.
3. Then steps 3–7 of the guide.

After that comes HC-AUDIT (read Core's `CheckBlockHeader` and
`ContextualCheckBlockHeader` line by line), then HC-FULLRUN.

## In flight

Nothing. The working tree is clean after the FV-Z3 commit.

## Needs owner

- **Q-HEADERS (for HC-FULLRUN):** is there a local `bitcoind` to read all
  ~920k mainnet headers from? Otherwise headers come from public Esplora APIs,
  rate-limited, taking hours.
- **Push / remote:** nothing has been pushed (D-016).
- **LICENSE:** none chosen.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? This is outward-facing.

## Verify the current state

Run from the repo root. All must pass before new work starts.

```sh
git status --short                      # expect: clean, or explained under "In flight"
zig build test --summary all 2>&1 | grep "tests passed"   # expect: 26/26 tests passed
(cd lean && lake build)                 # expect: "Build completed successfully"
grep -rnE "\bsorry\b|native_decide|bv_decide" lean/StarkedAir   # expect: no matches

cat > /tmp/ax.lean <<'EOS'
import StarkedAir
open StarkedAir.HeaderChain StarkedAir.Spec.Bitcoin
#print axioms header_chain_sound
#print axioms StarkedAir.Sha256.compress_sound_air
EOS
(cd lean && lake env lean /tmp/ax.lean)  # expect: propext, Classical.choice, Quot.sound

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
# Optional, slow (~15 min): .venv-fv/bin/python scripts/air_z3.py all --bv
```
