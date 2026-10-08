# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-08
- **HEAD at last update:** see `git log -1` (this commit)
- **Current milestone:** M1 and M2 done; M3 not started (waiting on owner decisions).
- **Current item:** none in flight.

## State in one paragraph

All 970,348 mainnet headers (0..970,347) satisfy the AIR, and the whole chain
is proven to one 0.98 MB root proof verified in 0.26 s, with chainwork equal
to Core's ([report](../reports/2026-10-08-full-chain.md)). Lean proves the
segment rules and the pub-level composition; the in-circuit verifiers and the
node circuit's code are trusted (verification.md).

## Next step (concrete)

1. **REC-FUZZ (proposed):** differential fuzzing of `plain_verifier.zig` against
   the native verifier (mutate real proofs; both must agree on accept/reject).
2. Optional: re-run `spike chain 20 70 26 data/headers.bin` with the independent
   VK (about 8 h); the run in the report used the proofs' own leaf hashes.
3. M3, once the owner decides the items below.

## In flight

- Nothing.

## Needs owner

- **M3 node:** where an archival (non-pruned) `bitcoind` runs (local SSD or a
  cloud VM, about 1 TB), and who sets it up. Cloud spend needs approval.
- **M3 scope:** start without script validation (M3a block structure + M3b UTXO
  accumulator, `assumevalid`-style), or include scripts (M3c)?
- **D-022:** lift it for M3 (GPU work now), given the data scale?
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
