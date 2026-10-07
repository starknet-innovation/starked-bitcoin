# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-07
- **HEAD at last update:** a1a0320 (plus this status commit)
- **Current milestone:** M1 (finish before M2, D-019). Remaining: `HC-FULLRUN`.
- **Current item:** `HC-FULLRUN`, in progress (header download running)

## State in one paragraph

`header_chain_sound` proves that any accepted segment satisfies `SegmentValid`:
every Bitcoin Core mainnet header rule except wall-clock `time-too-new`
(audited against Core, 2026-10-07). It uses standard axioms only. Z3
independently confirms four gadgets. Mainnet heights 0–2047 pass the full
pipeline: witness, AIR check, Metal proof and verification, segment chaining,
exact chainwork.

## Next step (concrete)

1. **Wait for the download.** Four workers fill `data/chunk_{0..3}.bin`
   (logs in `data/chunk_*.log`). They are resumable; if one dies, re-run the
   same command shown at the top of its log.
2. **Merge:**
   `python3 -I scripts/fetch_headers.py --merge data/chunk_0.bin data/chunk_1.bin data/chunk_2.bin data/chunk_3.bin`.
   This appends to `data/headers.bin` (heights 0..2619 are already there) and
   checks every link.
3. **Completeness on all headers:** `zig-out/bin/spike fullrun 16 check data/headers.bin`
   (build ReleaseFast first). Every failure is a header the AIR cannot express:
   investigate each one.
4. **Measure full-chain proving:** `zig-out/bin/spike fullrun 18 metal data/headers.bin`.
   Record the time and proof sizes in a report, then close M1.

## In flight

- Four `fetch_headers.py` workers (background, about 4–5 h from 2026-10-07).

## Needs owner

- **Push / remote:** nothing has been pushed (D-016).
- **LICENSE:** none chosen.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? This is outward-facing.

## Verify the current state

Run from the repo root. All must pass before new work starts.

```sh
git status --short                      # expect: clean, or explained under "In flight"
zig build test --summary all 2>&1 | grep "tests passed"   # expect: 27/27 tests passed
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
