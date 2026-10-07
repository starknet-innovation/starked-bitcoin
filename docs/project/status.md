# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-07
- **HEAD at last update:** 2cf67b0 (plus this status-only commit)
- **Current milestone:** M1 (header chain, locally, formally verified). Finish M1 before M2 (D-019).
- **Current item:** none in progress. **Next item: `HC-V5`** (chainwork)

## State in one paragraph

The header-chain AIR (`header_chain_v4`) enforces, per header: SHA256d,
prev-hash linkage, proof of work, height/period state, the difficulty retarget
and median time past. Each is proven sound in Lean with standard axioms only
(see [verification.md](../reference/verification.md)). Two things are
missing: chainwork (HC-V5), and a single chain-level theorem (HC-TOP) that,
among other things, proves each MTP window is the real predecessors' times.
Proving runs at about 280 headers/s on Metal (M4 Pro). There is no recursion
yet.

## Next step (concrete)

**HC-V5: chainwork.** Follow [guides/adding-an-air.md](../guides/adding-an-air.md):

1. **Spec.** Add `blockProof (target) = 2^256 / (target + 1)` to
   `lean/StarkedAir/Spec/Bitcoin.lean`, matching Core's `GetBlockProof`
   (`(~target / (target+1)) + 1`, which equals `⌊2^256 / (target+1)⌋`). Add
   `#guard`s, e.g. the work of `0x1d00ffff` = 4295032833.
2. **Design.** Work out Q-WORK below (exact or lower bound) first. Then
   plan the rows (241..255 are free) in `docs/airs/header-chain.md` § v5:
   - per-header work `q` with `q·(T+1) ≤ 2^256` (and `< (q+1)(T+1)` if exact);
   - a running 256-bit sum carried with a −256 offset;
   - public input/output for the segment's starting and ending cumulative
     work.

   `T` comes from the PoW row's mantissa and exponent one-hot (row 216).
   Reuse the byte-limb product/carry style of `retarget` (`P0`, `divCol`).
3. Then follow steps 3–7 of the guide.

## In flight

Nothing. The working tree is clean after the v4 proof commit.

## Needs owner

- **Q-WORK (decide before HC-V5 step 2):** should the proof expose **exact**
  cumulative chainwork (Core's value), or a **sound lower bound**?
  - Exact costs roughly twice the work rows (both inequality sides).
  - It lets verifiers compare the output with `getblockheader … chainwork`.
  - A lower bound is enough to claim "at least W work".
  - **Recommendation: exact.**
- **Push / remote:** nothing has been pushed (D-016). Should the repo get a
  remote?
- **LICENSE:** none chosen.
- **STWO-225-FU:** follow up on stwo-zig#225 upstream? This is
  outward-facing.

## Verify the current state

Run from the repo root. All must pass before new work starts.

```sh
git status --short                      # expect: clean, or explained under "In flight"
zig build test --summary all 2>&1 | grep "tests passed"   # expect: 23/23 tests passed
(cd lean && lake build)                 # expect: "Build completed successfully"
grep -rnE "\bsorry\b|native_decide|bv_decide" lean/StarkedAir   # expect: no matches

# Axioms of the main theorems (expect only propext, Classical.choice, Quot.sound)
cat > /tmp/ax.lean <<'EOF'
import StarkedAir
open StarkedAir.HeaderChain StarkedAir.Spec.Bitcoin
#print axioms StarkedAir.Sha256.compress_sound_air
#print axioms chain_sound_v2
#print axioms state_sound
#print axioms retarget_sound
#print axioms mtp_count
#print axioms mtp_window
#print axioms mtp_out
#print axioms mtp_core
EOF
(cd lean && lake env lean /tmp/ax.lean)

# JSON drift: committed AIRs must equal the Lean export
(cd lean && for n in add32_chain sha256_compress header_chain probe_oracle; do
  lake env lean --run Export.lean $n | cmp -s - ../airs/$n.json && echo "$n ok" || echo "$n DRIFT"; done)

# Docs: links, map coverage, headers (the /document skill's checker)
python3 ~/.claude/skills/document/scripts/check_docs.py .   # expect: 0 errors
```
