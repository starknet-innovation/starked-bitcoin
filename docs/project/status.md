# Status: pick up here

Rewritten at the end of every session; see [README.md](README.md#ending-a-session-log-progress).
If `HEAD at last update` doesn't match `git log -1`, this file is stale:
follow step 5 of [starting a session](README.md#starting-a-session-pick-up-work).

- **Updated:** 2026-10-10 (owner away 48 h; agent working through the agreed priorities)
- **HEAD at last update:** see `git log -1` (this file is committed with the work)
- **Current milestone:** M3 (block data and UTXO set). M1 and M2 done.
- **Current item:** PROOF-STORE full-chain run (in progress, see below). M3a.5 AIR stages stay
  **parked** (owner); its spec stage M3a.5a is done (`Spec/BlockFlat.lean`).

## State in one paragraph

All 970,348 mainnet headers are proven to one root (M1/M2, [report](../reports/2026-10-08-full-chain.md)),
before the header tree. Now each segment proves a (headers, Blake2s tree) system;
public inputs gain the tree root `T` (indices 108–123), nodes compute `T` in-circuit,
and the fold runs in MMR order, so the root's `T` is the MMR over all block hashes.
Lean proves it end to end at the public-input level (`chain_from_genesis_T`,
standard axioms only); the in-circuit verifiers and node code stay trusted
(verification.md). Tested end to end on 52 headers.

## Next step (concrete)

1. **The saved full-chain proof (PROOF-STORE, D-036).** `chainproof` is implemented and tested, and the
   pinned production VK is in `vk/`. Run with:
   `data/store/chainproof-run2 prove mainnet data/headers.bin 970348 data/store/mainnet-0-970347.sbchain`.
   It resumes from `data/store/mainnet-0-970347.sbchain.ckpt` (90,112 headers when last checked).
   - **Memory problem being investigated (2026-10-10):** the process footprint grew by GBs per production
     segment and reached 36–38 GB (heavy swap), so the run was stopped twice. Checkpoints are intact.
     Switching to libc malloc and fixing the checkpoint arena did not cure it at production size (test
     sizes stay flat). The measurement is in `data/store/exp2/`.
   - Then: verify in a fresh process; fetch the new headers (`scripts/fetch_headers.py`); extend with
     `--from`; time it; write a report.
2. **Done this session** (details in log.md):
   - REC-FUZZ;
   - spec-vs-Core fuzzing;
   - the MMR in Lean (`mmr_inclusion`, `fold_eq_mmr`);
   - genesis checks exported from Lean;
   - LogUp's Schwartz–Zippel step in Lean;
   - M3a.5a.
3. **Waiting on the owner:**
   - D-035 (M3a.5 AIR design) review;
   - whether to commit `docs/reports/2026-10-09-proof-review.md`. It is untracked now but was committed
     by mistake in e871e49 (local only; can be dropped from history before any push).


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
