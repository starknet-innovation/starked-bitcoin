# Away session (2026-10-09 → 10): saved chain proof, trust reductions, M3a.5a

**Owner's brief:** keep working for 48 h through the agreed priorities, moving on when one is blocked:
1. a saved, extendable full-chain proof (PROOF-STORE);
2. REC-FUZZ;
3. the MMR in Lean;
4. the spec fuzzed against Core;
5. M3a.5a as a fallback.

Nothing was pushed. Every commit is local, on `main`.

**Status at a glance** (filled in at the end of the session):

| Workstream | Result |
|---|---|
| PROOF-STORE | Implemented and tested; full-chain run *(result below)* |
| REC-FUZZ | Done: every mutation rejected by the circuit *(exhaustive run below)* |
| MMR in Lean | Done: `mmr_inclusion`, `fold_eq_mmr`; Zig sides cross-checked |
| Genesis checks from Lean | Done: `chain_from_genesis_checked`; `verifyRoot` reads the exported table |
| Spec vs Core | Done: about 860,000 mainnet-domain cases (756k header, 100k block kinds), 0 mismatches |
| LogUp Schwartz–Zippel in Lean | Done: `logup_sz`, `balancedExt_of_poly`; side conditions decided per system |
| M3a.5a (spec only) | Done: `checkBlock_none_iff`, `walk_eq_sigOps` and the rest; the AIR stages stay parked |

## 1. PROOF-STORE: a chain proof as a file

Design: [proof-store.md](../design/proof-store.md), decision D-036. Commits from `ed5d560` on.

- **`chainproof`** commands:
  - `setup` (the VK);
  - `prove` (with checkpoints, resume, `--from` for extension, `--segments`, `--max-log`);
  - `verify`;
  - `inclusion`.
- **The VK is pinned and the node shape frozen.** It covers segment log sizes 9..20, is committed in
  `vk/`, and is built into the binary: `chainproof verify mainnet <file>`. Digest `8a9a790e…`.
- **The verifier pins the root's request** (FRI configuration and columns): review finding 2. It also
  checks:
  - the plan's alignment;
  - every stored peak;
  - the genesis-state checks exported from Lean;
  - Bitcoin's genesis hash as leaf 0 of `T`;
  - by default, chainwork ≥ Bitcoin Core's `nMinimumChainWork`.
- **The file is extendable.** It stores the MMR peaks, and extension pushes aligned segments onto
  them. Tested on test parameters: prove 0–51, extend to 100 in a fresh process, and the result equals
  a from-scratch proof's `T`. A checkpoint resume was tested after killing a run.
- **Tamper tests** reject a flipped proof byte, a weaker FRI configuration, a changed public input, a
  misaligned plan, a non-leftmost genesis path, a wrong VK, and a truncated or corrupted file.

### The full-chain run

*(Filled in when the run ends.)*

### Memory: what went wrong and the fix

The first two attempts were stopped at footprints of 36–38 GB with about 22 GB of swap. Measuring
(`data/store/exp2`, `exp3`) showed this was not a leak but a transient peak:

| Phase | Footprint |
|---|---|
| Leaf of 4,096 headers (log 20) | peaks at 34–37 GB |
| Leaf of 2,048 headers (log 19) | about 22 GB |
| Node | about 19 GB |

So long runs now use `--max-log 19` (68 s per leaf, against 125–190 s for log 20 while swapping) and
`tools/prove_loop.sh`, which runs one bounded process per few segments, each resuming from the
checkpoint. Checkpoints made both restarts lossless.

## 2. Trust reductions (proof review 2026-10-09, §5)

| Item | Result |
|---|---|
| 1. Pinned config, genesis, VK constants; `verifyRoot`'s checks from Lean | Done: `RootChecks.lean` (`genesis_checks_sound`, `chain_from_genesis_checked`), `airs/genesis_checks.json` |
| 2. REC-FUZZ | Done: `src/recursion/fuzz.zig` |
| 3. MMR in Lean | Done: `Spec/Mmr.lean` |
| 4. LogUp Schwartz–Zippel | Done: `LogUpSZ.lean`, `LogUpSZSystems.lean` |
| 9. Spec ↔ Core | Done: `tools/specfuzz` |
| 10. AIR digest check (cheap half) | Done: every exported AIR re-serializes byte-identically; its digest is SHA-256 of Lean's text |

Details:

- **REC-FUZZ.** Every guessed proof value and statement input of a header-chain proof (82,972 sites)
  and a LogUp-system proof (1,952 sites) is mutated one at a time. The circuit must reject each
  mutation, and all are rejected by unsatisfied constraints (not by early errors). *(Exhaustive run
  below.)*
- **Spec vs Core.** Core's own C++ (sparse checkout at `c067aa71`) is linked into a harness that
  answers random and edge-case inputs; `SpecCases.lean` answers from the Lean specs.
  - Header kinds: `SetCompact`, `GetCompact`, `CalculateNextWorkRequired`, `GetBlockProof`,
    `CheckProofOfWorkImpl`, `GetMedianTimePast`.
  - Block kinds: `GetSigOpCount`, `ComputeMerkleRoot` with mutation, `CheckTransaction`, txid/wtxid.
  - 0 mismatches in the mainnet domain. Outside it (a retarget from any nBits), Core's 256-bit
    arithmetic wraps; every such divergence is checked to be a wrap.
  - The mainnet constants are checked against `chainparams.cpp`.
- **LogUp.** For tuples' fingerprint polynomials, all but `(N²L + 2N)·|K|` challenge pairs make a zero
  fraction sum imply balance. That is below 2⁻⁶⁶ per proof over QM31 for our sizes.

## 3. M3a.5a: the block rules as a conjunction (spec only)

`Spec/BlockFlat.lean`, standard axioms only:

- `checkBlock_none_iff`, `checkTx_none_iff`;
- `values_ok_iff`: the three per-output checks become "non-negative, total ≤ MAX_MONEY";
- `size_of_weight`: weight implies the other size limits;
- `walk_eq_sigOps`: the sigop byte automaton is Core's `GetSigOpCount(false)`, and is fuzzed against
  it too;
- `commitmentIndex_eq` / `commitmentIndex_some`;
- `not_coinbase_of_inputs`.

D-035, the AIR design, still awaits your review. Stages 5b–5e were not started.

## 4. Mistakes and open points

- I committed `docs/reports/2026-10-09-proof-review.md` by mistake in `e871e49` (via `git add docs`).
  It is untracked again (`f1ffeac`) and can be dropped from local history before any push.
- The first full-run attempt with log-20 leaves had to be stopped twice (memory, above).
- **Needs you:**
  - D-035;
  - whether the review report goes into the repo;
  - whether to push.
