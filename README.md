# starked-bitcoin

STARK proofs of Bitcoin consensus, built with
[stwo-zig](https://github.com/teddyjfpender/stwo-zig) (circle STARKs over
M31). The constraints are defined and **formally verified in Lean 4**, then
interpreted by the Zig prover and verifier.

**Goal:**

- Prove that a valid Bitcoin header chain from genesis to height H exists,
  with work W.
- Then prove the full UTXO set at H, with inclusion and non-inclusion proofs.
- Modules (scripts, OP_RETURN index, history) can plug in later without
  re-proving the base.

## Status

| Component | State |
|---|---|
| SHA-256 compression AIR | Implemented; **proven** equal to FIPS 180-4 |
| Header chain: SHA256d, linkage, proof of work, height/period state, difficulty retarget, median time past, exact chainwork | Implemented; **proven**: `header_chain_sound` shows any accepted segment satisfies these Bitcoin Core mainnet header rules |
| Header chain: minimum block version (BIP34/66/65) | Not yet (`HC-V6`) |
| Recursion / aggregation, CUDA, UTXO state | Not yet |

- Exact guarantees and trust assumptions:
  [docs/reference/verification.md](docs/reference/verification.md).
- What happens next: [docs/project/status.md](docs/project/status.md).

## Quick start

```sh
git submodule update --init third_party/stwo-zig
zig build test                       # Zig 0.15.2
cd lean && lake exe cache get && lake build   # Lean v4.33.1 + Mathlib
```

Details and benchmarks: [docs/guides/setup.md](docs/guides/setup.md).

## Repository layout

```
lean/StarkedAir/   AIR definitions, specs (SHA-256, Bitcoin Core) and soundness proofs (source of truth)
airs/              Exported AIRs (JSON, schema starked-air-v1). Generated; never edit by hand.
src/air/           IR parser, constraint interpreter, Stwo component, prove/verify
src/sha256/        SHA-256 reference and AIR witness
src/btc/           Header-chain and retarget witnesses
src/bin/spike.zig  Benchmark CLI (macOS / Metal)
testdata/          Mainnet headers used by the tests
bench/             External benchmarks (raito-sha256: Raito's Cairo SHA-256 under `scarb prove`)
third_party/       stwo-zig (pinned submodule; do not edit in place)
docs/              Documentation (see below)
```

## Documentation

### Where to find things

| You want to… | Read |
|---|---|
| Work on this repo as an agent (read order, hard rules) | [AGENTS.md](AGENTS.md) (`CLAUDE.md` imports it) |
| Understand the goals, architecture and trust model | [docs/design/overview.md](docs/design/overview.md) |
| See which Bitcoin rules are covered and how they're planned | [docs/design/consensus-rules.md](docs/design/consensus-rules.md) |
| Know exactly what is proven and what is trusted | [docs/reference/verification.md](docs/reference/verification.md) |
| Understand an AIR's layout, versions, tests and benchmarks | [docs/airs/sha256.md](docs/airs/sha256.md), [docs/airs/header-chain.md](docs/airs/header-chain.md) (earlier versions: [header-chain-history.md](docs/airs/header-chain-history.md)) |
| Understand the constraint IR and JSON format, or regenerate `airs/` | [docs/reference/ir.md](docs/reference/ir.md) |
| Find a Lean file or theorem, or learn the proof rules | [docs/reference/lean.md](docs/reference/lean.md) |
| Find a Zig module or API, or run the CLI | [docs/reference/zig.md](docs/reference/zig.md) |
| Know where test data came from | [docs/reference/testdata.md](docs/reference/testdata.md) |
| Look up a term (pst, nBits, LogUp…) | [docs/reference/glossary.md](docs/reference/glossary.md) |
| Set up a machine | [docs/guides/setup.md](docs/guides/setup.md) |
| Add or change an AIR, end to end | [docs/guides/adding-an-air.md](docs/guides/adding-an-air.md) |
| Read past experiment results | [docs/reports/](docs/reports/) |
| **Pick up work, log progress, see the roadmap and decisions** | **[docs/project/README.md](docs/project/README.md)** |

### Documentation structure

```
docs/
  design/     Why and what: goals, architecture, consensus-rule plans. Changes rarely.
  airs/       One file per AIR: layout, versions (newest first), statement proven, tests, benchmarks.
  reference/  Precise facts about the code: IR, Lean, Zig, test data, verification ledger, glossary.
  guides/     Step-by-step procedures: setup, adding an AIR.
  reports/    Dated, immutable write-ups of experiments and benchmarks (YYYY-MM-DD-<topic>.md).
  project/    Project management: process, status, roadmap, log, decisions.
```

### Documentation rules

These rules are mandatory for every contributor, human or agent.

1. **Docs change in the same commit as the code they describe.** A commit
   that changes behavior, a theorem, an AIR or a command, and leaves its doc
   stale, is incomplete.
2. **Every fact has exactly one home.** Pick the folder with the table below.
   Elsewhere, *link* to it; don't copy it. Duplicated facts drift.

   | The content is… | It goes in… |
   |---|---|
   | a goal, architecture choice or plan for a rule not built yet | `design/` |
   | about one AIR: layout, version history, proven statement, tests, benchmark numbers | `airs/<air>.md` |
   | a precise description of code, formats, data or guarantees | `reference/` |
   | a procedure someone follows step by step | `guides/` |
   | a one-time experiment or measurement with a conclusion | `reports/YYYY-MM-DD-<topic>.md` (never edited afterwards, except to add a "Superseded by" line) |
   | a decision and its rationale | `project/decisions.md` (also reflected in `design/` if architectural) |
   | progress, plans or status | `project/` (see its README) |

3. **Adding a file** means also adding it to the "Where to find things"
   table in this README, in the same commit. If a document isn't linked from
   here, it doesn't exist as far as other contributors are concerned.
4. **Header.** Every doc except `reports/` and the `project/` logs starts
   with a title and a line
   `Status: <draft|current|superseded> · Updated: YYYY-MM-DD`. Add
   `· Owner files: <paths>` when it describes specific code.
5. **Names:** lowercase-kebab-case `.md`. One topic per file. Split a file
   when it passes about 300 lines or covers two topics.
6. **Be precise and checkable:**
   - name theorems in backticks with their file;
   - give file paths relative to the repo root;
   - use absolute dates (`2026-10-07`, never "yesterday");
   - give commands that run as written.
7. **Claims need evidence.** "Proven" means a theorem name, and that theorem
   must appear in [verification.md](docs/reference/verification.md).
   "Tested" means a test name. Benchmark numbers need machine, backend,
   security profile, size and date. Never estimate a number and present it
   as measured. Mark unverified statements as such.
8. **AIR docs are versioned:** the newest version section goes first, and
   older sections stay as history. Mark anything a later version changes.
9. **Code comments** explain local *how*; docs explain *what* and *why*.
   Point code comments to docs by path (for example
   `See docs/airs/sha256.md`), and update those paths when you move a doc.
10. **Moving or renaming a doc:**
    - use `git mv`;
    - then fix every reference: `grep -rn "<old path>" src lean docs README.md`.

## Project management

Development is tracked in [docs/project/](docs/project/README.md):

- [status.md](docs/project/status.md): **start here** to pick up work.
- [roadmap.md](docs/project/roadmap.md): done and remaining work, by ID.
- [log.md](docs/project/log.md): session history.
- [decisions.md](docs/project/decisions.md): why things are the way they are.

The process (session start and end checklists, definition of done, git rules,
escalation) is in [docs/project/README.md](docs/project/README.md). Follow it.

## Git

Commit locally. Do not push, open PRs or file upstream issues without the
project owner's approval (decision D-016).

## License

None chosen yet (roadmap backlog: `LICENSE`).
