# Zig code reference

Status: current · Updated: 2026-10-07 · Owner files: `src/**`, `build.zig`

This page maps the Zig side. Zig **consumes** AIRs and never defines them; the
definitions live in Lean (see [ir.md](ir.md)). Zig has three jobs:

1. **Witness generation:** filling the trace for a given input.
2. **Proving and verifying,** using stwo-zig with an IR-interpreting component.
3. **Tests:** reference implementations, witness checks, tamper checks and
   end-to-end proofs.

## Module map

| File | Purpose | Key API |
|---|---|---|
| `src/root.zig` | Library root; re-exports modules and pulls in all tests | — |
| `src/air/ir.zig` | IR types, JSON parse/print, digest, degree analysis, preprocessed-column generation. `Builder` is for tests only. | `Air.parseJson`, `Air.digest`, `Air.genPreprocessed`, `Air.validate`, `Air.maxConstraintDegree` |
| `src/air/interp.zig` | The one constraint evaluator, generic over M31/QM31 and over how columns are read | `evalConstraints(F, air, pubs, scratch, ctx, out)`, `RowTrace`, `firstViolation` |
| `src/air/component.zig` | Stwo component backed by the interpreter, with parallel evaluation over the domain | `Component.init(alloc, air, log_size, pubs)` |
| `src/air/prove.zig` | Prove/verify any IR AIR on any backend. The transcript binds `log_size`, the AIR digest and the public inputs. The verifier recomputes the preprocessed root. | `AirStatement`, `prepare`, `prove(E, …)`, `verify(alloc, cfg, air, log_size, pubs, proof)`, `Engine(Backend)` |
| `src/air/gadgets/add32_chain.zig` | Spike gadget (chained 32-bit adds); witness and tests, including the forged-preprocessed-column test | — |
| `src/sha256/spec.zig` | Plain SHA-256 reference with a per-round trace | `compress`, `compressTraced`, `headerHash`, `HeaderBlocks` |
| `src/sha256/witness.zig` | Witness for the SHA-256 compression AIR (72-row period) | `generate`, `Words.place`, `columns`, `shaRole`, `readOutputAt` |
| `src/btc/header_chain.zig` | Witness for the header-chain AIR (256 rows per header): 3 compressions, PoW scratch (216–217), chain state (218–219), retarget (220–228), median time past (229–240) | `generate`, `generateFrom(alloc, log_size, headers, ChainStart)`, `windowFrom`, `SENTINEL`, `ChainStart.work`, `loadHeaders`, `N_PUB = 108` |
| `src/btc/work.zig` | Chainwork witness (rows 241–253) and `blockProof` reference (Core formula) | `scratch(word18, prev_work)`, `blockProof` |
| `src/btc/retarget.zig` | Retarget witness (rows 220–228) plus an independent `nextWork` reference | `scratch`, `nextWork`, `getCompact`, `compactValue` |
| `src/bin/spike.zig` | Benchmark/demo CLI (built on macOS only, links Metal) | see below |

## Conventions

- **Words.** Header words are raw big-endian 32-bit words, as they appear in
  the SHA-256 message schedule. Numeric fields (nBits, time) are
  little-endian inside them. `retarget.le` byte-swaps, and Lean's `leN` is the
  same function.
- **Public inputs.** A 32-bit word is two M31 values: `(lo16, hi16)`.
- **Witness generators** return an error rather than a bad trace when the
  input breaks a consensus rule the AIR enforces. Examples:
  `error.RetargetMismatch`, `error.UnexpectedCap`.
- **Every AIR test file has:**
  - a "witness satisfies the AIR" test, using `firstViolation` against the
    **Lean-exported** JSON;
  - at least one tamper test, where a single-cell change must be caught;
  - a prove-and-verify test on CPU.

## Build, test, run

```sh
zig build test                      # all tests (Zig 0.15.2; fetches stwo-zig via the submodule path)
zig build -Doptimize=ReleaseFast    # builds zig-out/bin/spike (macOS)
zig-out/bin/spike <log_size> <cpu|metal> [lean]          # add32 spike
zig-out/bin/spike sha <log_size> <cpu|metal>             # SHA-256 compression benchmark
zig-out/bin/spike headers <log_size> <cpu|metal> <file>  # header chain over a .hex file
zig-out/bin/spike fullrun <log_size> <check|cpu|metal> data/headers.bin [from] [to]
    # HC-FULLRUN: every segment's witness is checked against the AIR (check) or proven and
    # verified (cpu/metal); consecutive segments' public outputs must equal the next inputs
```

- Header files are one 80-byte header per line, as hex. `headers` takes
  `2^log_size / 256` headers from the file.
- Test data is described in [testdata.md](testdata.md).
- AIR JSON and test data are compiled in via `@embedFile` anonymous imports
  declared in `build.zig`: `air:<name>` and `testdata:<name>`.
- **Rule:** to add a JSON or test-data file, add the anonymous import in
  `build.zig` and reference it by that name. Do not use a relative path.

## Scripts

| File | Purpose |
|---|---|
| `scripts/fetch_headers.py` | Downloads all mainnet headers into `data/headers.bin` (verified hashes and links; chunk and merge modes for parallel runs) |
| `scripts/air_z3.py` | Z3 witness-uniqueness checks on exported AIRs (`list`, `check <preset>`, `all`, `--bv`). Needs `.venv-fv` (see the [Z3 report](../reports/2026-10-07-z3-uniqueness.md)). |

## Dependency on stwo-zig

- stwo-zig is pinned as the submodule `third_party/stwo-zig`. The packages
  used are `stwo_core`, `stwo_prover_engine`, `stwo_cpu_backend`,
  `stwo_metal_backend` and `stwo_proof_wire`.
- **Do not edit the submodule in place.** Generic changes go to the stwo-zig
  fork and are upstreamed when useful.
- **Verify claims about stwo-zig in its source code.** Its README summaries
  have been wrong before; CUDA support is one example.
