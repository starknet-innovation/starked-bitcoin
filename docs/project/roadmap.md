# Roadmap

Status: current · Updated: 2026-10-07

Rules:

- Every work item has a **stable ID**. Never reuse or renumber IDs.
- Statuses are defined in [README.md](README.md#statuses).
- Order within a milestone is the intended order.
- New discoveries go to the **Backlog**, with an ID, until they are scheduled.
- Milestones come from [design/overview.md](../design/overview.md#milestones).

## M1: header chain, locally, formally verified

| ID | Item | Status | Done when / notes |
|---|---|---|---|
| SPIKE | Lean-first single-source spike (IR, exporter, interpreter, prove/verify) | done (85507f4, 542d834) | [report](../reports/2026-10-06-lean-first-spike.md) |
| STWO-225 | Report the unpinned preprocessed root to stwo-zig | done (teddyjfpender/stwo-zig#225) | Follow-up: track the upstream fix (backlog `STWO-225-FU`) |
| SHA | SHA-256 compression AIR plus soundness | done (7ba4a21, 9a446cc) | `compress_sound_air` |
| IR-V1 | Public inputs and row-range preprocessed columns in the IR | done (66703fb) | |
| HC-V1 | Header chain: SHA256d, linkage, endpoints | done (82baf06, 6594fd3) | `chain_sound` |
| HC-V2 | Header chain: proof of work | done (fb5040e, 74df024) | `chain_sound_v2` |
| HC-V3A | Header chain: height, period boundary, nBits continuity, period-start time | done (6a3250e, b1660b5) | `state_sound` |
| HC-V3B | Header chain: difficulty retarget | done (c52ddcf, 9a03734) | `retarget_sound` |
| DOCS | Project documentation and PM process | done (97dbca4) | README, docs/ tree, project/ |
| HC-V4 | Median time past: `time > median(prev 11)` | done (35710cb, this commit) | Counting approach (D-018). Design: [consensus-rules.md](../design/consensus-rules.md). The first 11 headers of a segment need public inputs for earlier times. Done per [adding-an-air.md](../guides/adding-an-air.md). |
| HC-V5 | Exact chainwork (D-020): per-header `⌊2^256/(T+1)⌋`, accumulated, public in/out | done (1250f02, this commit) | Needs 256-bit limb arithmetic in the scratch rows |
| HC-TOP | A single top-level theorem combining `chain_sound_v2`, `state_sound`, `retarget_sound`, the v4 MTP theorems (and v5) into one statement about the public inputs | done (this commit: `header_chain_sound`) | Must prove, by induction with `mtp_window`, that each window is the real predecessors' times padded with `sentinel`, given the genesis/segment public-input convention; then apply `mtp_core`. One theorem plus a doc paragraph in verification.md. |
| BENCH-RAITO | Benchmark our SHA-256 AIR against Raito's Cairo SHA-256 | done (this commit) | Same machine, documented methodology, results in airs/sha256.md |
| HC-V6 **(next)** | Minimum block version (Core `ContextualCheckBlockHeader` "bad-version"): nVersion ≥ 2/3/4 from heights 227931/363725/388381 (BIP34/66/65) | todo | Found 2026-10-07: missing from `SegmentValid`. Done per [adding-an-air.md](../guides/adding-an-air.md); add to `SegmentValid` and `header_chain_sound`. |
| HC-AUDIT | Line-by-line audit of Core `CheckBlockHeader` + `ContextualCheckBlockHeader` (mainnet) against `SegmentValid`; record in verification.md | todo | Guards against further omissions like HC-V6 |
| HC-FULLRUN | Generate (and satisfy-check) the witness for every mainnet header, genesis to tip | todo | Needs all headers: local `bitcoind` preferred (Q-HEADERS), else rate-limited public API. Proves completeness on real data. |
| FV-Z3 | Tier-1 formal verification: Z3 search for under-constrained witnesses (adapt stwo-zig `scripts/air_uniqueness_board.py`) | done (this commit; [report](../reports/2026-10-07-z3-uniqueness.md)) | Runs on each exported AIR; results recorded |

## M2: full chain to the tip, on the H200

| ID | Item | Status | Notes |
|---|---|---|---|
| IR-LOGUP | LogUp / interaction terms in the IR (Lean semantics, export, interpreter) | todo | Port StarkWare's `tuple_inclusion` for the Lean side |
| VK | Verification key: preprocessed roots per (AIR, log_size), instead of recomputing in O(n) | todo | |
| GPU-CODEGEN | Generate CUDA/Metal constraint kernels from the IR | todo | Affects completeness and speed only, not soundness |
| RECURSION | Native-AIR recursion statement (verify a proof inside an AIR) | todo | Generic; candidate for upstreaming to stwo-zig |
| AGG | Segment aggregation: link segments through the public inputs, aggregate in a tree up to the tip | todo | |
| H200 | Run the full chain on the H200 | todo | Needs owner access |

## M3: block data and UTXO state

| ID | Item | Status | Notes |
|---|---|---|---|
| BLOCK-DATA | Per-block proof: raw block ↔ Merkle root; Blake2s commitment to the canonical encoding, including spent outputs | todo | [overview.md § Architecture](../design/overview.md) |
| UTXO | State module: sorted Merkle tree (Blake2s), inclusion and non-inclusion, matching Core's UTXO set | todo | Open: one combined tree or two (`Q-TREE`) |
| CATCHUP | Catch up from genesis | todo | |

## Later

Script module (secp256k1, Schnorr, interpreter) · OP_RETURN index module ·
history module · browser/phone verifier.

## Backlog (unscheduled)

| ID | Item | Notes |
|---|---|---|
| STWO-225-FU | Track the upstream fix for stwo-zig#225; drop our workaround if the fix lands | Outward-facing follow-up: ask the owner |
| AIRSTMT | `AirStatement` carries a pointer and an allocator (prototype ergonomics) | `src/air/prove.zig` |
| LIFT | Mixed trace sizes / lifting | Needed once components differ in size |
| INTERP-PROOF | Prove the Zig interpreter ≡ Lean semantics, or generate it | Currently differential-tested only |
| DRIFT-CI | Automate the JSON drift check and the sorry/axiom check in CI | Manual commands are in status.md for now |
| LICENSE | Choose a license | Needs an owner decision (possibly legal) |
| SIMP-LINT | Clean up unused-simp-argument warnings in the Lean files | Cosmetic |
