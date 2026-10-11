# Roadmap

Status: current · Updated: 2026-10-11

Rules:

- Every work item has a **stable ID**. Never reuse or renumber IDs.
- Statuses are defined in [README.md](README.md#statuses).
- Order within a milestone is the intended order.
- New discoveries go to the **Backlog**, with an ID, until they are scheduled.
- Milestones come from [design/overview.md](../design/overview.md#milestones).

## M1: header chain, locally, formally verified

| ID | Item | Status | Done when / notes |
|---|---|---|---|
| SPIKE | Lean-first single-source spike (IR, exporter, interpreter, prove/verify) | done (9b95bb6, a0e54a5) | [report](../reports/2026-10-06-lean-first-spike.md) |
| STWO-225 | Report the unpinned preprocessed root to stwo-zig | done (teddyjfpender/stwo-zig#225) | Follow-up: track the upstream fix (backlog `STWO-225-FU`) |
| SHA | SHA-256 compression AIR plus soundness | done (665b732, f18e90d) | `compress_sound_air` |
| IR-V1 | Public inputs and row-range preprocessed columns in the IR | done (1e3a824) | |
| HC-V1 | Header chain: SHA256d, linkage, endpoints | done (2fa7211, 69b2335) | `chain_sound` |
| HC-V2 | Header chain: proof of work | done (829a7e4, 3323650) | `chain_sound_v2` |
| HC-V3A | Header chain: height, period boundary, nBits continuity, period-start time | done (f9f7a95, 508cfd8) | `state_sound` |
| HC-V3B | Header chain: difficulty retarget | done (b7ab5ce, 5e219bb) | `retarget_sound` |
| DOCS | Project documentation and PM process | done (4df8c1e) | README, docs/ tree, project/ |
| HC-V4 | Median time past: `time > median(prev 11)` | done (6fa5376, this commit) | Counting approach (D-018). Design: [consensus-rules.md](../design/consensus-rules.md). The first 11 headers of a segment need public inputs for earlier times. Done per [adding-an-air.md](../guides/adding-an-air.md). |
| HC-V5 | Exact chainwork (D-020): per-header `⌊2^256/(T+1)⌋`, accumulated, public in/out | done (5199752, this commit) | Needs 256-bit limb arithmetic in the scratch rows |
| HC-TOP | A single top-level theorem combining `chain_sound_v2`, `state_sound`, `retarget_sound`, the v4 MTP theorems (and v5) into one statement about the public inputs | done (this commit: `header_chain_sound`) | Must prove, by induction with `mtp_window`, that each window is the real predecessors' times padded with `sentinel`, given the genesis/segment public-input convention; then apply `mtp_core`. One theorem plus a doc paragraph in verification.md. |
| BENCH-RAITO | Benchmark our SHA-256 AIR against Raito's Cairo SHA-256 | done (this commit) | Same machine, documented methodology, results in airs/sha256.md |
| HC-V6 | Minimum block version (Core `ContextualCheckBlockHeader` "bad-version"): nVersion ≥ 2/3/4 from heights 227931/363725/388381 (BIP34/66/65) | done (this commit) | Found 2026-10-07: missing from `SegmentValid`. Done per [adding-an-air.md](../guides/adding-an-air.md); add to `SegmentValid` and `header_chain_sound`. |
| HC-AUDIT | Line-by-line audit of Core `CheckBlockHeader` + `ContextualCheckBlockHeader` (mainnet) against `SegmentValid`; record in verification.md | done (this commit; verification.md § Coverage audit) | Guards against further omissions like HC-V6 |
| HC-FULLRUN | Generate (and satisfy-check) the witness for every mainnet header, genesis to tip | done (2026-10-08: heights 0..970,347, 0 failures; chainwork equals Core's; [report](../reports/2026-10-08-full-chain.md)) | Proves completeness on real data. |
| FV-Z3 | Tier-1 formal verification: Z3 search for under-constrained witnesses (adapt stwo-zig `scripts/air_uniqueness_board.py`) | done (this commit; [report](../reports/2026-10-07-z3-uniqueness.md)) | Runs on each exported AIR; results recorded |

## M2: full chain to the tip, one proof

Done 2026-10-08 (CPU, laptop): heights 0..970,347 in one root proof; [report](../reports/2026-10-08-full-chain.md). GPU/H200 runs are deferred (D-022).

| ID | Item | Status | Notes |
|---|---|---|---|
| IR-LOGUP | (moved to M3, see there) | moved to M3 | |
| VK | Verification key: node identity (from topology) and leaf identities per log size (from public data, `leafIdentity`), checked by `verifyRoot` | done (2026-10-08) | Per-AIR native VK (preprocessed roots per log size) still recomputed in O(n); not needed by the root verifier |
| GPU-CODEGEN | Generate CUDA/Metal constraint kernels from the IR | deferred (D-022) | Affects completeness and speed only, not soundness. After the full pipeline works. |
| RECURSION | Recursion via stwo-zig circuit recursion (D-023) | done (whole chain to one root, 2026-10-08) | Plan and as-built in [design/recursion.md](../design/recursion.md) |
| REC-PROFILE | Prove and verify a segment on the `proving_5a7c5ed` profile (Blake2sM31, `PcsConfigV2`) | done (this commit; `src/air/prove_rec.zig`) | Native verify passes; the proof shape is accepted by the in-circuit verifier's types |
| REC-MASK | Multi-offset masks + optional interaction in the circuit verifier (D-024), on submodule branch `starked/multi-offset-masks` | done (this commit; `src/recursion/plain_verifier.zig`) | A circuit verifier accepts a native `prove_rec` proof of an IR AIR with offsets; differential tests against the native verifier (accept/reject agree); adversarial tests |
| REC-SMOKE | Port StarkWare's `simple_statement` custom-AIR example to Zig and verify it in-circuit | dropped (superseded by REC-MASK: our own statement path is exercised end to end) | Exercises the `Statement` extension point |
| REC-LEAF | Leaf-wrap one segment proof: the plain in-circuit verifier (D-024) as a circuit, proved by stwo-zig's circuit prover, output `Blake2s(0 ‖ pubs)` | done (0eb473a, refactor 2d89e67; `src/recursion/leaf.zig`) | 2^20 segment (4,096 headers), 70 queries: 6 s leaf prove, 5 GB peak, 0.86 MB proof |
| REC-FOLD | Node circuit: verify two children in-circuit, check `PubLink`, output the combined digest under the identity key (D-025) | done (2d89e67; `src/recursion/node.zig`) | 24 s per node at production parameters; peak 16.5 GB RSS over the full chain |
| REC-COMPOSE | Lean: valid segments whose outputs equal the next inputs compose into a valid chain from genesis (pure spec theorem over `SegmentValid`) | done (this commit: `segment_compose`) | Provable now; no circuits involved |
| REC-STMT-EQ | Lean + tests: the in-circuit evaluation of our IR equals `Expr.eval` | partly done: the DAG half is proven (`dag_correct`); the in-circuit interpreter is tested (accept + five tamper rejections) and trusted | A Lean model of the circuit builder would be needed to prove the rest; recorded in verification.md |
| AGG | Fold driver, node identity from topology, outer root verifier (`verifyRoot`); Lean `pub_compose`, `leaf_valid`, `chain_from_genesis` | done (2026-10-08: heights 0..970,347 in one 0.98 MB root proof, verified in 0.26 s; [report](../reports/2026-10-08-full-chain.md)) | |
| H200 | Run the full chain on the H200 | deferred (D-022) | Needs owner access |

## M3: block data and UTXO state

| ID | Item | Status | Notes |
|---|---|---|---|
| BLOCK-SAMPLES | Sample blocks from public APIs, bound to the proven header file | done (798ebf4; 11 blocks in `testdata/blocks/`) | `scripts/fetch_blocks.py` |
| BLOCK-SPEC | Lean spec of Core's UTXO-independent block checks (`Spec/Block.lean`) | done (798ebf4): 11 samples valid, 9 mutations rejected with Core's reason | [block-data.md](../design/block-data.md) |
| BLOCK-AUDIT | Audit `Spec/Block.lean` against Core's source | done (2026-10-08): no accept/reject discrepancy; nTime now read from the header | [block-data.md](../design/block-data.md) |
| BLOCK-AIR | Block-data AIR (components + LogUp), M3a.1–M3a.6 | M3a.1 BLK-BYTES and M3a.2 BLK-FIELDS done and proven (2026-10-08); M3a.3 BLK-SHA and M3a.4 BLK-MERKLE (txid tree) done and proven (2026-10-09, `digest_tx`, `merkle_sound`); M3a.5 BLK-CHECKS done and proven (2026-10-10, `block_sound`); M3a.6 BLK-COMMIT done and proven (2026-10-10, `commit_sound`, D-038 proposed); BLOCK-AIR complete | [block-data.md](../design/block-data.md), [airs/block.md](../airs/block.md) |
| IR-LOGUP | LogUp / lookups in the IR (Lean semantics, export, interpreter, system prover, in-circuit verifier) | done (2026-10-08): `Lookup.lean`, `LogUp.lean`, `system.zig`, plain verifier; toy `user_bytes` | Lifting (mixed sizes) not yet: pad components to one size |
| CIRCUIT-GLUE | Leaf/node glue defined in Lean, exported, replayed in Zig (gate-identical), proven: `PubLink`, `NodeOut`, digests, key | done (2026-10-08): [glue-circuits.md](../design/glue-circuits.md) | Verifier part stays VERIFIER-LEAN |
| PROOF-STORE **(in progress)** | Save MMR peak proofs to disk so new blocks extend the proven chain without re-proving it | Implemented and tested (2026-10-10): `chainproof` setup/prove/verify/inclusion, pinned production VK in `vk/`, checkpoints, extension from a file; full-chain run to a saved file in progress | [proof-store.md](../design/proof-store.md), D-036. Only valid while circuits are unchanged (the VK digest makes a change an explicit error) |
| BLAKE2S | Blake2s compression AIR (RFC 7693) with a Lean soundness proof; shared by HC-HASHTREE and BLK-COMMIT | done (2026-10-08): `compress_sound_air`, [airs/blake2s.md](../airs/blake2s.md) | D-032 |
| HC-HASHTREE | Header chain exposes a Blake2s Merkle tree over all block hashes, indexed by height: per-segment subtree roots, combined in the nodes; re-prove the chain | done (2026-10-09): `tree_root_sound`, `chain_from_genesis_T`, MMR fold, inclusion proofs; full chain re-proven ([report](../reports/2026-10-09-full-chain-tree.md)) | D-032, D-033 |
| BLOCK-DATA | Per-block proof: raw block ↔ Merkle root; Blake2s commitment to the canonical encoding, including spent outputs | done 2026-10-10 (`hash_pub`, prove-block/verify-block, D-039 proposed); full blocks need lifting for memory | [overview.md § Architecture](../design/overview.md) |
| UTXO | State module: sorted Merkle tree (Blake2s), inclusion and non-inclusion, matching Core's UTXO set; prove Core's assumeUTXO `hash_serialized` (D-037) | in progress: multiset argument built and proven at spec level; epochs from genesis run (0–170 verified) | [utxo.md](../design/utxo.md); next: coin-component Lean links, final sorted pass |
| CATCHUP | Catch up from genesis | blocked: compute (cluster/GPU + lifting), after M3b | |

## VL: the in-circuit plain verifier, proven (VERIFIER-LEAN)

Scoped 2026-10-11 (owner). Steps 1–5 of
[verifier-formalization.md](../design/verifier-formalization.md) are done: the statement mixing,
transcript order, channel, Merkle paths, leaf hashing, DEEP responses, composition and balance checks
are Lean-generated and proven, gate-identical to the hand-written leaf (mainnet VK unchanged). What
remains:

| ID | Item | Status | Done when / notes |
|---|---|---|---|
| VL-E2E | End-to-end theorem for the plain verifier: compose the proven pieces, with LogUp soundness (`logup_sz`), the fingerprint Schwartz–Zippel step and the FRI assumption as named hypotheses | todo | One theorem: "leaf circuit satisfied ⇒ the AIR constraints and lookup balance hold on the committed traces for the stated public inputs ⇒ `leaf_valid`", standard axioms; recorded in verification.md. Do first: it turns the per-piece lemmas into one statement the project can make. |
| VL-POW | The proof-of-work bit check (`LeanChannel.pow`, `extractBits`) Lean-first | todo | Program + soundness theorem, gate parity with the hand-written Zig, mainnet VK unchanged. Small. |
| VL-OODS | The shifted OODS points (one `addPoints` per distinct offset — our code) Lean-first | todo | Same pattern as VL-POW. Small. |
| VL-ORACLE | REC-FUZZ native oracle: replay the mutation campaigns through the native verifier; accept/reject must agree with the circuit | todo | Campaign run and recorded in verification.md. Tests exactly the `sv.*` code that stays trusted under VL-FRI's option (a). |
| VL-FRI | The remaining stwo-zig code inside the leaf (`sv.*`): FRI commit/decommit and folding, the first circle-to-line layer, the last layer, query selection, DEEP quotients, circle arithmetic | blocked (owner: trust boundary) | Either (a) a decisions.md entry recording them as StarkWare-derived, parity-tested, trusted; or (b) the Lean-first program treatment extended to them. (b) is weeks of effort, comparable to steps 1–5 together, and would make the whole leaf circuit Lean-generated. |
| VL-NODE | The node circuit's use of stwo-zig's recursive verifier (`stark_verifier.verify`, `CircuitStatement`) | blocked (owner: trust boundary) | A decisions.md entry: keep trusted as StarkWare-derived (the node glue is already proven), or schedule an extension as its own item. |

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
| VERIFIER-LEAN | Prove our circuits (plain verifier, node) in Lean against a spec of the native verifier | Resumed 2026-10-10 (owner); steps 1–5 done. The remaining work is scheduled as the **VL table** above (owner, 2026-10-11). |
| REC-FUZZ | Mutation testing of `plain_verifier.zig` | **done (2026-10-10)**: `src/recursion/fuzz.zig`, every guessed value and statement input of a header-chain and a LogUp-system proof; all mutations rejected by the circuit. Follow-up: scheduled as VL-ORACLE |
| SPEC-FUZZ | Differential fuzzing of the Lean header and block specs against Bitcoin Core's own C++ | **done (2026-10-10)**: `tools/specfuzz`; header kinds (SetCompact, GetCompact, retarget, block proof, CheckProofOfWork, MTP) 750k cases and block kinds (sigops, Merkle root + mutation, CheckTransaction, txid/wtxid) 100k cases, 0 mismatches; constants checked against `chainparams.cpp` |
| LOGUP-SZ | LogUp's Schwartz–Zippel step in Lean | **done (2026-10-10)**: `LogUpSZ.lean` (`logup_sz`, `balancedExt_of_poly`); side conditions discharged per system by `decide` (`LogUpSZSystems.lean`) |
| MMR-LEAN | The MMR and inclusion proofs in Lean | **done (2026-10-10)**: `Spec/Mmr.lean` (`mmr_inclusion`, `fold_eq_mmr`), Zig sides cross-checked; genesis checks from Lean (`Gadgets/RootChecks.lean`) |
| DRIFT-CI | Automate the JSON drift check and the sorry/axiom check in CI | Manual commands are in status.md for now |
| LICENSE | Choose a license | Needs an owner decision (possibly legal) |
| SIMP-LINT | Clean up unused-simp-argument warnings in the Lean files | Cosmetic |
| LEAF-ONE-PROOF | Prove each segment once (borrowed native capture) | **done (2026-10-10)**: same circuits and VK; log-19 leaf peak RSS 12.8 GB, from 17.5 GB |
