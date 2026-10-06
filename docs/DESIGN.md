# starked-bitcoin — design

Status: draft, 2026-10-06. This records the decisions made so far. Sections marked
**OPEN** are still being worked out.

## Goal

Generate STARK proofs (Stwo, circle STARKs over M31) of:

1. **Chain:** a valid Bitcoin header chain from genesis to height `H`, with
   cumulative work `W`.
2. **State:** the full UTXO set at height `H`, committed as a canonical sorted
   Merkle tree. Proofs support both **inclusion and non-inclusion**.
3. Later modules, without re-proving the base: script and signature validation,
   historical indexes, an OP_RETURN index.

Proving runs on big machines (H200 / CUDA in production, Apple Metal locally).
Verification runs on small machines: desktop first, browser and phone later.

Non-goals for now:
- Deciding which chain is canonical. The proof shows that a valid chain with
  work `W` exists; verifiers compare it against other chains themselves.
- Query-server design.
- Browser verification.

## Prover stack

- **stwo-zig** is pinned as a git submodule at `third_party/stwo-zig`.
  Bitcoin-specific AIRs live in this repo. Generic changes go into a stwo-zig
  fork and are upstreamed when they are useful to others: native-AIR recursion
  statements, GPU codegen for custom AIRs, and constraint-IR export.
- **Native AIRs**, not Cairo. Raito (Cairo) is kept as a reference spec and a
  differential-test oracle.
- **Hash for our own commitments:** Blake2s, used for the state tree and
  block-data commitments. Bitcoin's own SHA-256d is proven as-is.

## Trust model

- **assumevalid:** scripts and signatures are not checked yet. Proof-of-work
  vouches for them. The script module (secp256k1, Schnorr, interpreter) plugs in
  later.
- Everything else Bitcoin Core enforces on headers, transaction structure,
  amounts and the UTXO set is proven.
- **Trusted:** soundness of Stwo/FRI/LogUp, plus the pinned toolchain.
  Formal verification aims to remove trust in our own AIRs (see below).

## Architecture: prove block data once, then attach modules

```
                       ┌─► state module   : UTXO root_in → root_out
block-data proof ──────┼─► script module  : all scripts/sigs valid   (later)
 (per block)           ├─► opreturn module: OP_RETURN index update   (later)
      ▲                └─► history module : history root update      (later)
 header-chain proof
```

- **The block-data proof.** For each block it checks the raw block against the
  header's Merkle root. It outputs a Blake2s commitment to a canonical,
  ZK-friendly encoding of that block. The encoding includes, for each input, the
  output it spends (amount, full scriptPubKey, height, is_coinbase), like
  Bitcoin Core's undo data. Witness data is committed too, so the script module
  can be added later.
- **Modules.** Each module proves statements about that commitment only. Adding
  a module means proving it for every block and re-running aggregation; nothing
  else is re-proven.
- **Parallelism.** A full node precomputes, for every block, `root_in`,
  `root_out` and witness hints, in the same way stwo-zig consumes Starknet PIEs.
  Blocks are proven independently and then aggregated in a tree. The
  aggregation step checks that adjacent blocks link up: `prev_hash`, roots and
  cumulative work.

## State tree (UTXO set)

- A canonical sorted (indexed) Merkle tree hashed with Blake2s. The root depends
  only on the set's contents, not on insertion order.
- Leaf: `{outpoint, amount, scriptPubKey, height, is_coinbase}`, fixed from day
  one so that adding modules later never forces a re-prove.
- Indexes:
  - by outpoint (membership and non-membership);
  - by `(script_hash, outpoint)` with sum annotations (exact balance, "empty").
  - **OPEN:** one combined tree or two.
- Matches Bitcoin Core's UTXO set exactly:
  - unspendable outputs (OP_RETURN and others) are excluded;
  - BIP30's duplicate coinbases at blocks 91842 and 91880 are handled;
  - the genesis coinbase is excluded.
- OP_RETURN outputs are tracked in a separate module/index.
- **Oracle:** the canonical root can be recomputed from `bitcoin-cli
  dumptxoutset` at any height, independently of any proof.

## Single source of truth for constraints — DECIDED: Lean-first

Soundness depends only on what the **verifier** evaluates: the native verifier
plus the in-circuit evaluator used for recursion. Prover kernels (CUDA/Metal)
affect completeness only. Plan:

- Each AIR is written **once**, as an evaluation function that is generic over
  the evaluator (Stwo's `EvalAtRow` pattern).
- stwo-zig already has a symbolic `ExprEvaluator` (with next-row offsets and
  LogUp) and a canonical, digest-identified `ConstraintProgram`
  (`src/core/constraint_framework/`). The Cairo frontend already generates GPU
  evaluation code from programs of this kind.
- From one program we derive:
  1. verifier-side evaluation, ideally by **interpreting the program itself**,
     so that the verified artifact is exactly what the verifier runs;
  2. the recursion circuit evaluator;
  3. CUDA and Metal kernels;
  4. a Lean export.
- The program's digest is bound into the proof statement.
- **Decided (spike, 2026-10-06; see `docs/spike-results.md`):**
  - AIRs are defined in Lean (`lean/StarkedAir/`), where their soundness is
    proven.
  - They are exported to canonical JSON (`airs/*.json`, schema
    `starked-air-v0`).
  - Zig consumes that JSON verbatim. Zig-side builders are for tests only.
  - Preprocessed columns are defined by the AIR, and the verifier pins their
    commitment root.

## Formal verification plan

Tiers:

0. Differential tests (Bitcoin Core, Raito, FIPS 180-4 vectors) and tests with
   tampered witnesses.
1. A Z3 search for under-constrained witnesses, adapted from stwo-zig's
   `scripts/air_uniqueness_board.py`.
2. Lean 4, per row: SHA-256 spec, gadget lemmas (u32 add with carry, XOR/range
   tables, rotations, σ/Σ, Ch/Maj), per-row soundness.
3. Lean 4, across rows: 64 rounds, message schedule, header-chain linkage, and
   LogUp balance → multiset relations.

The statement to prove for the header chain: if the trace satisfies the
constraints and the lookups balance, then each row computes SHA256d (FIPS
180-4), and the chain obeys Bitcoin Core's rules:
- prev-hash linkage;
- `hash ≤ target`;
- the nBits retarget (`GetNextWorkRequired`);
- timestamp > median-time-past of the last 11 blocks;
- cumulative work += ⌊2²⁵⁶/(target+1)⌋.

The "no more than 2 hours in the future" rule depends on wall-clock time and is
out of scope.

## Milestones

1. **M1:**
   - SHA-256 compression AIR (CPU, then Metal);
   - header-chain AIR, proving blocks 0..N locally;
   - benchmark against Raito's Cairo SHA-256;
   - constraint-IR design;
   - formal verification tiers 0–1.
2. **M2:** CUDA codegen, the native-AIR recursion statement, and parallel
   aggregation of the header chain to the tip on the H200.
3. **M3:** the block-data proof and the state module (sorted UTXO tree);
   catch-up from genesis.
4. **Later:** script module, OP_RETURN and history modules, browser verifier.
