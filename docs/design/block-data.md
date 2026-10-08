# Block data (M3a) — design

Status: draft · Updated: 2026-10-08

Awaiting owner review of the decisions at the end.

## What exists

- **Spec:** `lean/StarkedAir/Spec/Block.lean`. `checkBlock ctx raw` returns
  Core's reject reason for every UTXO-independent block rule:
  deserialization, `CheckBlock` (minus the header PoW, which the header chain
  proves) and `ContextualCheckBlock`. `BlockValid ctx raw` is
  `checkBlock ctx raw = none`. The context (`height`, `time`, `prevMtp`) comes
  from the header chain.
- **Fast execution, same spec:** `Spec/Sha256Fast.lean` proves a linear-time
  compression equal to the reference and registers it with `@[csimp]`.
- **Tests:** `lake env lean --run BlockCheck.lean <heights>`. All 11 samples in
  `testdata/blocks/` pass; they are bound to the proven header file by
  `scripts/fetch_blocks.py`. They include genesis, BIP30's 91722/91812/91842/91880,
  400000, segwit 481824, taproot 709632, the 3.96 MB 774628 and the tip
  970347. `BlockCheck.lean neg` runs 9 mutations of real blocks, each rejected
  with Core's reason (CVE-2012-2459 duplicate, tampered witness with the txid
  unchanged, value, negative value, non-final, witness before segwit, second
  coinbase, BIP34 height, empty block).
- **Audit against Core's source:** in progress (`BLOCK-AUDIT`).

## What the block proof must establish

For block `h`, with private input the raw block bytes:

1. `BlockValid ctx raw`, with `ctx` taken from the header chain.
2. Public outputs:
   - `h`;
   - the block hash, SHA256d of the first 80 bytes, which attaches the block
     to the header chain via `HC-HASHTREE`;
   - a commitment to the block's canonical encoding, for the modules
     ([overview.md § Architecture](overview.md)).

Lean target: `block_sound : AIR satisfied → BlockValid ctx raw ∧ outputs decode correctly`.

## Proposed structure: components linked by lookups (needs `IR-LOGUP`)

Blocks are variable-length data: transactions, scripts and witnesses of any
size. Fixed-offset AIRs cannot follow them, so the block proof needs several
components that exchange values through LogUp lookups:

| Component | Rows | Does |
|---|---|---|
| Byte stream | one byte per row (or 4) | The raw block with its position |
| Parser | one byte per row | Core's deserializer as a state machine: CompactSize decoding, segwit flag logic, field boundaries. Emits field events (tx start/end, value bytes, script bytes, witness items) |
| SHA-256 | 72 rows per compression (reuses the proven gadget) | Hashes three streams: the txid serialization (raw bytes minus the marker, flag and witness), the wtxid serialization (raw bytes) and the header |
| Merkle | one row per internal node | txid tree with the mutation check; witness tree; witness commitment |
| Checks | per tx / per output / per input | values and MoneyRange; duplicate inputs (sorted copy plus permutation); coinbase rules; finality; BIP34 prefix; sigop counting (a second, script-level state machine); weight counters |

**Soundness model for lookups:** Lean treats a lookup as multiset inclusion
between the components' emitted tuples; LogUp's cryptographic soundness
(Schwartz–Zippel over QM31) is trusted with Stwo. This mirrors how the AIR
proofs treat the STARK itself.

## Cost (rough, to be measured)

A 4 MB block is about 4 M parser rows plus about 2.5 passes of SHA-256 over
the bytes, roughly 2²⁴ rows in all. At the 2026-10-08 CPU rate (2²⁰ rows in about 16 s) that is
about 4–5 min per full block. The chain is a few hundred GB, so a full-chain
block run on CPU would take months. This is the performance wall D-027 expects;
GPU work starts when we get there. Early blocks are tiny and fast.

## Decisions for the owner

1. **Multi-component AIR with LogUp** (recommended) versus a monolithic AIR.
   Recommended, because variable-length data needs it anyway and
   `HC-HASHTREE` needs it too.
2. **The commitment's content now:** the overview plans a canonical encoding
   that includes each input's spent output (amount, script, height, coinbase
   flag), which M3b verifies. Fix the layout now with those slots (no re-prove
   later) or commit to the raw block only in M3a?
3. **The commitment hash:** Blake2s (native in the recursion circuit) or
   Poseidon2 over M31 (much cheaper inside AIRs).
4. **Order:** `IR-LOGUP` (Lean semantics, export, interpreter, the plain
   in-circuit verifier) first, then the parser, then SHA streams, Merkle and checks.
