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
- **Audit against Core's source (2026-10-08, bitcoin/bitcoin master):** no
  discrepancy changes accept or reject for a canonically serialized block.
  Each rule matches, including check order, boundaries, constants and edge cases:
  - deserialization: `ReadCompactSize`, `UnserializeTransaction`;
  - `CheckTransaction`, `ComputeMerkleRoot`, `CheckBlock`, `ContextualCheckBlock`;
  - `IsFinalTx`, `GetSigOpCount`, `push_int64`/`CScriptNum`;
  - the witness-commitment index, `GetBlockWeight`, and the mainnet activation heights.
  
  Follow-ups applied: the pre-CSV finality cutoff now reads the block's own
  `nTime` from its header, where `Ctx.time` used to come from outside;
  `BlockCheck` checks each sample's header against the proven header file.
  Documented differences:
  - the spec rejects trailing bytes after a block (Core ignores them; stricter, so sound);
  - every parse failure maps to the single reason `deserialize`.
  
  `ContextualCheckBlockHeader` (`bad-diffbits`, `time-too-old`, `bad-version`)
  is proven by the header chain. `time-too-new` depends on the node's clock and
  can't be proven.

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

## Plan (decided structure, D-028; sub-milestones)

**Key idea: check serialization, not parsing.** The prover supplies the parsed fields. The AIR
checks that serializing them reproduces the raw bytes exactly. Every field is one row claiming
a span `[start, start + len)` of the byte stream; the spans tile the stream in order. Core's
deserializer accepts exactly the canonical serializations (canonical CompactSize, flag rules),
so this is equivalent. It costs rows per *field* (tens per transaction), not per byte, except
where bytes must be hashed.

**Hash inputs are a few contiguous ranges.** A legacy transaction's txid message is one
contiguous range of the raw block. A segwit one is three: version; inputs and outputs; locktime.
They skip the marker, the flag and the witness. A wtxid message is the whole transaction. A
"message bytes" component walks these ranges byte by byte. Positions increase by one except at
the known boundaries, and bytes come from the byte table by lookup. It feeds the existing SHA-256
gadget word by word.

| Sub-milestone | Content | Lean |
|---|---|---|
| M3a.1 `BLK-BYTES` | Byte table: `(pos, byte)` with range check; block length | membership lemma per position |
| M3a.2 `BLK-FIELDS` | Field rows tiling the stream: header, tx count, per tx (version, marker/flag, vin/vout counts, outpoint, script length + span, sequence, value, witness counts and items, locktime); canonical CompactSize; segwit flag rules | serialization ⇔ `parseBlock` (Spec/Block.lean) |
| M3a.3 `BLK-SHA` | Message-byte walker plus multi-message SHA-256 (reusing `compress_sound_air`): txid, wtxid, header hash | stream = `serNoWit` / `serWit` |
| M3a.4 `BLK-MERKLE` | txid tree with the CVE-2012-2459 check, witness tree, witness commitment | `merkleRoot` |
| M3a.5 `BLK-CHECKS` | `CheckTransaction` (values, MoneyRange, coinbase length, prevout-null), coinbase position, finality, BIP34 prefix, sigops (opcode walk over script spans), sizes and weight | `checkBlock = none` |
| M3a.6 `BLK-COMMIT` | Canonical encoding (with spent-output slots, D-029) and its Blake2s commitment (D-030); needs a Blake2s AIR | encoding spec |

**Duplicate inputs.** `bad-txns-inputs-duplicate` needs a uniqueness argument (sorting).
Within a block, M3b's UTXO update rejects a second spend of the same coin, so M3a may leave this
rule to M3b. The statement then says so explicitly: `BlockValid` minus duplicate inputs, plus
M3b. Owner to confirm when M3a.5 starts.

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
