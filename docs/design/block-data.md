# Block data (M3a) — design

Status: current · Updated: 2026-10-08

Decisions taken (see the end): multi-component LogUp (D-028), spent-output slots from day one
(D-029), Blake2s commitment (D-030), duplicate inputs left to M3b (D-031). `IR-LOGUP` and
`BLAKE2S` are done. M3a.1 is done; see [airs/block.md](../airs/block.md).

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
| M3a.1 `BLK-BYTES` **(done)** | Byte table: `(pos, byte)` with range check; block length | `bytes_rows`, `read_byte` (membership per position) |
| M3a.2 `BLK-FIELDS` | Field rows tiling the stream: header, tx count, per tx (version, marker/flag, vin/vout counts, outpoint, script length + span, sequence, value, witness counts and items, locktime); canonical CompactSize; segwit flag rules | serialization ⇔ `parseBlock` (Spec/Block.lean) |
| M3a.3 `BLK-SHA` | Message-byte walker plus multi-message SHA-256 (reusing `compress_sound_air`): txid, wtxid, header hash | stream = `serNoWit` / `serWit` |
| M3a.4 `BLK-MERKLE` | txid tree with the CVE-2012-2459 check, witness tree, witness commitment | `merkleRoot` |
| M3a.5 `BLK-CHECKS` | `CheckTransaction` (values, MoneyRange, coinbase length, prevout-null), coinbase position, finality, BIP34 prefix, sigops (opcode walk over script spans), sizes and weight | `checkBlock = none` |
| M3a.6 `BLK-COMMIT` | Canonical encoding (with spent-output slots, D-029) and its Blake2s commitment (D-030); needs a Blake2s AIR | encoding spec |

### M3a.2 `BLK-FIELDS` design (2026-10-08)

**Target.** `fields_sound`: a satisfied (bytes, fields) system gives a block `b` with `Blk.WF b`
and `serBlock b = raw`. The existing round trip `parseBlock_serBlock` then gives
`parseBlock raw = some b`. So the AIR checks Core's *serializer*, which is simple; it never needs
Core's branchy parser.

**Tokens.** One row per token. Each row covers `[START, START+LEN)`; rows tile the block from 0 to
`LEN`, then padding rows (`LEN = 0`, at least one).

| Kind | Bytes | Read here |
|---|---|---|
| `BLK` | header (80) · CompactSize `nTx` | the CompactSize |
| `TXH` | version (4) · [`00 01` if segwit] · CompactSize `nIn` | marker/flag, CompactSize |
| `IN` | prevout hash (32) · n (4) · CompactSize `len` · scriptSig (`len`) · sequence (4) | CompactSize |
| `NOUT` | CompactSize `nOut` | CompactSize |
| `OUT` | value (8) · CompactSize `len` · scriptPubKey (`len`) | CompactSize |
| `WCNT` | CompactSize: stack size (segwit only, one per input) | CompactSize |
| `WITEM` | CompactSize `len` · item (`len`) | CompactSize |
| `LOCK` | locktime (4) | — |

- Opaque payloads (header, hashes, scripts, witness items, fixed-size fields) are not read here.
  Later components read them through the byte table.
- **CompactSize:** canonical forms 1/3/5 bytes, with value at most `MAX_SIZE = 2^25`. The
  9-byte form never occurs. Range checks use two 25-bit decompositions.
- **Grammar:** counters (txs, inputs, outputs, witness stacks, items) and two is-zero helpers
  choose the next row's kind.
- **Segwit:** the extended format (marker `00`, flag `01`) requires at least one non-empty
  witness stack in the transaction. That is exactly when `serWit` uses it.
- **Excluded (sound):** blocks with no transactions and transactions with no inputs. Core rejects
  both, and `Tx.WF` excludes the latter.

**Proof plan.**
1. A pure grammar layer: a token list accepted by the grammar is `serBlock` of a well-formed
   block, by structural recursion.
2. The AIR layer: rows ⇒ a grammar-accepted token list whose bytes tile `raw`, using
   `read_byte` for the bytes that are read.

### M3a.3 `BLK-SHA` design (draft, 2026-10-09)

**Target.** For transaction `t` of the parsed block `b` (from `fields_sound`), the system yields
`txid(t) = sha256d(serNoWit t)` and `wtxid(t) = sha256d(serWit t)`, and also the header hash
`sha256d(header)`. These feed the Merkle trees (M3a.4) and link the block to `T` (HC-HASHTREE).

**Byte ranges per transaction.** The fields component already knows the boundaries. At each locktime row
it yields `tx(i, a, seg, w, l)`:
- `a`: the transaction start (copied down from its head row);
- `seg`: the segwit flag;
- `w`: where the witness section starts (the row after the outputs);
- `l`: the locktime start.

Then:
- `serWit t` is raw bytes `[a, l + 4)`.
- `serNoWit t` is `[a, a + 4) ++ [a + 6, w) ++ [l, l + 4)` for segwit, and `[a, l + 4)` for legacy.

**Components.**

| Component | Rows | Does |
|---|---|---|
| `block_msg` | one per message byte (padding included) | Walks a message's ranges: raw position +1 per byte, jumping at the range boundaries taken from the `tx` tuple. Reads each byte from the byte table, appends SHA padding (`80`, zeros, the bit length), and yields 32-bit words every 4 rows |
| `block_sha` | 72 per compression | The proven SHA-256 compression AIR. Consecutive blocks of a message chain with constant offsets, as in the header chain. Each message gets one extra block that hashes the 32-byte digest, with constant padding words, giving SHA256d. Yields the final digest |

**Proof plan.**
1. The fields proof exposes each transaction's ranges: `tx_sim` already walks them.
2. The message stream equals `pad(serNoWit t)` (respectively `serWit`, or the header).
3. The compression chain equals `sha256d`, reusing `compress_sound_air`.

**Cost.** Hashing about two passes over the block (txid plus wtxid), plus padding, gives about
2 × size message rows and about 2.25 × size SHA rows. For a 4 MB block that is about 2²³ rows per
component. Without lifting (mixed component sizes), the byte table and fields must also pad to 2²³.
This is the M3 performance wall (D-027); see the decision below.

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

## Decisions (taken 2026-10-08)

The owner chose 1: multi-component (D-028); 2: slots now (D-029); 3: Blake2s (D-030); 4: this order.
The original questions follow for the record.

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
