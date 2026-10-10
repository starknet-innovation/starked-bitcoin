# Block data (M3a) — design

Status: current · Updated: 2026-10-09

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

### M3a.4 `BLK-MERKLE` design (draft, 2026-10-09)

**Target.** `merkle_sound`: in a satisfied (bytes, fields, msg, sha, merkle) system, with `b` the parsed
block, `merkleRoot (b.txs.map txid) = (headerMerkle b, false)`. That is, the root matches the header
field and no level is mutated (`bad-txnmrklroot` and `bad-txns-duplicate` cannot fire).

**Inner nodes are SHA messages.** A node's message is its children's digests, 64 bytes. As SHA-256
words, these are the left child's 8 state words, then the right child's: no byte shuffling. The SHA
component gets two new period kinds:
- `NODE`: the first block of a node message. It starts from the IV. Words 0–7 are the left child's
  digest and words 8–15 the right child's, read with two `digest` uses. It also uses the node's tuple
  `node(id, left, right, dup)` from the Merkle component.
- `NPAD`: the second block, the constant padding of a 64-byte message (`0x80000000`, zeros, `512`). It
  must follow a `NODE` period of the same id.
- The existing `DBL` period finishes the hash. Its length check `mlen(id, 128)` is yielded by the
  Merkle component for node ids, so `DBL` stays uniform.

`NODE` periods also check the mutation rule. Unless the node duplicates an odd last child (`dup`), the
two digests differ in some 16-bit limb. Per word row there are is-zero flags for the two limb
differences, a running product, and at the period end `NODE · (1 − dup) · alleq = 0`.

**The Merkle component.** It has one row per internal node, level by level.
- Columns: level size `CNT` and previous size `PCNT` (`2·CNT = PCNT + odd`), index `I`, the level's
  first row `BASE`, and the previous level's first row `PBASE`.
- Ids: node ids are `2^27 + row`, disjoint from message ids (`< 2^26 + 2`). Leaves are the txid
  messages, `1 + 2·j`.
- Children: on level 1, `left = 1 + 4i` and `right = left + 2`. On level `l > 1`,
  `left = 2^27 + PBASE + 2i` and `right = left + 1`. The last odd child pairs with itself
  (`right = left`, `dup = 1`).
- The leaf count is the block's transaction count. It is a new public input (`pub 1 = nTx`), which
  the fields' first row checks (`VAL = pub 1`).
- The root row (`CNT = 1`) uses `digest(root)` and compares its limbs with the header's Merkle field.
  That field is bytes 36–67, read as the header message's words 9–16 through `msgw(0, 36 + 4k, lo, hi)`.
  In internal byte order, digest word `k` is exactly those big-endian bytes.

**Soundness.** By induction on levels, every node id's digest is `sha256d(left ‖ right)` of its
children's digests (`digest_sound` extended to `NODE`/`NPAD` periods). Leaves are `txid (b.txs[j])` by
`digest_tx`. So the root row's digest is `merkleRoot` of the txids, read through `Spec.level`
(`(level l)[i] = sha256d (l[2i] ++ l[min (2i+1) (len−1)])`). The inequality flags give `dupPair = false`
on every level.

**Later (with M3a.5).** The witness tree uses the same machinery over `[0^32, wtxid(tx1), …]`. Its
commitment check (`sha256d(root ‖ nonce)` against the coinbase's last commitment output) depends on the
height and is contextual, so it goes with the M3a.5 checks.

**Stages.**
1. Spec: `Spec.level` by index, and `merkleRoot` as iterated levels.
2. SHA: `NODE`/`NPAD` periods and the mutation flags (Lean AIR, Zig witness, tests).
3. The Merkle component (Lean AIR, Zig witness, tests), and a 5-component system proof on samples.
4. Lean soundness.

**Duplicate inputs.** `bad-txns-inputs-duplicate` needs a uniqueness argument (sorting).
Within a block, M3b's UTXO update rejects a second spend of the same coin, so M3a may leave this
rule to M3b. The statement then says so explicitly: `BlockValid` minus duplicate inputs, plus
M3b. Settled by D-031 (owner, 2026-10-08): M3b's obligation.

### M3a.5 `BLK-CHECKS` design (approved 2026-10-10, D-035)

**Target.** `block_sound`: a satisfied block system, with public inputs `blockPubs ctx len nTx`, gives
`∃ b, parseBlock raw = some b`, and

    (∀ t ∈ b.txs, nodupBy (t.vin.map (·.prevout))) → checkBlock ctx raw = none

The duplicate-inputs premise is M3b's obligation (D-031). Side conditions on the context:
`height < 2^23` (the BIP34 push is then 4 bytes; that height is about 140 years away) and
`prevMtp < P` (until about 2038; revisit before then).

**Step 0: flatten the spec (pure Lean, no AIR).** `checkBlock` is a chain of `if`s that returns the
first error. Proving `= none` only needs every condition. `Spec/BlockFlat.lean` proves
`checkBlock c raw = none ↔ ∃ b, parseBlock raw = some b ∧ BlockOK c b`, where `BlockOK` is a
conjunction of independent per-block, per-tx, per-input and per-output facts. It also proves these
simplifications, which shrink the AIR:

| Spec rule | Equivalent fact the AIR checks | Why |
|---|---|---|
| per-output `vout-negative`, `vout-toolarge`, `txouttotal-toolarge` | every value `≥ 0` and the tx's total `≤ MAX_MONEY` | with non-negative values, every prefix sum and every value is at most the total |
| `bad-txns-oversize`, `bad-blk-length` (count and stripped size) | `weight ≤ 4,000,000` | `4·stripped ≤ 3·stripped + total`; each tx's stripped size is at least 10 bytes and at most the block's |
| `bad-cb-multiple` | no input of a tx with index `≥ 1` has a null prevout | that is already `bad-txns-prevout-null`; a second coinbase is such a tx |
| `bad-txns-vin-empty` | nothing | excluded by `Tx.WF` (M3a.2) |
| `sigOps` (the `ops` walk) | a byte automaton: skip push data, count `ac/ad` (+1) and `ae/af` (+20) | a truncated push (or truncated length bytes) ends `ops`. Skipping to the script's end does the same, since skipped bytes are never opcodes |
| `isFinal` | per tx: `lockTime = 0`, or `lockTime < threshold`, or every sequence is `0xffffffff` | as written |
| `commitmentIndex` | the last coinbase output matching the pattern; no later output matches | as written |

Each simplification is a lemma, and `BlockCheck.lean` cross-checks `BlockOK` against `checkBlock` on
the samples and the 9 mutations.

**Public inputs.** These are added after `pub 0 = len` and `pub 1 = nTx`:

- `pub 2 = height`
- `pub 3 = prevMtp` (amended: `pub 3 = prevMtp mod 2^16` and `pub 7 = prevMtp div 2^16`; see below)
- `pub 4..6`: the activation bits `[height ≥ BIP34]`, `[height ≥ CSV]` and `[height ≥ SEGWIT]`

The verifier and glue compute all of them from the header chain, as they already do for the
height. Making the bits public avoids comparisons on public values inside the AIR. The statement
takes `pubs = blockPubs ctx len nTx` as a hypothesis.

**New shared gadget: a 16-bit range table** (amended: built as an 8-bit table; see below). A fixed component with `2^16` rows: a preprocessed value
column, a multiplicity column and relation `REL_R16`. A value `x` is in `[0, B]` when `x` and `B − x`
are both in the table, or are split into in-table limbs. Bit columns, as in the fields component,
would cost about 30 columns per comparison; this costs one or two lookup sites.

**Fields component: per-token checks (rows: tens per tx; extra width is cheap).**

- **`OUT`** reads the 8 value bytes, at `START … START+7`:
  - byte 7 = 0, and bytes 3–6 form a hi limb `< 2^27` (range lookups), so the value is in
    `[0, 2^51)`;
  - a per-tx running total, two limbs with a carry, resets at `TXH`;
  - `LOCK` checks `MAX_MONEY − total ≥ 0` in limbs.
- **`NOUT`**: `VAL · INV = 1` (outputs are not empty).
- **`IN` of a tx with `TXI ≥ 1`** (a flag carried from the first `LOCK` row) shows a non-null prevout.
  The prover picks a position `q < 36` and the byte there, then shows either `q < 32` and the
  byte `≠ 0`, or `q ≥ 32` and the byte `≠ 0xff`. That takes one byte lookup, an inverse and the bits
  of `q`.
- **Finality**, with a mode per tx (three bits, summing to 1):
  - `ZERO`: the 4 lock-time bytes read as 0;
  - `LT`: the bytes are read and `byte3 < 128`, so `lockTime < 2^31` is exact in the field. With
    `TY = [lockTime ≥ 500,000,000]`, checked by two range comparisons, the threshold is
    `T = TY·cutoff + (1−TY)·height`, and `T − 1 − lockTime ≥ 0`;
  - `SEQ`: every `IN` row of the tx reads its 4 sequence bytes as the constant `0xff`, at
    `START + LEN − 4`, with multiplicity `SEQ·K_IN`.

  `cutoff` comes from a `ctx` tuple (below).
- **Witness bytes**: `W += SEG·(2 + START − WST)` on `LOCK` rows. This is the marker, flag and
  witness section, so `stripped = len − W` and `weight = 4·len − 3·W`.
- **Segwit count**: `NSEG += SEG` on `TXH` rows.
- **Script spans**: `IN` and `OUT` rows with a non-empty script yield `script(start, len)`, where
  `start = START + OFF + csLen`, with multiplicity 1. These feed the sigop walker.
- **Coinbase commitment candidates** (`OUT` rows of tx 0, segwit bit on):
  - `MATCH` is either `len ≥ 38` with the 6 bytes `6a24aa21a9ed` read as constants, or a mismatch
    witness: `len ≤ 37` (range), or a position `q < 6` whose byte differs from the pattern (inverse).
  - `CPOS` carries the latest match's script start; `HASC` carries whether one was seen.
- **Last row** yields `totals(W, NSEG, HASC, CPOS)` to the `ctx` component.

**Sigop walker (new component, one row per script byte).**

- Each script starts at a row using `script(start, len)` from the fields component.
- Rows walk `pos = start … start+len−1` and read `byte(pos, b)`.
- Classification is a lookup into a 256-row opcode table `(b, push_n, pd_k, sig)`:
  - `push_n`: the direct push length for `b < 0x4c`;
  - `pd_k`: 1, 2 or 4 length bytes for `4c/4d/4e`;
  - `sig`: 0, 1 or 20.
- State per row: `OP` (an opcode byte), `LB` (a length byte, with its index), `DATA` (a skipped
  byte), and the remaining skip count `R`.
  - A push sets `R`. The next row is `DATA` while `R ≠ 0`, via an is-zero test.
  - The script may end while `R > 0`; that is the truncated-push case.
  - `PUSHDATA4`'s length can exceed `P`. If its top byte is `≥ 2` the push is at least `2^25`, so it
    always runs to the end; an `INF` flag replaces `R`.
- `SIGOPS += OP·sig` across all scripts. The last row yields `sigops(total)` to `ctx`.

Soundness needs every yielded span to be walked exactly once, not only membership. LogUp balance
gives `#yields = #uses` per tuple when counts are below `P`. Spans are distinct, since their starts
differ. The walker uses spans only on its first rows.

Cost: one row per scriptSig and scriptPubKey byte, at most the block length, usually much less.
Merging the walker into the msg component, which already walks these bytes, is a later
optimization.

**Witness tree and commitment (Merkle and SHA reuse; no SHA change).**

- Two pseudo-digests come from the `ctx` component, with ids outside the message and node ranges:
  `ZERO_ID = 2^28` (32 zero bytes) and `NONCE_ID = 2^28 + 1` (the coinbase nonce).
- The Merkle component gains a tree bit `WT`. Witness-tree level 1 uses `left = 2 + 4i`, the wtxid
  messages, except leaf 0, which is `ZERO_ID`.
- Witness-tree nodes yield their node tuple with the 4th entry set to 1. In SHA that entry only
  gates the mutation check (`NNE = NODE·(1 − NDUP)`). Core ignores mutation in the witness tree, so
  this matches it. The txid tree keeps `WT = 0`, so `merkle_sound` is unchanged in substance.
- One extra Merkle row is the commitment node: `(witroot, NONCE_ID)` with the check off. Its digest
  is `sha256d(witroot ‖ nonce)`, which is exactly Core's check.
- Built only when the commitment is active, that is when the segwit bit is on and `HASC` is set.
  Otherwise there are no witness rows.

**`ctx` component (new, small fixed layout).** It does the once-per-block reads and comparisons.
Preferred layout: one row per read, with preprocessed offsets and constants, so the Lean proof is one
uniform row lemma.

- It uses `tx(0, A0, SEG0, W0, L0)` for the coinbase position, `totals` and `sigops`.
- **Coinbase shape**:
  - byte `A0 + 4 + 2·SEG0 = 0x01` (one input; the 1-byte CompactSize is canonical);
  - 32 zero hash bytes, then `ff ff ff ff`;
  - the scriptSig length byte `s` in `[2, 100]`, by two range lookups (a 1-byte CompactSize, since
    `s < 253`).
- **BIP34** (bit on): `s ≥ 4`, and the next 4 bytes are `03 h0 h1 h2`, with `h0 + 256·h1 + 65536·h2 =
  pub 2`, bytes range-checked and `h2 < 128`. That is `pushHeight` for heights in `[2^15, 2^23)`;
  BIP34 starts at 227,931.
- **Cutoff**: `cutoff = csv·pub 3 + (1 − csv)·time`, where `time` is header bytes 68–71 read from the
  byte table, with byte 71 `< 128` (true for every header before 2038) so it is exact in the field. It yields `ctx(cutoff)` for the fields' `LOCK` rows.
- **Commitment** (segwit bit on and `HASC`):
  - coinbase witness `W0`: `01 20` and 32 nonce bytes, `L0 = W0 + 34` (exactly one 32-byte item);
  - it yields `digest(NONCE_ID, nonce limbs)`;
  - it reads 32 bytes at `CPOS + 6`;
  - it uses `digest(COMMIT_NODE, those limbs)`.
- **No commitment** (bit off, or no `HASC`): `NSEG = 0`, since no tx has a witness
  (`unexpected-witness`).
- **Totals**:
  - `4,000,000 − (4·pub 0 − 3·W) ≥ 0`;
  - `20,000 − SIGOPS ≥ 0`, since the spec checks `sigops · 4 ≤ 80,000`;
  - both in limbs.

**System.** Today's five components are bytes, fields, msg, sha and merkle. This adds `r16`, `opc`,
`walk` and `ctx`, for nine. New relations:

| Relation | Tuple |
|---|---|
| `REL_R16` | `(x)` |
| `REL_OPC` | the opcode table row |
| `REL_SCRIPT` | `script(start, len)` |
| `REL_TOT` | `totals(W, NSEG, HASC, CPOS)` |
| `REL_SIGOPS` | `sigops(total)` |
| `REL_CTX` | `ctx(cutoff)` |

`REL_DIGEST` gains the two pseudo-ids.

**Stages** (each with Lean AIR, Zig witness and tests, then the Lean proof):

1. **M3a.5a, spec** — **done (2026-10-10, `Spec/BlockFlat.lean`, standard axioms only):**
   - `checkBlock_none_iff`, with `CtxFreeOK` and `CtxOK`;
   - `checkTx_none_iff` (`TxOK`) and `values_ok_iff`;
   - `size_of_weight`;
   - `walk_eq_sigOps` (the byte automaton is `sigOps`);
   - `commitmentIndex_eq` / `commitmentIndex_some` (last matching output);
   - `not_coinbase_of_inputs`.

   The equivalences make a runtime cross-check unnecessary.
2. **M3a.5b, per-tx checks**: the range table, public inputs 2–6, and the fields extensions (values,
   non-empty outputs, non-null prevouts, finality, `W`, `NSEG`, `totals`). Lean: per-tx facts of
   `BlockOK`.
3. **M3a.5c, coinbase and context**: the `ctx` component (coinbase shape, BIP34, cutoff, weight).
   Lean: the coinbase, BIP34, finality and weight parts.
4. **M3a.5d, sigops**: the opcode table and walker. Lean: `walk = Σ sigOps`, and the bound.
5. **M3a.5e, witness**: the witness tree, the commitment node and pseudo-digests, and the
   commitment check. Lean: the `checkBlockContextual` witness branch.
6. **`block_sound`**: assemble `BlockOK` and the `BlockFlat` equivalence.

**Tests.**

- All 11 samples prove or satisfy, including 774628 (3.96 MB) for row counts.
- Each of the 9 `BlockCheck neg` mutations is rejected at the expected constraint, plus new ones:
  - a sigop-heavy synthetic script;
  - a truncated `PUSHDATA4`;
  - a commitment output followed by a later decoy;
  - nonce length 33;
  - a non-final tx with one non-`ff` sequence;
  - `lockTime` exactly at the threshold.

**Risks.**

- The `ctx` row layout and the number of lookup sites. The component is tiny, so site count barely
  matters for cost, but it grows the Lean site enumeration.
- The walker's state machine is the largest new AIR. `ops`' spec is subtle: a truncated length
  stops, and so does a truncated push. Stage 1 proves the automaton equivalence first, so the AIR
  targets a simple spec.
- The time-based thresholds (`prevMtp`, header time) are kept below `P` by hypothesis. Past about
  2038 the comparison must move to limbs.

### M3a.5 as built (2026-10-10)

**Done and proven.** `block_sound` (`Block/BlockSound.lean`) holds with standard axioms only; the
proof map is in [airs/block.md](../airs/block.md#the-checks-block_tables-block_walk-block_ctx-block_wmerkle-m3a5-blk-checks-done-and-proven).
Changes from the design (D-035 amendments):

- **8-bit range table.** The nine components share one trace size; a `2^16` table would set
  `L ≥ 16` for every block. Values are split into bytes (`block_tables`, `R8`).
- **Eight public inputs.** `prevMtp` is public as two 16-bit limbs (`pub 3` low, `pub 7` high). With
  private limbs and one public value, `lo + 65536·hi ≡ prevMtp` also admitted `prevMtp + P`, a loose
  cutoff. The side conditions are `height < 2^23` and `prevMtp < 2^32`; the cutoff and lock times
  are compared in 16-bit limbs, so the 2038 limit in the risks below no longer applies.
- **Statement.** With `BlockPubs c pub` (`pub 2..7`), `8 ≤ L ≤ 24`:
  `∃ b, parseBlock raw = some b ∧ ((∀ t ∈ b.txs, nodupBy (t.vin.map (·.prevout))) → checkBlock c raw = none)`.
  `pub 0 = len` and `pub 1 = nTx` are fixed by the trace.
- **Relations.** As built: `R8`, `OPC`, `SCRIPT`, `TOT (W, NSEG, HASC)`, `CTX (cutoff limbs)`,
  `COMMIT (start, len)`, `SIGOPS`, `WCID`; the commitment output's position travels in `COMMIT`, not
  `TOT`.

### M3a.6 `BLK-COMMIT` design (proposed 2026-10-10, D-038; built and proven 2026-10-10)

**What it commits.** The block proof outputs, as public inputs, an 8-word Blake2s-256 commitment

    C = blake2s(blake2s(raw) ++ blake2s(undo))

- `raw` is the block's bytes (the byte table).
- `undo` is a version byte `0x01`, then the prover's spent-output records (D-029): one per input of
  every transaction after the coinbase, in block order. Each record is Core's `TxOutSer` without the outpoint:
  - `code = height·2 + coinbase` (4 bytes, LE);
  - the amount (8 bytes, LE);
  - the script, with its CompactSize length.

M3a hashes `undo` without checking it (D-029); M3b proves that the records equal the coins it removes.
Records are self-delimiting and follow input order, so M3b reads them alongside the parsed inputs.
Each record plus the input's outpoint is exactly `TxOutSer`, which assumeUTXO's `hash_serialized` hashes
(D-037).

**Why two inner hashes.**
- `blake2s(raw)` lets a module open the raw block with Blake2s alone, without redoing SHA256d and the
  Merkle tree.
- `blake2s(undo)` is independent of the block bytes, so a module that needs only the spent outputs
  opens only them.
- The outer hash is one compression (64 bytes).

**Components** (one shared trace size):
- **`undo` byte table:** like `block_bytes`, a `(pos, byte)` table with a range check. Its length is
  public input 8. The stream starts with a version byte `0x01` (so the table is never empty).
- **`b2msg`:** a byte walker for the two streams and the outer message. It reads bytes by lookup,
  packs little-endian 32-bit words as 16-bit limbs, zero-pads the last block, and yields
  `b2word(stream, block, k, lo, hi)`.
- **`b2s`:** the proven Blake2s compression, 88 rows per block. It reads its 16 message words and
  chains `h` from the previous block of the same stream. The counter `t` and final flag `f` are
  derived from the stream's length. The outer hash's message is the two inner digests. Its output
  words' 16-bit limbs are public inputs 9–24.

**Lean target.** `commit_sound`: in a satisfied system, `pub 9..16` equals
`blake2s(blake2s(raw) ++ blake2s(undo))`, as words, with `raw` the block's bytes and `undo` the undo
table's bytes. It extends `block_sound`'s statement.

**Stages.**
1. `Spec`: the commitment `blockCommit raw undo`, and a pure-Zig cross-check against `std.crypto`
   Blake2s.
2. AIRs and witnesses (`undo`, `b2msg`, `b2s` as a block component), with tests.
3. Lean: the message walker reads the stream (`b2msg_sound`); chained compressions compute
   `hashBlocks` (`chain_sound`, using `compress_sound_air`); the outer hash; `commit_sound`.

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
