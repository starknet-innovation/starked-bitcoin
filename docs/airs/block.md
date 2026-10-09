# Block AIRs (M3a)

Status: current · Updated: 2026-10-08

Design: [design/block-data.md](../design/block-data.md). One system per block,
with components linked by LogUp lookups (D-028). Component 0 is the byte table;
the others read bytes from it.

## `block_bytes` (M3a.1 `BLK-BYTES`)

Lean: `lean/StarkedAir/Block/Bytes.lean`. Zig witness: `src/block/bytes.zig`.

| Column | Meaning |
|---|---|
| 0 `POS` | Row index |
| 1 `BYTE` | The byte at `POS` |
| 2–9 | Bits of `BYTE` (the range check) |
| 10 `ACTIVE` | `1` exactly on rows `r < LEN` |
| 11 `MULT` | Free multiplicity: how often the position is read |

- **Public input:** `LEN` (`pub 0`), the block length in bytes.
- **Preprocessed columns:** `isFirst`, `notLast`.
- **Constraints:**
  - `POS` starts at 0 and steps by 1;
  - `BYTE` is the sum of its 8 boolean bits;
  - `ACTIVE` is boolean, is 1 at row 0, and is a prefix: once 0, it stays 0;
  - the drop from 1 to 0 happens at `POS = LEN`;
  - if every row is active, then `LEN` is the row count.
- **Lookup:** relation `REL_BYTE = 3`, tuple `(POS, BYTE)`, multiplicity
  `ACTIVE · MULT`.

**Theorems** (standard axioms only):

- `bytes_rows`: in a satisfied trace with `0 < n < P` rows,
  - `POS r = r`;
  - every byte is below 256;
  - `LEN ≤ n`;
  - row `r` is active iff `r < LEN`.
- `yield_sound`: a row yielding with nonzero multiplicity yields
  `(r, byte r)` with `r < LEN`.
- `read_byte`: suppose a system has `bytes` as component 0, and its other
  components read `REL_BYTE` with multiplicity `−1` or `0` (fewer than `P`
  reads). Then every read with multiplicity `−1` of `(p, b)` reads a real byte:
  `p = r < LEN` and `b` is the block's byte `r`.

**Tests:** `zig build -Dtest-filter="block bytes" test`. On the genesis block
(285 bytes), with the test reader `block_reader` (`Testing/BlockReader.lean`):

- reading the 80 header bytes proves and verifies;
- a wrong byte is rejected (`LookupsUnbalanced`);
- a read at position 300, past the end, is rejected even when the table's
  multiplicity is forged there;
- a wrong `LEN` violates the constraints.

Costs: 12 main columns, one row per byte.

## `block_fields` (M3a.2 `BLK-FIELDS`, proven)

Lean: `lean/StarkedAir/Block/Fields.lean` (grammar layer: `Spec/BlockTokens.lean`). Zig:
`src/block/fields.zig` (tokenizer and witness).

One row per token: block head, tx head, input, output count, output, witness stack count,
witness item, locktime; then padding (at least one row).

- **Tiling:** row `r` covers `[START, START + LEN)`, and the rows tile `[0, LEN_pub)`. `START`
  is range-checked below 2²⁵.
- **Reads:** only CompactSize bytes and a segwit head's marker `00` and flag `01`, through the
  byte table. Opaque payloads aren't read here.
- **Canonical CompactSize:** the 1/3/5-byte forms, with value at most `MAX_SIZE`, using two
  25-bit range checks.
- **Grammar:** counters (txs, inputs, outputs, witness stacks, items) and two is-zero helpers
  choose each row's kind from the previous row.
- **Exclusions:** blocks with no transactions and transactions with no inputs are excluded, as
  is the extended format with all-empty witnesses. Core rejects all three.
- **Shape:** 112 main columns; constraints of degree at most 3, checked by `#guard`.

**Proven** (standard axioms only):
- **Grammar layer:**
  - `toksBlock_sound`: accepted tokens are `serBlock b` of a well-formed `b`;
  - `toksBlock_parse`: Core's deserializer reads them back as `b`.
- **AIR layer** (`Block/FieldsSound.lean`):
  - row facts: one-hot kinds, transitions, is-zero decisions, counters;
  - CompactSize decoding (`compact_ser`), checking that its bytes are the block's (`compact_slice`) and
    the segwit marker (`marker_read`) through the byte table;
  - each row's token serializes to its slice (`tok_bytes`), and the rows tile the block (`tiling`);
  - the grammar runs row by row: `ins_sim`, `outs_sim`, `items_sim`, `wits_sim`, `tx_sim`, `txs_sim`,
    `block_sim`.
- **Headline, `fields_sound`:** if the (bytes, fields) system with `2^L ≤ 2^25` rows per component is
  satisfied and its lookups balance, then `parseBlock` of the block's bytes succeeds. Those bytes are a
  canonically serialized block, read back in full.

**Found while proving:** the 5-byte CompactSize's top byte needed a bound. Without it, bytes encoding
`P + v` decoded to `v` modulo the field prime and passed both range checks. Fixed with two bit columns
(95a05bc).

**Tests:**
- The 6 small samples tokenize, satisfy the constraints, and prove and verify with the byte
  table.
- The 5 large ones satisfy the constraints:

  | Block | Size | Rows | Segwit txs |
  |---|---|---|---|
  | 400000 | 949 KB | 13,669 | 0 |
  | 481824 | 989 KB | 14,939 | 7 |
  | 709632 | 1.4 MB | 36,048 | 1,714 |
  | 970347 (tip) | 1.6 MB | 53,104 | 3,558 |
  | 774628 | 3.96 MB | 522 | 36 |

- Negative cases are rejected: a script length off by one breaks the tiling, and a tampered
  CompactSize byte leaves the lookups unbalanced.

## `block_msg` and `block_sha` (M3a.3 `BLK-SHA`, done and proven)

Lean: `Block/Msg.lean`, `Block/Sha.lean`; proofs `Block/MsgSound.lean`, `Block/ShaSound.lean`. Zig: `src/block/msg.zig`, `src/block/sha.zig`.

**`block_msg`** has one row per byte of a padded SHA-256 message.
- **Messages:**
  - the header: id 0, bytes `[0, 80)`;
  - per transaction `i`, the txid message (id `1 + 2i`) and the wtxid message (id `2 + 2i`), with
    ranges from the fields tuple `tx(i, a, seg, w, l)`. A segwit txid message is split around the
    marker/flag and the witness section.
- **Bytes:** data bytes come from the byte table. The SHA padding is checked in the AIR: `80`, zeros up
  to byte 56 of a block, then the 64-bit length.
- **Alignment:** messages start at rows `≡ 0 (mod 64)`.
- **Yields:** 32-bit words `msgw(id, index, lo, hi)`, and padded lengths `mlen(id, len)`.
- **Shape:** 38 columns.

**`block_sha`** is the proven SHA-256 compression AIR, unchanged, plus per-period values: message id,
block index, and first-block / second-hash / unused flags.
- Continuation periods chain with constant offsets.
- First blocks and second hashes start from the IV.
- Message words are looked up from `block_msg`.
- A second hash checks the padded length first, so hashing can't stop early. Its message is the
  previous digest plus constant padding.
- It yields `digest(id, 16 limbs)` = SHA256d.
- Shape: 132 columns.

**Tests:**
- (bytes, fields, msg, sha) proves and verifies for blocks 0, 170 and 91812. The header digest equals
  Core's block hash, and the txid digests reproduce the header's Merkle root.
- On two segwit blocks (481824 and 709632, with 7 and 1,714 split txid messages, about 2.4 M message
  rows and up to 41,386 compressions, 2²²), the traces satisfy the constraints, and the txid digests
  reproduce the header roots.
- Rejected: a wrong message word, and a message hashed one block short.

**Proven (Lean, standard axioms only):**
- `block_sha`, `digest_sound`: a `DBL` period's digest is SHA256d of its message's words, read block by
  block from the first block, using `compress_sound_air`.
- `block_msg`, row level:
  - `whole_msg`: a header, wtxid or legacy txid message reads bytes `TA, TA + 1, …` and ends exactly
    at `TL + 3`;
  - `split_msg`: a segwit txid message reads `[TA, TA + 4)`, then piece 1 from `TA + 6` up to `TW − 1`,
    then piece 2 from `TL` up to `TL + 3`, each piece ending exactly at its boundary;
  - `pad_ok`, `pad_bytes`, `top_lt`: then `0x80`, zeros to byte 56 of a block, and the length bytes;
  - `belongs`, `word_yield`, `len_yield`: every used row belongs to a message. A word yield is the
    message's bytes `j − 3 .. j`, and a length yield is the padded length.
  - `msg_pad`: a message's rows are `Spec.Block.pad` of its data bytes. This assumes at most `2^27`
    rows, so the bit length stays below `P`.

- System linking (`Block/Link.lean`, the system bytes, fields, msg, sha):
  - `sha_use_linked`: every SHA word or length use is matched by a message yield;
  - `sha_word`: each SHA message word is bytes `j − 3 .. j` of a message with the same id, where
    `j − 3 = 64 · BLKI + 4 · (row − 4)`;
  - `sha_len`: a second hash's message has padded length `64 · (blocks hashed)`;
  - `msg_read`: a message data row reads the block byte at its position;
  - `msg_tuple_linked`: a non-header message's tuple is yielded by a fields row;
  - `lock_unique` (`Block/TxIndex.lean`): one lock-time row per transaction index; `mid_tuple`,
    `same_bytes`: messages with the same id have the same tuple and the same bytes.
- **Headline, `digest_sha256d`** (`Block/HashSound.lean`): in a satisfied hashing system (at most `2^25`
  rows), each second-hash period outputs `Spec.Block.sha256d` of the data bytes of a message with the
  period's id. `HashSpec.sha256d_eq` restates the spec as block compressions plus the digest block.

- **Transaction serializations** (`Spec/TxSplit.lean`, `Block/TxRanges.lean`, `Block/TxBytes.lean`):
  on a transaction's lock-time row, `serWit = R[TXA, START + 4)`, and for segwit
  `serNoWit = R[TXA, TXA + 4) ++ R[TXA + 6, WST) ++ R[START, START + 4)` (`tx_bytes`, `lock_tx`). The
  fields' byte-read lemmas are generic over a read oracle, so `hashSys` uses them too.
- **Messages are those serializations** (`whole_tx`, `split_tx`). `txs_rows` and `block_index` show
  the block parses as `b`, `b.header` is its first 80 bytes, and the transaction ending at the lock-time
  row with `i` lock-time rows above it is `b.txs[i]`.
- **Headline, `digest_tx`** (`Block/HashSound.lean`): in a satisfied hashing system (at most `2^25` rows)
  the block parses as `b`, and each second-hash digest is `SHA256d(b.header)` or the `wtxid`/`txid` of
  `b.txs[TI]`.
