# Block AIRs (M3a)

Status: current · Updated: 2026-10-10

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

## `block_merkle` and SHA node blocks (M3a.4 `BLK-MERKLE`, txid tree done and proven)

Lean: `Block/Merkle.lean`, `Block/Sha.lean` (node blocks); proofs `Block/MerkleSound.lean`. Zig:
`src/block/merkle.zig`. Design: [block-data.md](../design/block-data.md) (M3a.4), decision D-034.

- **SHA node blocks:** a `NODE` period's message words are its children's digests, read with two
  `digest` uses at rows 11 and 19, and its tuple is read with `node(id, left, right, dup)`. `NPAD` is the
  constant padding block of a 64-byte message, and `DBL` finishes as usual.
- **Mutation check:** rows 12–19 of a node block compare word `t` with word `t − 8` limb by limb
  (is-zero flags, running product `ALLEQ`). Unless `dup`, `ALLEQ` must be 0 at row 19.
- **`block_merkle`:** one row per internal node, level by level; then the root row.
  - Node ids are `NB + row` (`NB = 2^27`).
  - Level 1's children are the txid messages `1 + 4i`, `+ 2`; higher levels' are the previous level's
    nodes.
  - The leaf count is public input 1, which the fields' first row checks.
  - The root row reads the root's digest and the header's Merkle field (the header message's words
    9–16).
- **Shapes:** SHA 144 columns, 6 lookups; Merkle 41 columns, 11 lookups. The five-component system has
  30 lookup sites per row.
- **Tests:**
  - The 5-component system proves and verifies on blocks 0, 170 and 91812.
  - Blocks 481824 and 709632 (1,866 and 2,043 transactions; 1,870 and 2,044 nodes) satisfy the SHA and
    Merkle constraints, and the roots equal the headers'.
  - Rejected: a tampered root limb; a block whose two transactions are identical (CVE-2012-2459), which
    fails at the node block's mutation check.
- **Proofs so far:** the earlier results carry over to the 5-component system (`Link`, `HashSound`).
  Byte-message digests take "the id is below `NB`" (`node_mid`: node blocks carry Merkle ids).
  `Spec.MerkleLevels`: `level_get`, `dupPair_false`, `merkleRoot_step`.

- **Soundness:**
  - **Headline, `merkle_sound`** (`Block/MerkleLink.lean`): in a satisfied 5-component system (at most
    `2^25` rows), the block parses as `b` and `merkleRoot (b.txs.map txid) = (headerMerkle b, false)`. So
    `bad-txnmrklroot` and `bad-txns-duplicate` cannot fire.
  - Merkle rows (`MerkleSound`):
    - `level_rows`, `tree_rows`: level `l` occupies rows `baseL l … + cntL l` with the expected columns;
    - `root_row`: the root row reads entry `(H, 0)`;
    - `kids`: a node row's children as tree entries.
  - SHA node blocks (`ShaSound`):
    - `node_out`: a node's output is SHA256d of its block;
    - `npad_message`: the padding block is constant;
    - `node_distinct`: a non-duplicating node block's two halves differ (the mutation check).
  - Links (`Link`, `MerkleLink`):
    - `node_row`, `digest_linked`, `merkle_word_linked`: lookup links;
    - `node_period`: a node id's second hash follows its padding and node blocks;
    - `node_children`, `node_setup`: a node block's words and children;
    - `id_digest`: every tree entry's second hash outputs that entry of the txid tree;
    - `tree_hashed`: no level has equal pairs;
    - `header_word`: the root row's words are header bytes 36–67.
  - Spec: `Spec.MerkleLevels` (`level_get`, `dupPair_false`, `merkleRoot_lvs`); `HashSpec`
    (`sha256d_pair`, `stateBytes_inj`, `stateBytes_of_words`).

**Witness tree:** done with M3a.5 (`block_wmerkle`, below).

## The checks: `block_tables`, `block_walk`, `block_ctx`, `block_wmerkle` (M3a.5 `BLK-CHECKS`, done and proven)

Lean: `Block/Tables.lean`, `Block/Walk.lean`, `Block/Ctx.lean`, `Block/WMerkle.lean`, and the fields
extension in `Block/Fields.lean` (`chkC`, `chkLookups`). Zig: `src/block/checks.zig`, `walk.zig`,
`ctx.zig`, `wmerkle.zig`, `system.zig`. Design: [block-data.md § M3a.5](../design/block-data.md#m3a5-blk-checks-design-approved-2026-10-10-d-035)
and its as-built notes; decision D-035 (with its amendments).

**System.** Nine components share one trace size: 0 bytes, 1 fields, 2 msg, 3 sha, 4 merkle,
5 tables, 6 walk, 7 ctx, 8 wmerkle; 77 lookup sites per row, `L ≤ 24`. Eight public inputs:
`len`, `nTx`, `height`, `prevMtp mod 2^16`, the BIP34/CSV/segwit bits, `prevMtp div 2^16`.

| Relation | Id | Tuple | Yielded by | Used by |
|---|---|---|---|---|
| `R8` | 9 | `(x)`, `x < 256` | tables | fields, walk, ctx range slots |
| `OPC` | 10 | opcode row `(b, pushN, isK 4c/4d/4e, sigN, nzp)` | tables | walk |
| `SCRIPT` | 11 | `(start, len)` of a non-empty script | fields | walk (first row) |
| `TOT` | 12 | `(W, NSEG, HASC)` | fields (last row) | ctx |
| `CTX` | 13 | `(cutoff lo, cutoff hi)` | ctx | fields (row 0) |
| `COMMIT` | 14 | `(start, len)` of the marked output | fields | ctx |
| `SIGOPS` | 15 | `(total)` | walk (last row) | ctx |
| `WCID` | 16 | commitment node id | wmerkle | ctx |

- **`block_tables`:** 7 periodic preprocessed columns over `0…255` (`id`, `pushN`, `isK` ×3, `sigN`,
  `nzp`) and two multiplicity columns.
- **Fields extension** (columns 118–189): per-tx finality mode (`FZ`/`FL`/`FS`, `TY`), output value
  bytes and running totals (`TLO`/`THI` with carry, `MAXLO`/`MAXHI` bounds), the non-null-prevout
  witness (`ZT`, `GIN`, one auxiliary byte read `AQ`/`BQ`), lock-time limbs against the cutoff, `W`
  and `NSEG` running sums (`DW = 2·TXH·SEG + (WCNT+WITEM)·LEN`, row-local), script spans, and the
  commitment output selection (`ISC`, `AFT`, `HASC`, `REQ` with `MML`/`MMB` mismatch witnesses).
- **`block_walk`:** one row per script byte; an automaton (`op`, push length bytes, push data,
  truncated tail) accumulating `sigW` per opcode; 51 columns.
- **`block_ctx`:** rows 0–131 of a 256-row period read the coinbase (input count, null prevout,
  scriptSig length, BIP34 push), the header time, the coinbase witness and the commitment script, and
  check the weight and sigop limits; 41 columns, 11 lookups.
- **`block_wmerkle`:** the txid tree's layout over `[0^32, wtxid(tx 1), …]` plus the commitment node
  `(root, NONCE_ID)`; 27 columns.

**Soundness.** Headline: **`block_sound`** (`Block/BlockSound.lean`, standard axioms only). A satisfied
system with `BlockPubs c pub`, `height < 2^23`, `prevMtp < 2^32` and `8 ≤ L ≤ 24` gives
`∃ b, parseBlock raw = some b` and, if no transaction repeats a prevout (M3b, D-031),
`checkBlock c raw = none`. Its parts:

| File | Result |
|---|---|
| `BlockSetup` | `Setup` (grammar context, parsed block, txs at lock rows); the fields' read oracles in block bytes |
| `BlockTxs` | `txs_basic` (inputs, outputs, values), `txs_later` (no null prevout after tx 0), `cb_facts` (coinbase shape, scriptSig, BIP34 bytes) |
| `BlockSums` | `weight_ok`, `sigops_ok` |
| `BlockFinal` | `final_ok` (every tx final for the cutoff), `bip34_ok` |
| `BlockCommit` | `commit_ok` (`commitmentIndex`, `witCheck`, or no witness) |
| `WMerkleSound`, `WMerkleLink` | witness-tree rows; `wmerkle_sound`: the commitment digest is `SHA256d(root ++ nonce)` |
| `ScriptSum` | the script multiset (`yields_eq_uses`): walker total = fields' scripts' sigops |
| `FieldsTotals`, `FieldsScripts`, `FieldsCommit`, `TxWits`, `Coinbase` | fields-side totals, script terms, output selection, witness sections, coinbase input |
| `SysLink` | the cross-component tuples (`tx0_link`, `tot_link`, `sigops_link`, `commit_link`, `cutoff_link`) and read oracles |
| `TxChecks`, `ValueSound`, `CtxSound`, `WalkSound` | per-component checks |

## The commitment: `block_undo`, `block_b2msg`, `block_b2s` (M3a.6 `BLK-COMMIT`, done and proven)

Lean: `Block/Undo.lean`, `Block/B2Msg.lean`, `Block/B2s.lean`; proofs `Block/B2MsgSound.lean`,
`Block/B2sSound.lean`, `Block/B2Bridge.lean`, `Block/B2Link.lean`; spec `Spec/BlockCommit.lean`,
`Spec/Blake2sBlocks.lean`. Zig: `src/block/commit.zig`. Design: [block-data.md § M3a.6](../design/block-data.md),
decision D-038 (amended 2026-10-10).

`C = blake2s(undo)`, with `undo = 0x01 ++ records` (one `TxOutSer`-without-outpoint per input after the
coinbase, unchecked here, D-029). The raw block is bound by the public block hash (`hash_pub`, below).
Public inputs: `pub 8` the undo length, `pub 9 + 2i + h` limb `h` of commitment word `i`, `pub 25..40`
the block hash. The system has 12 components and 41 public inputs; 96 lookup sites per row.

- **`block_undo`:** the byte table's AIR with its length read from `pub 8`, relation `UBYTE` (17).
- **`block_b2msg`:** one row per 32-bit message word of the undo stream; bytes past the length are zero.
  Active-byte flags are monotone and counted against the length, and only block 0 may start inactive,
  so the stream has `max 1 ⌈len/64⌉` blocks. Yields `b2w(block, k, lo, hi)` and `b2b(block, last, t)`.
  16 columns, 6 lookups.
- **`block_b2s`:** the proven Blake2s gadget (300 columns) plus 12: each used period hashes a block,
  chained from the previous period (never at period 0); the last block yields its digest words (`b2d`);
  rows 0–7 read `b2d(k, pub (9 + 2k), pub (10 + 2k))`.

**Soundness.** Headline **`commit_sound`** (`B2Link`, standard axioms only): in a satisfied system with
`8 ≤ L ≤ 24`, `pub (9 + 2i + h) = half16 (C i) h` where `C = hashBlocks h0 0 undo`, and
`blockCommit undo = digest C` (`blockCommit_eq`).

| File | Result |
|---|---|
| `B2MsgSound` | `prefix_of_count`, `on_prefix`, `layout`, `stream_count`, `walker_sound` |
| `B2sSound` | `period_compress` (gadget), `h_first`, `h_chain`, `tf`, `msg_word` |
| `B2Link` | `undo_read`, `walker_fact`, `period_block`, `chn_pos`, `chain_state`, `last_digest`, `digest_yield`, `commit_sound` |
| `Spec/Blake2sBlocks` | `compress_congr`, `hashBlocks_eq` (block by block) |

**The block hash** (`HashPub.hash_pub`): the context component reads `digest(0, pub 25..40)` at row 0, so
public inputs 25–40 are the limbs of `SHA256d(header)`.

**Limits.** At one shared trace size the system has about 880 columns. A block above about 3.5 MB needs
`2^23` rows, more memory than a 24 GB machine has for the in-memory check; a ~1 MB block (2²²) builds
and checks its witness in ~4 min at ~14 GB, and proving it needs more. Full blocks need per-component
sizes (lifting) or a larger machine.
