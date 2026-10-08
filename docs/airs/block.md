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

## `block_fields` (M3a.2 `BLK-FIELDS`, AIR defined; soundness proof in progress)

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

**Proven:** the grammar layer.
- `toksBlock_sound`: accepted tokens are `serBlock b` of a well-formed `b`.
- `toksBlock_parse`: Core's deserializer reads that back as `b`.

**To prove:** rows ⇒ accepted tokens whose bytes tile the block.

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
