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
