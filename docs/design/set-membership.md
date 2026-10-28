# Coin-set membership (D-050)

Status: current · Updated: 2026-10-28 (circuit, root, proofs, CLI and the Lean soundness of the root done; GPU run pending)

Part of the coin-set pass ([set-pass.md](set-pass.md)).

The pass also proves a Merkle root over the set's records, so a coin's presence (or absence) in a proven
set is checked with ~1 KB.

- **Leaf** `i`: `Blake2s-256(key(i − 1) ‖ encRec(record i))`, with `key` the 36-byte outpoint key (txid
  bytes, then `vout` big-endian: the sort order) and 36 zero bytes before the set's first record. A
  leaf message is at least 93 bytes, so it is never a node's 64-byte message.
- **Node**: `Blake2s-256(left ‖ right)` (one compression, counter 64, final).
- **Segment tree**: heap-indexed over `2·HALF` slots (`HALF` public, a power of two per pass): node `j`
  (`1 ≤ j < 2·HALF`) hashes nodes `2j`, `2j + 1` when `j < HALF`, else slots `2(j − HALF)`,
  `2(j − HALF) + 1`; slot `s` is record `s`'s leaf when `s` is below the segment's record count, else 32
  zero bytes. Node 1 is the segment's root (public).
- **Set root**: the segment roots combined by the set tree (its node hashes `left ‖ right`), so the
  pass's root follows the set tree's shape.
- **Proofs**: membership is the record, the previous key, and the path (siblings and sides) from its
  leaf to the set root; non-membership of an outpoint is the leaf whose previous key is below it and
  own key above it (or the last record, whose key the final state gives).

**Components** (the segment system grows from nine to twelve):

| Component | Rows | Role |
|---|---|---|
| `set_rec` | per record | also yields the previous key as 9 words, `pkey(r, w, lo, hi)`, and `rec` twice (the stream and the leaf walker each consume it once) |
| `set_lw` | per leaf-message word | each record's message `key(r − 1) ‖ record r` as little-endian words, 16 rows per block; words 0–8 from `pkey`, the rest from the byte table; yields `lw(r, b, k, lo, hi)` and per block `lb(r, b, last, t)` |
| `set_lc` | 88 per block | Blake2s compressions (the gadget), per record: the IV on its first block, chained after; counter and final flag from `lb`; the last block yields `leaf(r, digest)` |
| `set_mt` | 88 per node | one compression per node of `left ‖ right` (counter 64, final); children from `node` or `leaf` yields (zero past the record count, by range-checked flags); yields `node(j, digest)`; row 0 consumes `node(1, ROOT)`, so the root is computed and public |

Public inputs: `ROOT` (16 limbs at 550), `HALF` (566); 567 in all. The record count must not exceed
`2·HALF`, and `1 ≤ HALF ≤ 2^24` (both checked in `set_mt`).

**Use.** `chainproof set-member <set.bin> <work-dir> <txid>:<vout> <out.sbmember>` writes the proof (the
pass's segment logs from `<work-dir>/seg/0.sbseg`; the txid in display order) and checks it against the
pass's root; `chainproof verify-member <work-dir> <dir>:<to>[…] <file>` verifies the pass under the epoch's
challenge, then the proof against its root and last key.

**Proof status (Lean): proven.** `set_root_sound` (`SetPass/PassChain.lean`): a verified pass root of
shape `t` with root limbs `R` gives records `es` (the segments' records, in order) that fold the pass from
the verifier's start state to its final one, and `R` is the root of a segment tree of shape `t` whose
leaves are the segments' Merkle roots `Spec.SetMerkle.passRoots s0.last segs`: each segment's root is
`segRoot HALF last seg`, the heap tree of its records' leaves `Blake2s-256(key(previous) ‖ encRec)`
(`Spec/SetMerkle.lean`), or Blake2s has a collision. The pieces:

- `set_seg_root` (`SegRoot`): a sound segment's public `ROOT` is `segRoot HALF s.last seg`.
- `set_mt` (`MTSound`, `MTLink`, `MTTree`): every node yield of node `j` carries `node HALF leaves j`
  (strong induction from the heap's bottom); the public root is node 1. `set_mt` range-checks
  `1 ≤ HALF ≤ 2^24`.
- `set_lc` (`LCSound`, `LeafLink`): `block_b2s`'s constraints are `set_lc`'s; each used period reads
  its record's words, chains within the record, and the last block's yields are the leaf's words.
- `set_lw` (`LWSound`, `LeafLink`): each row lies in its record's window; its word is the leaf message's
  (previous-key words from `set_rec`, file bytes from the byte table, zero past the end).
- `EncIn` now requires zero last-key bytes when there is no last record (the verifier's start state has
  them), so the set's first leaf starts with 36 zero bytes.

**Cost** (*est.*): about 4.75 Blake2s compressions per record instead of 1.35 (the file's 1.35, the
leaf's 2, the tree's ~1.4 with `HALF = 2^15`). Segments shrink to ~47k records (the leaf compressions
bind at 2^23 rows): ~3,450 segments per set, about 1.5–2 times the pass cost without the root.
