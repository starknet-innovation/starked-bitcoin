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

**Use.** `chainproof set-member <set.bin> <work-dir> <out.sbmember> <txid>:<vout>...` writes the proofs
of one or more outpoints to one file (the pass's segment logs from `<work-dir>/seg/0.sbseg`; txids in
display order; the segment roots computed once) and checks each against the pass's root.
`chainproof verify-member <work-dir> <dir>:<to>[…] <file>... [--witness-script <hex>]` verifies the pass
under the epoch's challenge once, then every proof in the files (single-proof files from before are
read too) against its root and last key, rejects an outpoint given twice, and prints each coin (amount,
height, scriptPubKey) and the total of the unspent ones.

**Witness script** (`--witness-script`): every unspent coin in the files must pay to the script's P2WSH
scriptPubKey `OP_0 <32> sha256(script)`; a bare `m <key>… n OP_CHECKMULTISIG` script is decoded and
printed (threshold and keys). The script is public, so this is a check outside the proof, not a new
statement. What it shows: those coins were unspent in the set after `<to>`, locked by that script, so
the multisig held *at least* their total. It does not show the multisig held nothing else (there is no
completeness proof over a script). Test vector: the strkBTC bridge's 3-of-5, P2WSH `00208e4e98…9754b`
(`set_tree.zig`).

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
