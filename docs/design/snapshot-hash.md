# SNAP-HASH: a canonical Merkle hash of the UTXO set (proposal)

Status: draft · Updated: 2026-11-19 · Owner files: `docs/design/set-membership.md`, `lean/StarkedAir/Spec/SetMerkle.lean`, `src/block/set_seg.zig`

Answers: which hash of the UTXO set Bitcoin Core could compute natively and a proof could open per
coin; what it costs each side; what changes in the set pass. Nothing here is built or agreed with
anyone. Roadmap item SNAP-HASH; asked on Delving t/3070 (ajtowns, post 5).

## Why a new hash

Core pins assumeUTXO snapshots by `hash_serialized`: one SHA-256 stream over every coin
(`kernel/coinstats.cpp`). It is sequential: a snapshot is checked only after reading all of it
(70.7 s for 9.4 GB on the node, 2026-11-13), and it opens no single coin.

The seal also proves a Merkle root ([set-membership.md](set-membership.md)), but that root is ours:
Blake2s, a leaf that chains the previous key, and a shape that follows the proving segments. Core
cannot be asked to reproduce it.

Wanted: one hash that (1) Core computes with code it already has, (2) is cheap to prove, (3) opens a
coin's presence or absence in about 1 KB, (4) lets a snapshot be checked chunk by chunk.

## The proposal

| Part | Choice |
|---|---|
| Order | Core's: txid in internal byte order, then `vout` as a number (the coins database's order, and `hash_serialized`'s) |
| Coin bytes | `TxOutSer`, unchanged: outpoint (36 bytes), `height·2 + coinbase` (4 bytes LE), amount (8 bytes LE), script with its CompactSize length |
| Leaf `i` | `SHA256(T_leaf ‖ TxOutSer(coin i))` |
| Node | `SHA256(T_node ‖ left ‖ right)` |
| Shape | complete binary tree of depth `d = ⌈log2 n⌉` over the `n` coins; positions `n … 2^d − 1` hold 32 zero bytes |
| Hash | `SHA256(T_root ‖ block hash ‖ n (8 bytes LE) ‖ top node)` |

`T_x` is a BIP340-style tag prefix, `SHA256(tag) ‖ SHA256(tag)`: 64 bytes, so each of the three
hashes starts from a constant midstate. A leaf and a node can then never be confused, whatever the
coin's length.

- **Presence** of a coin: its `TxOutSer`, its position `i < n`, and `d` siblings.
- **Absence** of an outpoint: the coins at positions `i` and `i + 1` whose outpoints lie on either
  side of it (or position 0 alone, or `n − 1` alone), with their paths; adjacent paths share all but a
  few siblings. `n` is in the hash, so the edges are checkable.
- **Chunks**: `2^k` consecutive coins starting at a multiple of `2^k` are one subtree. A snapshot
  shipped with the list of its chunk roots is checked chunk by chunk, in any order, in parallel.

Size: with `n` = 164,539,066 (the set after 972,500), `d` = 28: a presence proof is 28 × 32 = 896
bytes plus the coin.

## Why these choices

- **SHA-256, not Blake2s.** Core has SHA-256 and nothing else to add. And in our AIRs SHA-256 is the
  cheaper one: 72 rows × 188 columns = 13,536 trace cells per 64-byte block (`block_sha`), against
  88 rows × 406 columns = 35,728 for Blake2s (`block_b2s`). Blake2s was chosen for our own commitments
  because it is native in the recursion circuits (D-007, D-030), not because its AIR is cheap. A
  statement to the contrary was made on Delving (t/3070, post 6) and needs correcting.
- **`TxOutSer` unchanged**: Core already produces these bytes for `hash_serialized` and MuHash.
- **A plain leaf.** Ours chains the previous key so one path proves absence. With a canonical shape,
  positions prove adjacency, and Core hashes each coin on its own.
- **Zero padding to a power of two** rather than an RFC 6962 tree (split at the largest power of two
  below `n`): the heap-indexed tree with zero slots is what `set_mt` already proves. Either works; the
  count is in the hash in both.
- **The block hash in the hash**: the value names the chain point it was computed at.
- **Not MuHash**: incremental, but it opens no coin and a 3072-bit product is expensive to prove
  ([utxo-hash-scope.md](utxo-hash-scope.md)).

## Cost

Per coin, in SHA-256 compressions: a leaf is 2 for a `TxOutSer` of 56–119 bytes (a P2WPKH coin is 71
bytes, a P2TR coin 83), a node is 2 (64 bytes, then the padding block), and there is one node per coin.
About 4 per coin; the exact leaf average needs the set's length histogram.

| | Compressions per coin | Trace cells per coin (*est.*) |
|---|---|---|
| Current: `hash_serialized` + Blake2s leaf + Blake2s tree | 1.35 SHA + 3.4 Blake2s | 140k |
| Proposal alone | 4 SHA | 54k |
| Proposal, and `hash_serialized` still proven | 5.35 SHA | 72k |

*Est.*: compressions × cells per compression; the set pass has other components (parsing, the coin
tuple). The current counts are from set-membership.md.

For Core (*est.*, not measured): about 6.6·10^8 compressions for the set after 972,500, against
2.2·10^8 for `hash_serialized`; parallel where `hash_serialized` is not.

A variant cuts a node to one compression: `compress(IV_node, left ‖ right)` with no padding block.
Three compressions per coin, but it is not a standard use of SHA-256.

## What changes here

- `set_lw` drops the previous-key words; the leaf message is the record re-serialized as `TxOutSer`
  (the set file's record may not be `TxOutSer` byte for byte: check `encRec`).
- `set_lc` and `set_mt` use the SHA-256 gadget with a constant initial state instead of Blake2s.
- Segments cover `2^j` coins from a multiple of `2^j`, `j` chosen so the segment fits its trace, so a
  segment root is a node of the canonical tree. The verifier checks that the segments tile `[0, n)`.
- The tree above the segments (a few thousand nodes) is one more small SHA-256 proof, or is computed by
  the verifier from the segment roots. To decide: the recursion circuits hash with Blake2s.
- `Spec/SetMerkle.lean`, `set_root_sound`, the member proofs, the website's verifier and
  `chainproof verify-member` follow.
- `hash_serialized` stays proven until Core pins something else: it is what makes the proof check
  against Core as of 2026-11-19.

The set passes are redone (D-054 changes the block commitment, so they are redone in any case).

## Open

1. Standard tagged SHA-256 (4 compressions per coin) or the one-compression node (3).
2. Zero padding or the RFC 6962 shape.
3. Whether the hash should also commit to the total amount, as `gettxoutsetinfo` reports it.
4. Whether Core would compute it at all: nothing here is useful until someone there wants it. The
   write-up goes to Delving first; no circuit work before a reaction.
5. Relation to Utreexo, which commits to the same coins in insertion order for a different purpose
   (updates per block, no absence proofs). UNVERIFIED: its leaf encoding and hash function; to check
   before the write-up cites it.
