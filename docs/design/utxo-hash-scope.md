# Scoping: proving Core's UTXO-set hash (assumeUTXO) — note

Status: scoping note (2026-10-10), no decision. From the proof review's recommended order (item 4:
"scope the MuHash / no-inflation outputs early, because they shape the UTXO commitment"). Figures
marked *est.* are rough and need checking before any external use.

## What Core pins

Bitcoin Core's mainnet parameters (`kernel/chainparams.cpp` at `c067aa71`) pin assumeUTXO snapshots
by `hash_serialized`:

| Height | `hash_serialized` |
|---|---|
| 840,000 | `a2a5521b…68f96` |
| 880,000 | `dbd19098…dcea9` |
| 910,000 | `4daf8a17…f1568` |

A node loading a snapshot trusts these constants, which are reviewed in Core's pull requests. Proving
that the UTXO set reached by valid blocks from genesis has exactly this hash would make an assumeUTXO
snapshot checkable without trusting the constant. As far as we know, no one does this today (review §7).

**`HASH_SERIALIZED`** (`kernel/coinstats.cpp`) is SHA256d (`HashWriter`) over, for every coin in
LevelDB key order (txid in internal byte order, then output index), `TxOutSer`:
- the outpoint (36 bytes);
- `height << 1 | coinbase` (4 bytes);
- the `CTxOut`: amount (8 bytes) and the script with its CompactSize length.

It is one linear hash over the whole set; it cannot be updated per block.

**MuHash3072** (`gettxoutsetinfo muhash`, not used by assumeUTXO) is incremental. Each coin's
`TxOutSer` is hashed (SHA-256, then ChaCha20 expansion to 3072 bits) and multiplied into a numerator
(insert) or a denominator (remove), modulo 2^3072 − 1103717; a final division gives the hash.

## Cost (est.)

- **UTXO set size:** about 170–190 M coins at height about 970k, about 75 serialized bytes each, so
  about 13 GB. *est.*; could be measured with `gettxoutsetinfo` on the node, but that scan is heavy.
- **`HASH_SERIALIZED` once per snapshot:**
  - about 13 GB / 64 B ≈ 2 × 10⁸ SHA-256 compressions;
  - at about 72 rows each (the block SHA component), about 1.5 × 10¹⁰ rows;
  - at the measured CPU rate (2²⁰ rows in about 16 s), about 65 CPU-hours plus recursion. A one-off
    job per snapshot; feasible.
- **MuHash over the whole history:**
  - every output created and every input spent, about 5–7 × 10⁹ coin events (*est.*);
  - each costs a SHA-256, a ChaCha20 expansion (6 blocks) and a 3072-bit modular multiplication
    (192 × 16-bit limbs; about 37k limb products before reduction), so hundreds of rows per event;
  - about 10¹² rows, two orders of magnitude above `HASH_SERIALIZED`;
  - only attractive if a per-block incremental hash is needed for other reasons.

## What this means for the UTXO module (M3b)

1. **Target `HASH_SERIALIZED` at Core's snapshot heights,** not MuHash: it is what Core pins, and it
   is much cheaper as a one-off.
2. **The UTXO commitment must allow a sorted traversal in Core's key order** (txid bytes, then
   index), with each coin's `TxOutSer` fields. D-029's spent-output slots already include amount,
   script, height and the coinbase flag. A tree sorted by outpoint gives the order directly. The
   proof would walk the leaves in order and feed `TxOutSer` bytes to the SHA component, then check
   SHA256d = the pinned constant.
3. **No-inflation comes nearly free:** the same traversal sums the amounts. A statement "total
   amount ≤ the subsidy schedule up to height H" needs only the sum and the height. Core reports the
   same sum (`total_amount`), so it can be cross-checked.
4. **Unknowns:**
   - the exact coin count and serialized size at 910k;
   - whether LevelDB's key order differs from plain outpoint order (the key is `'C'` + txid +
     VARINT(n), so within one txid VARINT byte order may differ from numeric order). Core's
     `ApplyHash` iterates a `std::map<uint32_t>` per txid, so the hash order within a txid is numeric
     n. Check this when designing the tree.

## Not decided here

This is scoping only. Choosing the UTXO commitment (`Q-TREE`) and whether assumeUTXO compatibility is
a goal are owner decisions.
