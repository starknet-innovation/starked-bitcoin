# UTXO module (M3b) — design proposal

Status: proposal for the owner (2026-10-10, D-040 proposed). Nothing here is built. It decides
`Q-TREE`, which the roadmap leaves to the owner. Figures marked *est.* are rough.

## What M3b must prove

For every block, given its proof (M3a: `block_sound`, `commit_sound`, `hash_pub`):

1. **Spends exist:** every input after the coinbase spends a coin that was created earlier (in an
   earlier block, or earlier in the same block) and not spent since. This includes D-031: no outpoint
   is spent twice, inside one transaction or across transactions.
2. **Undo records are those coins:** record `j` of the block's undo stream (D-038) is the spent coin's
   height, coinbase flag, amount and script (D-029).
3. **Coinbase maturity:** a coinbase coin is spent at least 100 blocks after its creation.
4. **Amounts:** a transaction's inputs sum to at least its outputs (the fee), and the block's
   coinbase claims at most the subsidy plus fees. Inputs' amounts come from the undo records.
5. **Unspendable outputs never enter the set:** `OP_RETURN` scripts and scripts over 10,000 bytes
   (Core's `IsUnspendable`).
6. **BIP30 history:** the two duplicate coinbase pairs (91722/91880 and 91812/91842) overwrite, as
   Core did; all later txids are unique (BIP34).
7. **The set itself, at chosen heights:** its `HASH_SERIALIZED` equals Core's pinned assumeUTXO
   constant (D-037), and its total amount is within the subsidy schedule (no inflation).

Script validity (signatures) is M3c, not M3b.

## Two ways to keep the set

### A. A sorted Merkle tree updated per block (the roadmap's current wording)

Each block proves its spends by inclusion paths and deletes them, then inserts its new coins with
non-inclusion paths, so the root moves from `R_{h-1}` to `R_h`.

- **Cost per coin event:** about three paths of ~28 levels (180 M leaves), with one Blake2s
  compression (88 rows) per level: about 7,400 rows. *est.*
- **Whole history:** about 6 × 10⁹ coin events (outputs created plus inputs spent), so about
  4 × 10¹³ rows. *est.* That is about 40× the block proofs themselves (next section).
- **For:** each block's statement is self-contained (`R_{h-1} → R_h`); following the tip is natural.
- **Against:** the cost; sequential root updates inside a block make the AIR long and serial.

### B. A chain-wide multiset argument (recommended)

Treat the UTXO set as offline memory checked by LogUp over the whole history:
- every created coin contributes `+1/(z − enc(coin))`;
- every spent coin contributes `−1/(z − enc(coin))`;
- the set at the end contributes `−1/(z − enc(coin))` for each remaining coin;
- the total must be zero.

A coin's tuple is its outpoint, height, coinbase flag, amount and script digest. To keep the spending
order, it also carries a position: `(height, transaction index)`.

- **Created coins** come from the block proof's parsed outputs (the fields component already reads
  every output's amount and script range).
- **Spent coins** come from the inputs' outpoints plus the undo records. So requirement 2 holds by
  construction: the tuple subtracted is the undo record's.
- **Order:** each spend checks that its coin's position is strictly earlier than the spending
  transaction's. This covers same-block spends and spending an output created later.
- **Duplicates (D-031):** a coin spent twice subtracts its tuple twice against one creation, so the
  sum is not zero. The set at the end is sorted strictly by outpoint, so it holds each coin once.
- **The challenge `z`:** it must be drawn after every tuple is fixed. History is known before proving,
  so:
  1. compute every block's commitment `C_h` (D-038) natively;
  2. derive `z` from the MMR of the `C_h`;
  3. prove each block with `z` as a public input;
  4. the final aggregation checks that `z` is the hash of the MMR of the proven `C_h`.

  This is commit-then-challenge, with the commitment checked at the end. Each epoch of history (for
  example, up to an assumeUTXO height) uses one `z`.
- **The set at the end** is the sorted coin list. The pass that subtracts it also computes
  `HASH_SERIALIZED` in Core's order and the total amount, so requirement 7 comes from the same pass.
  Chaining epochs means the next epoch starts by adding this list.
- **Cost:** a few LogUp columns per coin event inside each block proof: about one row per event, so
  about 10¹⁰ rows over history, plus the final sorted pass (about 2 × 10⁸ SHA-256 compressions, about
  1.5 × 10¹⁰ rows, *est.*, already scoped in [utxo-hash-scope.md](utxo-hash-scope.md)).
- **For:**
  - two to three orders of magnitude cheaper than A;
  - no per-block tree;
  - the undo records are checked for free;
  - `HASH_SERIALIZED` and no-inflation share the final pass.
- **Against:**
  - a statement holds only for a whole epoch: a single block's proof alone says nothing about its
    spends;
  - following the tip needs either short epochs (each paying a sorted pass over the set) or approach A
    for the last stretch;
  - the soundness argument is global, so the Lean proof is about a system of all blocks, not one.

## Recommendation (D-040, proposed)

B for catch-up and for the assumeUTXO statement. Revisit A (or a hybrid) only for tip following. Lean:
- a spec of Core's coins view as a fold over blocks;
- the multiset lemma: with zero total and strictly sorted final set, the spend multiset is the
  creation multiset minus the final set;
- per-block links to M3a's parsed outputs and undo records.

## What changes in M3a

Nothing in proven M3a statements. M3b adds to the block system:
- a coin-event component: one row per created or spent coin, its tuple, and its position check;
- a public `z` and the block's partial LogUp sum.

The block commitment (D-038) already fixes the undo format, so existing block proofs keep their
meaning. They are not reused, though: blocks are re-proved with `z`, so catch-up should wait for M3b.

## Compute wall (CATCHUP)

Block proofs alone: about 970k blocks. A recent full block is about 2²¹–2²² rows across ~900 columns
at one size, and needs 13–20 GB in the in-memory check on this laptop. *Measured on block 400000:
see status.md.* Even at a few minutes per block, that is years of single-laptop CPU time. Catch-up
needs a proving cluster (or GPU) and lifting (per-component trace sizes). It is not a laptop job.
