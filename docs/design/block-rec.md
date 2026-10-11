# Aggregating block proofs and following the tip (BLOCK-REC, UTXO-TREE)

Status: current · Updated: 2026-10-11

From the owner discussion of 2026-10-11 (D-042, amending D-040's tip clause). Two subjects that
meet at the tip: folding block proofs into one recursive proof (`BLOCK-REC`), and how the proven
UTXO state advances block by block (`UTXO-TREE`). Figures marked *est.* are rough.

## Sizing: RAM is per-worker and bounded; the wall is throughput

No step of the architecture needs chain-proportional memory. Everything large is a tree of bounded
segments with carried public state — the pattern that proved 970k headers on a 24 GB laptop
(`prove_loop`, checkpoints, recursion):

- **A block proof is the largest indivisible trace**, and its size is bounded by a consensus
  constant (4M weight), not by chain length: about a 2²²–2²³ trace, roughly 40–80 GB to prove
  (*est.* — measure it; see Open). One 128–256 GB machine covers the worst case forever, and
  `LIFT` (mixed component sizes) lowers it.
- **The epoch's final-set pass** (~180 M coins at scale) is a linear scan, segmentable exactly like
  the header chain: each segment subtracts its slice and exposes as public the running fraction
  sum, the last outpoint (strict sortedness across the boundary), the SHA midstate
  (`HASH_SERIALIZED`) and the running amount total. The set streams from disk.
- **Catch-up** is on the order of 10¹¹–10¹² rows (every block byte crosses the byte and SHA
  components): thousands of CPU-hours, *est.* — a throughput problem, embarrassingly parallel,
  since once `z` is computed natively every block proof is independent and the aggregation tree
  parallelizes by level. A fleet of ordinary 64 GB machines beats any single large one.

## BLOCK-REC: the aggregator circuit

As of 2026-10-11 the epoch statement is closed natively (`verify-epoch`). BLOCK-REC moves it in-circuit so one
root proof covers chain, blocks and coin events.

**Node obligations, per level:**

1. verify the two children in-circuit (the leaf wraps the 15-component block system — far wider
   than the header leaf: ~900 OODS columns, 216 lookup sites per row);
2. link consecutive heights;
3. add the children's coin-fraction partial sums (QM31 additions);
4. add the input counts and enforce the epoch total below p − 1 (the multiset cap; the first epoch
   may need a split, see utxo.md);
5. carry `(z, α)` and check every leaf used the same pair;
6. fold the MMR of the block commitments `C_h`;
7. fold the block hashes (public inputs 25–40) into a height-ordered MMR with the **same shape as
   the header tree's `T`**;
8. at the root: `z = H(seed)` with the D-041 v2 seed (both sets' encodings, the `C_h` MMR), closing
   commit-then-challenge in-circuit.

Obligation 7 lets the outer verifier bind blocks to the header chain by **one root-to-root
equality** with the chain proof's `T`, replacing D-039's native pass over `headers.bin`.

**Leaf packing.** ~840k per-block leaves would mean ~840k node steps (~24–30 s each, thousands of
CPU-hours of aggregation alone). Early blocks are a few hundred bytes, so pack many blocks into one
row-bound trace: pre-2013 history fits hundreds of blocks per 2²² trace. Needs multi-block support
in the block system; interacts with `LIFT`.

**VK.** The epoch tree gets its own pinned VK. D-036's frozen chain VK is untouched; the two roots
meet in the outer verifier.

**Lean.** Mostly done in spirit: `epoch_systems_core` is already stated over "block systems at
consecutive heights sharing the challenge with a balanced public sum" — the exact shape the
aggregator delivers — and the glue machinery (Lean-first circuit programs, proven, replayed
gate-identically, D-025) exists. BLOCK-REC is engineering-heavy, not proof-heavy.

**Freeze before catch-up.** The one expensive mistake available is re-proving ~840k blocks under a
changed interface. Before CATCHUP starts, freeze the block proof's public inputs and the leaf/VK —
the design here fixes what the aggregator needs public, and it is already public (partial sum,
input count, `C_h`, height, block hash, `z`).

## Following the tip

Three layers at three cadences:

| Layer | Mechanism | Cadence | State |
|---|---|---|---|
| Headers | `extend_tip.sh` pushes aligned segments onto the saved MMR peaks | minutes | done |
| Block validity | standalone self-contained `.sbblock` files (D-039), bound by the public block hash | per block (hardware-gated for 1 MB blocks) | done |
| UTXO state | baseline + per-block tree updates + re-baseline (below, D-042) | per block | scheduled |

**Why epochs alone cannot follow the tip.** An epoch close costs O(set) regardless of how few
blocks it covers: the final-set pass (~2²⁸ rows at scale) plus seed binding is about a day of one
laptop or an hour of a large server, *per close* (*est.*). Rolling epochs (`--from`, built and
proven as `epoch_from_sound`) therefore give a proven set daily at best, never per block. Per-block
proven state needs a mechanism whose cost is proportional to the *block*: the tree.

**The hybrid (D-042):**

1. **Baseline.** Close a multiset epoch at a checkpoint height (assumeUTXO heights first, D-037 /
   D-040). One extra segmented pass proves the sorted final set builds a Blake2s sorted-tree root
   `R` (~360 M compressions, *est.*, one-off per baseline, segmentable like everything else).
2. **Tip stretch.** Per-block tree-update proofs advance `R`: each spend shows inclusion and
   deletes; each created coin shows non-inclusion and inserts (Core key order, D-037). About 7,400
   rows per coin event (*est.*), so a busy block is 2²⁵–2²⁶ rows — a minute or two on a server,
   inside the block interval. The prover keeps the ~12 GB tree on disk and streams paths.
3. **Re-baseline.** Periodically close the next epoch from the previous set. Its final set must
   rebuild to the same root the incremental updates reached: the multiset argument and the tree
   argument check each other. Each assumeUTXO-height close still anchors to Core's pinned
   `hash_serialized`.

Until UTXO-TREE exists, the interim tip product is **baseline + native deltas**: a verifier holding
the baseline set applies each new block's committed coin events (bound by `C_h`) natively — a few
thousand events per block. No circuits needed; this works once a baseline epoch exists.

## Open

- Measure the worst-case block proving footprint (block 400000 at 2²² on a ≥128 GB machine) to pin
  the per-worker RAM constant.
- Multi-block leaf design (with `LIFT`): packing rule, public-input shape for a multi-block trace.
- The sorted tree's exact encoding: leaf = `TxOutSer` fields in Core key order (D-037); arity;
  empty-subtree convention for non-inclusion.
- Whether tip tree updates batch several blocks per proof (latency vs. proof count).
- The update AIR's Lean soundness statement (inclusion, non-inclusion, delete, insert, root
  transition) — the new proof work of UTXO-TREE.
