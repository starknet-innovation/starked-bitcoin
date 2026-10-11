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

**Lean (2026-10-11, `Block/AggregateBlocks.lean`):** the public-input statement of the tree is proven:
`rng_leaf` (a proven block whose leaf checks its BIP30 flag and `αₖ = α₁ᵏ` is a proven one-block
range), `rng_node` (two proven ranges, linked by height, with one challenge, give their union; the sums
add), `epoch_hyps_of_rng` (a proven range gives exactly the block hypotheses of `epoch_systems_core`,
with its summed partial sum). Not yet covered: the seed and the hash binding (D-043). The leaf's own checks are Lean-first: `Circuit/BlockLeaf.lean`
(`checksP`, `checks_sound`, `checks_pub`: `αₖ = α₁ᵏ` and the BIP30 flag from the height, exactly
`rng_leaf`'s hypotheses), replayed in `block_leaf.zig` (`airs/block_leaf_checks.json`; tested: honest
inputs pass, a flipped flag or a wrong weight fails).

**Lean (earlier note).** Mostly done in spirit: `epoch_systems_core` is already stated over "block systems at
consecutive heights sharing the challenge with a balanced public sum" — the exact shape the
aggregator delivers — and the glue machinery (Lean-first circuit programs, proven, replayed
gate-identically, D-025) exists. BLOCK-REC is engineering-heavy, not proof-heavy.

**Freeze before catch-up.** The one expensive mistake available is re-proving ~840k blocks under a
changed interface. Before CATCHUP starts, freeze the block proof's public inputs and the leaf/VK —
the design here fixes what the aggregator needs public, and it is already public (partial sum,
input count, `C_h`, height, block hash, `z`).

## The block-proof interface for aggregation (proposed, D-043)

Found 2026-10-11 while specifying BLOCK-REC against what `verify-epoch` checks natively. Everything the
native epoch verifier checks per block must become a leaf or node obligation; three things in the
current interface do not compose in a tree.

**What `verify-epoch` checks per block today** (public inputs of the block system, `N_PUB = 161`):
- 0–1 block length, tx count; 8 undo length (informational);
- 2 height; 3, 7 the previous-block MTP (two 16-bit limbs); 4–6 the BIP34/CSV/segwit flags;
  158–160 the BIP30 "lost" flag and the subsidy (all functions of the height except the MTP);
- 9–24 the commitment `C_h`; 25–40 the block hash (bound to the chain's `T` by an inclusion path,
  with the 11 predecessor headers for the MTP);
- 41–152 the challenge `(γ, z, αᵏ)`; 153–156 the partial sum; 157 the input count.

**1. The seed must be tree-shaped.** The D-041 v2 seed is one Blake2s over `from ‖ to ‖ digests ‖
(hash_h ‖ C_h)` for every block: a linear stream no node can fold. Proposal (seed v3): the blocks
enter as a binary Merkle tree of leaves `Blake2s(hash_h ‖ C_h)` with the header tree's aligned shape
(absolute heights, so a range `[a, b]` is a list of aligned perfect subtrees); the seed hashes the
range, the two set digests and that list of subtree roots. Each node folds its children's roots; the
root circuit (or the outer verifier) computes the seed and checks `(γ, z, α) = challenge(seed)`.
Changing the seed re-proves epochs (0–1000: about 20 minutes).

**2. The block hashes bind to the chain per aligned subtree.** A range's block-hash tree equals the
chain's `T` only for a range from genesis. With the aligned shape above, each of the range's O(log n)
perfect subtrees is a node of the header tree; the outer verifier checks each against `T` with an
inclusion path (`Spec/Mmr.lean`), as `checkWindow` does per block today.

**3. The previous-block MTP has no aggregator obligation.** It is a function of the 11 preceding
headers' times, which a block leaf does not see. Options:
- **(A) The block proof carries its window (recommended).** The block system takes the 11
  predecessor headers, links them by prev-hash up to its own header (already hashed in-circuit), and
  computes the MTP (the header chain's MTP gadget and `mtp_core` exist). The MTP leaves the
  interface: context becomes a function of the height and the block's own hash. About 33 extra
  SHA-256 compressions per block, a block-system AIR change (large-block test, re-prove epochs), and
  Lean: the window linkage and `mtp_core` reuse.
- **(B) Nodes carry a sliding window.** Leaves expose their own header time; a range summary carries
  its last 11 times and its first 11 blocks' unresolved MTP claims; a node resolves the right child's
  claims against the left child's times (a median of 11 in-circuit). No block AIR change, but the
  node logic is the most intricate part of the aggregator, and the epoch's first 11 blocks still need
  the times before the range (inclusion paths at the root).
- (C) Per-height MTP in the header tree: re-proves the frozen chain VK (D-036). Not recommended.

**4. Height-derived context in the leaf.** The flags, the lost flag and the subsidy are fixed
functions of the height (`checks.pubs`, `lostHeight`, `coin.pubs`); the block leaf recomputes them in
the circuit from the height (a small Lean-first program) instead of exposing them.

**5. The leaf's summary.** The challenge's 112 limbs reduce to `(γ, z, α)` (12 limbs) once the leaf
checks `αₖ = αᵏ`. A block leaf's public summary: height, block hash, `C_h`, partial sum, input count,
`(γ, z, α)`; with (A), nothing else. A node: the range, the aligned subtree roots (hash‖C leaves), the
summed partial sum and input count (checked below `2^30` at the root, as `verify-epoch` does), the
shared `(γ, z, α)`.

**Measured (2026-10-11):** the plain verifier accepts a block-170 proof in-circuit (`zig build
blockleaf`): at test strength 0.88 M variables, at production strength (70 queries, 26 PoW bits)
8.27 M variables (add 185 k, sub 423 k, mul 480 k, pointwise 160 k, Blake2s updates 20.5 k), built in
under 2 s, circuit satisfied; proved with stwo-zig's circuit prover (70 queries, 26 PoW bits) in 5.2 s,
peak RSS 5.1 GB, proof 858 KB (M4 Pro, CPU). The verifier circuit grows with the logarithm of the
block trace (Merkle depths, FRI layers), not with the block, so a block leaf should stay near this
cost for large blocks too (*est.*; to measure at 2^22). Leaf packing (above) matters less than
estimated: per-leaf cost is seconds, not the header leaf's 31 s.

## Built so far (2026-10-11, night)

- **Seed v3** (D-043 part 1, the forced part): `epoch.zig` `seedFrom` over aligned perfect subtrees of
  `seedLeaf = Blake2s(hash ‖ C_h)` leaves (tag v3). Epochs re-proved: 0–170 verifies to the same set
  (171 coins, `hash_serialized 7105b60f…`).
- **Block leaf** (`block_rec.zig` `buildLeafCircuit`): the plain verifier over the block system, the
  Lean leaf checks (`Circuit/BlockLeaf.lean`: `αₖ = α₁ᵏ`, BIP30 flag, the seed leaf by the header
  tree's proven node gadget), `lt30` on the height and input count (`block_leaf_sum`), and the digest of
  the 51-limb summary.
- **Block node** (`block_rec.zig` `buildNodeCircuit`): two children verified in-circuit (stwo-zig's
  recursive verifier, as the header node) and the Lean glue `blockNodeProgram`
  (`Circuit/BlockNode.lean`, `node_sound`): equal sizes, linked heights, equal challenges, summed `s`
  and `nin` (`lt30` against wrap), both roots folded.
- **Measured** (`zig build blockrec -- data/epoch 0`, M4 Pro CPU): blocks 0 and 1 of the v3 epoch as two
  leaves (15.5 s each, padded to the shared shape) and one node (15.9 s); every proof verified
  natively, the node's digest equal to the native `joinSummary`; peak RSS 15.1 GB; proofs 981 KB.
- **Height-derived context in the leaf** (D-043 part 4, `Circuit/BlockCtx.lean`, `ctx_sound`, standard
  axioms): the BIP34/CSV/segwit flags (`f·(H − c) + (1 − f)·(c − 1 − H) < 2^30`) and the subsidy's limbs
  (`H = 210000·q + r`, a one-hot over 64 halvings selecting a Lean-computed table) are the height's;
  replayed in the block leaf (`airs/block_leaf_ctx.json`; tested at activation and halving boundaries,
  tampered flags and subsidy rejected). New hints `div`, `mod` (glue). Blocks 0–1 demo re-run with it:
  leaves 17 s each, node 24 s, peak 16.1 GB.
- **Epochs under seed v3:** 0–170 and 171–1000 re-proved and verified (171 coins `7105b60f…`, 998 coins
  `29a42ec2…`, unchanged).
- **Still to build:** the outer verifier (the aligned forest of root summaries against the seed v3,
  the challenge, the final set's balance and the chain's `T`), the epoch driver over all blocks, the
  MTP (D-043 part 3).
- **Lean, the tree's semantics** (`Circuit/BlockTree.lean`, standard axioms): `SumOk v` (the 51 limbs
  describe a proven range of `2^ℓ` blocks whose hash and seed roots are the perfect trees over its
  blocks' hashes and seed leaves); `sumOk_leaf` (a proven block whose leaf checks hold, with 16-bit
  hash limbs, has a proven summary), `sumOk_node` (the node glue's facts, `node_sound`, take two proven
  children to a proven output), `epoch_hyps_of_sum` (a proven root summary gives `epoch_systems_core`'s
  block hypotheses with its partial sum). Trusted wiring: the Zig assembly of the leaf summary from
  the block's public inputs (`block_rec.zig` `buildLeafCircuit`), as for the header leaf.

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
