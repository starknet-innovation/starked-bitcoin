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

## The block-proof interface for aggregation (D-043, accepted 2026-10-12)

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

**Costing A and B (2026-10-12, for the owner's choice).**
- **A, in the block system.** The block system already hashes its header as one of `block_sha`'s
  message streams (`sha256d(header)`, public 25–40) and reads `time` from header bytes 68–71 through
  the byte table. A adds an *ancestry* segment to the byte stream: the 11 predecessor headers (880
  bytes), each hashed as a further header message (3 compressions each, ~33 × 72 rows ≈ 2.4 k rows), a
  link constraint per header (its digest = the next header's prev-hash field, bytes 4–35, through the
  message words as the Merkle-root check already reads them), and a median-of-11 over their times
  (the header chain's MTP window gadget, `mtp_core`; a sorting network of ~50 comparators). The
  context then loses `prevMtp` (public 3 and 7 become derived). Lean: the linkage (the existing
  `msgw` lemmas) and a block-side copy of `mtp_core`'s proof, roughly a session. Re-proves epochs (an
  hour at 0–1000); the large-block test after the AIR change. Nothing changes in the tree.
- **B, in the nodes.** No AIR change; leaves expose their own header time (bytes 68–71, already read
  in-circuit) and their claimed `prevMtp`. A range summary grows by its last 11 times and its first 11
  blocks' claims (44 limbs); a node resolves the right child's first claims against the left child's
  times and its own (a median of 11 per resolved claim, up to 11 per node); the epoch's first 11
  claims need the 11 times before the range, as inclusion paths at the outer verifier. Lean: the
  window's composition (new, intricate), roughly two sessions. Node circuits grow by ~11 medians.
- **Recommendation stays A:** the obligation stays local to one proof, the tree stays simple, and
  every node pays nothing; the cost is one AIR change made once, before CATCHUP.

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
  (171 coins, `hash_serialized 7105b60f…`). Epoch 171–1000 through 11 trees (2026-10-12): proved in 25 859 s (830 leaves, ~31 s/leaf
  wall incl. nodes; peak footprint 40.7 GB), `forest-1000.bin` 10.8 MB, verified in 1.4 s against
  the flat run's 63.8 s; same set (998 coins, `29a42ec2…`, Core's HASH_SERIALIZED).
- **Block leaf** (`block_rec.zig` `buildLeafCircuit`): the plain verifier over the block system, the
  Lean leaf checks (`Circuit/BlockLeaf.lean`: `αₖ = α₁ᵏ`, BIP30 flag, the seed leaf by the header
  tree's proven node gadget), `lt30` on the height and input count, and the digest of the 51-limb summary
  (Lean-first since 2026-10-12: `blockLeafOut`, `leafOut_vec`).
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
- **The epoch forest and its outer verifier** (`block_forest.zig`; `chainproof prove-epoch-tree` /
  `verify-epoch-tree`): setup (shared shape, the block leaf's identity per block trace size, the node's;
  `<dir>/blockvk.bin`), one recursion tree per aligned subtree of the seed v3 decomposition, each root
  with its block-hash subtree's path in the chain's header tree (`<dir>/forest-<to>.bin`). The verifier
  checks per root the pinned identity, the key expected from the blocks' trace sizes, the proof, the
  range; one challenge, equal to `challenge(seedOfRoots(…))` over the roots' seed subtrees and both
  sets' digests; each block-hash subtree against `T`; then the balance against the final set.
  Epoch 0–3: one tree, proved in 115 s, verified in 0.1 s after the chain (2.1 s); tampers rejected
  (a summary limb: `WrongDigest`; a path bit: `HashesNotTheChain`; a set missing a coin:
  `ChallengeMismatch`).
  **Epoch 0–170 (2026-10-12):** 171 block proofs as 5 trees (128 + 32 + 8 + 2 + 1), proved in 90 min
  (M4 Pro CPU, peak RSS 17.7 GB), forest file 4.9 MB; verified in 0.6 s after the chain proof (2.1 s):
  the coin set after block 170, 171 coins, `hash_serialized 7105b60f…` — the same as the native
  `verify-epoch`.
- **The previous-block MTP (D-043 part 3, option A, 2026-10-12):** a 16th block-system component,
  `block_anc` (`Block/Anc.lean`, witness `src/block/anc.zig`), reusing the header chain's SHA256d,
  plumbing and prev-hash linkage over 256-row periods. With the CSV bit: periods 0–10 are the 11
  predecessors (oldest first), period 11's hash is the block hash (public 25–40), and at most 5 of
  the 11 times are above the MTP (public 3, 7) and at most 5 below, so it is their median. A copy of
  `FIRST` read 2048 rows down forces at least 4096 rows. Below CSV the MTP limbs are 0 (the cutoff is
  the block's own time). No lookups, no new preprocessed columns, no public times; the tree is
  unchanged. Cost: 125 columns (+~11% of the block system's width), and CSV-era blocks need log ≥ 12;
  the leaf over blocks 0–3 went from 115 s to 161 s. Lean: `AncSound.anc_sound` (the header chain's
  `header_hash`/`header_link` reused through `chainSat`: the ancestry trace satisfies the header
  chain's base constraints for public inputs read from the trace), `median_of_counts`,
  `BlockAnc.blockSys_sat` (the 16-component system projects onto `hashSys`), `block_mtp`,
  `BlockPubOk.mtp`. Epoch 0–3 re-proved through the forest: same set.
- **Still to build:** a persisted, pinned block VK
  shipped like the chain VK (today `blockvk.bin` is written by the prover's setup); the outer verifier's
  composition is proven end to end, modulo named hypotheses (`forest_sound`, Circuit/BlockRec.lean,
  VL-NODE, 2026-10-12); the link from `verifyForest`'s checks to its premises is by inspection, as for
  the header chain's root verifier.
- **Lean, the tree's semantics** (`Circuit/BlockTree.lean`, standard axioms): `SumOk v` (the 51 limbs
  describe a proven range of `2^ℓ` blocks whose hash and seed roots are the perfect trees over its
  blocks' hashes and seed leaves); `sumOk_leaf` (a proven block whose leaf checks hold, with 16-bit
  hash limbs, has a proven summary), `sumOk_node` (the node glue's facts, `node_sound`, take two proven
  children to a proven output), `epoch_hyps_of_sum` (a proven root summary gives `epoch_systems_core`'s
  block hypotheses with its partial sum). The leaf summary's assembly is Lean-first (`blockLeafOut`, 2026-10-12);
  the tree and the outer verifier are composed end to end in `Circuit/BlockRec.lean` (`tree_sound`,
  `forest_sound`, VL-NODE, verifier-formalization.md).

## Leaf packing measured (2026-10-14, spike)

k block proofs verified in **one** circuit (`recursion/block_pack.zig`: the block-leaf body
`block_rec.leafBody` k times, the output Blake2s over the k leaf digests). Capacity measurement only:
the in-circuit join of the k summaries (the node glue's checks, a few hashes per pair) and its Lean
statement are not written yet. Blocks 0–15 (L 11, production block proofs), circuit proved with
stwo-zig's circuit prover (70 queries, 26 PoW bits, fold step 4).

- **Size is linear in k**: 8.4 M builder variables per block (11.3 M after padding); each doubling of k
  adds one to every component's log size (k = 1: trace 2²¹; k = 16: 2²⁵).
- **GPU** (resident CUDA circuit prover, `src/gpu/cuda/pack.zig`, H200, 2026-10-14). Every proof
  byte-identical to the CPU proof of the same circuit and verified natively:

  | k | trace | planned device arena | GPU prove | per block | CPU (pod) | proof |
  |---|---|---|---|---|---|---|
  | 1 | 2²¹ | 7.2 GiB | 1.34 s | 1.34 s | 8.1 s | 494 KB |
  | 2 | 2²² | 13.5 GiB | 1.28 s | 0.64 s | 12.3 s | 515 KB |
  | 4 | 2²³ | 26.0 GiB | 3.21 s | 0.80 s | 25.3 s | 535 KB |
  | 8 | 2²⁴ | 51.1 GiB | 5.99 s | 0.75 s | 54.8 s | 575 KB |
  | 16 | 2²⁵ | 101.2 GiB | 11.52 s | 0.72 s | 96.7 s | 597 KB |

  Plus, outside the prove: native verification of the k block proofs and the circuit build (0.8 s per
  block, host), and the optional native check of the circuit proof (0.5 s per block). Device kernels
  are ~1 s of the 11.5 s at k = 16; the rest is host ingress (5.6 GiB pageable H2D) and the static
  preprocessed hash, so the GPU prove has headroom.
- **Capacity is GPU memory**, ~6.3 GiB per block: 24 GB card k = 2, 48 GB k = 4, 80 GB (H100) k = 8,
  141 GB (H200) k = 16. k = 32 (~202 GiB) fits no single card. The field and domain bounds
  (trace + blowup ≤ 30) would allow k = 256. k is effectively a power of two (padding).
- **FRI geometry on CUDA:** only fold step 4 is qualified in stwo-zig; a last FRI layer folding a
  remainder of 1 produced a proof that fails verification (`InnerLayerCommitmentInvalid`, k = 1 with
  last layer 0). The driver picks the last-layer degree bound `trace log mod 4` so every fold is a 4.
  To report upstream.
- **CPU** (M4 Pro, 24 GB): k = 1 3.7 s, k = 2 7.3 s, k = 4 37.5 s (12.6 GB); k = 8 swaps (433 s).

**Superseded for mixed sizes (2026-10-14, the full survey).** A packed leaf verifies k *block* proofs
with the plain verifier. Its circuit, and so its identity in the VK, depends on the tuple of the k blocks'
(L, profile). Block sizes change from block to block: only 7,906 of the chain's 60,706 aligned 16-block
groups have a single size. Packing only uniform aligned runs gives 1.6 blocks per leaf over the chain
(606,293 leaves). So the width goes into the node instead (below). The capacity numbers above still hold
for what one GPU proves per circuit.

## Wide nodes (2026-10-14)

A **wide node** verifies `2^a` child *circuit* proofs (block leaves or nodes padded to one shared
shape) and joins their summaries. A child's circuit hash is an output of the in-circuit verifier, so
children of any block size mix freely, and the key mechanism carries their identities to the outer
verifier as today: `K = Blake2s(h₀ ‖ k₀ ‖ … ‖ h_{2^a−1} ‖ k_{2^a−1})`.

- **Lean** (`Circuit/BlockNodeK.lean`, standard axioms):
  - `blockNodeK a`: the children's sections (as the binary node's), the balanced join (`joinT`, the
    binary node's `nodeOut` at every inner vertex), the key and the digest. Exported for `a = 1 … 4` as
    `airs/block_node_k<a>.json`; the 16-child program is 19,275 ops.
  - `joinT_sound` and `nodeK_sound`: the node's output is the digest of a proven summary (`SumOkP`)
    under the key of its children's hashes and keys.
  - `treeK_sound`, `forestK_soundP` and `forestK_epochV`: the tree and the outer verifier over trees with
    wide nodes (`TreeK`), under the named hypotheses of `BlockRec.Trust` per arity (`TrustK`).
- **Zig** (`recursion/block_node_k.zig`): the circuit (the glue with stwo-zig's recursive verifier at
  every hook), its shape fixpoint, the native key and join, prove and verify.
  `blockpack widenode <dir> <from> <a> [prove]`, on the Mac CPU:
  - `a = 1` (blocks 0–1): the circuit's output equals the native digest **and the binary node's**. It
    proved and verified in 15.1 s (981 KB).
  - `a = 2` (blocks 0–3, and blocks 168–171, which mix 2^11 uniform and 2^12 tiered leaves): satisfied,
    with the output equal to the native digest (50.6 M vars).
  - Both arities reject swapped children (the link checks) and a wrong child key (the hook's digest).
- **Child verifier cost** (`blockpack nodecost`): one child circuit proof verified in-circuit costs
  12.6 M vars at FRI fold 1 and **6.4 M vars at fold 4**. The plain verifier of a block proof costs 8.4 M.
- **Shared shape** (`blockpack shapes`; the fixpoint of leaf and node, trace log):

  | children | fold 1 | fold 4 (trace log a multiple of 4) |
  |---|---|---|
  | 2 | 2^23 (node 25.3 M vars) | 2^24 (12.9 M) |
  | 4 | 2^24 (53.9 M) | 2^24 (25.8 M) |
  | 8 | 2^25 (114.8 M) | **2^24 (51.6 M)** |
  | 16 | 2^26 (243.9 M) | 2^28 (124.2 M) |

  At fold 4, the trace log must be a multiple of 4 *today*, and only because of the CUDA circuit prover.
  It fails when the last fold is a remainder (`~/Workshop/stwo-zig/CUDA_FRI_REMAINDER_FOLD_BRIEF.md`).
  Everything else accepts a remainder round at last layer 0 (checked on the CPU, 2026-10-14):
  - the in-circuit verifier (Debug build, trace logs 20–25);
  - `circuit_cpu` with the native circuit verifier (a 2^21 leaf);
  - a 2-child node over such leaves (`SB_FOLD=4 blockpack widenode data/epoch-pack 0 1 prove`): satisfied,
    proved and verified in **7.3 s, 521 KB** (fold 1: 15.1 s, 981 KB), 11.6 M vars.

  What does need last layer 0 is the in-circuit verifier (`fri.zig:77` asserts it). So the earlier
  workaround, last layer = trace log mod 4, gives proofs that can't be children. With the CUDA fix, every
  proof can keep its natural trace log at fold 4.

  Until then, 8 children at 2^24 is the widest node that fits an 80 GB card (2^24 ≈ 51 GiB of device
  memory, ~6 s on H200, from the packing runs).
- **The open cost: one shared shape pads every leaf to it.** A block leaf is 2^21 natively but 2^24 in
  the shape, 8× the work. The way out is **per-level shapes**: leaves at their natural shape; a node over
  leaves (whose hooks verify leaf-shaped proofs); and a node over nodes. Two node circuits per arity, both
  running `blockNodeK a`. Lean only needs `nodeH` indexed by the variant (the hook's verifier is
  abstract in `TrustK`). It needs natural trace logs at fold 4 (the CUDA remainder-fold fix), or fold 1
  on the CUDA circuit prover (fails, below).
- **On a GPU (2026-10-14, `src/gpu/cuda/widenode.zig`, `scripts/pod/widenode.sh`; RunPod H100 SXM 80 GB,
  sm_90, 28 vCPUs).** It uses stwo-zig's resident CUDA circuit prover. A device proof becomes a node child
  (`leaf.CircuitProof`) as stwo-zig's `circuit_cuda/recursion_source.zig` does it:
  - the verifier proof is `fromVerifiedCapture`;
  - the request and the circuit hash are computed on the host.

  Every proof is checked twice natively: `resident_verifier.verify`, then stwo-zig's circuit verifier on
  the serialized proof.
  - **The 8-child node works on the GPU**: 8 block leaves (blocks 164–171; block 170 is 2^12 tiered,
    the others 2^11 uniform) are proved at the shared 2^24 shape (fold 4, last layer 0), then the node
    over them.
    - The node's output digest equals `block_node_k.expected`'s.
    - **All 9 proofs are byte-identical to the CPU prover's** (`--cpu`).

    | step | GPU | CPU (pod) |
    |---|---|---|
    | leaf at 2^24, each | 4.2–5.2 s (8 leaves: 36.9 s) | 39–43 s |
    | node at 2^24 (51.6 M vars, 78.5 M padded) | 4.4 s | 38 s |
    | device-proof verification, each | 3.1–3.3 s | |
    | circuit verifier, each | 0.35 s | |
    | host per leaf: pad, check, preprocess | 5.7 s | |

    - Device peak: 45.65 GiB per proof (planned = measured; nvidia-smi 47.3 GB), every proof 575,016 B.
    - Host peak RSS: 8.7 GiB, or 35 GiB with the CPU proofs.
    - End to end without the CPU proofs: 135 s for 8 blocks. The GPU prove is 5.2 s per block; the
      rest is host work and verification.
    - Inside each GPU prove, the static preprocessed hash on the host is 3.1–3.4 s. It is the same for
      every leaf of the shape, so caching it (`expected_preprocessed_root`) would save most of that.
  - **The CUDA circuit prover fails at fold 1**: block 0's leaf (2^21, last layer 0) gave a proof that
    the native verifier rejects (`FRI verification failed: FirstLayerCommitmentInvalid`). The CPU prover
    at fold 1 is fine (Mac: 2.1 s, 858 KB, accepted by the circuit verifier).
    - Fold 4 on the same pod: 1.55 s at 2^21 (k = 1) and 1.42 s at 2^22 (k = 2). Their proofs have the
      same SHA-256 as the CPU proofs made on the Mac.
    - So per-level shapes on CUDA need a stwo-zig fix: the remainder fold at fold 4 (preferred: the CPU,
      native and in-circuit verifiers already accept it, see above), or fold 1.
  - **Also**: the circuit verifier rejects any proof whose last layer is not 0 (`VerificationFailed`,
    seen on CPU at fold 4 with last layer 1). Such a proof can only be used for timing, never as a child.
- **Next:**
  1. stwo-zig: the remainder fold at fold 4 (or fold 1) on the CUDA circuit prover
     (`CUDA_FRI_REMAINDER_FOLD_BRIEF.md`, with both errors);
     until then, the 2^24 shape (8 children, about 5 s of GPU per block on an H100);
  2. per-level shapes;
  3. the forest and outer verifier over `TreeK` (`block_forest.zig` `expected` by arity).

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
