# Header commitment tree (HC-HASHTREE) — design

Status: current · Updated: 2026-10-08

**Goal:** the final proof carries one 32-byte root `T` committing to every block
hash by height, so anyone can point to "the block at height h has hash X" with a
short inclusion proof (D-032: Blake2s throughout).

## Shape: a Merkle Mountain Range (D-033)

- Leaves: the block hashes (SHA256d of each header, as its 8 SHA-256 state words),
  in height order.
- Internal node: `hnode(l, r)` = Blake2s-256 of `l ‖ r` (16 little-endian words,
  one compression with `t = 64`, final, the standard parameter block). Checked
  against Python's hashlib (`Spec/HeaderTree.lean`) and Zig's std
  (`src/btc/header_tree.zig`).
- `T` is the MMR root:
  - fold the leaves left to right, merging the top two whenever they cover
    equally many leaves;
  - then merge the remaining peaks right to left ("bagging").
  
  `T` is canonical for a given tip. An inclusion proof is the list of siblings
  from leaf to `T`, about `log2(N)` hashes: about 20–22 for the 2026-10 chain,
  under 1 KB.
- **Segments:** the plan (`spike.zig` `plan`) is greedy, largest first, so every
  segment of `2^k` headers starts at a multiple of `2^k`, and sizes never
  increase.
  - A segment's leaves therefore form a perfect subtree, and folding segment
    roots in MMR order gives the same `T` as folding single leaves (tested).
  - Segments have at least 2 headers: a 1-header segment has no tree node, so an
    odd last header is left for the next run.

## Inside a segment: one system, two components

Lean: `Gadgets/HeaderTree.lean`. Zig witness: `header_tree.generate`.

- **`headers`** (`header_chain_v7`):
  - the header-chain AIR, unchanged, plus one multiplicity column;
  - at row 215 of header `j` it yields `node(0, height − h₀, hash)`.
- **`tree`** (`blake2s_tree`):
  - the proven Blake2s AIR (88-row periods);
  - plus a node level `ℓ` and position `p`, copied down each period, with the
    level range-checked to 5 bits and nonzero;
  - plus constant compression inputs (`h₀`, `t = 64`, final).
  
  Lookups:
  - row 0 uses `node(ℓ−1, 2p, left)` and `node(ℓ−1, 2p+1, right)` (the message);
  - row 87 yields `node(ℓ, p, output)`, with a free multiplicity.
- **Public entry:** the verifier adds `node(K, 0, T)` with multiplicity −1
  (`system.verifyExt`; in-circuit `PlainStatement.ext`).
- **Soundness** (`tree_root_limbs` / `tree_root_sound`, standard axioms only):
  if the system with `2^L` rows balances with the entry `node(L−8, 0, x)`, then
  `x` is the limbs of `rootAt hash (L−8) 0`, the perfect tree over the segment's
  block hashes.
  - Proof: induction on the level.
  - Every looked-up tuple at level `ℓ ≤ K`, position `p < 2^(K−ℓ)` holds the
    subtree root.
  - Leaves come only from headers, since tree yields have level ≥ 1.
  - Level and position are bounded, so there is no field wrap-around.
- Tuples carry 16-bit limbs. The IR's lookup width limit rose from 15 to 32.

## Public inputs and aggregation

- **Public inputs:** a leaf's public inputs are the header chain's 108, then
  `T`'s 16 limbs (indices 108–123).
- **Leaf circuit** (`leaf.buildLeafCircuit`):
  - verifies the system proof with the entry `node(K, 0, pubs[108..124])`;
  - outputs `Blake2s(0 ‖ pubs)`.
- **Node circuit** (`node.treeNode`):
  - range-checks the children's limbs;
  - packs each pair into a u32 wire `lo + hi·i`;
  - computes `blake2sU32s(T_L ‖ T_R)` (64 bytes);
  - splits each output word into two guessed u16 limbs that must recombine to it.
  
  The native counterpart is `node.combine`. Indices below 108 are unchanged
  (`PubLink`, `combine`).
- **Fold:** `node.foldAll` and the verifier's `expectedRoot` both use
  `header_tree.mmrFold` over segment header counts. The VK lists them
  (`Vk.sizes`), so the identity key pins the fold shape.
- **Lean** (`Gadgets/AggregateTree.lean`, standard axioms only):
  - `PubValidT p`: `PubValid`, plus a binary tree whose leaves are the block
    hashes of the same headers, in order, and whose root's limbs are
    `pubs[108..124]`.
  - `leaf_valid_T`: leaves, from `tree_root_limbs` and `chain_sound_v2`.
  - `pub_compose_T`: nodes, given `NodeOut`, the node circuit's spec.
  - `chain_from_genesis_T`: the root.
  
  The Lean tree's shape is existential; the verifier fixes it through the key.
- **Tools:**
  - `header_tree.mmrRoot` recomputes `T` from headers natively; `spike` checks
    the root proof's `T` against it.
  - `inclusionProof` and `verifyInclusion` produce and check proofs for a height.

## Plan

1. Lookup width limit 15 → 32 (Zig native and in-circuit). **Done.**
2. Lean spec: `hnode`, `rootAt`, `HTree`, perfect subtrees. **Done.**
3. Tree and header-v7 components, Zig witness, `tree_root_sound`. **Done.**
4. Leaf over the system; node computing `T`. **Done.**
5. Lean: `PubValidT`, `pub_compose_T`, `leaf_valid_T`, `chain_from_genesis_T`. **Done.**
6. MMR fold, VK sizes, native root and inclusion proofs. **Done**, pending the
   end-to-end run.
7. Re-prove the whole chain (`spike chain 20 70 26`, about 8 h). **Todo.**

## Trusted (see verification.md)

- The node's `treeNode` matches `NodeOut`. It is stwo-zig's `blake2sU32s`
  gadget plus our packing; tested against the native combine.
- The leaf's public-entry handling in the plain verifier: tested; a wrong root
  is rejected natively.
