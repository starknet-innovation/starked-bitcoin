# Header commitment tree (HC-HASHTREE) — design

Status: current · Updated: 2026-10-08

**Goal:** the final proof carries one 32-byte root `T` committing to every block
hash by height, so anyone can point to "the block at height h has hash X" with a
short inclusion proof (D-032: Blake2s throughout).

## Shape: a Merkle Mountain Range

- Leaves: the block hashes (SHA256d of each header, as its 8 SHA-256 state words),
  in height order.
- Internal node: Blake2s-256 of `left ‖ right` (16 words, one compression with
  `t = 64`, final).
- A segment of `2^k` headers starts at a multiple of `2^k` (the segmentation from
  genesis guarantees this), so its leaves form a perfect subtree; the segment
  proves that subtree's root.
- The recursion fold runs in **MMR order**: segments left to right, merging the
  top two whenever they have equal size, which makes them Merkle siblings. At the
  end, the remaining peaks are merged right to left ("bagging"). Every merge joins
  adjacent height ranges, so the chain link check (`PubLink`) applies unchanged.
- `T` is the MMR root: canonical for a given tip and append-friendly. An inclusion
  proof for height `h` is the sibling path inside the peak plus the bagging path,
  about `log2(N)` hashes (about 20–22 for the 2026-10 chain, under 1 KB).

## Inside a segment

- **Tree component** (`blake2s_tree`): the proven Blake2s AIR, plus, per 88-row
  period:
  - a node index `i` (copied down the period, range-checked to `< 2^20`);
  - an `active` flag;
  - constant compression inputs (`h₀`, `t = 64`, final).
  
  Lookups:
  - uses `node(2i)` and `node(2i+1)` as the message;
  - yields `node(i)` with its output.
  
  The root (node 1) is pinned to the public inputs. `compress_sound` applies
  because the constraints are a superset of the Blake2s AIR's.
- **Header component:** each header `j` yields `node(2^k + j)` with its hash.
- **Soundness argument:** leaves come only from headers; every other yielded node
  is a Blake2s of yielded children with larger indices. Strong induction on the
  index (bounded, so no field wrap-around) gives: every yielded node value is the
  correct subtree root, whichever period yielded it.
- Lookup tuples carry 16 limbs plus an index, so the IR's lookup width limit rises
  from 15 to 32.

## Public inputs and aggregation

- The segment's public inputs gain `T` (8 words as 16 limbs).
- **Nodes:**
  - compute `T = Blake2s(T_L ‖ T_R)` in-circuit (Blake2s is native there);
  - place it in the combined public inputs;
  - otherwise behave as today (`PubLink`, identity key).
  
  The fold order changes to MMR order.
- **Lean:** `PubValid` gains "there is a tree over the segment's block hashes in
  order whose root is `T`"; `pub_compose` extends with the node case.

## Plan

1. Lookup width limit 15 → 32 (Zig native and in-circuit).
2. Lean spec: MMR shape, perfect subtree roots, inclusion-path semantics.
3. Tree component AIR (Lean) and its soundness (lookups + induction).
4. Header chain v7 as a system (header + tree components); pubs + `T`.
5. Lean: extend `header_chain_sound` and `Aggregate.lean` with `T`.
6. Zig: system-based header proving, node circuit computing `T`, MMR fold,
   outer verifier, inclusion-proof generator and checker.
7. Re-prove the whole chain.
