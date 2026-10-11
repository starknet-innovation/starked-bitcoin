# Decisions

Status: current · Updated: 2026-10-07

Append-only. A reversal is a new entry that says `Supersedes D-NNN`; also
add `Superseded by D-MMM` to the old entry's status field (the only allowed
edit).

- **By** is `owner` (the project owner decided) or `agent` (proposed by the
  implementer and not objected to).
- Agent decisions that change scope, trust model or public statements need
  owner approval first. See [README.md](README.md#escalation-when-to-stop-and-ask-the-owner).

Template:

```
### D-NNN — <title>
Date: YYYY-MM-DD · By: owner|agent · Status: active
Decision: <one or two sentences>
Why: <reasons; alternatives rejected>
```

---

### D-001 — New repo; Raito as reference only
Date: 2026-10-06 · By: owner · Status: active
Decision: Build `starked-bitcoin` from first principles. Raito
(`~/Workshop/raito`) is a reference spec and test oracle, not a fork.
Why: Raito is abandoned and Cairo-based. A from-scratch design can target
native AIRs and exhaustive state.

### D-002 — Prover: stwo-zig
Date: 2026-10-06 · By: owner · Status: active
Decision: Use stwo-zig. Production runs on an H200 (CUDA); local work on an
M4 Pro (Metal).

### D-003 — Native AIRs, not Cairo
Date: 2026-10-06 · By: owner · Status: active
Why: Performance, and AIRs small enough to verify formally.

### D-004 — assumevalid first; pluggable script module later
Date: 2026-10-06 · By: owner · Status: active

### D-005 — Exhaustive UTXO state with inclusion and non-inclusion
Date: 2026-10-06 · By: owner · Status: active
Decision: A canonical sorted Merkle tree. Current UTXO set first, history
later. Matches Bitcoin Core's set exactly; OP_RETURN outputs are tracked
separately.
Why: Utreexo gives membership only; non-inclusion is a requirement.

### D-006 — Parallel per-block proofs plus aggregation
Date: 2026-10-06 · By: owner · Status: active
Decision: A full node supplies root_in/root_out and hints. Blocks are proven
independently and aggregated.

### D-007 — Blake2s for our own commitments
Date: 2026-10-06 · By: owner · Status: active
Why: Owner preference over Poseidon.

### D-008 — Where code lives
Date: 2026-10-06 · By: owner · Status: active
Decision: Bitcoin-specific AIRs live in this repo. Generic prover changes go
to a stwo-zig fork and are upstreamed if useful. The pinned submodule is
never edited in place.

### D-009 — Lean-first single source of truth
Date: 2026-10-06 · By: owner ("do it right"), confirmed by the spike · Status: active
Decision: AIRs are defined and proven in Lean, exported to JSON
(`starked-air-v1`), and interpreted by Zig. Zig never defines constraints.
Why: Soundness proofs must be about exactly what the verifier runs. See the
[spike report](../reports/2026-10-06-lean-first-spike.md).

### D-010 — Formally verify the AIRs
Date: 2026-10-06 · By: owner · Status: active
Decision: Every AIR gets a Lean soundness theorem with standard axioms only.

### D-011 — Proof scope: "a valid chain exists"
Date: 2026-10-06 · By: owner · Status: active
Decision: Choosing the canonical chain is left to verifiers.

### D-012 — Browser verification deferred
Date: 2026-10-06 · By: owner · Status: active

### D-013 — The verifier pins the preprocessed commitment
Date: 2026-10-06 · By: agent · Status: active
Why: Without it, a prover can switch selectors off (reproduced forgery;
stwo-zig#225).

### D-014 — SHA-256 AIR layout: 72-row period, bits plus 16-bit limbs, no lookups
Date: 2026-10-06 · By: agent · Status: active
Why: Keeps soundness to bit-vector lemmas. Lookups can be revisited if
benchmarks demand it. See [airs/sha256.md](../airs/sha256.md).

### D-015 — Header-chain layout: 256 rows per header, consensus checks in scratch rows 216–255
Date: 2026-10-06 · By: agent · Status: active
Why: Constant offsets between a header's three compressions and its checks.
No LogUp needed yet.

### D-016 — Git: commit locally; never push without owner approval
Date: 2026-10-06 · By: owner · Status: active

### D-017 — Documentation and PM structure
Date: 2026-10-07 · By: owner (request), agent (structure) · Status: active
Decision: The README is the map; `docs/{design,airs,reference,guides,reports,project}`;
the PM process lives in [README.md](README.md).

### D-018 — Median time past by counting, not sorting
Date: 2026-10-07 · By: owner · Status: active
Decision: HC-V4 enforces `time_j > MTP` as "at least ⌊k/2⌋+1 of the k ≤ 11 previous times are strictly below `time_j`", with a range-checked difference per comparison. It does not sort inside the circuit.
Why: For a sorted list `s`, `t > s[⌊k/2⌋]` ⟺ `#{i : t_i < t} ≥ ⌊k/2⌋+1`. Counting is cheaper and much easier to prove than an in-circuit sort.

### D-019 — Finish M1 before starting M2
Date: 2026-10-07 · By: owner · Status: active
Decision: Complete HC-V4, HC-V5, HC-TOP, BENCH-RAITO and FV-Z3 before recursion/aggregation work.

### D-020 — Exact cumulative chainwork
Date: 2026-10-07 · By: owner · Status: active
Decision: HC-V5 exposes Core's exact chainwork: per header `floor(2^256 / (T+1))` (`GetBlockProof`), summed. It is not a lower bound.
Why: Verifiers can compare the proven value directly with `getblockheader … chainwork`.

### D-021 — Chainwork circuit requires target ≥ 2^128 (exponent s ≥ 16)
Date: 2026-10-07 · By: agent · Status: active
Decision: The HC-V5 work constraints require the PoW exponent `s = nSize − 3 ≥ 16`, so `q = ⌊2^256/(T+1)⌋ < 2^128` fits in 16 bytes and the whole computation fits in rows 241..253.
Why: This is a completeness restriction only. Soundness is unaffected: a header with `s < 16` cannot be proven at all. Mainnet targets so far have `s ≥ 20`, and `s < 16` would need about 2^128 expected hashes per block. The alternative, 32-byte `q`, does not fit the 15 free rows without doubling the rows per header (about 2× slower proving).

### D-022 — Defer GPU/H200 work until the full pipeline works
Date: 2026-10-07 · By: owner · Status: active
Decision: After M1, go to recursion/aggregation and then the UTXO state. GPU codegen and H200 runs (`GPU-CODEGEN`, `H200`) wait until headers + recursion + full UTXO set work end to end.
Why: Proving the whole header chain is estimated at about 1 h on the M4 Pro (extrapolated, not measured), so performance is not the bottleneck. Optimizing before the system is complete is premature.

### D-023 — Recursion via stwo-zig's circuit recursion (native, no Cairo)
Date: 2026-10-07 · By: agent · Status: active
Decision: Aggregate segment proofs with stwo-zig's ported StarkWare circuit recursion (PR #204): segments proven on the `proving_5a7c5ed` profile, a Bitcoin segment statement for the in-circuit verifier, leaf-wrap plus the fold tree. Details: [design/recursion.md](../design/recursion.md).
Why: It reuses an existing, byte-parity verifier rather than writing one, and it is consistent with D-003 and D-008. The Cairo-verifier route costs millions of Cairo steps per segment, and a bespoke recursion AIR would be the most work and the highest audit burden.

### D-024 — Extend the in-circuit verifier to multi-offset masks (Q-MASK option B)
Date: 2026-10-07 · By: owner · Status: active
Decision: Keep our AIRs and Lean proofs. Extend stwo-zig's circuit verifier so a trace column can be sampled at several row offsets (one OODS sample point per (column, offset), quotients batched as the native verifier does). The interaction (LogUp) phase becomes optional for AIRs without lookups. The work happens on a local branch of the `third_party/stwo-zig` submodule (`starked/multi-offset-masks`), not pushed until the owner decides (D-016, D-008).
Why: Preserves the formally verified AIR. The extension is new verifier code with no Rust parity oracle, so it is validated by differential tests against the native verifier and by adversarial tests; recorded in verification.md.

### D-025 — Our own node circuit: in-circuit linking and a circuit-identity key
Date: 2026-10-08 · By: agent · Status: active
Decision: Aggregate with our own node circuit (`src/recursion/node.zig`) instead of upstream's multiverifier. Every leaf and node outputs `Blake2s(key ‖ 108 public inputs)`. A node verifies two child circuit proofs, recomputes each child's digest from the guessed key and public inputs, and checks `PubLink` (right input state = left output state; heights +1 with 16-bit limbs and a carry). It outputs the digest of `combine(pL, pR)` (left input state, right output state) under `key = Blake2s(hL ‖ kL ‖ hR ‖ kR)` (circuit hashes and keys of the children; 0 for leaves). Leaves and nodes are padded to one shared target, so one node circuit verifies both. The outer verifier checks the root proof against the node circuit's preprocessed root, recomputes the expected key from the tree shape and the known leaf/node circuit hashes, and checks genesis input state.
Why: Upstream's multiverifier only hashes child digests, so linking would be checked outside the proof, which is not succinct. Checking the link inside every node keeps the root statement at one segment's size. The Lean side is proven at the public-input level (`pub_compose`, `leaf_valid`, `chain_from_genesis` in `Gadgets/Aggregate.lean`); the node circuit's Zig code mirrors `PubLink` one-to-one and is a trusted component (verification.md).

### D-026 — M3 starts with M3a (block structure); the owner provides the node
Date: 2026-10-08 · By: owner · Status: active
Decision: M3a first: block structure (transaction parsing, Merkle root, witness commitment, size and weight limits, `CheckTransaction`-style checks). M3b (UTXO set) comes later; Utreexo is not required: the UTXO commitment should favour an organized, searchable set. The owner sets up an archival `bitcoind` (local network or cloud). Until then, work from sample blocks fetched from public APIs.
Why: It keeps scope small, and Lean specs and AIRs can be built and tested on samples. The node is needed for full-scale runs and for M3b.

### D-027 — GPU work only when performance blocks progress
Date: 2026-10-08 · By: owner · Status: active
Decision: Continues D-022 into M3: Lean proofs and circuits first; acceleration once a measured performance wall is hit.
Why: Correctness and provability before speed.

### D-028 — Block data as multiple components linked by LogUp; IR-LOGUP first
Date: 2026-10-08 · By: owner · Status: active
Decision: The M3a block-data proof uses several components (byte stream, parser, SHA-256, Merkle, checks) linked by LogUp lookups. Work order: `IR-LOGUP` first, then the parser, then hashing, Merkle and checks.
Why: Variable-length data cannot be followed with fixed row offsets, and `HC-HASHTREE` needs lookups too. See [block-data.md](../design/block-data.md).

### D-029 — The block commitment reserves spent-output slots from day one
Date: 2026-10-08 · By: owner · Status: active
Decision: The canonical block encoding committed by the M3a block proof includes, for every input, the spent output (amount, scriptPubKey, creation height, coinbase flag), filled by the prover from undo data. M3a commits to these slots without checking them; M3b proves they equal the coins removed from the UTXO set.
Why: M3a block proofs stay valid when M3b (and M3c, whose Taproot sighash needs spent amounts and scripts) arrive; re-proving every block would cost months of CPU.

### D-030 — Blake2s for the block commitment
Date: 2026-10-08 · By: owner · Status: active
Decision: The block-data commitment uses Blake2s-256.
Why: Mature, native in the recursion circuit (Blake gate), easy for anyone to recompute. Cost inside AIRs is higher than Poseidon2 (bit operations); revisit only if hashing becomes the measured bottleneck (D-027). Both are post-quantum in the usual sense for hashes (about 128-bit preimage security under Grover at 256-bit output); to be reviewed.

### D-031 — Duplicate inputs are excluded by M3b, as a named obligation
Date: 2026-10-08 · By: owner · Status: active
Decision: M3a does not prove Core's `bad-txns-inputs-duplicate` rule. M3b's UTXO update must reject a transaction listing the same outpoint twice (inputs removed one at a time, so a second removal fails), and M3b's soundness theorem must cover it explicitly.
Why: A uniqueness argument inside M3a needs sorting. The rule exists in Core because "the UTXO step will catch it" was false for Core's check-then-spend design (CVE-2018-17144: the check was skipped in block validation, which allowed crashes and inflation). M3b must not repeat that assumption.

### D-032 — Blake2s for the header tree; order: Blake2s AIR, header tree, then M3a
Date: 2026-10-08 · By: owner · Status: active
Decision: `HC-HASHTREE` hashes with Blake2s inside the AIRs and in the recursion nodes. Work order: a Blake2s compression component with its Lean proof (shared with the block commitment, D-030), then `HC-HASHTREE` (header AIR v7, node circuit, outer verifier, full-chain re-proof), then M3a.1–M3a.6.
Why: One hash throughout keeps the verifier simple; Blake2s is native in the recursion circuit; the Blake2s AIR is needed for M3a anyway.

### D-033 — The header commitment is a Merkle Mountain Range over block hashes
Date: 2026-10-08 · By: owner · Status: active
Decision: `HC-HASHTREE` commits to block hashes in height order as an MMR: each segment proves its aligned perfect subtree root; the recursion fold runs in MMR order (merge equal-size neighbours, then bag the peaks); nodes hash children roots with Blake2s. Design: [header-tree.md](../design/header-tree.md).
Why: The MMR follows the segments and the recursion naturally (no padding nodes or extra circuits), is canonical for a tip and append-friendly. Inclusion proofs are about log2(N) hashes; the verifier needs the chain length to know the shape.

### D-034 — Merkle nodes are SHA messages; the transaction count is public
Date: 2026-10-09 · By: Claude (agent), on the owner's "go ahead" for M3a.4 · Status: active
Decision: Inner Merkle nodes are hashed by the existing SHA component, with two new period kinds (`NODE`: words from the children's digests; `NPAD`: constant padding). A Merkle component lays out the tree level by level and yields node tuples and lengths. The block's transaction count becomes public input 1, checked by the fields' first row. The mutation check (CVE-2012-2459) runs in the `NODE` period. The witness tree reuses this; its commitment check moves to M3a.5. Design: [block-data.md](../design/block-data.md#m3a4-blk-merkle-design-draft-2026-10-09).
Why: Reuses the proven compression and `digest_sound`; child digests are already state words, so no byte handling. Without a public (or otherwise bound) count, a prover could hash a prefix of the transactions.

### D-035 — M3a.5 checks a flattened spec with four new components
Date: 2026-10-09 · By: Claude (agent), design pass on the owner's request; **approved by the owner 2026-10-10** · Status: active
Decision:
- **The spec is flattened in Lean first.** `checkBlock = none` is proven equivalent to a conjunction
  `BlockOK`, with simplifications:
  - the value rules reduce to "values are non-negative and the total is at most `MAX_MONEY`";
  - the size rules reduce to weight;
  - `bad-cb-multiple` reduces to `prevout-null`;
  - sigops become a byte automaton.
- **The context is public.** Height, `prevMtp` and the three activation bits become public inputs 2–6,
  computed by the verifier.
- **Four new components:**
  - a 16-bit range table;
  - an opcode table;
  - a sigop walker, one row per script byte;
  - a small `ctx` component for once-per-block reads (coinbase shape, BIP34, cutoff, commitment,
    weight and sigop totals).
- **Per-token checks go in the fields component.**
- **The witness tree reuses the Merkle and SHA components with no SHA change.** Its nodes turn the
  mutation check off, as Core does. The commitment is one more node, `(witroot, nonce)`, with the
  nonce and the zero leaf supplied as pseudo-digests.

Duplicate inputs stay with M3b (D-031). Design:
[block-data.md](../design/block-data.md#m3a5-blk-checks-design-approved-2026-10-10-d-035).

Why:
- Proving `= none` needs only the conditions, not Core's error order.
- The simplifications cut the AIR work, for example one total comparison per transaction instead of
  three checks per output.
- Public activation bits avoid comparisons on public values inside the AIR.
- Reusing the SHA and Merkle components keeps the proven compression untouched.

Amendments (2026-10-10, Claude, during implementation; **confirmed by the owner 2026-10-10**):
- **The range table is 8-bit** (`block_tables`, relation `R8`), not 16-bit. All block components
  share one trace size, so a `2^16`-row table would force every block to `L ≥ 16`. Wider values
  are split into bytes. Owner: keep 8-bit; after per-component trace sizes (lifting) land, measure
  what a 16-bit table would save and switch only if it pays, before any large proving run.
- **The previous MTP is public as two 16-bit limbs:** `pub 3` (low) and a new `pub 7` (high). With
  one public value and private limbs, limbs summing to `prevMtp + P` also satisfied
  `lo + 65536·hi = pub 3` in M31, which would have loosened the finality cutoff. Found while
  proving `block_sound`. The side condition is now `prevMtp < 2^32`, not `< P`.
- **`block_sound` is proven** (`Block/BlockSound.lean`, standard axioms only), with hypotheses
  `height < 2^23`, `prevMtp < 2^32`, `BlockPubs c pub`, and no repeated prevout in a transaction (D-031).

### D-036 — The chain proof is a file of MMR peaks under a pinned, frozen VK
Date: 2026-10-10 · By: Claude (agent), on the owner's "get started" (owner chose extendable over re-verifiable only); **confirmed by the owner 2026-10-10** · Status: active
Decision:
- **The node shape is frozen.** It covers leaves of every segment log size 9..20, so the VK never
  changes with the run.
- **The production VK is pinned.** It is committed in `vk/` and built into `chainproof`.
- **The file is extendable.** It stores the segment plan, the MMR peaks and the bagged root, plus
  leaf 0's path. Extension pushes aligned segments onto the peaks.
- **The verifier pins the root's request.** It checks the PCS config and the columns, the plan's
  alignment, every peak, the Lean-exported genesis-state checks and Bitcoin's genesis hash as leaf 0.
- **Writes are atomic,** and long runs checkpoint after every segment.

Design: [proof-store.md](../design/proof-store.md).

Why:
- The first full run kept nothing.
- An unpinned request let a stored proof claim weaker FRI parameters.
- A run-dependent node shape would have orphaned the stored peaks at the first extension.

### D-037 — assumeUTXO compatibility is a goal
Date: 2026-10-10 · By: owner · Status: active
Decision: The UTXO module (M3b) must be able to prove that the UTXO set reached by valid blocks from
genesis hashes to the `hash_serialized` value Bitcoin Core pins for its assumeUTXO snapshots
(`HASH_SERIALIZED`, SHA256d over the coins in Core's key order). So:
- the UTXO commitment (`Q-TREE`, still open) must allow a sorted traversal in Core's coin order,
  with each coin's `TxOutSer` fields (outpoint, height and coinbase flag, amount, script);
- the target is `HASH_SERIALIZED` at Core's snapshot heights, not MuHash (see the scoping note);
- the same traversal yields the total amount, for a no-inflation statement.

Why: it makes an assumeUTXO snapshot checkable without trusting the constant in Core's
`chainparams.cpp`. As far as we know, no one does this today.

Scoping: [utxo-hash-scope.md](../design/utxo-hash-scope.md).

### D-038 — The block commitment hashes the raw block and an undo record
Date: 2026-10-10 · By: Claude (agent), on the owner's "go forward, finish M3" · Status: **amended by
the owner 2026-10-10** (see the amendment at the end of this entry)
Decision:
- `C = blake2s(blake2s(raw) ++ blake2s(undo))`, output as 8 public words.
- `undo` is a version byte `0x01` then one record per input after the coinbase, in block order (the
  byte also keeps the undo table non-empty). A record is Core's
  `TxOutSer` without the outpoint: the 4-byte code (height·2 + coinbase), the 8-byte amount and the
  script with its CompactSize length.
- M3a hashes `undo` unchecked (D-029); M3b proves it.

Design: [block-data.md § M3a.6](../design/block-data.md#m3a6-blk-commit-design-proposed-2026-10-10-d-038).
Why:
- The raw block makes the encoding trivially canonical: modules re-parse with the proven fields
  component, and no second encoding needs a proof.
- The records plus outpoints are `TxOutSer`, the unit of assumeUTXO's `hash_serialized` (D-037).
- Two inner hashes let a module open only what it needs.


Amendment (owner, 2026-10-10): **`C = blake2s(undo)` only.** The raw block is bound by the public
block hash (inputs 25–40): for a valid block, the header's Merkle root and the coinbase's witness
commitment fix every byte, and `block_sound` proves both. This drops the raw block's Blake2s stream
(the larger part of the commitment's cost). The undo format (2b) and the version byte (2c) stay.
A later proof that re-reads the raw block checks it against Bitcoin's SHA-256 trees, not Blake2s.
Built 2026-10-10 (5014aeb): `commit_sound` re-proven; 96 lookup sites per row.

### D-039 — A block proof is a file bound to the chain proof by its public block hash
Date: 2026-10-10 · By: Claude (agent), on the owner's "go forward, finish M3" · Status: active (**owner decisions 2026-10-10** at the end of this entry)
Decision:
- **Block hash public:** public inputs 25–40 are the 16-bit limbs of `SHA256d(header)`. The context
  component reads `digest(0, pub 25..40)` once, and SHA's free yield multiplicity serves it, so no new
  component and no external lookup entries. Proven: `HashPub.hash_pub`.
- **File `.sbblock`:** log size, the 41 public inputs, the claimed LogUp sums, stwo's postcard
  encoding of the STARK, provenance (`src/block/proof_file.zig`).
- **Verifier (`chainproof verify-block`):**
  1. verify the chain proof under its pinned VK and the minimum chainwork;
  2. bind `headers.bin` to it: its block hashes fold to the proof's MMR root `T`;
  3. verify the block STARK under a pinned FRI configuration (70 queries, 26 PoW bits, as the chain
     proof), refusing a file made with any other;
  4. check public inputs 2–7 (height, previous median time past, soft-fork flags) against the headers,
     and 25–40 against the header at that height.
  Inputs 0, 1, 8 (block length, transaction count, undo length) and 9–24 (the commitment) are
  outputs of the statement.
- **Undo data** comes from a node's `getblock <hash> 3` (`scripts/fetch_undo.py`), checked against the
  proven headers; the prover refuses an empty undo stream for a block that spends outputs.

Why:
- Binding through the headers (not an in-circuit inclusion path) reuses the chain proof unchanged and
  costs the verifier one pass over 80-byte headers (about 2 s for 970k headers).
- The block proof is not yet folded into the recursive chain proof: a ~900-column, 12-component
  verifier circuit is a separate step (`BLOCK-REC`, backlog). Until then a block proof is a standalone
  file of about 0.5–2 MB.

Owner decisions (2026-10-10): **self-contained files**: the file carries the block's header and the 11
before it with MMR inclusion paths, so a verifier needs only the chain proof and the block file (no
`headers.bin`). Strength matches the chain proof (70 queries, 26 bits). Standalone now; `BLOCK-REC`
after M3b. Built 2026-10-10: file version 2 carries the window; `chainproof rebind-block` rebuilds it for
a longer chain without re-proving.

### D-040 — M3b keeps the UTXO set by a chain-wide multiset argument, not a per-block tree
Date: 2026-10-10 · By: Claude (agent), **approved by the owner 2026-10-10** · Status: active (decides `Q-TREE`)
Decision (proposed): created coins add `1/(z − coin)` and spent coins subtract it, with the coin's
tuple taken from the parsed outputs and from the undo records. Each spend checks that the coin's position
`(height, tx index)` is earlier. Over an epoch the sum, minus the strictly sorted final set, is zero.
`z` is drawn from the MMR of the block commitments, computed before proving and checked at the end.
The final set's pass also gives `HASH_SERIALIZED` (D-037) and the total amount.
Design: [utxo.md](../design/utxo.md).
Why: about 10¹⁰ rows over history against about 4 × 10¹³ for a per-block sorted Merkle tree (*est.*);
it checks the undo records (D-029) and duplicate inputs (D-031) by construction. Cost: statements hold
per epoch, not per block, and tip following needs short epochs or a tree for the last stretch.

Owner decisions on D-040 (2026-10-10):
- Build the multiset argument first. A per-block tree (hybrid, for the stretch after the last epoch) is
  built only if assessment shows tip following needs it.
- Epochs end at Bitcoin Core's assumeUTXO heights (840,000, 880,000, 910,000), so each yields a check
  of Core's pinned `hash_serialized`: trustlessness for what Core ships.
- Tip following: start by matching Core's snapshots, compute them, then assess.
- Cost estimate corrected: script fingerprints cost about one row per script byte, so M3b adds roughly
  10–30% to the block proofs (*est.*), not 10¹⁰ rows in total.

### D-041 — Every value behind an epoch event's tuple is fixed before the epoch challenge
Date: 2026-10-11 · By: Claude (agent) · Status: active (soundness fix within D-040; owner to review)
Decision: the epoch seed hashes the initial and final coin sets' full encodings (`setDigest`, Blake2s of
`encodeSet`), and each undo record carries the spent coin's creating-transaction index (3 bytes after
the code) and its `serTxOut` length (2 bytes) inside the Blake2s-committed undo stream, read by URec: the
index equals the coin row's `CTX`, the length is the record's `TL`, so the records' boundaries follow from
the committed bytes.
Why: the LogUp and fingerprint bounds (`balance_of_sum`, `fp_separates`) hold for events chosen before
the challenge. Before this fix, three inputs to the fractions were chosen after it: the final set (read
at verification, not in the seed), the initial set's transaction indices (`hash_serialized` omits
them), every input's claimed `CTX` (a free trace column), and the records' lengths `TL` (constrained
only to tile the stream, so the boundaries, and with them every claim, were a trace choice; found
2026-10-11 while assembling the epoch proof). With hundreds of free choices, a
generalized-birthday (Wagner) search over QM31 sums can make a false epoch balance at feasible cost
(*est.*: practical with 2^4 lists of 2^31 candidates). Cost: 5 columns, 5 byte lookups and 1 constraint
in URec, 5 bytes per spend in the commitment; epoch proofs made before the fix must be re-proved.

### D-042 — The hybrid UTXO tree is scheduled: per-block tree updates at the tip, epochs as baselines
Date: 2026-10-11 · By: owner, in discussion with Claude (agent) · Status: active (amends D-040's tip clause)
Decision: D-040 left the per-block tree as a contingency ("only if assessment shows tip following
needs it"). The assessment is made: following the tip with proven state needs it, so it is scheduled
(`UTXO-TREE`), structured as:
- **Baseline:** a multiset epoch closed at a checkpoint height (assumeUTXO heights first), plus one
  segmented pass proving the sorted final set builds a Blake2s sorted-tree root `R`;
- **Tip stretch:** per-block tree-update proofs advance `R` (spends: inclusion + delete; creations:
  non-inclusion + insert, in Core key order per D-037);
- **Re-baseline:** the next epoch close, from the previous set, must rebuild to the same root the
  incremental updates reached — the multiset and tree arguments cross-check each other.
Until UTXO-TREE exists, the interim tip product is the baseline plus native application of each
block's committed coin events.
Design: [block-rec.md](../design/block-rec.md).
Why:
- An epoch close costs O(set) however few blocks it covers (the final-set pass), so rolling epochs
  give a proven set daily at best, never per block. Per-block proven state needs per-block cost
  proportional to the block, which only the tree gives (about 7,400 rows per coin event, *est.*).
- RAM is not the constraint: no step needs chain-proportional memory (per-worker traces are bounded
  by the 4M-weight consensus constant; the final-set pass and catch-up are segmentable and
  parallel). The constraint is cadence, which the tree fixes.
