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

### D-043 — The block-proof interface for aggregation
Date: 2026-10-11 · By: Claude (agent) · Status: **accepted** (owner, 2026-10-12: option A for (3); "no
need to export the timestamps")
Proposal: before CATCHUP freezes the block interface, (1) the epoch seed becomes tree-shaped (seed v3:
aligned binary tree of `Blake2s(hash_h ‖ C_h)` leaves), (2) block hashes bind to the chain's `T` per
aligned subtree, (3) the previous-block MTP is proven inside the block proof from its 11 predecessor
headers linked by prev-hash (option A), (4) the leaf recomputes height-derived context, (5) leaves and
nodes expose the compact summary listed in block-rec.md.
Design and the alternatives for (3): [block-rec.md § The block-proof interface](../design/block-rec.md#the-block-proof-interface-for-aggregation-proposed-d-043).
Why: the v2 seed is a linear stream no recursion node can fold, and the MTP context has no
aggregator obligation; both change the block proof, which must not change after CATCHUP.
Implemented (2026-10-12): (1), (2), (4) in the recursion (block-rec.md § Built so far); (3) as a 16th
block-system component, `block_anc` (`Block/Anc.lean`, `AncSound.anc_sound`, `BlockAnc.block_mtp`):
the 11 predecessors and the block's header hashed and linked in the header chain's layout, the MTP
limbs (public 3, 7) pinned to their median; below the CSV height the limbs are 0. The times stay
private; the tree carries nothing for the MTP.

### D-044 — The recursion's trust boundary: stwo-zig's verifier circuits upstream, our wiring here
Date: 2026-10-12 · By: owner, with Claude (agent) · Status: **accepted**
Decision:
- **VL-FRI belongs upstream.** stwo-zig's in-circuit verifier gadgets (`sv.*`: FRI commit and
  decommit, folding, query selection, DEEP quotients, circle arithmetic) are stwo-zig code, not ours.
  Their formalization runs in the stwo-zig repo, briefed in `~/Workshop/stwo-zig/VERIFIER_FORMALIZATION_BRIEF.md`
  (a separate agent). Until it lands they are trusted as StarkWare-derived and parity-tested, with
  VL-ORACLE as evidence.
- **VL-NODE is split.** The recursive verifier itself (`stark_verifier.verify`, `CircuitStatement`) goes
  upstream, under the same brief. Our wiring around it moves to Lean-first programs here, with
  theorems and named hypotheses for the trusted call (branch `vl/node-wiring`). That wiring is the
  statement passed, the child digest binding, the circuit hash, the key and the root output.
- **Node mutation testing is not scheduled.** It would test the upstream half as we use it. Run it if
  the upstream work stalls, or before any external soundness claim.
Why: "everything we wrote is proven, only StarkWare-derived software is trusted" (verifier-formalization.md).
The gadgets serve every stwo-zig user, so their proofs belong where the code lives.
Review: soundness claims built on this boundary need review before external use.

### D-045 — Per-component trace sizes: two profiles, Lean generalized, old theorems kept verbatim
Date: 2026-10-12 · By: owner, with Claude (agent) · Status: **accepted** ("Go ahead")
Decision: the block system's components may have different trace sizes
([component-sizes.md](../design/component-sizes.md)).
- **Profiles:** two, chosen per block.
  - *uniform* is today's system; its proofs stay byte-identical.
  - *tiered*: {sha, msg, bytes, walk} at L; {fpwalk, b2s, undo, b2msg} at L−2; the rest at L−5
    (minimum 8); ctx and tables at 8; anc at 12. A block that doesn't fit the tiers uses *uniform*.
- **Keys:** block VKs are keyed by (L, profile).
- **Lean:** generalized to arbitrary size vectors.
- **Acceptance (owner constraint, "anything proven today should be proven after the change"):**
  `Compat.lean` restates every current theorem's statement verbatim as a corollary at the constant size
  vector, and the build must pass it. The mixed-size soundness assumption (`StarkSoundV`) is a new named
  hypothesis; it is checked against Stwo's lifting soundness argument before anything relies on it.

### D-046 — Default size profile: tiered from 2^12, uniform below
Date: 2026-10-13 · By: owner ("make tiered the default for L ≥ 12, keep uniform for small blocks") · Status: **accepted**
Decision: the production tools choose the profile by size (`block.system.sizesAuto`, `Opts.auto`).
- A block whose uniform size is at least 2^12 (`TIERED_MIN_L`) is proved *tiered*. If it doesn't fit the
  tiers it falls back to *uniform*, as before (D-045).
- Smaller blocks stay *uniform*: tiering gains nothing there and costs ~5 % proof size (block 0: 718 KB
  vs 681 KB).
- Defaults: `chainproof prove-block` and `prove-epoch` (`--uniform` / `--tiered` force one),
  `cuda-prove` (`--size auto|uniform|tiered`), `metal-prove` (`METAL_PROVE_UNIFORM` / `METAL_PROVE_TIERED`).
  The library's `Opts` default stays uniform so tests and golden hashes keep their meaning.
- Why: tiered is the only profile that fits 2^23 blocks on one GPU (53 GiB vs ~186 GiB) and reaches 2^24
  (`SizeOk`).
- Open: tiered proofs rest on `StarkSoundV`, sent for review to stwo-zig
  (`~/Workshop/stwo-zig/LIFTING_SOUNDNESS_BRIEF.md`); the review gates freezing the block VK set.

### D-047 — The epoch layers' VKs are pinned in the binary
Date: 2026-10-26 · By: owner · Status: active
Decision: The epoch verifiers (`verify-chain`, `verify-epoch-wide`, `verify-epoch-root`,
`verify-epoch-tree`) accept only the tree, root and join VKs committed in `vk/epoch/` and embedded in
`chainproof`, as the header chain's VK already is. `--unpinned` accepts others for tests and says so.
`chainproof setup-vks` remakes the VKs from public inputs (the forests, one block proof per size key,
the Lean-exported programs) so anyone can check a pinned VK is the honest circuits'. A new size class
or chain shape adds a pinned VK in a reviewed commit.
Why: the verifiers read these VKs from the prover's files, so a dishonest prover could name a circuit
that outputs the expected digest and checks nothing. Recomputing them in every verifier was rejected:
it needs the block proofs and minutes per verification.


### D-048 — The coin-set pass: scope, balance, anchor
Date: 2026-10-27 · By: owner ("Ok on all 3") · Status: accepted
Decision (docs/design/set-pass.md):
- **Scope:** prove all three boundary sets of the current chain (after blocks 935,000, 945,000 and
  972,500). The 945,000 set closes one epoch and opens the next, so its pass computes its fractions
  under both challenges.
- **Balance:** first checked natively by `verify-chain` on the set-pass roots' public values (no set
  files); folding it into the join, so one proof covers everything, comes later.
- **Anchor:** the start set's `hash_serialized` is compared with Bitcoin Core's pinned assumeUTXO value
  at height 935,000, built into the binary with the `chainparams.cpp` line cited, as
  `nMinimumChainWork` is.
Why: a verifier then needs no set file (today three 14.2 GB files and ~33 minutes); the pass computes
exactly the digest and fraction the block proofs bind, so nothing proven is redone.

### D-049 — A verify-only header chain file
Date: 2026-10-27 · By: owner ("Do option 1 to shrink the header proof") · Status: accepted
Decision: `.sbchain` gains a root kind `compact`: the root proof without the peak proofs.
`chainproof compact` writes it from a verified full file; every verifier accepts it; extension refuses
it. The full file stays the prover's, for extending at the tip.
Why: the root's public inputs are attested by the root alone (its circuit and key follow from the
plan), so the peaks only serve extension. 13.8 MB → 0.99 MB. No circuit, VK or proof changes.
Rejected for now: folding the header root into the join (a new circuit; planned with the set pass's
final step) and a compression proof (only worth it after that).

### D-050 — A per-coin commitment in the set pass
Date: 2026-10-27 · By: owner ("Yes, I need it. I'm ok with it only at specific heights", "go ahead.
You can also proceed with the GPU run") · Status: accepted
Decision (docs/design/set-pass.md § Membership): the set pass also proves a Merkle root over the set's
records, so anyone can check that a coin is (or is not) in a proven set with ~1 KB instead of the set
file. Leaf `i` is Blake2s-256 of `key(i − 1) ‖ record i` (the previous record's outpoint key, 36 zero
bytes for the first): one leaf proves membership, and one leaf whose previous key is below an outpoint
and own key above it proves non-membership. Nodes are Blake2s-256 of `left ‖ right` (64 bytes; leaves
are at least 93 bytes, so a node is never a leaf). Each segment hashes its records into a perfect
tree of `2^D` slots (empty slots are 32 zero bytes); the set tree combines segment roots with the same
node hash. Only at the proven heights (the epoch boundary sets); every height (a per-epoch tree of
spends, or per-block updates) is left for later.
Why: the pass's existing commitments (the file's Blake2s, `hash_serialized`, the fraction sums) are
sequential or aggregate, so a single coin can only be checked against them with the whole file.

### D-051 — The chain seal: the balance and set links folded into one proof over the join and the set roots
Date: 2026-11-04 · By: agent (owner: "do everything that needs to be done to complete our goal, don't stop";
the goal being status.md's next step, "fold the balance check and the header root into the join") · Status: accepted
(owner, 2026-11-05: "we good. Accept and push."; the pinned seal VK accepted as written by `prove-seal`)
Decision (docs/design/chain-seal.md):
- **A new top circuit, not a changed join.** `chainSeal ms gen` verifies the chain's last join and the
  set-pass roots in-circuit and checks there what `verify-chain --set-proofs` checked natively: `acc`
  and every epoch root's `rest` opened, the set roots' summaries opened to the passes' start and final
  state vectors, the balance per epoch, the Blake2s finish of each pass to the digest the epoch root
  bound, the count and height ranges. The join, root, tree and set VKs are unchanged and stay pinned;
  the seal's identity is pinned as `vk/epoch/seal-935001-972500.vk`.
- **SHA-256 stays native.** `hash_serialized` is finished natively from the public final state; the
  seal commits to the Blake2s digest of the SHA-256 state (`shaEnd`, `shaStart`). No SHA-256 gadget
  exists in the glue language.
- **The header root and the `T` paths stay native for now** (SEAL-T): per epoch child an in-circuit MMR
  inclusion with sides computed from the position's and the leaf count's bits, about 2^20 more G gates.
Why: one proof whose public values state the chain's range, start and end sets and the end set's facts
is what a Starknet verifier or a Core fork can check; six proofs plus glue is not. A new circuit keeps
every proven layer (and its $) as is; the seal verifies them.
Rejected: changing the join's program (every join and root VK would move, and the roots at 2^25 would
be re-proved); a SHA-256 gadget for the seal (weeks, for two compressions over public bytes).

### D-052 — SEAL-T: the header chain root and the block-hash paths inside the seal
Date: 2026-11-06 · By: agent (owner: "push and go for it, don't stop until you're done or you need me", SEAL-T among the items) · Status: accepted
(owner, 2026-11-09: "cool, then validate it"; after the mainnet proof, the pinned VK `vk/epoch/sealt-935001-972500.vk` and `sealT_soundW`)
Decision (docs/design/chain-seal.md § The header chain in-circuit):
- **A new program, `chainSealT ms gen D`** (`Circuit/ChainSealT.lean`), additive: `chainSeal ms gen`, its VK
  and the mainnet seal of D-051 are unchanged. The header chain root proof is one more child (hook
  `S + 1`, its 124 public inputs opened); the genesis checks (`HeaderTree.genesisChecks`) run in-circuit;
  `T` is read from its public inputs; every epoch child's block-hash root and the genesis block hash get
  an MMR inclusion path of `D` steps (guessed siblings, guessed side bits, a guessed length whose one-hot
  masks the steps), ending at `T`.
- **The sides and lengths go into the output message, not into the circuit's logic.** They are a
  function of the position and the header count only (`HT.inclusionSides`), which the verifier computes
  (arithmetic, no hashing) when it rebuilds the message; this binds each path to its position without an
  in-circuit MMR-shape gadget. The message also carries the tip, its height and the chainwork, which the
  verifier's minimum-work check reads.
- **`D = 32`** for the exported programs: in the MMR over `n < 2^N` leaves a leaf in peak `j` (of size
  `2^p`, `p ≤ N − 1 − j` as the peaks shrink) is `p + j + 1 ≤ N` steps from the root, so 32 steps cover
  every chain below 2^31 headers. Mainnet's 32 children need at most 19, genesis 20.
- **The header root's verifier configuration comes from the pinned header VK** (`node.Identity`: columns
  and PCS config), so `setup-seal-vk` needs no header proof.
Why: after D-051 `verify-seal` still verified the header chain root natively and checked 32 block-hash
paths against `T`; with this, its native work is the plan's key, the positions' sides, the sets' facts
and one STARK verification. Sides in the message are what a verifier would compute anyway to know which
blocks the seal covers; an in-circuit sides gadget would cost a bit decomposition of the position and the
count and a proof of the MMR fold's shape for no change in what the verifier must know.
Rejected: changing `chainSeal` in place (the D-051 VK and mainnet seal would no longer verify until
re-proved); one range proof per epoch from the children's roots (the fold's topology depends on the
positions and the count, so a fixed circuit would need the same guessed structure as paths).


### D-053 — NODE-BOOT step 2: the patched node skips background validation
Date: 2026-11-13 · By: owner ("skip, and push") · Status: accepted
Decision: the Core patch of NODE-BOOT step 2 loads a snapshot whose `hash_serialized` and base block are
attested by a verified seal (`chainproof verify-snapshot`) and does **not** run background validation of
the blocks below the snapshot's base. The node is usable within minutes of loading the snapshot.
Why: background validation re-downloads and re-validates the whole chain, which is the cost the seal
exists to remove; keeping it would give the node no lasting saving over stock assumeUTXO.
Consequence: the node trusts what the seal proves and nothing more. Signatures and scripts below the
base are not checked (the proof's assumevalid-like gap, `docs/design/overview.md`), and soundness rests
on the proof system and its Lean model. Release only after external review of the patch and of that
trust statement.
Rejected: keeping background validation (safer, but saves nothing at steady state over stock
assumeUTXO with a hardcoded hash).


### D-054 — Time-based BIP68: the claimed median time is committed; the block commitment changes
Date: 2026-11-19 · By: owner ("I accept") · Status: accepted
Decision: for each time-locked input the undo stream carries the claimed median time past of the block
before the spent coin's, so the claim is under the block commitment `C_h` and fixed before the epoch
challenge; one resolver proof per epoch checks the claims against the header chain
([connect-rules.md](../design/connect-rules.md), option A).
Consequence: `C_h` changes for every block, hence the epoch challenges, hence the set passes are redone
(about $75 each at the 972,500 set's size, 2026-11-03 bill). They are redone anyway by SNAP-HASH and by a
run from genesis; all changes land in one re-prove.
Why: a claim that is a free trace value could be chosen after the challenge is known; `LogUpSZ` covers
only tuples fixed before it (the reason for D-041).
Rejected: (B) a claims digest folded by the tree (no commitment change, one more digest in every leaf and
node circuit); (C) per-height MTP in the header tree (re-proves the frozen chain VK, D-036); (D) leaving
time-based locks unproven.

### D-055 — TIERS-2: try a tighter size profile before the next full re-prove
Date: 2026-11-19 · By: owner ("Yes let's try") · Status: accepted
Decision: add a third size profile, closer to what the components need, and use it for the next full
re-prove if it holds up. The offsets are fixed after CONNECT-RULES, which grows `walk` and `coin`.
Measured on blocks 935,001–972,500 with the current AIRs
([report](../reports/2026-11-19-block-cost-split.md), result 4): one profile (`msg`, `bytes` at L−1;
`walk`, `b2s`, `b2msg`, `undo` at L−4; `fpwalk` at L−3; `fields` L−7; `coin` L−8; `urec` L−9; the Merkle
components L−10) fits 87 % of the blocks and, with `tiered` as the fallback, proves 40 % fewer cells.
A second new profile adds one point.
Cost: Zig only on the proof side (the Lean theorems hold for any size vector under `SizeOk`, D-045); a
new set of block VKs and leaf circuits, the CUDA arena table, and a GPU timing to confirm that cells
predict time.

### D-056 — CONNECT-RULES step 2: additive Lean statements; six `Compat.lean` pins re-pinned
Date: 2026-11-19 · By: agent (Claude); **to confirm by the owner** · Status: proposed (applied)
Decision: (1) the height-based relative lock is added to Lean beside the existing statements, under new
names (`connectTxL`, `ClaimsLockOK`, `block_factsL`, `epoch_coreL`, `epoch_systems_coreL`): none of the
100 statements of the `Compat.lean` gate changes, and each still holds. The linking lemmas that state the
input relation's tuple or the lookup counts follow the AIR (`int_sum`, `in_match_l`, `coin_row_tok`,
`chk_use_mult`, `coin_r8`, `hashRows`: 216 → 223 sites per row). (2) Six pins of `Compat.lean` are re-pinned without a
proven equality to the old body: `Block.Coin.constraints`, `Block.Coin.lookups`, `Block.Coin.N_MAIN`,
`Block.Fields.constraints`, `Block.Fields.chkLookups`, `Block.Fields.fields`.
Why: the D-045 gate allows a re-pin only with an equality to the old body. An AIR that gains a rule
cannot meet that: its constraint and lookup lists are new. The owner approved the AIR change (D-054,
connect-rules.md: "each of 2–4 changes the block AIRs"). `Compat.lean` now says what changed in the six
(`repin_coin_constraints`, `repin_fields_constraints`: the old list followed by `lockC`, by `rfl`).
Steps 3 and 4 will need the same for `block_walk`, `block_fpwalk` and `block_coin`.
Rejected: changing `connectTx` and `ClaimsOK` in place (it breaks the gate's statements and makes
`epoch_systems_core` need the CSV bit, which the recursion does not provide).
To undo: revert the six hashes; the build then fails on the pins and nothing else.

Confirmed by the owner, 2026-11-20 ("That works."): D-056 is accepted, and the work stays on the branch `connect-rules`.

### D-057 — CONNECT-RULES step 3: a block-only opcode table; the AIR before its Lean soundness; `strict` always on
Date: 2026-11-20 · By: agent (Claude); **confirmed by the owner 2026-11-20** · Status: active (applied on branch `connect-rules`)
Decision: (1) The accurate sigop count needs three more opcode columns. `block_tables` is shared with the
set-pass system, so the block system uses a copy, `block_tablesb` (`Tables.tablesB`), and the set-pass AIRs,
keys and Lean proofs do not change. (2) Step 3's AIRs, witness and tests are committed with the Lean proofs
repaired (every earlier theorem holds, `lake build` passes) but **without** the soundness of the P2SH and
witness parts, which is the next work item; the docs say "enforced and tested, not proven" until it lands.
(3) The AIR applies the P2SH and witness sigop parts to every block (`strict`), where Core exempts block
170,060; the difference can only reject, and matters only for a from-genesis run.
Why: (1) changing the shared table would change the set VK and its proofs for no gain; (2) the soundness
proof is several sessions of work, and the AIR is needed to re-measure sizes (TIERS-2) and to build step 4;
(3) a per-block flag would be one more public input pinned by the leaf.
Rejected: a 17th component for the accurate walk (recursion and GPU plumbing); deriving the three opcode
facts with range lookups in the walker (more columns on the largest of these components).
To undo: (1) point `hashSys` component 5 back at `Tables.tables` after widening it; (3) add a public bit.
Confirmed by the owner, 2026-11-20 ("I'm ok but I want the lean proof asap"): D-057 is accepted. The soundness proof of (2) landed the same day (`block_sigop_cost`, `epoch_systems_coreS`).
Sixteen `Compat.lean` pins re-pinned under D-056.

### D-058 — CONNECT-RULES step 4: the claim's format and place in the public sum; four gate statements change; how to resolve the claims is open
Date: 2026-11-20 · By: agent (Claude); **to confirm by the owner** · Status: proposed (parts 1–2 applied on branch `connect-rules`; part 3 open)
Decision: (1) **Block side as built.** Every in-circuit undo record ends with a 4-byte claimed median time
past (0 when unused; one format, no flag). `block_coin` checks `MTP(h−1) ≥ claim + 512·lock` on every input
whose time lock is enforced, a zero lock included, and adds the claim's fraction to the **same** public
partial sum through a second running sum, under a tuple tagged in slot 19 (`65536`, a value no coin event
has there). The claim's key is the coin's height. Public inputs and recursion circuits do not change.
(2) **Four `Compat.lean` statements change**, the first since the gate exists: `URec.rows_sound` (a record is
4 bytes longer) and `epoch_blocks`, `epoch_systems_core`, `epoch_systems_wf` (the blocks' public sums are
taken net of their claims, `claimSum`). Eight pins are re-pinned under D-056.
(3) **Open: how the claims are resolved** ([connect-rules.md](../design/connect-rules.md) "Step 4").
The resolver proof of D-054's option A is sound only if its list of claims is fixed before the epoch
challenge (its digest in the seed), which the accepted design does not say. Options: R2, that resolver with
the seed change (a new proof system inside the recursion, a path per claim); R5, no resolver: the coin's
event carries `MTP(c − 1)` from its creation, the spend's event carries the claim, and the existing coin
balance forces them equal (changes the event encoding, the set-pass AIR and the set file; `block_anc`
below the CSV height for a run from genesis); D, leave time locks unproven. Agent's recommendation: R5.
Why: (1) keeping the claims in the existing sum avoids a new public input, hence any change to the leaf,
node, root and seal circuits; the tag keeps claims and events apart in one LogUp argument. Enforcing a zero
lock costs one claim and avoids proving in the AIR that the median time past never decreases. (2) The
public sum is no longer the events' sum, so the old statements are false as written; "net of claims" is
what the block systems prove today. (3) is a soundness question and changes what is re-proven, so it is the
owner's.
Rejected: a separate public input for the claims' sum (every recursion circuit would carry it); a claim
only on time-locked records (a flag per record and a variable record length for no measurable saving:
4 bytes on 2.8·10^8 records per 37,500 blocks is about 3 % of the undo stream).
To undo: (1) drop `Coin.timeC`, the seven range lookups and columns 173–192, `URec.MT` and its four reads;
(2) revert the four statements and the eight hashes. Under R5, the fraction of (1) and all of (2) are
undone by the design itself.

Decided by the owner, 2026-11-23 ("Let's do R5"): part (3) is **R5**; parts (1) and (2) are superseded by D-059.

### D-059 — CONNECT-RULES step 4, as built under R5: the coin carries its time; what changes in the gate
Date: 2026-11-23 · By: owner (the choice of R5, D-058) and agent (Claude) (the form below) · Status: applied on branch `connect-rules`; the agent's choices (2)–(5) are **to confirm by the owner**
Decision: (1) **A coin's time** is the median time past of the block before its creating block. It is part
of the coin: 4 bytes little-endian after its `serTxOut`, in the bytes the coin tuple fingerprints, in every
undo record and in the set file's records. A time-based relative lock is checked against the undo record's
time; the existing coin balance makes it the creating block's public previous median time past.
(2) **The tuple keeps its 26 entries.** The time goes into the fingerprint (`EX`: the segment's fingerprint
extended by the four bytes at `γ`) and the length slot (`+ 4`), not into packed limbs as D-058 sketched.
(3) **The set file**: a record's `len` counts the time (`ser = serTxOut ‖ time`, at least 12 bytes). The
file digest and the Merkle leaf cover the record whole; Core's `hash_serialized` stream leaves the time out.
(4) **Below the CSV height the time is 0**, because a block's public previous median time past is 0 there
(D-043 part 3).
(5) **The gate**: `URec.rows_sound`, `epoch_coin_run`, `epoch_blocks`, `epoch_systems_core`,
`epoch_systems_wf` change (a spent value is `(code, coinBytes ser mtp)`; the length bound is `+ 4`; an
initial coin is `RealCoin`); 14 pins re-pinned, 9 added (2,227). The claim sum of D-058 (1), its tuple and
"net of claims" are removed.
Why: (2) fingerprinting `serTxOut ‖ time` needs no range decomposition on input rows (the bytes come from
the committed undo stream), leaves the set-pass record AIR as it is (it already fingerprints `ser` whole)
and keeps the challenge layout, hence the recursion circuits. (3) keeps the leaf "the previous key and the
record as the file has it", so the leaf AIRs and their proofs do not change; only the SHA stream skips 4
bytes. (4) is forced by what the creating block's proof states today.
Limits accepted with this form (to be checked by the owner; both are security statements):
- a proof that starts from a snapshot takes the times of the coins older than its start from the set file,
  and Core's `hash_serialized` does not cover them. R2 would not have had this limit;
- for a run from genesis, time locks on coins created below the CSV height are checked against time 0,
  which differs from Core for spends within about a year after the CSV height, until `block_anc` runs
  below it.
Rejected: three 11-bit parts packed into 16-bit-limb slots (D-058's sketch: three columns and their range
checks on every row, and a change of the tuple in the set pass); leaving the time out of the Merkle leaf
(two record lengths under one relation, or a changed leaf format).
To undo: revert the commit; the proofs of 935,001–972,500 on `main` do not depend on it.

### D-060 — ANC-PRE-CSV: the previous median time past is proven from height 11, keyed on the public height
Date: 2026-11-23 · By: owner ("I'll eventually want to … prove from genesis, so build whatever is needed for that"; "Do 2") and agent (Claude) (the form below) · Status: **accepted** (owner, 2026-11-24: "D060: Ok"); applied on branch `connect-rules`
Decision: (1) `block_anc` proves a block's previous median time past (public inputs 3 and 7) at every
height from 11 on, the first block with 11 predecessors. Before, it did so from the CSV height (419,328)
only (D-043 part 3), so coins created below it carried time 0 (D-059, limit 2).
(2) The component is switched on by the **public height** (input 2), not by the CSV bit (input 5):
`act = ∏_{j<11} (H − j)`, a product over a public input, of degree 0 in the trace. The hash and count
constraints are multiplied by `act`. A new column (125) holds `act⁻¹`; the limbs are 0 unless
`act · inv = 1`, so they are 0 at heights 0–10 and free otherwise. No new public input; the leaf and node
circuits do not change in shape.
(3) At heights 0–10 the limbs stay 0, so a coin created there carries time 0, not Core's median of fewer
than 11 times.
(4) The gate: `Block.Anc.anc_sound`, `Block.block_mtp` and `Block.BlockPubOk.mtp` are restated (cases
`height < 11` and `11 ≤ height`, where they were CSV bit 0 and 1); `Anc.PUB_CSV` unpinned, `act`, `gates`,
`anc` re-pinned, `PUB_H`, `prodH`, `INV` added (2,229 pins).
Why: a run from genesis needs every coin's time bound to the chain; a time lock is at most 65,535 × 512 s
(about 388 days), so the coins that matter are those created in the year before the CSV height. Keying on
the height avoids a 162nd public input and a change of every recursion circuit.
Limit kept (a security statement, to check): coins created at heights 0–10 carry time 0. Core would use
their real median time (January 2009). The first block that can enforce a time lock is 419,328 (2016), so
for those coins every lock is met under both values; the proof does not show this, it follows from the
chain's timestamps.
Cost: every block proof below the CSV height gains a 4,096-row ancestry trace (126 columns), where it had
256 rows. Every block VK changes (as steps 2–4 already require).
Rejected: a new public bit for the activation (changes the public-input count, the leaf circuit and every
VK shape); handling fewer than 11 predecessors in the AIR (a variable-length median for eleven blocks);
switching on at a later height justified by timestamps (a chain fact in the statement for 400,000 blocks
instead of 11).
My first version of (2) was wrong: it forced the limbs to 0 with `∏_{j≠k} (H − j)` terms, which are
nonzero above height 10 too, so every valid block from height 11 was rejected. The Lean soundness proof
passed (it does not prove completeness); the Zig tests caught it.
To undo: revert the commit.

### D-061 — TIERS-2: the `tight` size profile, as built
Date: 2026-11-23 · By: owner (D-055; "Do … 4 as well") and agent (Claude) (the offsets and the rule) · Status: **accepted** (owner, 2026-11-24: "DO61: ok") as the profile for recent blocks; applied on branch `connect-rules`; timed on an H100 on 2026-11-24 (log session 46b)
Decision: a third profile, `tight` (`system.Profile`, value 2): sha at L; msg and bytes at L−1; fpwalk,
b2s, undo, b2msg at L−3; walk at L−4; fields L−7; coin L−8; urec L−9; merkle and wmerkle L−10 (floor 8);
ctx and tables 8; anc 12. L is what `tiered` uses (the largest of sha, msg, bytes, walk). `sizesAuto`
takes `tight` when the block fits it, else `tiered`, else `uniform`.
Measured (`scripts/tier_search.py` on `survey` needs of blocks 935,001–972,500 with this branch's AIRs):
39.1 % fewer proven cells than `tiered` alone; 34,913 of 37,500 blocks fit. A second new profile would add
about five points and is not built.
Format: a forest size key holds L in 6 bits, `tiered` as bit 7 (as before) and `tight` as bit 6; the block
tree's VK gains a third leaf table, encoded only when used.
Measured after (2026-11-24, needs of blocks 0–492,992): `tight` is taken by 1–6 % of the blocks from height
100,000 to 492,992 and saves 0.0 % of their cells; it is a profile for recent blocks.
Open: the offsets come from 37,500 recent blocks. For a run from genesis they should be searched again on
the whole chain (`replay --needs`, added for this); the CUDA arena table has no `tight` row yet; one GPU
timing must confirm that cells predict time.
To undo: remove the enum value; `auto` then chooses as before.
