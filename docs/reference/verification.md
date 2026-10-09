# What is proven, what is trusted

Status: current · Updated: 2026-10-07

This is the project's assurance ledger. **Update it in the same commit as
any change to a theorem, an AIR or the trust base.** A claim about what the
system guarantees that doesn't appear here is not a claim the project makes.

> Formal statements are summarized informally here. The Lean theorem is
> authoritative. Have security-relevant claims reviewed before relying on
> them externally.

## Proven in Lean (standard axioms only)

**Headline:** `HeaderChain.header_chain_sound` (`Gadgets/TopSound.lean`). A
satisfying trace proves `SegmentValid` (`Spec/Chain.lean`), the whole
segment's validity under Core's mainnet header rules, from decoded public
inputs to decoded public outputs. The rows below are the per-rule theorems it
is built from.

| Property | Theorem | AIR version |
|---|---|---|
| SHA-256 compression = FIPS 180-4 | `Sha256.compress_sound_air` | sha256_compress v1 |
| Blake2s compression = RFC 7693 `F` (message limbs 16-bit) | `Blake2s.compress_sound_air` | blake2s_compress v1 |
| Header hash = SHA256d(header) | `HeaderChain.chain_sound` | header_chain v1+ |
| prev-hash linkage; first prev-hash and tip hash = public inputs | `chain_sound` | v1+ |
| Proof of work (Core `CheckProofOfWork`, mainnet; target ≤ powLimit) | `chain_sound_v2`, `header_pow` | v2+ |
| Height counter, nBits constant inside a period, period-start time | `state_sound` | v3a+ |
| Difficulty retarget at positive multiples of 2016 (Core `GetNextWorkRequired`, mainnet, including the powLimit cap) | `retarget_sound` | v3b |
| Exact chainwork: per-header `q = GetBlockProof(nBits)`; `W_j = W_{j−1} + q_j`; last `W` public | `work_q`, `work_step`, `work_out` | v5 |
| Minimum block version (Core "bad-version", BIP34/66/65 heights) | `version_sound` | v6 |
| Median time past: ≥ 6 of the 11 window times are below the header's time; the window shifts along the chain and is public at segment ends; equals Core's `GetMedianTimePast` rule given the window form | `mtp_count`, `mtp_window`, `mtp_out`, `mtp_core` (with `mtpOk_iff_count`, `sentinel_sound`) | v4 |
| Aggregation at the public-input level: every header-chain trace yields proven public inputs; a node over two proven children passing `PubLink` yields proven combined inputs; proven inputs with genesis input state give a valid chain from genesis to the decoded tip | `leaf_valid`, `pub_compose`, `chain_from_genesis` (`Gadgets/Aggregate.lean`) | v6, node circuit (D-025) |
| Header tree: a (headers, tree) system with `2^L` rows balancing with the entry `node(L−8, 0, x)` has `x` = limbs of the perfect Blake2s tree root over the segment's block hashes | `tree_root_limbs`, `tree_root_sound` (`Gadgets/HeaderTreeSound.lean`) | header_chain_v7 + blake2s_tree |
| Aggregation with the tree: as above, plus a binary tree over the same headers' block hashes, in height order, whose root's limbs are public inputs 108–123 | `leaf_valid_T`, `pub_compose_T` (given `NodeOut`), `chain_from_genesis_T` (`Gadgets/AggregateTree.lean`) | v7 system, node circuit with `treeNode` |
| Glue circuits: the in-circuit Blake2s gadget computes Blake2s; the node program enforces `PubLink` and `NodeOut` and computes the digests and key; with valid children the node's inputs are valid | `blake2s_sound`, `pubsDigest_sound`, `link_sound`, `treeNode_sound`, `node_sound`, `node_compose`, `node_digest`, `node_key`, `node_child_digests`, `leaf_digest` (`Circuit/*.lean`) | node_glue, leaf_glue |
| Block bytes and fields (M3a.1–2): the byte table holds the block (`r < LEN`, bytes < 256); a satisfied, balanced (bytes, fields) system's block bytes parse (Core's deserializer, all bytes consumed) | `bytes_rows`, `read_byte` (`Block/Bytes.lean`); `toksBlock_parse` (`Spec/BlockTokens.lean`); `fields_sound` (`Block/FieldsSound.lean`) | block_bytes, block_fields |
| Lookups: balance ⇒ every used tuple is in the table (fewer than `P` uses); LogUp formula ⇒ the fractions sum to the claimed sum; toy byte range check | `used_in_table` (`Lookup.lean`), `logup_sum` (`LogUp.lean`), `user_bytes` (`Testing/ByteLookup.lean`) | IR v2 |

## Coverage audit against Bitcoin Core (2026-10-07)

Bitcoin Core `master`, fetched 2026-10-07:
- `CheckBlockHeader` (`validation.cpp`) checks `CheckProofOfWork` →
  covered (`powOk`; `DeriveTarget` rejects negative, zero, overflow and
  `> powLimit`).
- `ContextualCheckBlockHeader` checks, in order:
  - `bad-diffbits` (`GetNextWorkRequired`, `pow.cpp`): mainnet has
    `fPowAllowMinDifficultyBlocks = false` and `enforce_BIP94 = false` →
    covered (continuity plus `nextWork`);
  - `time-too-old` (MTP) → covered;
  - `time-timewarp-attack` (BIP94) → testnet4/regtest only, not mainnet;
  - `time-too-new` → out of scope (wall-clock time);
  - `bad-version` → covered (v6).
- `AcceptBlockHeader` adds only `duplicate-invalid`, `prev-blk-not-found`
  and `bad-prevblk` (chain structure, covered by linkage plus validity of
  every earlier header in the chain), and `too-little-chainwork` (anti-DoS,
  not validity).
- `GetBlockProof` / `GetBitsProof` (`chain.cpp`): `(~T / (T+1)) + 1`, or 0 for
  a negative, overflowing or zero target → matches `blockProof`.

Result: `SegmentValid` covers every mainnet header-validity rule except
`time-too-new`.

## Not yet constrained (header chain)

- Wall-clock time: `time ≤ now + 2h` is out of scope by design.
- Version-bit signalling (BIP9) does not affect header validity. (The
  minimum-version rule does, and is enforced; see the table above.)
- Testnet and regtest rules: the specs are mainnet only.

**Aggregation soundness (spec level):** `segment_compose` (`Spec/Compose.lean`).
Two valid segments, the second starting where the first ends (`Link`), form
one valid segment. By induction, any number of linked segments from genesis
form a valid chain.

**Independent check:** Z3 witness-uniqueness on four gadget windows (MTP flag,
height decomposition, retarget clamp, PoW one-hot). See the
[Z3 report](../reports/2026-10-07-z3-uniqueness.md).

## Trusted, not proven

| Assumption | Mitigation |
|---|---|
| Stwo protocol soundness (circle FRI, Fiat–Shamir, Blake2s channel) | Upstream; out of scope |
| stwo-zig implements Stwo correctly | Upstream tests. We pin the preprocessed root ourselves (stwo-zig#225). |
| The Zig interpreter matches Lean `Expr.eval` | Differential test against `probe_oracle` (`src/air/interp.zig`). Since 2026-10-10 every exported AIR also re-serializes byte-identically after parsing, so the digest the verifiers mix is SHA-256 of Lean's exact text (`ir.zig` test). |
| The JSON exporter is a faithful printer | **Mostly proven (2026-10-07):** the node array it prints is `Air.toDag`, and `dag_correct` (`Dag.lean`) proves that it evaluates, in any commutative ring, to each constraint (`Expr.evalR`; `eval_eq_evalR` links this to `Expr.eval`). What remains trusted is the 7-case `nodeJson` string printer and the Zig JSON parser. Drift check in [status.md](../project/status.md). |
| Committed `airs/*.json` equals the current Lean definitions | Drift check (regenerate and `cmp`) |
| The specs in `Spec/*.lean` match Bitcoin Core | `#guard`s on real mainnet values, and Zig tests on mainnet headers. Not proven against Core's C++. **Differentially fuzzed against Core's own code (2026-10-10, `tools/specfuzz`, Core c067aa71):** `SetCompact` (validity and value), `GetCompact`, `CalculateNextWorkRequired` (mainnet domain: previous target ≤ powLimit), `GetBlockProof`, `CheckProofOfWorkImpl` (incl. hashes at target ± 2), `GetMedianTimePast`: 600,000 cases, 0 mismatches. Outside the mainnet domain the retarget diverges only where Core's 256-bit arithmetic wraps (checked case by case); the chain never reaches it, since the previous nBits passed `powOk`. Mainnet constants checked against `chainparams.cpp`. **Block spec too (2026-10-10, `core_block_cases.cpp`):** `CScript::GetSigOpCount(false)`, `ComputeMerkleRoot` with the mutation flag, `CheckTransaction` on Core-serialized transactions (every reason except vin-empty and oversize occurs) and txid/wtxid: 100,000 cases, 0 mismatches (with 150,000 more header cases). Not fuzzed against Core: the version rule, `CheckBlock`/`ContextualCheckBlock` as wholes (they need `ChainstateManager`/`validation.cpp`). |
| Lean kernel, Mathlib, toolchain | Pinned versions |
| LogUp soundness: fractions summing to zero for random `(z, α)` ⇒ the relations balance (Schwartz–Zippel over QM31) | **Proven (2026-10-10, `LogUpSZ.lean`):** outside a set of at most `(N²·L + 2N)·|K|` challenge pairs (`N` distinct tuples, length `< L`), denominators are nonzero and a zero sum gives `BalancedExt` (`logup_sz`, `balancedExt_of_poly`), for relations of one arity and ids below `P`. With `N ≤ 2^26`, `L ≤ 32` over QM31 (`|K| ≈ 2^124`) that is below `2^-66` per proof. Still trusted: that the committed batch fractions are the entries' fractions (Stwo's encoding; tested) and that Fiat–Shamir gives `(α, z)` as if uniform (random-oracle model). The arity and id side conditions are discharged by `decide` for the header-tree, block-fields and block-hash systems (`LogUpSZSystems.lean`); public entries must have their relation's arity (one entry, checked by the verifier's construction). |
| Our LogUp code (`component.zig`, `system.zig`, the plain verifier's LogUp) implements the formula of `logup_sum` | Tested: honest system proofs verify natively and in-circuit; out-of-range values, forged sums and tampered samples are rejected. Not proven (VERIFIER-LEAN, parked). |
| **(M2)** Our plain in-circuit verifier path (`src/recursion/plain_verifier.zig`, D-024) correctly verifies our proofs | New code with no Rust parity oracle. Built from stwo-zig's audited-by-parity pieces; tested to accept honest proofs. **REC-FUZZ (2026-10-10, `src/recursion/fuzz.zig`):** every guessed proof value (roots, OODS samples, claimed sums, decommitted values, auth paths, FRI commitments, coefficients and witnesses, PoW nonce; M31 wrappers also out of range) and every statement input is mutated one at a time on a header-chain and a LogUp-system proof, and each mutation must be rejected by the circuit. Still to do: a differential oracle with the native verifier on the same mutations, and review. |
| **(M2, planned)** The recursive verifier circuit: stwo-zig's port of StarkWare's circuit recursion (PR #204) correctly implements Stwo verification in-circuit | Not formally verified anywhere, as of 2026-10-07; stwo-zig's Lean work is RISC-V-only. Byte-parity tests against StarkWare's Rust; audit; independent native check of the final root. The composition (`REC-COMPOSE`) and our in-circuit statement (`REC-STMT-EQ`) are to be proven in Lean. |
| **(M2, mostly proven 2026-10-08)** The node and leaf glue (`PubLink`, `combine`, the tree root, digests, key) | **Proven** from the gate semantics: `node_sound`, `node_compose`, `node_*digest*`, `node_key`, `leaf_digest` ([glue-circuits.md](../design/glue-circuits.md)). Still trusted: gate semantics (`Op.holds` = what the circuit AIR enforces), constant finalization, the replay (`glue.zig`, parity-tested against the previous builders), word- vs byte-level Blake2s (`#guard`s at 64/128/528 bytes), and the verifier hooks. |
| **(HC-HASHTREE)** The fold shape: the prover (`store.Prover`, `HT.pushPeak`/`bagPeaks`) and the verifier's expected key (`store.verifyChain`, `expectedRoot`) fold the segment plan the same way, and the plan is aligned (`HT.validPlan`), so the tree is the canonical MMR | Shared code; tested (aligned segment folds equal `mmrRoot` for several cuts and after extension). Lean's `PubValidT` leaves the shape existential. **Proven in Lean (2026-10-10, `Spec/Mmr.lean`):** for the canonical MMR, a verified path at height `h` gives `leaves[h]` unless Blake2s collides (`mmr_inclusion`); Zig's `inclusionSides` matches Lean's on all `n ≤ 64`; and folding an aligned plan with the push-and-merge stack gives `mmr` (`fold_eq_mmr`). Still trusted: that the Zig fold and key computation are this model, and that the key binds the shape (Blake2s). |
| **Root verifier obligation:** the root proof's preprocessed root is the node circuit's and its request (PCS config, preprocessed columns) is the pinned one; its output digest equals `Blake2s(K ‖ P)` with `K` recomputed from the tree shape and the known leaf/node circuit hashes, and `P`'s input state is genesis (prev-hash 0, height 0, sentinel window, work 0) | Checked by the outer verifier (`node.verifyRoot`, `store.verifyChain`). **Since 2026-10-10:** the request is pinned (`ConfigNotPinned` otherwise; review finding 2); the genesis-state checks are the Lean-exported `airs/genesis_checks.json`, proven to give `chain_from_genesis_T`'s hypotheses (`chain_from_genesis_checked`); leaf 0 of `T` must be Bitcoin's genesis hash (leftmost path). The verifier must still compare the chainwork with a trusted minimum. |

## Known completeness gaps

These are deliberate: valid blocks that cannot be proven, not invalid blocks
that can.

- nBits with `nSize < 3` (targets < 2²⁴) cannot be laid out by the PoW
  gadget. No real block can meet such a target.
- A retarget whose previous exponent is outside 3..29 is rejected by the
  witness (`UnsupportedTargetEncoding`). This doesn't occur on mainnet.
- A header whose target is below 2^128 (exponent `s < 16`) cannot be proven
  (D-021). Mainnet targets have `s ≥ 20`; `s < 16` needs about 2^128 hashes.
- At heights below 11, a header with time 0 cannot be proven: the zero
  sentinels are not below 0. Core would reject it anyway, because the
  genesis time is above 0.

## Cross-gadget dependencies

These are soundness couplings. Re-check them whenever either side changes.

- `mtp_window` takes `T_1` from the row-220 copy of the predecessor's time
  (`copy_facts`), which the retarget also uses. Changing that copy affects both.
- `retarget_sound` relies on the PoW row: it uses `header_pow_ex` for
  `s ≤ 26` and `s = 26 → mant < 2^16`. Without those, the division branch
  could claim a target above powLimit.
