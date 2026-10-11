# Formalizing our circuits in Lean (resumed 2026-10-10)

Status: in progress · Updated: 2026-10-11

Parked by the owner on 2026-10-08; resumed on the owner's request on 2026-10-10 ("the in-circuit
plain verifier proof"). Steps 1–4 below are done (the glue, `glue-circuits.md`).
**Goal:** everything *we* wrote is proven; only StarkWare-derived software is
trusted. As of 2026-10-08, `src/recursion/plain_verifier.zig` (our in-circuit verifier for
segment proofs) and `src/recursion/node.zig` (link checks, digests, key) are
trusted code ([verification.md](../reference/verification.md)).

## Trust boundary (to confirm with the owner when resuming)

- Trusted: Stwo's protocol soundness and StarkWare's native verifier.
- **stwo-zig is a third-party port** of StarkWare's Rust, byte-parity tested.
  The node circuit uses its in-circuit recursive verifier
  (`stark_verifier.verify`, `CircuitStatement`). Either treat stwo-zig as
  "StarkWare-derived, parity-tested" or extend this work to that verifier.

## Target theorem

circuit satisfied ⇒ our Lean spec of the native Stwo verifier accepts ⇒
*(trusted: Stwo soundness)* ⇒ a trace satisfying the AIR exists ⇒
`header_chain_sound` / `leaf_valid`.

## Plan (cheapest first)

1. **Gate semantics** in Lean: eq, add, sub, mul (QM31), `m31ToU32`, Blake G gate.
2. **Lean-first circuit generators**, as for AIRs: a builder monad emitting gates;
   proofs about the generator for all sizes (never about a 5 M-gate instance).
   Bridge to Zig by circuit hash: the Lean-generated topology must have the same
   circuit hash as the Zig one; the hash is already in the VK, so the bridge is
   sound and cheap.
3. **Quick win:** the node's link checks ≡ `PubLink`, `combine` (Aggregate.lean).
4. **Blake2s gadget ≡ Blake2s** (like the SHA-256 proof).
5. **Lean spec of the native Stwo verifier** for our profile (`proving_5a7c5ed`:
   Blake2sM31 channel, Merkle, OODS, DEEP, FRI, PoW). Its fidelity to StarkWare's
   verifier is checked by differential tests on real proofs (accept/reject).
6. **Circuit ⇒ spec**, hardest last: FRI (circle-to-line first layer, folding,
   last layer), DEEP quotient ordering (including the duplicated sample of
   two-offset columns), Merkle decommitment with mixed column sizes, transcript.
   The composition check reuses `dag_correct`.

**Size:** the largest Lean effort so far, roughly 3–6× the header-chain proof
(several weeks of agent time). Each stage removes code from the trusted list.

## Meanwhile

`REC-FUZZ`: differential fuzzing of the plain verifier against the native one
(mutate real proofs; both must agree). Cheap, and still useful afterwards.

## Resumed 2026-10-10: the plain verifier, our code first

`verifyPlain` (`src/recursion/plain_verifier.zig`) mixes two kinds of code:
- **stwo-zig's in-circuit verifier pieces** (`sv.*`): the channel, FRI commit/decommit, Merkle paths,
  query selection, DEEP quotients (`computeFriInput`), circle arithmetic. These are a parity-tested port
  of StarkWare's; trusted for now, like the native verifier.
- **Our code:** the orchestration (transcript order, statement mixing, the LogUp balance check, the order
  of the DEEP responses, leaf hashing) and `compositionAtOods`: every constraint at the OODS point
  through the exported DAG, the LogUp batches, Horner-combined, divided by the vanishing polynomial.

Order of work (each Lean-first: a program of `Circuit.Op`s, exported, replayed by `glue.zig`, with a
gate-parity test against the hand-written Zig, then proven):
1. **Ops** `zero`, `one`, `inv` (the builder elides gates around variables 0 and 1, so parity needs them).
2. **`compositionAtOods`**: the DAG part (from `dag_correct`), then the LogUp batches. Theorem: the
   circuit's value, in the QM31 field (`Spec/QM31.lean`), is the Horner combination of the constraints
   (evaluated on the OODS samples) and the LogUp terms, times the hook's `1/Z(oods)`.
3. The statement mixing and the LogUp balance check.
4. The DEEP response order and leaf hashing.
5. Then the trust question for `sv.*`.

### Done (2026-10-10): the composition check

- **The program:** `Circuit/Composition.lean` and `Circuit/CompositionLogUp.lean` define
  `compositionAtOods` as a program of ops: the DAG of each component, the constraint Horner, LogUp
  denominators, cumulative sums, the claimed sum's share, and the batches. Hooks: inputs (0), `1/Z(oods)`
  (1), `1/2^L` (2).
- **Proven** (`Circuit/CompositionSound.lean`, standard axioms): `sys_sound`. If the ops hold and
  hook 2 returns `1/2^L`, the result is the Horner combination, with the random coefficient, of every
  component's constraint values (`evalR` at the OODS samples, via `dag_correct`) and LogUp batch terms,
  times hook 1's value.
- **In production:** the leaf replays `airs/composition_leaf.json`, and the hand-written function is the
  reference. Tests:
  - gate-for-gate parity, on the header-chain AIR, the byte LogUp system and the whole leaf circuit;
  - the leaf identity still equals the pinned mainnet VK (segment log 9).

  So the circuits, the VK and existing proofs are unchanged.
- **Trusted for this step:** hooks 1 and 2 (stwo-zig's vanishing inverse, the interned constant), and the
  LogUp batch terms' meaning. That meaning (the native verifier's LogUp constraint) is `LogUp.lean`'s
  `logup_sum`; linking `batchTerm` to it is the next sub-step.

### Done (2026-10-10): the LogUp balance check

`Circuit/Balance.lean`: `balanceProg` (zero, the claimed sums, per public entry its denominator,
multiplicity, inverse, product), `balance_sound`. If the ops hold, the claimed sums plus the entries'
fractions are zero over QM31, every entry's denominator nonzero. The leaf replays
`airs/balance_leaf.json`; the leaf circuit stays gate-identical and the mainnet VK unchanged.

**Open note:** `LogUp.lean`'s prose writes the denominator `z − combine`; the circuit and native code use
`combine − z`. The proofs are each internally consistent, and real proofs verify; align the prose (or
restate `logup_sum`) when linking `batchTerm` to it.

### Done (2026-10-10): the statement mixing

`Circuit/Statement.lean`:
- **`statement_sound`** (full form): given the log size and the AIR digests as constants, the words the
  transcript absorbs are exactly the native statement encoding;
- **production form** (`partOpsH`): the header constants come from hook 4, because the AIR digests are
  computed in Zig. **`pub_mixed`**: each public input enters the transcript as its exact M31 value, in
  order; that is the binding of the public inputs to the proof.

The leaf replays `airs/statement_leaf.json`; it is gate-identical, and the mainnet VK is unchanged.

**What of `verifyPlain` is now Lean-generated and proven:** the statement mixing (public inputs), the LogUp
balance check, and the composition check. Still hand-written: the order of the transcript's other calls,
the DEEP response list, and leaf hashing for the Merkle decommitment (calls into stwo-zig).

### Done (2026-10-10): Merkle leaf hashing

`Circuit/LeafHash.lean`: `leafHash` (each value through `m31_to_u32`, then the proven Blake2s gadget) and
`leaf_sound`: the leaf the circuit checks against each Merkle path is `blake2sWords` of the row's values
as u32 words, matching the Blake2sM31 hasher's leaf (trusted correspondence with stwo's native hasher).
The leaf replays `airs/leafhash_{104,434,12,8}.json` (its four trees' widths). Tests: direct parity at
widths 8 and 434; the whole leaf circuit is gate-identical; the mainnet VK is unchanged.

### Done (2026-10-10): the DEEP response list

`Circuit/Deep.lean`: `samples` labels the mixed OODS values (tree, column, offset) in mixing order;
`deepList` is the response table in stwo's order (a two-sample column preceded by its periodicity
sample). `deep_sound`: every response's value index points at the mixed sample with the response's
label. `deep_complete`: every mixed sample is used. The leaf replays `airs/deep_leaf.json`
(`PlainStatement.deep`): each response's value is the very variable that was mixed, and its point is
the OODS point shifted by its offset (looked up from the points computed for that tree; an unknown
offset is rejected). The order itself is stwo's, checked by verifying real proofs.

### Done (2026-10-10): step 5, the channel, the Merkle paths, the transcript order

Owner decision (2026-10-10): prove the channel transcript and the Merkle path; state FRI soundness as
an assumption.

- **Merkle paths** (`Circuit/Merkle.lean`): `merkleNode` (stwo-zig's cond-flip, then the proven Blake2s
  of `left ‖ right`), the path fold and the root check. `path_check_sound`: with Boolean bits, the
  committed root is `specRoot`, the Blake2s Merkle root of the leaf along the authentication path.
  The leaf replays the level program (`airs/merkle_node.json`) for the trace trees. The level loop and
  the final word-by-word equality in `merklePathVia` mirror `path`/`pathCheck` (a few lines of Zig).
- **The channel** (`Circuit/Channel.lean`): a spec of `Blake2sM31Channel` (`Spec.mixU32s`,
  `mixCommitment`, `mixQm31s`, `drawTwo`, `powMix`) and the circuit programs. `absorb_sound`: unpacking
  QM31 inputs to words, Blake2s, `reduceHashValue` give the spec digest; per operation
  `mixU32s_sound`, `mixQm31s_sound`, `draw_sound`, `drawQm31_sound`, `drawPoint_sound` (the point is
  `((1 − t²)/(1 + t²), 2t/(1 + t²))`, `1 + t² ≠ 0`), `powMix_sound`. The leaf drives stwo-zig's channel
  state with these programs (`LeanChannel`) for every top-level call: commitments, the statement, the
  lookup elements, the claimed sums, the coefficient, the OODS point, the samples (3757 values), the
  DEEP coefficient, the digest update after the proof of work.
- **The transcript order** (`Circuit/Transcript.lean`): the event list and the Fiat–Shamir property
  (`elements_bound`, `coeff_bound`, `oods_bound`, `quotient_bound`, `queries_bound`: each challenge
  is drawn after everything it must bind). `verifyPlain` steps through the exported list next to each
  channel event and refuses to build the circuit if its order differs (`TranscriptCheck`).
- **New ops:** `pmul` (`pointwiseMul`) and `unused` (`markAsUnused`).
- **Tests:** per-operation channel parity with stwo-zig (same gates, same digests and draws), including
  the 3757-value mix; Merkle path parity (honest and tampered root); the transcript check (a swapped
  order is refused); whole-leaf parity; the mainnet VK unchanged; leaf proving.
- **Fix found on the way:** `glue.parse` counted a constant's coordinates as registers, so a program
  with a large constant (the balance multiplicity, the unit-vector inverses) allocated ~2^31
  registers per run. Registers now come from register fields only; the leaf tests' peak memory went
  from 14 GB to 6 GB.

**Not proven (stays stwo-zig's or ours, stated):**
- ~~The proof-of-work check~~ (done 2026-10-11, VL-POW, below).
- **FRI and query selection** (`friCommit`, `friDecommit`, `mixFriConfig`,
  `getQuerySelectionInputFromChannel`, `selectQueries`), the DEEP quotients, circle points. Their
  channel calls and the FRI layers' Merkle paths use the same primitives as above (gate-identical at the
  tested sizes), but they run inside stwo-zig.
- ~~The shifted OODS points~~ (done 2026-10-11, VL-OODS, below).

### Done (2026-10-11): the proof-of-work check (VL-POW)

`Circuit/Pow.lean`: `powCheckP` emits stwo-zig's `Channel.pow` check call for call (the prefixed hash,
the nonce mask, the hash with the nonce, `extract_bits` over 31 bits with `validate_extract_bits`, the
low `n_bits` equal to zero), with constants created where the Zig creates them (the builder interns
constants by first use). New op `guess` (unconstrained) and hints `lsb`, `inv_or_zero` (`glue.zig`).
`powCheck_sound`: if its ops hold and `n_bits ≤ 30`, `Spec.powOk`: the nonce's coordinates 2, 3 are zero
and limb 0 of `blake2s_m31(blake2s_m31(0x12345678 ‖ digest ‖ n_bits) ‖ nonce)` is divisible by
`2^n_bits` (the 31-bit decomposition is unique: `1…1` is excluded as the encoding of 0). Exported for
`n_bits` 0, 4 and 26 (`airs/channel_pow_check_*.json`); `LeanChannel.pow` uses the program when one
matches, else stwo-zig's. Tests: gate parity and equal verdicts with stwo-zig's `pow` (valid at 0 and
4 bits with a ground nonce, invalid with a nonzero high coordinate, a wrong nonce, or 26 bits with a
random nonce); the leaf's identity is still the pinned mainnet VK.

### Done (2026-10-11): the shifted OODS points (VL-OODS)

`Circuit/Oods.lean`: the M31 circle group (`cpAdd`, `cpMul` by doubling), stwo's generator
`(2, 1268011823)`, `traceGen L` (`= gen · 2^(31−L)`), `shiftPt L off` (`mulSigned`); `#guard`s check the
generator's order is exactly `2^31` and `traceGen L`'s divides `2^L` (`L ≤ 20`). `shiftP`: the
Lean-computed constants `shiftPt L off`, then `addPoints`'s six gates; `shift_sound`: the result is
the circle sum of the OODS point and `shiftPt L off` over QM31. `airs/oods_shift_leaf.json`: one program
per log size 8–24 and per offset of the header-chain leaf's components (and −1). `verifyPlain` uses a
table entry when there is one (`shiftPoint`), else stwo-zig's `mulSigned` and `addPoints`. Test: every
entry's constants equal stwo-zig's `mulSigned` and its gates and values equal `addPoints`'.

### Assumption: STARK (FRI) soundness

Stated, not proven. For the leaf's parameters (Blake2s Merkle commitments, the configured blowup, query
count and proof-of-work bits): if the circuit built by `verifyPlain` is satisfied, then except with
probability at most the configuration's soundness error (in the random-oracle model for Blake2s),
the committed traces are close to polynomials of the claimed degree whose values at the OODS point are
the mixed samples. Everything Lean-proven above (composition, LogUp balance, statement, DEEP responses,
leaf hashes, Merkle paths, channel, transcript order) is what turns that into "the AIR constraints and
the lookup balance hold on the committed traces for the stated public inputs".

### Done (2026-10-11): the end-to-end theorem (VL-E2E)

`Circuit/EndToEnd.lean`, standard axioms:
- **`plain_sound`** (any system of components with lookups, one trace size): if the composition program
  and the balance program hold, the public-input registers hold `pub`, and the composition value equals
  the sampled composition value `C`, then under `StarkSound` there are main columns on which every
  component's AIR holds (`Air.Satisfied`); and if `(α, z)` is good for those traces' entries
  (`SZGood`), the system balances with the public entries: `sys.SatisfiedExt`.
- **`plain_leaf_valid`**: for the (headers, tree) system with the root entry `node(L − 8, 0, pubT)`,
  the leaf's public inputs are proven: `PubValidT pub`, the leaf guarantee the aggregation composes.
- **`sz_good_bound`**: `SZGood` fails on at most `(N²·W + 2N)·|QM31|` pairs (`logup_sz`).

The steps, all proven: `partTerms_eq` (the composition's terms are the components' constraint and
batch terms, `terms`, at the OODS valuation), `evalR_row` and `row_batch` (the same terms at a row are
the trace's values), `comp_frac_sum` (vanishing batch terms with nonzero denominators give
`Σ fractions = claimed`: `logup_sum` plus the batch pairing), `fracSum_sites` and `fingerprint_poly`
(the circuit's fingerprints are the entries' tuple polynomials), `fracSum_ext` and `balance_sound`
(all fractions sum to zero), then `logup_sz`'s conclusion and `balancedExt_of_poly`.

**Named hypotheses (not proven):**
- `StarkSound`, the row form of the assumption above: if the Horner combination of `terms` at the OODS
  samples, times `1/Z(oods)`, equals `C`, then base-field main and interaction columns exist on which
  every term vanishes at every row. Its premises' plumbing (DEEP responses, Merkle leaves and paths,
  channel, transcript order) is the proven part of step 5; FRI itself is VL-FRI.
- `SZGood` at the circuit's `(α, z)`. Its probabilistic reading needs the extracted columns to be the
  committed ones (fixed before `(α, z)`, `elements_bound`); the theorem is stated for the columns
  `StarkSound` returns.
- **Wiring facts** of `verifyPlain` (hand-written Zig, stated as hypotheses): the components in order
  match the system, each has lookups; the claimed sums enter the balance check in component order; the
  public-input registers are base-field values `pub`; the public entries' value registers are base
  (and for the header leaf, the one entry is `node(L − 8, 0, pubT)` with multiplicity −1); hook 2 is
  `1/2^L`; the composition value is compared with the sampled `C`; one trace size for all components
  (true until `LIFT`).
