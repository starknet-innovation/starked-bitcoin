# Recursion and aggregation (M2) — design

Status: draft · Updated: 2026-10-07

How segment proofs become one proof for the whole chain. This note records the
options surveyed and the chosen architecture (decision D-023). Progress is
tracked in [project/roadmap.md](../project/roadmap.md) (`RECURSION`, `AGG`).

## What already exists (checked in source, 2026-10-07)

stwo-zig PR #204 is in our pinned submodule (`third_party/stwo-zig` @
`4afa09d`). It is a byte-parity port of StarkWare's circuit recursion
(`starkware-libs/proving` @ `5a7c5ed`):

| Piece | Path (in `third_party/stwo-zig`) |
|---|---|
| Gate-circuit builder (QM31 ops, Blake2s G-gates, M31/U32) | `src/frontends/circuit/builder/` |
| In-circuit Stwo verifier (channel, merkle, fri, oods, constraint_eval, logup, verify) | `src/frontends/circuit/stark_verifier/` |
| Generic statement interface (`preprocessedRoot`, `componentLogSizes`, `evaluateComponent`, `publicLogupSum`, …) | `src/frontends/circuit/stark_verifier/verify.zig` |
| k-to-1 fold circuit | `src/frontends/circuit/statements/multiverifier.zig` |
| Leaf-wrap / fold / tree drivers | `src/integrations/circuit_cpu/recursion/` |
| Protocol revisions (`stwo_7b211ed` vs `proving_5a7c5ed`) | `src/core/protocol_revision.zig` |
| Design doc | `design/starknet-proving-pipeline/recursion/02-design.md` |

UNVERIFIED (from the PR #223 description, not reproduced): leaf-wrapping one
Cairo proof takes about 13 s and about 40 GB peak; one fold about 8 s and
about 14 GB. The Cairo `stwo_circuit_verifier` on the root is about 9.7 M
Cairo steps.

## Options

1. **Native circuit recursion (chosen).**
   - Re-prove segments on the `proving_5a7c5ed` profile (Blake2sM31 channel,
     unprefixed Blake2s Merkle, `PcsConfigV2`).
   - Write a `BitcoinSegmentStatement` whose `evaluateComponent` evaluates our
     IR through the circuit builder.
   - Leaf-wrap each segment proof, then fold with the existing tree.
   - Segment chaining (outputs of segment k = inputs of segment k+1) is
     checked in the aggregation layer.
   - No Cairo anywhere.
2. **Cairo verifier route** (Raito-style, as a tree): implement the `Air`
   trait for our IR in Cairo (`stwo_cairo_verifier`) and prove its execution
   with stwo-cairo, then fold. This is the most production-proven route, but
   it costs millions of Cairo steps and a full Cairo proof per segment, and it
   cuts against D-003 (native AIRs).
3. **Bespoke native recursion AIR** (like stwo-zig's RISC-V lane). This is
   the most work, nothing is reusable, and it brings a new soundness-audit
   burden.

## Why option 1

- It is consistent with D-003 (native AIRs) and D-008 (generic machinery
  comes from stwo-zig; Bitcoin-specific code stays here).
- The recursive verifier is StarkWare's design, ported at byte parity, so we
  inherit its correctness work rather than writing a verifier.
- Our constraint evaluation in-circuit is about 14k QM31 gates, which is
  negligible next to the verifier's Blake2s work.
- An optional final step, the Cairo `stwo_circuit_verifier` on the root,
  keeps Starknet settlement open.

## Blocker found 2026-10-07: mask offsets (Q-MASK)

The in-circuit verifier samples **one** OODS value per trace column (offset 0),
plus the previous row for LogUp cumulative-sum columns only.
- `stark_verifier/proof.zig`: `trace_at_oods` has one value per column;
  `at_prev` exists only for interaction columns.
- `oods.zig`: the sample points are the OODS point and its previous row.

That matches StarkWare's AIR style: row-local constraints, rows linked by
LogUp. Our AIRs read columns at many row offsets (−399..+7, 2,514
column/offset pairs in `header_chain_v6`), so our proofs cannot be checked by
the verifier as-is. Options:

| | Option | Keeps our AIR and Lean proofs | Trust impact | Work |
|---|---|---|---|---|
| A | Rewrite the AIRs row-locally, linking rows with LogUp (StarkWare's framework shape) | No: AIRs and proofs are redone, and LogUp soundness must be formalised (StarkWare's `tuple_inclusion` is a starting point) | None: unmodified verifier | Very large |
| B | Extend the in-circuit verifier to multi-offset masks: a sample point per (column, offset) and a matching quotient batching, mirroring the native verifier that already accepts our proofs | Yes | The extension is new verifier code with no Rust parity oracle. Mitigation: differential testing against the native verifier, plus adversarial tests | Medium (generic, belongs in a stwo-zig fork per D-008) |
| C | Verify the native proof some other way (Cairo `stwo_cairo_verifier` with a custom `Air`, or a zkVM) | Yes, if that verifier supports masks (UNVERIFIED for Cairo) | Cairo-verifier trust | Large, and against D-003 |

Recommendation: **B**. Our strongest asset is the formally verified AIR, and B
keeps it. The circuit cost of about 2.5k extra OODS samples is small next to
the verifier's Blake2s work (INFERRED).

## Status of the plain path (2026-10-07)

`src/recursion/plain_verifier.zig` is a parallel in-circuit verifier built only
from stwo-zig's public circuit pieces; the byte-parity path is untouched. It
replays `prove_rec`'s native transcript, samples each main column at its
offsets, emits the DEEP responses in native order (including the duplicated
sample of two-offset columns), checks the composition through the AIR's
exported DAG, and decommits three trees.
- **Test:** a mainnet header-chain segment (2¹² rows) proven with `prove_rec`
  is accepted (value mode, `isCircuitValid`). The circuit is rejected after
  tampering with a public input, an OODS sample, a decommitted value, a FRI
  coset value or the composition root, and accepted again once restored.
- **Size:** about 5.1 M circuit variables for a 2¹² segment.
- **Validation:** every value the circuit checks comes from the native
  verifier's capture of the same proof, so native and circuit agree on
  acceptance (UNVERIFIED in general; differential fuzzing is a follow-up).

## Aggregation as built (2026-10-08, D-025)

- **Leaf** (`src/recursion/leaf.zig`): the plain verifier checks one segment
  proof in-circuit; the circuit outputs `Blake2s(0⁸ ‖ pubs)` (108 public
  inputs as u32 words, `guessM31` so the encoding is injective).
- **Node** (`src/recursion/node.zig`): verifies two child circuit proofs with
  stwo-zig's `CircuitStatement` + `verify`, after recomputing each child's
  digest from a guessed key and public inputs. It checks `PubLink` (the Lean
  definition, line by line: input state of the right child = output state of
  the left; heights +1 via 16-bit limbs and a carry bit, range-checked as
  `m31ToU32(x) = x`). Output: `Blake2s(K ‖ combine(pL, pR))` with
  `K = Blake2s(hL ‖ kL ‖ hR ‖ kR)`.
- **Shape:** leaves of every size and the node are padded to one target
  (fixpoint as upstream's `sharedTargetFixpoint`), so one node circuit
  verifies leaves and nodes. A leaf's circuit hash depends only on its log
  size (tested); the node's identity is derived from topology (tested).
- **Tree:** layers pair left to right; an unpaired last entry is carried up.
- **Outer verifier** (`verifyRoot`): native circuit-proof verification; the
  root's preprocessed root must be the node circuit's; the output must equal
  `Blake2s(K_expected ‖ P)`, with `K_expected` recomputed from the leaf circuit
  hashes and the node hash; `P`'s input state must be genesis. Then
  `chain_from_genesis` (Lean) gives a valid chain from genesis to `P`'s tip.
- **Lean:** `leaf_valid`, `pub_compose`, `chain_from_genesis`
  (`Gadgets/Aggregate.lean`), standard axioms only. The node circuit's code is
  trusted to implement `PubLink`/`combine` (verification.md).
- **Measured** (M4 Pro, CPU, 70 queries, 26-bit PoW): leaf of a 2²⁰ segment
  (4,096 headers) 31–33 s padded to the shared shape, plus 33 s for the segment
  proofs; node 24 s; root proof 0.98 MB, verified in 0.22 s; peak RSS 13.3 GB
  for a 2-leaf tree.

## Open questions

- **Q-CHAIN:** resolved (D-025): chaining is checked inside every node.
- **Q-REGISTRY:** resolved: our own shape (leaf + node fixpoint), not the
  Cairo-sized registry.
- **Q-MEM:** resolved for now: 13.3 GB peak at 2²⁰ leaves on the 24 GB laptop.
- **What is proven and what is trusted** (decided 2026-10-07):
  - The composition (segments → chain) is a pure Lean theorem, **proven**:
    `segment_compose` (`Spec/Compose.lean`). The aggregator only has to check
    `Link`: prev-hash = tip, height + 1, nBits, time, period start and work.
    The window obligation of `header_chain_sound` is discharged by linking:
    take segment 2's real window to be segment 1's history; the public window
    inputs then match. Only the genesis segment's inputs must equal fixed
    constants (sentinel window, zero work).
  - Our in-circuit statement must provably evaluate our IR (`REC-STMT-EQ`).
  - The recursive verifier circuit itself is trusted, in the same class as
    Stwo: it is not formally verified anywhere as of 2026-10-07. See
    [reference/verification.md](../reference/verification.md).

## Plan

1. `REC-PROFILE`: prove and verify a segment on `proving_5a7c5ed` natively.
2. `REC-SMOKE`: port StarkWare's `simple_statement` (custom-AIR example) to
   Zig and verify it in-circuit, which exercises the extension point.
3. `REC-LEAF`: `BitcoinSegmentStatement` (IR → builder), then leaf-wrap one
   segment proof.
4. `REC-FOLD`: fold two leaves and measure time and memory.
5. `AGG`: the chaining aggregator, then the whole chain to one root.
