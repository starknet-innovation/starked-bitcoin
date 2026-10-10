# Formalizing our circuits in Lean (resumed 2026-10-10)

Status: in progress · Updated: 2026-10-10

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
