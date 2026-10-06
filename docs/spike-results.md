# Spike: Lean-first single source of truth — results (2026-10-06)

**Verdict: go.** The full loop works end to end on a gadget that has the
SHA-256 AIR's building blocks:

```
Lean definition ──► Lean soundness proof (standard axioms only)
      │
      └─► lake exe export-air ──► airs/add32_chain.json (starked-air-v0)
                                        │
                Zig: parse → interpret (verifier + prover composition)
                                        │
                     prove on CPU / Metal ──► verify ✓ (byte-identical proofs)
```

## What was built

| Piece | Where |
|---|---|
| IR syntax + semantics (cyclic rows, wrap-around, AIR-defined preprocessed columns) | `lean/StarkedAir/IR.lean` |
| M31 primality via Lucas–Lehmer (no `native_decide`) | `IR.lean`, `P_prime` |
| Gadget: chain of 32-bit adds (bits, 16-bit limbs, carries, next-row ref, `not_last` selector) | `lean/StarkedAir/Gadgets/Add32Chain.lean` |
| Soundness: `Satisfied ⇒ Z = (X+Y) mod 2³² ∧ X(r+1) = Z(r) for r < n−1` | `Add32Chain.sound` |
| JSON exporter (post-order DAG with sharing) | `lean/StarkedAir/Export.lean` |
| Zig IR + JSON parser + digest | `src/air/ir.zig` |
| One interpreter shared by verifier (QM31 at OODS point) and prover (M31 on eval domain) | `src/air/interp.zig`, `src/air/component.zig` |
| Proving spec; transcript binds the AIR digest; verifier pins the preprocessed root | `src/air/prove.zig` |
| CLI: `zig-out/bin/spike <log_size> <cpu\|metal> [lean]` | `src/bin/spike.zig` |

## Evidence

- `#print axioms Add32Chain.sound` → `[propext, Classical.choice, Quot.sound]`.
- StarkWare's `trace_sound` and `tuple_inclusion` (formal-proofs/Stwo, Lean
  v4.23-rc2) build cleanly and depend on the same three standard axioms only.
- Zig tests (11 passing):
  - the FIPS / genesis / random SHA256d vectors;
  - the Zig witness satisfies the Lean-exported AIR;
  - tampered witness → the prover refuses (`ConstraintsNotSatisfied`);
  - a proof checked against a different AIR → `OodsNotMatching`;
  - a **forged preprocessed column** (all-zero selector hiding a broken chain)
    → `PreprocessedRootMismatch`.
- Lean-exported AIR at 2¹⁶ rows (99 columns, 102 constraints):

  | Backend | Prove | Verify | Proof |
  |---|---|---|---|
  | CPU | 0.22 s | 0.01 s | 745 KB |
  | Metal | 0.25 s | 0.01 s | 745 KB |

  CPU and Metal proofs are byte-identical.

## Lessons

1. **Preprocessed columns must be part of the AIR definition and pinned by the
   verifier.** Otherwise a prover can switch selectors off. stwo-zig's native
   examples (e.g. `examples/xor.zig` `verify`) take the preprocessed commitment
   from the proof unchecked. A forgery against `xor` was reproduced and filed as
   teddyjfpender/stwo-zig#225.
2. **Structured Lean definitions make the proof easy.** The gadget proof is
   about 60 lines: a limb-evaluation lemma by induction, bounds, field→ℕ
   lifting, then `omega`. This matches StarkWare's finding that raw flattened
   polynomials are impractical to reason about.
3. The exporter's subexpression sharing made proving *faster* than with the
   Zig-built AIR (0.22 s vs 0.61 s on CPU at 2¹⁶), because the interpreter
   evaluates fewer nodes.
4. The prover refuses invalid witnesses, so verifier-side soundness tests need
   forged proofs. That is how the preprocessed-root test is built.

## Known gaps (spike scope)

- **Wrap-around semantics on the Zig side are tested only indirectly**,
  through end-to-end proofs with a +1 offset. A dedicated differential test of
  the Lean `Expr.eval` against Zig `interp` over random traces should come
  next. One option: export a Lean `#eval` oracle.
- **No interaction / LogUp in the IR yet** (needed for SHA ↔ header linkage).
  Port StarkWare's `tuple_inclusion` for the Lean side.
- **The verifier recomputes the preprocessed root**, which is O(N). Production
  should ship per-(AIR, log_size) roots in a verification key.
- **The interpreter is the correctness baseline, not the fast path.** GPU
  kernels generated from the same IR come later (M2).
- **The `export-air` executable links all of Mathlib** (a slow first build).
  Switch to an `#eval`-based exporter.
- **`AirStatement` carries a pointer and an allocator** — prototype
  ergonomics only.
- **Single trace size only**; no lifting.
