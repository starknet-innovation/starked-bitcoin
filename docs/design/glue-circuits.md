# Glue circuits, Lean-first (CIRCUIT-GLUE)

Status: current · Updated: 2026-10-08

The leaf and node recursion circuits are gate lists over QM31 variables, built
with stwo-zig's circuit builder. Each one contains a full Stwo verifier, which
stays trusted (VERIFIER-LEAN, parked), plus **glue**: our own logic around it.
The glue is now defined in Lean, exported, replayed in Zig, and proven.

## Pipeline

1. **Define in Lean.** `lean/StarkedAir/Circuit/Gadgets.lean` defines the glue
   as programs of ops:
   - **Ops:** const, add, sub, mul, eq, M31/u16 guesses with value hints,
     m31→u32, the Blake2s G gate, triple xor, and *hooks* where the host runs
     the verifier.
   - **Gadgets:** `guessU32`, `blake2s` (= `blake2sU32s`), `pubsDigest`,
     `range16`, `linkChecks`, `treeNode`.
   - **Programs:** `nodeProgram`, `leafProgram`.
   
   Op order is exactly the order of the builder calls in the code they replaced.
2. **Export.** `lake env lean --run Export.lean node_glue|leaf_glue` writes
   `airs/node_glue.json` and `airs/leaf_glue.json`.
3. **Replay.** `src/recursion/glue.zig` turns each op into its builder call.
   - Registers are single-assignment (checked), so one Lean register is one
     circuit variable.
   - `node.buildNodeCircuit` and `leaf.buildLeafCircuit` are now the replay plus
     the verifier at the hooks.
4. **Parity.** The `glue parity` tests (leaf; node in topology and value mode)
   check that the replayed circuits have the same gates, in the same order, over
   the same variables and values, as the previous hand-written builders. Those
   builders are kept as `buildLeafCircuitRef` and `buildNodeCircuitRef`. Circuit
   hashes, VKs and existing proofs are therefore unchanged.

## What is proven

All standard axioms only. `Op.holds` is each op's meaning.

| Theorem | Statement |
|---|---|
| `blake2s_sound`, `blake2s_words` (`Circuit/BlakeSound.lean`) | The gadget's result wires hold word-level Blake2s (`hashW`/`blake2sWords`) of its message wires |
| `pubsDigest_sound` | The public-input digest is Blake2s of the key words, then each input's value as a word |
| `link_sound` (`Circuit/NodeSound.lean`) | `linkChecks` ⇒ `PubLink` on the children's inputs |
| `treeNode_sound` | `treeNode` ⇒ the root limbs are `limbsOf (hnode a b)` |
| `node_sound` | The node program ⇒ `PubLink` and `NodeOut`, the hypotheses of `pub_compose_T` |
| `node_compose` | Node program plus valid children ⇒ valid node inputs (`PubValidT`) |
| `node_child_digests`, `node_key`, `node_digest`, `leaf_digest` | The digests each verifier hook checks, the identity key, and the output digests, as Blake2s of the right words |

## What stays trusted

- **Gate semantics:** `Op.holds` matches what the circuit AIR enforces for each
  gate (stwo-zig `circuit.zig` `check`, and upstream's gate components).
  Constants equal their values (`finalize_constants`). Guesses are constrained
  at finalization (M31: `x ⊙ 1 = x`; u16: `m31_to_u32(x) = x`).
- **The replay:** `glue.zig` maps each op to the builder call with that meaning.
  It's about 100 lines, and the parity tests cover it.
- **Word-level vs byte-level Blake2s:** `hashW` matches the byte-level spec,
  which is hashlib-tested. This is shown by `#guard`s at the three sizes used
  (64, 128, 528 bytes), not by a general proof.
- **Everything at the hooks:**
  - the verifiers;
  - in the leaf, the wiring of the public entry `node(K, 0, T)` into the plain
    verifier statement.
- **What the digests buy:** binding a child's public inputs to its verified
  proof relies on the verifier checking that digest, and on Blake2s collision
  resistance.
