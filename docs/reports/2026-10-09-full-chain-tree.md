# Full chain with the header tree: one root proof binding every block hash (2026-10-09)

**Verdict:** the whole mainnet header chain (heights 0..970,347) is proven recursively into **one root
proof of 0.98 MB**, which the outer verifier accepts. The proof now also carries the header-tree root `T`:
the MMR root over all 970,348 block hashes, in height order. The `T` in the root proof equals the MMR root
recomputed independently from the headers. Chainwork and tip are unchanged from the
[2026-10-08 run](2026-10-08-full-chain.md) and equal Core's.

## Run

- **Command:** `zig-out/bin/spike chain 20 70 26 data/headers.bin` (ReleaseFast, M4 Pro, 14 cores,
  24 GB). Production FRI: 70 queries, 26-bit PoW, blowup 1.
- **Code:** binary built at `fdd5a03`, which includes the fix for the multi-component prover race. A first
  attempt without that fix failed at the start (`ConstraintsNotSatisfied`); see the log for 2026-10-08,
  session 3.
- **Segments:** 237 of 4,096 headers (2²⁰ rows), then the tail in decreasing powers of two, 243 in all.
  The fold runs in MMR order (D-033).
- **Started** 2026-10-08 about 16:45; **finished** 2026-10-09 09:03.

## Result

```
chain ROOT VERIFIED: headers 0..970347, 243 leaves, 242 nodes; leaves 45317s, fold 5098s, verify 1.09s; root proof 981000 bytes
  header MMR root T over 970348 block hashes: 06385baf 20475ba7 c00410ff fe404c84 985cc757 5c06e651 624d46ad 7e9a0bf0
  tip height 970347, chainwork 0x14d8dcca8e53277d43d257680, tip state words ddbc872d ba41b03a 80e818b9 7c8244ce 8cf38889 6e630100 00000000 00000000
```

- **`verifyRoot`:** checked the node circuit's identity, and the identity key expected for the MMR fold
  shape over the 243 segment sizes. It also checked the genesis input state.
- **Verification key:** the leaf circuit hashes come from public data (`leafIdentity`, one per segment
  size), not from the leaf proofs. This closes the caveat in the 2026-10-08 report.
- **`T`:** the root's public inputs 108..123 equal `header_tree.mmrRoot` over the block hashes, which
  are recomputed natively with std SHA-256 from `data/headers.bin` (`checkTreeRoot`). An inclusion proof
  for any height can be produced and checked against this `T` (`inclusionProof`, `verifyInclusion`).
- **Chainwork and tip:** identical to the 2026-10-08 run, so equal to Core's (see that report).

## Timing

| Phase | This run | 2026-10-08 (no tree) |
|---|---|---|
| Shape and VK (node and leaf identities) | 947 s | — |
| 243 leaves | 45,317 s (12.6 h) | 18,170 s (5.0 h) |
| 242-node fold | 5,098 s (1.4 h) | — |
| Root verification | 1.09 s | 0.26 s |
| Total | about 51,360 s (14.3 h) wall | 29,351 s (8.2 h) wall |

- **Leaves:** a full segment now takes about 160–190 s for the segment proof plus 18–45 s for the leaf
  circuit. The segment proof grew because it covers the header chain *and* the Blake2s tree component.
  Both must have the same row count until lifting (mixed sizes) exists.
- **Root verification:** it now includes deriving the VK. The 0.26 s figure did not.
- **Comparison:** the previous run shared the machine for its first 3.6 h, so the ratio is approximate.
  Peak memory was not recorded this time.

## Validity of the result for the current code

Since this binary was built, two kinds of change landed:
- the leaf and node glue became Lean-defined programs replayed in Zig (CIRCUIT-GLUE);
- M3a work, which doesn't touch the header proofs.

The `glue parity` tests show that the replayed circuits are gate-for-gate identical to the ones this run
proved, in topology and with values. The circuit hashes and VK are therefore unchanged, and this proof
stands for the current code.

## Trust

See [verification.md](../reference/verification.md). Since the previous report:
- **The glue is proven:** `node_sound`, `node_compose` and the digests.
- **The tree is proven:** `tree_root_sound` and `chain_from_genesis_T`.
- **Still trusted:** the in-circuit verifiers (VERIFIER-LEAN), gate semantics, and Stwo itself.
