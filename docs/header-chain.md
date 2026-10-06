# Header-chain AIR

## v1 (2026-10-06): SHA256d + linkage — proven sound

- **Definition:** `lean/StarkedAir/Gadgets/HeaderChain.lean`
  (export: `airs/header_chain.json`, 208 constraints, 36 preprocessed columns,
  32 public inputs).
- **Witness:** `src/btc/header_chain.zig`
- **Proof:** `lean/StarkedAir/Gadgets/HeaderChainSound.lean`, theorem
  `chain_sound`. It depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

**Layout:** 256 rows per header.

| Rows | Contents |
|---|---|
| 0–71 | compression 0 (IV, header bytes 0..63) |
| 72–143 | compression 1 (bytes 64..79 + padding) |
| 144–215 | compression 2 (IV, digest + padding) |
| 216–255 | reserved for proof-of-work and difficulty checks |

Because 256 divides the trace length, there are no partial headers.

**Statement proven.** For a trace satisfying the AIR with `2^logSize` rows
(logSize ≥ 8), let `H = 2^logSize/256`. Then:

1. `sha256d(header_j) = hash_j` for every `j < H`. Here `header_j` is the 20
   words read from the trace and `hash_j` is read from compression 2's finalize
   rows. `sha256d` is FIPS 180-4 SHA-256 applied twice
   (`lean/StarkedAir/Spec/Bitcoin.lean`, checked against the genesis block).
2. `prevHash(header_j) = hash_{j−1}` for `1 ≤ j < H` (header words 1..8).
3. `prevHash(header_0)` = public inputs 0..15, as 8 words of (lo, hi) limbs.
4. `hash_{H−1}` = public inputs 16..31.

**What this does not establish yet:**
- **Proof-of-work.** `hash ≤ target(nBits)` and the validity of nBits are next.
- **Difficulty transitions, timestamps (median time past), cumulative work.**
- **The usual trust base:**
  - Zig interpreter ≡ Lean semantics (differential-tested, not proven);
  - the exporter is a faithful printer;
  - the soundness of Stwo itself.

**Tests:** real mainnet blocks 0..15 satisfy the AIR, and the tip hash equals
block 15's. Tampering is caught: a broken link (at the expected row), a wrong
padding word, and a wrong claimed tip.

**Benchmark (M4 Pro, Metal, secure profile):**

| Rows | Headers | Prove | Throughput |
|---|---|---|---|
| 2¹⁴ | 64 | 0.16 s | |
| 2¹⁶ | 256 | 0.33 s | |
| 2¹⁸ | 1,024 | 1.7 s | ≈ 600 headers/s |
