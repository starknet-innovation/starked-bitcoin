# Benchmark: our SHA-256 AIR vs Raito's Cairo SHA-256 (2026-10-07)

**Verdict:** for SHA256d of block headers, our native AIR proves roughly
**250× faster on CPU** than Raito's Cairo SHA-256 proven with `scarb prove`.
Our *full* header-chain AIR (all consensus rules, not just hashing) is still
roughly **100× faster** than Raito's hashing alone. Roadmap `BENCH-RAITO`.

## Question

Does a native AIR beat Cairo for the dominant cost of a header chain, SHA256d
of 80-byte headers (3 compressions each)?

## Method

- **Machine:** Apple M4 Pro, 14 cores, 24 GB. Everything runs on CPU unless
  stated otherwise.
- **Raito:** `utils::sha256::compute_sha256_u32_array` at Raito commit
  `48c237ac941d8061a857ecd111d7e81107912556`, pulled as a pinned git
  dependency (no code copied).
  - Program: `bench/raito-sha256/src/lib.cairo`. For `i < n`, it double-hashes
    the genesis header with nonce `i`. Its output was checked against Python
    `hashlib`.
  - Commands, run from `bench/raito-sha256`:
    `scarb --profile release prove --execute --arguments <n>` (scarb 2.18.0,
    built-in Stwo prover), and `scarb --profile release execute` alone to
    separate out execution time.
  - `scarb prove` exposes no security parameters. UNVERIFIED: its defaults are
    assumed comparable (Stwo production defaults).
- **Ours:** `zig-out/bin/spike`, ReleaseFast, CPU backend, 70 queries,
  26-bit PoW:
  - `spike sha 16 cpu` (SHA-256 compression AIR only);
  - `spike headers 14|16 cpu testdata/mainnet_headers_0_1024.hex` (the
    full header-chain AIR v5).

## Results

| Prover | Workload | Headers | Prove time | Throughput | Peak memory | Proof |
|---|---|---|---|---|---|---|
| Raito Cairo, `scarb prove` | SHA256d only | 64 | 27.0 s (27.8 s total − 0.8 s execute) | 2.4 headers/s | 7.5 GB | 12.3 MB (JSON) |
| Raito Cairo, `scarb prove` | SHA256d only | 256 | 165 s (167.8 − 2.8) | 1.55 headers/s | 14.0 GB | 13.8 MB (JSON) |
| Ours, SHA-256 AIR | SHA256d only (910 compressions at 2¹⁶) | ≈ 303 | 0.50 s | ≈ 600 headers/s (1,806 comp/s) | — | 0.78 MB (binary) |
| Ours, header chain v5 | **all header rules** | 64 | 0.18 s | 358 headers/s | — | 0.71 MB |
| Ours, header chain v5 | **all header rules** | 256 | 1.66 s | 154 headers/s | — | 0.92 MB |
| Ours, header chain v5 (Metal) | all header rules | 1024 | 4.28 s | 239 headers/s | — | 1.11 MB |

Raito's 256-header run is 20.0 M Cairo steps (about 78 k steps per header),
with 3.6 M range-check and 1.2 M bitwise builtin uses.

## Conclusions and follow-ups

- **SHA256d alone:** about 600 vs 1.5–2.4 headers/s, roughly 250× in our
  favour on CPU.
- **Our full consensus AIR vs Raito's hashing alone:** about 154 vs 1.55
  headers/s at 256 headers, roughly 100×. That holds although ours also
  checks PoW, retarget, MTP and chainwork.
- **Caveats:**
  - These are different provers (stwo-cairo in Rust vs stwo-zig).
  - The Cairo proof includes the general-purpose Cairo VM AIR. That is the
    price of programmability, not inefficiency in Raito's SHA code.
  - Proof sizes are not comparable byte-for-byte (JSON vs binary encoding).
  - Raito's real pipeline uses `cairo-prove`/bootloader setups; this
    benchmark measures only its SHA-256 function under `scarb prove`.
- This supports decision D-003 (native AIRs).
- No follow-up is required for M1. GPU constraint kernels (roadmap
  `GPU-CODEGEN`) would widen the gap.
