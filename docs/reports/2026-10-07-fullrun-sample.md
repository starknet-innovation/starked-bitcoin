# Full-chain run: 10,240-header sample (2026-10-07)

**Verdict:** mainnet heights 0..10,239 pass the whole pipeline. Every segment's
witness satisfies the exported AIR (`header_chain_v6`); every segment is
proven and verified on Metal; consecutive segments chain through their public
inputs; the final chainwork is exact. Extrapolated full-chain proving time on
the M4 Pro is about 70 min (roadmap `HC-FULLRUN`).

## Method

- **Data:** `data/sample_0_10240.bin`, built from `data/headers.bin` plus
  `data/chunk_0.bin` (downloaded by `scripts/fetch_headers.py`). All 10,239
  links were re-verified and the genesis hash pinned.
- **Machine:** Apple M4 Pro (14 cores, 24 GB). The header download was still
  running in the background, so the numbers are slightly pessimistic.
- **Commands** (ReleaseFast):
  - `zig-out/bin/spike fullrun 16 check data/sample_0_10240.bin`: 40
    segments of 256 headers, checked against the AIR with the CPU
    interpreter.
  - `/usr/bin/time -l zig-out/bin/spike fullrun 18 metal data/sample_0_10240.bin`:
    10 segments of 1,024 headers, proven and verified (70 queries, 26-bit
    PoW).

## Results

| Run | Segments | Failures | Time | Notes |
|---|---|---|---|---|
| check (2¹⁶ rows) | 40 × 256 headers | 0 | 77.3 s | Final chainwork `0x280028002800` = 10,240 × `0x100010001` (difficulty 1 throughout) |
| Metal prove + verify (2¹⁸ rows) | 10 × 1,024 headers | 0 | 48.5 s total, 44.3 s proving | 231 headers/s; 11.36 MB of proofs (1.11 MB each); peak RSS 1.31 GB |

Segment chaining was checked at every boundary: tip → prev-hash, height + 1,
nBits, period start, time, MTP window, chainwork.

## Extrapolation (not measured)

- **Proving all 970,348 headers** at 231 headers/s takes about 70 min. Per-header
  cost is flat in era, since the AIR does the same work for every header.
- **Proof bundle size** depends on segment size:
  - 2¹⁸ rows (1,024 headers): about 948 proofs, about 1.05 GB;
  - 2²⁰ (4,096): about 237 proofs at about 1.3 MB each, about 0.3 GB;
  - 2²² (16,384): about 60 proofs, about 0.1 GB, but peak memory would be
    about 20 GB (16 × the 2¹⁸ figure), which is borderline on 24 GB.
- Recursion and aggregation (M2) replace the bundle with one proof.

## Full-chain run plan

1. Download completes; merge with
   `python3 -I scripts/fetch_headers.py --merge data/chunk_{0,1,2,3}.bin`.
   The merge verifies every link.
2. Completeness: `spike fullrun 16 check data/headers.bin` (about 2 h on CPU).
   A failure means a real header the AIR cannot express: investigate it and
   fix it before proving.
3. Proving: `spike fullrun 20 metal data/headers.bin`. The trial segment size
   is 2²⁰, chosen to balance memory and bundle size; fall back to 18 if memory
   is tight. Record the time, peak memory, bundle size, and the final
   chainwork compared with an independent source.
4. Write the report and close `HC-FULLRUN`, and with it M1.
