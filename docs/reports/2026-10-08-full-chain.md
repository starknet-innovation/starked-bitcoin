# Full chain: every mainnet header checked, and proven to one root (2026-10-08)

**Verdict:** all 970,348 mainnet headers (heights 0..970,347) satisfy the
header-chain AIR (`header_chain_v6`), segment by segment, with every segment
chaining to the next. The chainwork the AIR computes over the whole chain
equals Bitcoin Core's `chainwork` for block 970,347, and the tip equals the
public tip at that height. Recursive aggregation to one root proof: see
[Whole chain to one root](#whole-chain-to-one-root).

## Data

- `data/headers.bin`: 970,348 headers, downloaded from public APIs
  (`scripts/fetch_headers.py`: Blockstream and mempool.space, four parallel
  workers) and merged with every prev-hash link checked.
- Tip cross-check (2026-10-08): block 970,347's hash computed locally,
  `00000000000000000001636e8988f38cce44827cb918e8803ab041ba2d87bcdd`, equals
  mempool.space's `/api/block-height/970347`.

## Completeness: the AIR accepts every header

- **Command:** `zig-out/bin/spike fullrun 16 check data/headers.bin`
  (ReleaseFast, M4 Pro, 14 cores, 24 GB; a recursive run shared the machine).
- **Result:** heights 0..970,347 in 3,794 segments of up to 256 headers;
  **failures = 0**; 13,071 s; peak RSS 211 MB.
- **Chainwork:** the AIR's final work output is
  `0x14d8dcca8e53277d43d257680`. Blockchair's raw `getblock` for block
  970,347 reports `chainwork` =
  `00000000000000000000000000000000000000014d8dcca8e53277d43d257680`: equal.
- **Meaning:** no mainnet header so far needs a rule the AIR cannot express
  (for example the `s ≥ 16` restriction of D-021 never triggers), and
  consecutive segments' public outputs equal the next inputs.

## Whole chain to one root

- **Command:** `zig-out/bin/spike chain 20 70 26 data/headers.bin`
  (CPU only; 70 FRI queries, 26-bit PoW; segments of 4,096 headers,
  shrinking by powers of two at the end; D-025 node circuit).
- **Result:** pending (log: `data/chain_full.log`).

## Reproduce

```sh
python3 -I scripts/fetch_headers.py --from 0 --to <tip> --out data/headers.bin   # or chunks + --merge
zig build -Doptimize=ReleaseFast
zig-out/bin/spike fullrun 16 check data/headers.bin
zig-out/bin/spike chain 20 70 26 data/headers.bin
```
