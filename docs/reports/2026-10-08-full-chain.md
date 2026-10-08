# Full chain: every mainnet header checked, and proven to one root (2026-10-08)

**Verdict:** all 970,348 mainnet headers (heights 0..970,347) satisfy the
header-chain AIR (`header_chain_v6`), segment by segment, with every segment
chaining to the next. The chainwork the AIR computes over the whole chain
equals Bitcoin Core's `chainwork` for block 970,347, and the tip equals the
public tip at that height. The whole chain is also proven recursively into
**one root proof of 0.98 MB that the outer verifier accepts in 0.26 s**,
binding genesis, the tip hash, the height and the exact chainwork.

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
- **Result:** `chain ROOT VERIFIED: headers 0..970347, 243 leaves, 242 nodes`.
  `verifyRoot` checked the node circuit identity, the expected identity key
  over all 243 leaf circuit hashes, the digest of the root's public inputs,
  and the genesis input state.
- **Root public outputs:** height 970,347; chainwork
  `0x14d8dcca8e53277d43d257680` (equal to Core's, above); tip state words
  `ddbc872d ba41b03a 80e818b9 7c8244ce 8cf38889 6e630100 00000000 00000000`,
  which is the block hash above in SHA-256 internal byte order.

| Phase | Time | Notes |
|---|---|---|
| Shape and node identity | 71 s | Fixpoint over the leaf sizes used (2²⁰ … 2⁸ rows) and the node |
| 243 leaves | 18,170 s (5.0 h) | About 33–60 s segment proofs (two CPU proofs, the plain verifier needs a captured copy) + 22–32 s leaf circuit proof each; the first 3.6 h shared the machine with the check run |
| 242 nodes | 5,773 s (1.6 h) | About 24 s each |
| Root verification | 0.26 s | Native circuit-proof verification plus key and genesis checks |
| Total | 29,351 s (8.2 h) wall | Peak RSS 16.5 GB; peak memory footprint 26.8 GB (the 24 GB machine compressed memory; no swap-outs) |

- **Verification key, caveat:** in this run `verifyRoot` used the leaf
  circuit hashes reported by the leaf proofs themselves. The verifier must
  derive them independently. `leafIdentity` (added after the run) derives
  each leaf circuit's identity from public data (the first segment from
  genesis at that size), and `spike chain` now verifies the root against those.
  Checked after the run: `spike chain 20 70 26 data/headers.bin 3692`
  (7 leaves at 2¹⁹, 2¹⁸, 2¹⁷, 2¹⁴, 2¹³, 2¹¹, 2¹⁰ rows, the same sizes as the full run's
  tail) and `spike agg 20 2 70 26` (2²⁰, heights 4,096..8,191) verify with the
  independent VK. A re-run of the whole chain with the independent VK has not
  been done (about 8 h).
- **Not yet optimized (D-022):** CPU only; each segment is proven twice;
  leaves are padded to the node's size. The Metal path proves segments at
  about 231 headers/s ([sample report](2026-10-07-fullrun-sample.md)).
- **Trust:** see [verification.md](../reference/verification.md): the
  in-circuit verifiers (ours and stwo-zig's) and the node circuit's
  implementation of `PubLink` are trusted code; the composition is proven in
  Lean (`pub_compose`, `chain_from_genesis`).

## Reproduce

```sh
python3 -I scripts/fetch_headers.py --from 0 --to <tip> --out data/headers.bin   # or chunks + --merge
zig build -Doptimize=ReleaseFast
zig-out/bin/spike fullrun 16 check data/headers.bin
zig-out/bin/spike chain 20 70 26 data/headers.bin
```
