# Test data

Status: current · Updated: 2026-10-07 · Owner files: `testdata/**`, `airs/probe_oracle.json`

Each data file has a row here. **Add the row in the same commit as the
file.**

| File | Contents | Source | Used by |
|---|---|---|---|
| `mainnet_headers_0_16.hex` | Headers at heights 0..15, one 80-byte header per line, as hex | Blockstream Esplora API (`/api/block-height/<h>`, then `/api/block/<hash>/header`) | header-chain v1 tests |
| `mainnet_hash_15.txt` | Block hash at height 15 | Same | tip-hash check |
| `mainnet_headers_0_1024.hex` | Heights 0..1023 | Same | PoW and chain-state tests, `spike headers` benchmark |
| `mainnet_headers_1984_2048.hex` | Heights 1984..2047 (crosses the boundary at 2016; the cap branch is used at 2016) | Same | v3a/v3b tests |
| `mainnet_headers_32192_32320.hex` | Heights 32192..32319 (first real difficulty change, at 32256) | Same | v3b tests |
| `mainnet_header_30240.hex` | The header at height 30240, the start of the period that ends at 32255 | Same | v3b tests (period-start time) |
| `mainnet_headers_1973_1984.hex` | Heights 1973..1983: the median-time-past window before the 1984 segment | mempool.space Esplora API (same endpoints); hash-links into `mainnet_headers_1984_2048.hex` | v4 tests |
| `mainnet_headers_32181_32192.hex` | Heights 32181..32191: the window before the 32192 segment | mempool.space Esplora API; hash-links into `mainnet_headers_32192_32320.hex` | v4 tests |
| `airs/probe_oracle.json` | Lean-computed `Expr.eval` values on a fixed trace | `lake env lean --run Export.lean probe_oracle` | `interp.zig` differential test |

## Rules

- **Fetch real chain data only from a public source, and record the source
  here.** Prefer re-verifying it with a local `bitcoind`
  (`bitcoin-cli getblockheader <hash> false`) when one is available.
- Hashes are checked by the tests themselves: linkage and tip hash. A
  corrupted file fails the tests and does not pass silently.
- Keep files small, at most a few thousand headers. Benchmarks that need more
  data fetch it outside the repo.
- Register every file as an anonymous import in `build.zig`
  (`testdata:<name>`).
