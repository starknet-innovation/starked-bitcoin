# WEB-MEMBER: the coin-set website

Status: current · Updated: 2026-11-09 · Owner files: `web/`, `src/bin/webverify.zig`, `src/bin/chainproof.zig` (`serve-member`), `src/recursion/set_tree.zig` (`SegIndex`)

This file answers: what the website does, how to build and test it, and how to deploy it.

## What it does

1. **Verifies the seal in the browser.** `webverify.wasm` is the SEAL-T verifier (`chain_seal.verify`,
   `store.rootExpect`, the assumeUTXO anchor) compiled to WebAssembly, with every pinned VK embedded
   (header, join, both trees, set, SEAL-T). The page downloads the compact header-chain file (986 KB) and
   the seal (631 KB) and checks them, which takes about 0.4 s. A seal of another kind or under another VK
   is rejected.
2. **Checks a coin.** It fetches an `.sbmember` file (the same bytes `chainproof set-member` writes) from
   `serve-member`, or the visitor picks a local file. `verify_member` checks each path against the Merkle
   root and the last key of the seal the page just verified. The server is not trusted: a wrong path
   fails.

Not covered: the site states the set after block 972,500 only. TIP-ITER moves it forward.

## Build and test

```
web/build.sh                                  # wasm + page + proof files → zig-out/web/site
python3 -m http.server -d zig-out/web/site 8000
node web/test/verify.mjs zig-out/web/webverify.wasm data/store/mainnet-to-972502.compact.sbchain data/seal972/outT/seal-972500.bin [file.sbmember]
node web/test/browser.mjs http://127.0.0.1:8000/ [<url of an .sbmember>]   # headless Chrome, macOS path
```

Expected (2026-11-09):
- `verify.mjs`: `"ok":true`, 164,539,066 coins, 2,010,133,549,560,777 sat, root `f74e9573…`, tip
  972,501 `…0107ead0…4663` (equal to the node's `getblockhash 972501`), in about 0.47 s.
- With `bridge-972500.sbmember`: 66 coins, 13,689,057,287 sat, in 5 ms.
- Tampers (checksum recomputed): body offsets 200 and 5000 give `WrongDigest`; 300000 and 600000 give
  `CircuitProofRejected`. Without the checksum fix: `ChecksumMismatch`. The D-051 seal gives
  `WrongSealKind`.
- `browser.mjs`: "Verified in 0.4 s", then "66 proof(s) verified".

`zig build web -Dtarget=wasm32-wasi -Doptimize=ReleaseFast` builds only the wasm (3.1 MB). WASI is there
only for the C library the dependencies link: the module reads no files, and `worker.js` stubs WASI. The
prover's C kernels are not compiled for wasm (`build.zig`).

## Serve membership proofs

```
chainproof serve-member <set.bin> <work-dir> <port> [--bind <ip>]     # default bind 127.0.0.1
```

- `GET /member?op=<txid>:<vout>[,…]` (at most 16) returns `application/octet-stream`, an `.sbmember`
  file. `GET /health` returns `ok`. CORS is `*`.
- The first start builds `<work-dir>/segindex.bin`: each segment's end offset and root. This took about
  5 minutes for mainnet, measured with `set-member`. Every start checks that the index folds to the
  pass's root.
- Each query parses one or two segments; it took 0 ms on the test set. The set file is memory-mapped.
- Tested 2026-11-09 on the test chain's set after block 15 (`data/test-chain/e15`): one present coin, an
  absent coin below the first key and one above the last. All three were accepted by `verify-member`.

**Mainnet (not yet running):** on the node, `chainproof serve-member out972/set-972500.bin
setgpu/passes/s972500 8090` from `/data/replay`. Then either set `web/config.json` to
`{"member": "<public URL>"}` behind a TLS reverse proxy, or tunnel it for a private demo
(`ssh -L 8090:127.0.0.1:8090 …` and `{"member": "http://127.0.0.1:8090"}`). Exposing the node publicly is
the owner's call.

## Deploy

The site is static (`zig-out/web/site`, about 4.8 MB): any static host. Serve `.wasm` as
`application/wasm`. Public launch is gated on external review (roadmap WEB-MEMBER).
