# WEB-MEMBER: the coin-set website

Status: current · Updated: 2026-11-12 · Owner files: `web/`, `.github/workflows/pages.yml`, `src/bin/webverify.zig`, `src/bin/chainproof.zig` (`set-index`, `serve-member`), `src/recursion/set_tree.zig` (`SegIndex`, `memberInSegment`)

This file answers: what the website does, how it is hosted, how to build and test it, and how to deploy it.

## What it does

1. **Verifies the seal in the browser.** `webverify.wasm` is the SEAL-T verifier (`chain_seal.verify`,
   `store.rootExpect`, the assumeUTXO anchor) compiled to WebAssembly, with every pinned VK embedded
   (header, join, both trees, set, SEAL-T). The page downloads the compact header-chain file (986 KB) and
   the seal (631 KB) from `web/proofs/` and checks them in about 0.4 s. A seal of another kind or under
   another VK is rejected.
2. **Checks a coin by byte range (default).** The set file (14.2 GB) sits unchanged in object storage.
   - The page downloads the set's segment index once (533 KB, `chainproof set-index`). It holds `HALF` and,
     for each of the 7,014 segments, its end offset, Merkle root and last key.
   - `load_index` rejects an index whose roots don't fold to the verified seal's root.
   - Per outpoint, `locate` picks the segment and the page fetches only that range (about 2 MB) with an
     HTTP `Range` request.
   - `verify_segment` (`set_tree.memberInSegment`) hashes the segment's leaves (the first leaf's previous
     key is the previous segment's last key), builds the path, and checks it with the same `verifyMember`
     as the native verifier, against the seal's root and last key.
   - Storage is not trusted: a wrong index entry or segment byte fails (tests below).
3. **Picks a random coin** ("Pick a random UTXO in the snapshot"): `pick_segment` maps a random 32-bit
   number to a byte of the set file, so a segment is picked in proportion to its size, and
   `pick_in_segment` (`set_tree.keyInSegment`) takes a random record of it. The button only fills the box;
   Check proves the coin as any other. The segment stays cached in the page, so Check does not download it
   again (it is still hashed against the seal's root). Coins are close to equally likely, not exactly:
   a coin in a segment with fewer, larger records is slightly favoured.
4. **Or checks an `.sbmember` file** (from `chainproof set-member` or `serve-member`) that the visitor
   picks, with `verify_member`.

What it costs a visitor: 4.7 MB once (page, wasm, proofs), 0.5 MB for the index on the first lookup, then
about 2 MB per coin.

Not covered:
- The site states the set after block 972,500 only; TIP-ITER moves it forward.
- The outpoint `000…000:0` has no proof of absence: the set's first leaf uses 36 zero bytes as its
  previous key, so the bracket `prev < key` fails (`NotBracketed`). That outpoint is the coinbase input
  marker, never an output; the native `verify-member` behaves the same.

## Hosting

| Part | Where | Size |
|---|---|---|
| Page, `webverify.wasm`, `web/proofs/` | GitHub Pages, built by `.github/workflows/pages.yml` on pushes to `main` (on `ubuntu-24.04-arm`: on x86_64 the build hits an LLVM crash in stwo-zig's host codegen) | 4.8 MB |
| `set-972500.bin` and `set-972500.segindex` | Object storage with public read, CORS, and HTTP Range support (e.g. Cloudflare R2: no egress fees, about $0.21/month for 14.2 GB) | 14.2 GB + 533 KB |

`config.json` tells the page where the set lives: `{"set": "<URL of the set file>", "index": "<URL of
the index>"}`. In CI it is written from the repository variables `SET_URL` and `INDEX_URL`. A local
`web/config.json` overrides that, and `{"member": "<URL>"}` selects a `serve-member` server instead.

### Live deployment (2026-11-12)

- Site: https://starknet-innovation.github.io/starked-bitcoin/ (Pages source "GitHub Actions").
- Bucket: Cloudflare R2 `starked-bitcoin`, public at `https://pub-94aee70efd7b44649d45a2c33f0ab6b1.r2.dev`
  (r2.dev: rate-limited; move to a custom domain before launch and update the two variables).
- CORS allows only `https://starknet-innovation.github.io` (GET, HEAD, header `Range`).
- Uploaded from the node with rclone (bucket-scoped key, `no_check_bucket = true`; key deleted after).
  The public copy of `set-972500.bin` hashes to `2b878bfd96084e4e…`, equal to the node's file.
- Live check (headless Chrome, `browser.mjs --ops` with the five outpoints below): seal verified in 0.5 s,
  "5 proof(s) verified: 3 unspent, 2 absent".
- A rebuild needs `gh workflow run pages --ref main` (a re-run of an old deploy fails: its artifact expires).

### Setting up the bucket

1. Create a bucket and give it a public URL (an R2 custom domain; r2.dev is rate-limited).
2. Upload from the node, where the files are:
   - `/data/replay/out972/set-972500.bin` (sha256 starts `2b878bfd96084e4e`);
   - `/data/replay/setgpu/set-972500.segindex`.

   Use `rclone copy` or `aws s3 cp --endpoint-url …`: both do multipart uploads.
3. CORS: allowed origin `https://starknet-innovation.github.io`, methods `GET` and `HEAD`, allowed header
   `Range`, exposed headers `Content-Range` and `Content-Length`.
4. Repository settings: set Pages' source to "GitHub Actions", and add the variables `SET_URL` and
   `INDEX_URL`. Then run the `pages` workflow, or push to `main`.

## Build and test

```
web/build.sh                                  # wasm + page + proofs → zig-out/web/site (checks web/proofs/SHA256SUMS)
node web/test/serve.mjs zig-out/web/site 8000 /data/set.bin=<set file> /data/set.segindex=<index>   # static + Range + CORS
node web/test/verify.mjs zig-out/web/webverify.wasm web/proofs/chain-972502.sbchain web/proofs/sealt-972500.bin [file.sbmember | --range <index> <set file> <txid:vout>...]
node web/test/browser.mjs http://127.0.0.1:8000/ [<url of an .sbmember> | --ops <txid:vout,...> | --pick <n>]   # headless Chrome (macOS path)
```

`serve.mjs` also proxies a mapped URL (`/data/set.bin=https://…/set-972500.bin`), which tests a local build
against the bucket despite its CORS policy. On 2026-11-12, `--pick 8` that way: 8 random coins, all present
and verified, one segment download each, Check about 0.2 s.

Locally, without the 14 GB file: a sparse file of the set's size, holding only the segments under test.
`data/web/set-972500-sparse.bin` takes 10 MB on disk.

Expected (2026-11-09/10):
- `verify.mjs`: `"ok":true`, 164,539,066 coins, 2,010,133,549,560,777 sat, root `f74e9573…`, tip 972,501
  `…0107ead0…4663` (equal to the node's `getblockhash 972501`), in about 0.47 s.
  - Tampers (checksum recomputed): body offsets 200 and 5000 give `WrongDigest`; 300000 and 600000 give
    `CircuitProofRejected`. Without the checksum fix: `ChecksumMismatch`. The D-051 seal gives
    `WrongSealKind`.
  - `bridge-972500.sbmember`: 66 coins, 13,689,057,287 sat, in 5 ms.
- `--range` on mainnet (index from the node, segments 3000, 3001, 5027, 6177, 7013), about 10 ms per coin:
  - two bridge coins: present;
  - `fff…f:7`: absent, after the last record;
  - a segment's last key: present;
  - the key just above it: absent, bracketed by the next segment's first record.

  Tampers: a flipped root in the index gives `IndexRootMismatch`. A flipped last key (segment 5026) or a
  flipped byte in segment 5027 gives `NotInRoot`.
- `browser.mjs --ops` with those five: "Verified in 0.5 s", then "5 proof(s) verified: 3 unspent, 2
  absent". `000…0:0` gives `NotBracketed`.

`zig build web -Dtarget=wasm32-wasi -Doptimize=ReleaseFast` builds only the wasm (3.1 MB). WASI is there
only for the C library the dependencies link: the module reads no files, and `worker.js` stubs WASI. The
prover's C kernels are not compiled for wasm (`build.zig`).

## The segment index

`chainproof set-index <set.bin> <work-dir> <out>`: `passSegments` over the set, then a check that the
roots fold to the pass's root and that the last end is the file's size. On the node for
`set-972500.bin`: 7,014 segments, `HALF` 16,384, 276 s, 8.4 GB peak RSS, 533,084 bytes. Format
`SBSEGIX2`: count (u64), `HALF` (u32), then per segment its end (u64), root (8 × u32) and last key (36
bytes), little-endian.

## Optional: a proof server

`chainproof serve-member <set.bin> <work-dir> <port> [--bind <ip>]` (default bind 127.0.0.1):
- `GET /member?op=<txid>:<vout>[,…]` (at most 16) returns an `.sbmember` file; `GET /health` returns `ok`.
  CORS is `*`.
- It caches the index as `<work-dir>/segindex.bin`.
- Tested on the test chain's set (`data/test-chain/e15`): a present coin, one below the first key and
  one above the last, all accepted by `verify-member`.
- Not needed with object storage. It suits a private demo over an SSH tunnel (`{"member":
  "http://127.0.0.1:8090"}`).

Public launch is gated on external review (roadmap WEB-MEMBER).
