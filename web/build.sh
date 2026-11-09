#!/usr/bin/env bash
# Assembles the WEB-MEMBER site in zig-out/web/site: the page, webverify.wasm, and the two proof files.
# Usage: web/build.sh [<chain.sbchain> <seal.bin>]   (defaults: the mainnet SEAL-T inputs under data/)
# Serve locally:  python3 -m http.server -d zig-out/web/site 8000
set -euo pipefail
cd "$(dirname "$0")/.."
CHAIN=${1:-data/store/mainnet-to-972502.compact.sbchain}
SEAL=${2:-data/seal972/outT/seal-972500.bin}
zig build web -Dtarget=wasm32-wasi -Doptimize=ReleaseFast
OUT=zig-out/web/site
rm -rf "$OUT"; mkdir -p "$OUT/data"
cp web/index.html web/app.js web/worker.js zig-out/web/webverify.wasm "$OUT/"
cp "$CHAIN" "$OUT/data/chain.sbchain"
cp "$SEAL" "$OUT/data/seal.bin"
[ -f web/config.json ] && cp web/config.json "$OUT/"
node web/test/verify.mjs "$OUT/webverify.wasm" "$OUT/data/chain.sbchain" "$OUT/data/seal.bin" >/dev/null && echo "site in $OUT: seal verifies under node"
