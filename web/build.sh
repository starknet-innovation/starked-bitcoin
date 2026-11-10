#!/usr/bin/env bash
# Assembles the WEB-MEMBER site in zig-out/web/site: the page, webverify.wasm, and the two proof files.
# Usage: web/build.sh [<chain.sbchain> <seal.bin>]   (defaults: the mainnet SEAL-T files in web/proofs/)
# config.json: web/config.json if present, else from $SET_URL and $INDEX_URL if set (CI).
# Serve locally:  python3 -m http.server -d zig-out/web/site 8000
set -euo pipefail
cd "$(dirname "$0")/.."
CHAIN=${1:-web/proofs/chain-972502.sbchain}
SEAL=${2:-web/proofs/sealt-972500.bin}
(cd web/proofs && shasum -a 256 -c SHA256SUMS >/dev/null)
zig build web -Dtarget=wasm32-wasi -Doptimize=ReleaseFast
OUT=zig-out/web/site
rm -rf "$OUT"; mkdir -p "$OUT/data"
cp web/index.html web/app.js web/worker.js zig-out/web/webverify.wasm "$OUT/"
cp "$CHAIN" "$OUT/data/chain.sbchain"
cp "$SEAL" "$OUT/data/seal.bin"
if [ -f web/config.json ]; then cp web/config.json "$OUT/"
elif [ -n "${SET_URL:-}" ]; then printf '{"set": "%s", "index": "%s"}\n' "$SET_URL" "$INDEX_URL" > "$OUT/config.json"; fi
node web/test/verify.mjs "$OUT/webverify.wasm" "$OUT/data/chain.sbchain" "$OUT/data/seal.bin" >/dev/null && echo "site in $OUT: seal verifies under node"
