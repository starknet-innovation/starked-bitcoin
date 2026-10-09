#!/bin/sh
# Extends a saved chain proof to the current tip (PROOF-STORE):
#   1. appends new mainnet headers to data/headers.bin (scripts/fetch_headers.py: each header's
#      SHA256d and prev-hash link are checked, genesis is pinned);
#   2. proves the new segments from <in.sbchain> in bounded steps (tools/prove_loop.sh, log 19);
#   3. verifies the result in a fresh process (pinned VK, Core's nMinimumChainWork).
# Usage: tools/extend_tip.sh <chainproof> <in.sbchain> [out dir, default data/store]
set -eu
CP="$1"; IN="$2"; DIR="${3:-data/store}"
cd "$(dirname "$0")/.."
python3 -I scripts/fetch_headers.py
N=$(( $(wc -c < data/headers.bin) / 80 ))
OUT="$DIR/mainnet-to-$N.sbchain"
[ -f "$OUT" ] && { echo "extend_tip: $OUT exists"; exit 0; }
START=$(date +%s)
tools/prove_loop.sh "$CP" mainnet data/headers.bin "$N" "$OUT" 4 --max-log 19 --from "$IN"
echo "extend_tip: proved in $(( $(date +%s) - START )) s"
"$CP" verify mainnet "$OUT"
