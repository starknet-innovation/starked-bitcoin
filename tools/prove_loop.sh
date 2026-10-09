#!/bin/sh
# Proves a chain in bounded-memory steps: one `chainproof prove --segments K` process per step,
# each resuming from the checkpoint, until the proof file exists (PROOF-STORE).
# Usage: tools/prove_loop.sh <chainproof> <vk> <headers.bin> <to> <out.sbchain> <K> [prove options...]
# Options (e.g. --max-log 19, --from <in.sbchain>) are passed to every step; a step resumes from the
# checkpoint when one exists, so --from only matters for the first.
set -u
CP="$1"; VK="$2"; HDR="$3"; TO="$4"; OUT="$5"; K="$6"
shift 6
while [ ! -f "$OUT" ]; do
  "$CP" prove "$VK" "$HDR" "$TO" "$OUT" --segments "$K" "$@" || { echo "prove_loop: step failed (exit $?)"; exit 1; }
done
echo "prove_loop: done, $OUT"
