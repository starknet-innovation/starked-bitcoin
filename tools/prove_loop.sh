#!/bin/sh
# Proves a chain in bounded-memory steps: one `chainproof prove --segments K` process per step,
# each resuming from the checkpoint, until the proof file exists (PROOF-STORE).
# Usage: tools/prove_loop.sh <chainproof> <vk> <headers.bin> <to> <out.sbchain> [K] [--from <in.sbchain>]
set -u
CP="$1"; VK="$2"; HDR="$3"; TO="$4"; OUT="$5"; K="${6:-1}"
shift 6 2>/dev/null || shift $#
while [ ! -f "$OUT" ]; do
  "$CP" prove "$VK" "$HDR" "$TO" "$OUT" --segments "$K" "$@" || { echo "prove_loop: step failed (exit $?)"; exit 1; }
  # --from only matters for the first step; later steps resume from the checkpoint.
  set --
done
echo "prove_loop: done, $OUT"
