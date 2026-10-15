#!/usr/bin/env bash
# cuda-epoch on a pod (src/gpu/cuda/epoch.zig). Data in $DATA (default /workspace/data, see
# docs/design/gpu-cuda.md § Batch proving): headers.bin, chain.sbchain, epoch/{blocks,undo} (heights
# 0..E) and sample/{blocks,undo} with sample/heights.txt (any heights, e.g. a sample per size class).
#   epoch.sh check [E]    epoch 0..E (default 100), production: device vs --mock (CPU) proofs, byte-identical
#   epoch.sh sample       the sample, production, device: per-block timings and a per-class summary
#   epoch.sh sample-check the sample's blocks up to SAMPLE_CPU_MAX_L (default 19) again with --mock: byte-identical
#   epoch.sh verify       the sample on the device again with --verify (each proof checked on the host)
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
DATA=${DATA:-$WORK/data}
mkdir -p "$LOGS"
bin=$SRC/zig-out/bin/cuda-epoch

timed() {
  local name=$1; shift
  echo "== $name: cuda-epoch $* (log $LOGS/$name.log)"
  nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 500 > "$LOGS/$name.smi.csv" &
  local smi=$!
  /usr/bin/time -v "$bin" "$@" > "$LOGS/$name.log" 2>&1
  local rc=$?
  kill $smi 2>/dev/null; wait $smi 2>/dev/null
  local util
  util=$(awk -F', ' '{gsub(/ %/,"",$3); s+=$3; n++} END {if (n) printf "%.0f", s/n}' "$LOGS/$name.smi.csv")
  grep -E "^(epoch|standalone|CUDA|  L )|error|Error" "$LOGS/$name.log" | tail -25
  echo "   mean GPU utilization ${util}%; host peak RSS $(grep 'Maximum resident' "$LOGS/$name.log" | awk '{print $NF}') kB; exit $rc"
  return $rc
}

same() {
  if diff -rq "$1" "$2" > /dev/null; then echo "   BYTE-IDENTICAL: $1 = $2 ($(ls "$1" | wc -l) files)"; else echo "   DIFFER: $1 vs $2"; diff -rq "$1" "$2" | head; return 1; fi
}

case ${1:-} in
  check)
    E=${2:-100}
    for kind in dev cpu; do
      d=$WORK/epoch-$kind; rm -rf "$d"; mkdir -p "$d"; ln -s "$DATA/epoch/blocks" "$d/blocks"; ln -s "$DATA/epoch/undo" "$d/undo"
    done
    timed epoch-dev "$DATA/headers.bin" "$WORK/epoch-dev" "$E" "$DATA/chain.sbchain" || exit 1
    timed epoch-cpu "$DATA/headers.bin" "$WORK/epoch-cpu" "$E" "$DATA/chain.sbchain" --mock || exit 1
    same "$WORK/epoch-dev/proofs" "$WORK/epoch-cpu/proofs" && cmp "$WORK/epoch-dev/set-$E.bin" "$WORK/epoch-cpu/set-$E.bin" && echo "   coin sets equal"
    ;;
  sample)
    d=$WORK/sample-dev; rm -rf "$d"; mkdir -p "$d"; ln -s "$DATA/sample/blocks" "$d/blocks"; ln -s "$DATA/sample/undo" "$d/undo"
    timed sample-dev "$DATA/headers.bin" "$d" - "$DATA/chain.sbchain" --heights "$DATA/sample/heights.txt"
    ;;
  sample-check)
    max=${SAMPLE_CPU_MAX_L:-19}
    awk -v m="$max" '$2 ~ /^[0-9]+$/ && $2 <= m {print $1}' "$LOGS/sample-dev.log" > "$WORK/sample-small.txt"
    d=$WORK/sample-cpu; rm -rf "$d"; mkdir -p "$d"; ln -s "$DATA/sample/blocks" "$d/blocks"; ln -s "$DATA/sample/undo" "$d/undo"
    timed sample-cpu "$DATA/headers.bin" "$d" - "$DATA/chain.sbchain" --heights "$WORK/sample-small.txt" --mock || exit 1
    for f in "$d"/proofs/*.sbblock; do cmp "$f" "$WORK/sample-dev/proofs/$(basename "$f")" || { echo "   DIFFER: $(basename "$f")"; exit 1; }; done
    echo "   BYTE-IDENTICAL: $(ls "$d/proofs" | wc -l) sample proofs (L <= $max) = device"
    ;;
  verify)
    d=$WORK/sample-verify; rm -rf "$d"; mkdir -p "$d"; ln -s "$DATA/sample/blocks" "$d/blocks"; ln -s "$DATA/sample/undo" "$d/undo"
    timed sample-verify "$DATA/headers.bin" "$d" - "$DATA/chain.sbchain" --heights "$DATA/sample/heights.txt" --verify
    ;;
  *) echo "usage: epoch.sh check [E] | sample | sample-check | verify"; exit 2 ;;
esac
