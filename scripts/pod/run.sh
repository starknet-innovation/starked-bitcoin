#!/usr/bin/env bash
# The pod sequence: block 0 (test profile uniform → tiered → production), then block 400000 tiered
# production against the saved CPU proof hash. Each step stops the sequence on failure.
#   run.sh            whole sequence
#   run.sh <step>     one step: small-test-uniform | small-test-tiered | small-prod-uniform | small-prod-tiered | large-prod-tiered
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
mkdir -p "$LOGS"
cd "$SRC"
bin=$SRC/zig-out/bin/cuda-prove

# Saved CPU proof of block 400000, tiered, production profile (compact storage + discard_mains).
LARGE_SHA=cbcf7026134f9a71
LARGE_LEN=1131354

step() {
  local name=$1; shift
  local log=$LOGS/$name.log
  echo "== $name: cuda-prove $* (log $log)"
  # Device memory, sampled every 200 ms while the step runs.
  nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 200 > "$LOGS/$name.smi.csv" &
  local smi=$!
  /usr/bin/time -v "$bin" "$@" > "$log" 2>&1
  local rc=$?
  kill $smi 2>/dev/null; wait $smi 2>/dev/null
  local peak
  peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2>m) m=$2} END {print m+0}' "$LOGS/$name.smi.csv")
  grep -E "^\[|DIFF|MISMATCH|BYTE|verify|device|planned|error" "$log" | tail -25
  echo "   nvidia-smi peak memory.used: ${peak} MiB; host peak RSS: $(grep 'Maximum resident' "$log" | awk '{print $NF}') kB; exit $rc"
  if [ $rc -ne 0 ]; then echo "== $name FAILED (see $log)"; exit $rc; fi
}

run() {
  case $1 in
    small-test-uniform) step "$1" --small 0 --profile test --size uniform --save-device "$LOGS/$1.proof" ;;
    small-test-tiered) step "$1" --small 0 --profile test --size tiered --min-log 12 --save-device "$LOGS/$1.proof" ;;
    small-prod-uniform) step "$1" --small 0 --profile production --size uniform ;;
    small-prod-tiered) step "$1" --small 0 --profile production --size tiered --min-log 12 ;;
    large-prod-tiered) step "$1" --large 400000 --profile production --size tiered --skip-cpu --cpu-sha $LARGE_SHA --cpu-len $LARGE_LEN --save-device "$LOGS/$1.proof" ;;
    *) echo "unknown step $1"; exit 2 ;;
  esac
}

if [ $# -gt 0 ]; then run "$1"; exit; fi
for s in small-test-uniform small-test-tiered small-prod-uniform small-prod-tiered large-prod-tiered; do run "$s"; done
echo "== RUN DONE =="
