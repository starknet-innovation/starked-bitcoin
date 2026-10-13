#!/usr/bin/env bash
# The pod sequence: block 0 (test profile uniform → tiered → production), then block 400000 tiered
# production against the saved CPU proof hash. Each step stops the sequence on failure.
#   run.sh            whole sequence
#   run.sh <step>     one step: small-test-uniform | small-test-tiered | small-prod-uniform | small-prod-tiered | large-prod-tiered
#                     | large-prod-tiered-hostlogup (A/B: the first version, LogUp on the host)
#                     | large-prod-tiered-hostwitness | xl-970347-hostwitness (A/B: every column built and uploaded by the host)
# LogUp and the witness of block_sha, block_b2s and tree 0 run on the device by default;
# EXTRA="--host-logup" (or "--host-witness") run.sh <step> runs any step with host LogUp (host witness).
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
  # shellcheck disable=SC2086
  set -- "$@" ${EXTRA:-}
  echo "== $name: cuda-prove $* (log $log)"
  # Device memory, sampled every 200 ms while the step runs.
  nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 200 > "$LOGS/$name.smi.csv" &
  local smi=$!
  /usr/bin/time -v "$bin" "$@" > "$log" 2>&1
  local rc=$?
  kill $smi 2>/dev/null; wait $smi 2>/dev/null
  local peak
  peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2+0>m) m=$2+0} END {print m+0}' "$LOGS/$name.smi.csv")
  grep -E "^\[|DIFF|MISMATCH|BYTE|verify|device|planned|witness|error" "$log" | tail -30
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
    large-prod-tiered-hostlogup) step "$1" --large 400000 --profile production --size tiered --skip-cpu --cpu-sha $LARGE_SHA --cpu-len $LARGE_LEN --host-logup ;;
    large-prod-tiered-hostwitness) step "$1" --large 400000 --profile production --size tiered --skip-cpu --cpu-sha $LARGE_SHA --cpu-len $LARGE_LEN --host-witness ;;
    # 2^23 tiered, device only, against the CPU proofs made on the H100 pod (2026-10-13): end-to-end timing.
    xl-970347) step "$1" --large 970347 --profile production --size tiered --skip-cpu --cpu-sha f6ff8ac953601dea --cpu-len 1184413 --save-device "$LOGS/$1.proof" ;;
    xl-970347-hostwitness) step "$1" --large 970347 --profile production --size tiered --skip-cpu --cpu-sha f6ff8ac953601dea --cpu-len 1184413 --host-witness ;;
    xl-774628) step "$1" --large 774628 --profile production --size tiered --skip-cpu --cpu-sha c015e4b36600463a --cpu-len 1185434 --save-device "$LOGS/$1.proof" ;;
    # Any large sample (src/block/checks.zig samples_large) with the CPU reference proved on the pod:
    #   run.sh large <height> <uniform|tiered>   (2^23 tiered: ~51 GiB device, H100 80 GB)
    large) step "large-$2-$3" --large "$2" --profile production --size "$3" --save-cpu "$LOGS/large-$2-$3.cpu.proof" --save-device "$LOGS/large-$2-$3.proof" ;;
    *) echo "unknown step $1"; exit 2 ;;
  esac
}

if [ $# -gt 0 ]; then run "$@"; exit; fi
for s in small-test-uniform small-test-tiered small-prod-uniform small-prod-tiered large-prod-tiered; do run "$s"; done
echo "== RUN DONE =="
