#!/usr/bin/env bash
# A coin-set pass on a pod (docs/design/gpu-cuda.md § Set pass): segments with cuda-set (our archive),
# the tree with cuda-set-tree (stwo-zig's circuit archive), both resumable.
#   prove_set.sh build                                  cuda-set, cuda-set-tree (circuit archive reused if built), chainproof (CPU)
#   prove_set.sh check <set.bin> <ch.bin> <logs>        segment 0 on the device and the CPU: byte-identical, verified
#   prove_set.sh stages <set.bin> <ch.bin> <logs> [n] [jobs]
#                                                       the first n segments (default 20) with --stages (H2D bytes and
#                                                       device stage times), device witness; then 4 with --host-witness (A/B)
#   prove_set.sh run <name> <set.bin> <ch.bin> <logs> [cuda-set options]
#                                                       every segment, then the tree and pass.bin, verified
# <ch.bin>: `chainproof set-challenge <dir>:<to>[:<from>:<prev-set.bin>] <ch.bin>` (where the epoch's
# forest and set files are). <logs>: twelve comma-separated component logs (the arena must fit the device:
# see the doc's table). Outputs on the persistent volume: $WORK/<name>/{challenge.bin,seg/,stree/,setvk.bin,pass.bin},
# and in $LOGS <name>.seg.log / <name>.tree.log (stderr), <name>.tree.lines, <name>.status, <name>.smi.csv.
# Detach a run from the ssh session:
#   nohup scripts/pod/prove_set.sh run s935000 $DATA/set-935000.bin $DATA/ch-945000.bin 22,8,6,15,21,20,22,22,22,21,22,22 > /dev/null 2>&1 &
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
mkdir -p "$LOGS"
cd "$SRC"
st=$SRC/third_party/stwo-zig
archive() {
  local found
  found=$(find "$st/.zig-cache" -path '*stwo-circuit-cuda-runtime*' -name libstwo_cuda_kernels.a 2>/dev/null)
  [ -n "$found" ] && ls -t $found | head -1
  return 0
}
cmd=${1:?usage: prove_set.sh build | check <set.bin> <ch.bin> <logs> | run <name> <set.bin> <ch.bin> <logs> [options]}
shift
case "$cmd" in
build)
  set -e
  time zig build cuda-archive-plan -Dcuda=true -Dcuda-arch="$CUDA_ARCH"
  # shellcheck disable=SC2086
  time zig build install $CUDA_FLAGS            # cuda-set (and cuda-prove, cuda-epoch) on our archive
  if [ -z "$(archive)" ]; then
    (cd "$st" && time zig build benchmark-circuit-cuda-resident -Doptimize=ReleaseFast \
      -Dcuda-nvcc=$CUDA_HOME/bin/nvcc -Dcuda-host-cxx=/usr/bin/g++ \
      -Dcuda-host-runtime=$LIBDIR/libstdc++.so.6 -Dcuda-host-unwind-runtime=$LIBDIR/libgcc_s.so.1 \
      -Dcuda-ar=/usr/bin/ar -Dcuda-home=$CUDA_HOME -Dcuda-library-dir=$CUDA_HOME/lib64 -Dcuda-arch=$CUDA_ARCH -Dcuda-build-jobs=$(cpus))
  fi
  lib=$(archive)
  echo "circuit archive: $lib"
  # shellcheck disable=SC2086
  time zig build cuda-set-tree $CUDA_FLAGS -Dcuda-circuit-archive="$(dirname "$lib")"
  time zig build -Doptimize=ReleaseFast -p zig-out-cpu
  ls -l zig-out/bin/cuda-set zig-out/bin/cuda-set-tree zig-out-cpu/bin/chainproof
  echo "== SET BUILD DONE =="
  ;;
check)
  set -e
  set_bin=${1:?set.bin}; ch=${2:?ch.bin}; logs=${3:?logs}
  dir=$WORK/set-check-$(date -u +%Y%m%dT%H%M%S)
  # Segment 0: device proof, CPU proof of the same witness, byte comparison, host verification.
  /usr/bin/time -v zig-out/bin/cuda-set "$set_bin" "$dir" --challenge "$ch" --logs "$logs" --first 1 --cpu-check 1 --verify --jobs 1 2>&1 | tee "$LOGS/set-check.log" | grep -vE "^\s"
  grep -q "byte-identical" "$LOGS/set-check.log" && echo "== SET CHECK OK: $dir/seg/0.sbseg ==" || { echo "== SET CHECK FAILED =="; exit 1; }
  ;;
stages)
  set -e
  set_bin=${1:?set.bin}; ch=${2:?ch.bin}; logs=${3:?logs}; n=${4:-20}; jobs=${5:-6}
  dir=$WORK/set-stages-$(date -u +%Y%m%dT%H%M%S)
  zig-out/bin/cuda-set "$set_bin" "$dir/device" --challenge "$ch" --logs "$logs" --first "$n" --jobs "$jobs" --stages --cpu-check 1000000 2>&1 | tee "$LOGS/set-stages.log" | grep -E "^[0-9]|stages|SEGMENTS|byte-identical|MISMATCH"
  zig-out/bin/cuda-set "$set_bin" "$dir/host" --challenge "$ch" --logs "$logs" --first 4 --jobs "$jobs" --stages --host-witness 2>&1 | tee "$LOGS/set-stages-host.log" | grep -E "^[0-9]|stages|SEGMENTS"
  # The two runs prove the same segments: the files must be equal.
  for f in "$dir"/host/seg/*.sbseg; do cmp -s "$f" "$dir/device/seg/$(basename "$f")" || { echo "== DEVICE/HOST WITNESS FILES DIFFER: $f =="; exit 1; }; done
  echo "== SET STAGES OK: $dir (device-witness and host-witness segment files equal) =="
  ;;
run)
  name=${1:?name}; set_bin=${2:?set.bin}; ch=${3:?ch.bin}; logs=${4:?logs}
  shift 4
  dir=$WORK/$name
  mkdir -p "$dir"
  date -u +"START %FT%TZ $set_bin logs $logs $*" >> "$LOGS/$name.status"
  nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 1000 >> "$LOGS/$name.smi.csv" &
  smi=$!
  # Every 500th segment is also proved on the CPU (byte-identical or the run stops).
  /usr/bin/time -v zig-out/bin/cuda-set "$set_bin" "$dir" --challenge "$ch" --logs "$logs" --cpu-check 500 "$@" 2>> "$LOGS/$name.seg.log"
  rc=$?
  if [ $rc = 0 ]; then
    /usr/bin/time -v zig-out/bin/cuda-set-tree "$dir" --jobs "$(( $(cpus) > 8 ? 8 : $(cpus) ))" --cpu-check 1000 >> "$LOGS/$name.tree.lines" 2>> "$LOGS/$name.tree.log"
    rc=$?
  fi
  kill $smi 2>/dev/null; wait $smi 2>/dev/null
  {
    date -u +"END %FT%TZ exit $rc"
    echo "segments $(ls "$dir/seg" | wc -l), tree proofs $(ls "$dir/stree" 2>/dev/null | wc -l); $(grep -h "SEGMENTS DONE\|TREE DONE\|VERIFIED" "$LOGS/$name.seg.log" "$LOGS/$name.tree.log" | tail -3 | tr '\n' ' ')"
  } >> "$LOGS/$name.status"
  exit $rc
  ;;
*) echo "unknown command $cmd"; exit 2 ;;
esac
