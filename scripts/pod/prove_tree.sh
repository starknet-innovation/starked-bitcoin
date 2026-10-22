#!/usr/bin/env bash
# An epoch's recursion forest with wide nodes on a pod with cuda-epoch-tree, resumable
# (src/gpu/cuda/epoch_tree.zig, docs/design/block-rec.md).
#   prove_tree.sh build                       stwo-zig's circuit archive (reused if built), then cuda-epoch-tree
#   prove_tree.sh <name> <from> <to> [opts]   cuda-epoch-tree options, e.g. --jobs 6 --cpu-check 1000
# Input: the epoch's block proofs in $DATA/proofs/<h>.sbblock, and for the assembly $DATA/headers.bin
# and $DATA/chain.sbchain. Outputs on the persistent volume: $WORK/<name>/treevk.bin,
# tree/<k>-<x>.sbproof and, once every proof is made, the forest forestk-<to>.bin (chainproof
# prove-epoch-wide, which then has nothing left to prove), with SET_DIGESTS the epoch root
# epochroot-<to>.bin and rootvk.bin (prove-epoch-root, CPU), and in $LOGS <name>.log (stderr: levels, the end),
# <name>.lines (one line per proof), <name>.status (START, END, exit code, peaks) and <name>.smi.csv.
# A stopped run started again proves only what is missing. Detach it from the ssh session:
#   nohup scripts/pod/prove_tree.sh t945000 935001 945000 --jobs 6 > /dev/null 2>&1 &
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
if [ "${1:-}" = build ]; then
  set -e
  if [ -z "$(archive)" ]; then
    (cd "$st" && time zig build benchmark-circuit-cuda-resident -Doptimize=ReleaseFast \
      -Dcuda-nvcc=$CUDA_HOME/bin/nvcc -Dcuda-host-cxx=/usr/bin/g++ \
      -Dcuda-host-runtime=$LIBDIR/libstdc++.so.6 -Dcuda-host-unwind-runtime=$LIBDIR/libgcc_s.so.1 \
      -Dcuda-ar=/usr/bin/ar -Dcuda-home=$CUDA_HOME -Dcuda-library-dir=$CUDA_HOME/lib64 -Dcuda-arch=$CUDA_ARCH -Dcuda-build-jobs=$(cpus))
  fi
  lib=$(archive)
  echo "circuit archive: $lib"
  # shellcheck disable=SC2086
  time zig build cuda-epoch-tree $CUDA_FLAGS -Dcuda-circuit-archive="$(dirname "$lib")"
  # chainproof (CPU only) for the forest's assembly.
  time zig build -Doptimize=ReleaseFast -p zig-out-cpu
  ls -l zig-out/bin/cuda-epoch-tree zig-out-cpu/bin/chainproof
  echo "== TREE BUILD DONE =="
  exit 0
fi
name=${1:?usage: prove_tree.sh build | prove_tree.sh <name> <from> <to> [options]}
from=${2:?from}
to=${3:?to}
shift 3
dir=$WORK/$name
mkdir -p "$dir"
ln -sfn "$DATA/proofs" "$dir/proofs"
log=$LOGS/$name.log
[ -s "$log" ] && mv "$log" "$log.$(date -u +%Y%m%dT%H%M%S)"
date -u +"START %FT%TZ $from..$to $*" >> "$LOGS/$name.status"
nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 1000 >> "$LOGS/$name.smi.csv" &
smi=$!
/usr/bin/time -v "$SRC/zig-out/bin/cuda-epoch-tree" "$dir" "$from" "$to" "$@" >> "$LOGS/$name.lines" 2> "$log"
rc=$?
if [ $rc = 0 ]; then
  # The assembly needs the epoch's start, not the previous set (only verification reads it).
  /usr/bin/time -v "$SRC/zig-out-cpu/bin/chainproof" prove-epoch-wide "$DATA/headers.bin" "$dir" "$to" "$DATA/chain.sbchain" --from "$from" not-read >> "$log" 2>&1
  rc=$?
fi
# The epoch root (one proof for the epoch), on the CPU: SET_DIGESTS="<prev hex|-> <fin hex>".
if [ $rc = 0 ] && [ -n "${SET_DIGESTS:-}" ]; then
  # shellcheck disable=SC2086
  /usr/bin/time -v "$SRC/zig-out-cpu/bin/chainproof" prove-epoch-root "$DATA/headers.bin" "$dir" "$to" "$DATA/chain.sbchain" --from "$from" not-read --set-digests $SET_DIGESTS >> "$log" 2>&1
  rc=$?
fi
kill $smi 2>/dev/null; wait $smi 2>/dev/null
util=$(awk -F', ' '{gsub(/ %/,"",$3); s+=$3; n++} END {if (n) printf "%.1f", s/n}' "$LOGS/$name.smi.csv")
peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2+0>m) m=$2+0} END {print m}' "$LOGS/$name.smi.csv")
{
  date -u +"END %FT%TZ exit $rc"
  echo "tree proofs $(ls "$dir/tree" | wc -l); mean GPU util ${util}%; peak GPU memory ${peak} MiB; host peak RSS $(grep 'Maximum resident' "$log" | awk '{print $NF}') kB"
} >> "$LOGS/$name.status"
exit $rc
