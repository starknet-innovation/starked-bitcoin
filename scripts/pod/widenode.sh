#!/usr/bin/env bash
# Wide node and fold-1 leaf on the pod (src/gpu/cuda/widenode.zig, docs/design/block-rec.md § Wide nodes).
#   widenode.sh build            stwo-zig's circuit archive (its own build; reused if already built), then cuda-widenode
#   widenode.sh run A <from> <k>... [--fold f] [--cpu]   leaf (k = 1) / packed (k > 1) at natural size, fold f (default 1)
#   widenode.sh run B <from> [--cpu | --cpu-node]        8 leaves <from..from+7> at the 2^24 shape + the 8-child node, fold 4
# Block proofs come from $WORK/epoch-pack/proofs/<h>.sbblock (shipped). Run bootstrap.sh first
# (NO_BUILD=1 bootstrap.sh … skips our block-prover archive, which this does not need).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
mkdir -p "$LOGS"
cd "$SRC"
st=$SRC/third_party/stwo-zig
archive() { ls -t $(find "$st/.zig-cache" -path '*stwo-circuit-cuda-runtime*' -name libstwo_cuda_kernels.a 2>/dev/null) 2>/dev/null | head -1; }
case ${1:-} in
  build)
    set -e
    if [ -z "$(archive)" ]; then
      # The same NVIDIA inputs as CUDA_FLAGS, under stwo-zig's own option names.
      (cd "$st" && time zig build benchmark-circuit-cuda-resident -Doptimize=ReleaseFast \
        -Dcuda-nvcc=$CUDA_HOME/bin/nvcc -Dcuda-host-cxx=/usr/bin/g++ \
        -Dcuda-host-runtime=$LIBDIR/libstdc++.so.6 -Dcuda-host-unwind-runtime=$LIBDIR/libgcc_s.so.1 \
        -Dcuda-ar=/usr/bin/ar -Dcuda-home=$CUDA_HOME -Dcuda-library-dir=$CUDA_HOME/lib64 -Dcuda-arch=$CUDA_ARCH -Dcuda-build-jobs=$(nproc))
      # Sanity: stwo-zig's own resident benchmark (checks its proof against the Rust digest).
      (cd "$st" && ./zig-out/bin/stwo-circuit-cuda-resident-bench fibonacci internal vectors/circuit/r7/prove_profiles.json | head -3)
    fi
    lib=$(archive)
    echo "circuit archive: $lib"
    # shellcheck disable=SC2086
    time zig build cuda-widenode $CUDA_FLAGS -Dcuda-circuit-archive="$(dirname "$lib")"
    ls -l zig-out/bin/cuda-widenode
    echo "== WIDENODE BUILD DONE ==" ;;
  run)
    shift
    exp=${1:?A or B}; shift
    name=widenode-$exp-$(echo "$@" | tr ' ' '_' | tr -d '-')
    log=$LOGS/$name.log
    echo "== $name (log $log)"
    nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 200 > "$LOGS/$name.smi.csv" &
    smi=$!
    /usr/bin/time -v zig-out/bin/cuda-widenode "$exp" "$WORK/epoch-pack" "$@" > "$log" 2>&1
    rc=$?
    kill $smi 2>/dev/null; wait $smi 2>/dev/null
    peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2+0>m) m=$2+0} END {print m+0}' "$LOGS/$name.smi.csv")
    grep -vE "^\s+stage |^\s+[A-Z].*: [0-9]" "$log" | grep -vE "^\s*$" | tail -60
    echo "   nvidia-smi peak memory.used: ${peak} MiB; host peak RSS: $(grep 'Maximum resident' "$log" | awk '{print $NF}') kB; wall $(grep 'Elapsed (wall' "$log" | awk '{print $NF}'); exit $rc"
    exit $rc ;;
  *) echo "usage: widenode.sh build | widenode.sh run A <from> <k>... [--fold f] [--cpu] | widenode.sh run B <from> [--cpu|--cpu-node]"; exit 2 ;;
esac
