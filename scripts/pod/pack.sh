#!/usr/bin/env bash
# Leaf-packing spike on the pod (src/gpu/cuda/pack.zig, docs/design/block-rec.md § Leaf packing).
#   pack.sh build              stwo-zig's circuit archive (its own build), then cuda-pack linked to it
#   pack.sh run <k>... [--cpu] k block proofs from $WORK/epoch-pack/proofs in one circuit, proved on the GPU
# Run bootstrap.sh first (Zig, deps, source). The proofs come from `chainproof prove-epoch` (shipped).
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
mkdir -p "$LOGS"
cd "$SRC"
case ${1:-} in
  build)
    set -e
    st=$SRC/third_party/stwo-zig
    # The same NVIDIA inputs as CUDA_FLAGS, under stwo-zig's own option names.
    (cd "$st" && time zig build benchmark-circuit-cuda-resident -Doptimize=ReleaseFast \
      -Dcuda-nvcc=$CUDA_HOME/bin/nvcc -Dcuda-host-cxx=/usr/bin/g++ \
      -Dcuda-host-runtime=$LIBDIR/libstdc++.so.6 -Dcuda-host-unwind-runtime=$LIBDIR/libgcc_s.so.1 \
      -Dcuda-ar=/usr/bin/ar -Dcuda-home=$CUDA_HOME -Dcuda-library-dir=$CUDA_HOME/lib64 -Dcuda-arch=$CUDA_ARCH -Dcuda-build-jobs=$(nproc))
    lib=$(ls -t $(find "$st/.zig-cache" -path '*stwo-circuit-cuda-runtime*' -name libstwo_cuda_kernels.a) | head -1)
    echo "circuit archive: $lib"
    # Sanity: stwo-zig's own resident benchmark (checks its proof against the Rust digest).
    (cd "$st" && ./zig-out/bin/stwo-circuit-cuda-resident-bench fibonacci internal vectors/circuit/r7/prove_profiles.json | head -3)
    # shellcheck disable=SC2086
    time zig build cuda-pack $CUDA_FLAGS -Dcuda-circuit-archive="$(dirname "$lib")"
    ls -l zig-out/bin/cuda-pack
    echo "== PACK BUILD DONE ==" ;;
  run)
    shift
    name=pack-$(echo "$@" | tr ' ' '_' | tr -d '-')
    log=$LOGS/$name.log
    nvidia-smi --query-gpu=timestamp,memory.used,utilization.gpu --format=csv,noheader -lms 200 > "$LOGS/$name.smi.csv" &
    smi=$!
    /usr/bin/time -v zig-out/bin/cuda-pack "$WORK/epoch-pack" 0 "$@" > "$log" 2>&1
    rc=$?
    kill $smi 2>/dev/null; wait $smi 2>/dev/null
    peak=$(awk -F', ' '{gsub(/ MiB/,"",$2); if ($2+0>m) m=$2+0} END {print m+0}' "$LOGS/$name.smi.csv")
    grep -E "^k=|stage|rror|MISMATCH" "$log"
    echo "   nvidia-smi peak memory.used: ${peak} MiB; host peak RSS: $(grep 'Maximum resident' "$log" | awk '{print $NF}') kB; exit $rc"
    exit $rc ;;
  *) echo "usage: pack.sh build | pack.sh run <k>... [--cpu]"; exit 2 ;;
esac
