# Shared settings for the pod scripts (sourced). Image: runpod/pytorch:1.0.2-cu1281-torch280-ubuntu2404.
export CUDA_HOME=${CUDA_HOME:-/usr/local/cuda-12.8}
# Zig, the source and an epoch's inputs go on the container disk (local, fast; /workspace can be NFS,
# which refuses chown and is slow for many small files). What a run produces (proofs, sets, logs) goes
# to /workspace, the persistent volume: it survives a container restart, not a host failure, so
# scripts/pod/follow.sh also copies the proofs off the pod as they come.
export ZIG_DIR=${ZIG_DIR:-/root/zig}
export PATH=$CUDA_HOME/bin:$ZIG_DIR:$PATH
export WORK=${WORK:-/workspace}
export SRC=${SRC:-/root/starked-bitcoin}
export DATA=${DATA:-/root/data}
export LOGS=${LOGS:-$WORK/logs}
# SM targets compiled into the archive and accepted by the session: 89 = RTX 4090 / L40S,
# 80 = A100, 90 = H100 / H200. One target builds ~3x faster; set CUDA_ARCH=sm_89 etc. to match the pod.
export CUDA_ARCH=${CUDA_ARCH:-sm_80,sm_89,sm_90}
# The CPUs the container may use: its cgroup quota (cpu.max), which `nproc` does not see.
cpus() {
  local q p
  read -r q p < /sys/fs/cgroup/cpu.max 2>/dev/null || { nproc; return; }
  if [ "$q" = max ]; then nproc; else echo $(( (q + p - 1) / p )); fi
}
export LIBDIR=/usr/lib/x86_64-linux-gnu
[ "$(uname -m)" = aarch64 ] && LIBDIR=/usr/lib/aarch64-linux-gnu
# stwo-zig's NVIDIA build inputs (third_party/stwo-zig/src/integrations/circuit_cuda/README.md).
export CUDA_FLAGS="-Dcuda=true -Doptimize=ReleaseFast \
 -Dcuda-nvcc=$CUDA_HOME/bin/nvcc -Dcuda-host-cxx=/usr/bin/g++ \
 -Dcuda-host-runtime=$LIBDIR/libstdc++.so.6 -Dcuda-host-unwind-runtime=$LIBDIR/libgcc_s.so.1 \
 -Dcuda-ar=/usr/bin/ar -Dcuda-home=$CUDA_HOME -Dcuda-library-dir=$CUDA_HOME/lib64 \
 -Dcuda-driver-dir=$CUDA_HOME/lib64/stubs -Dcuda-arch=$CUDA_ARCH -Dcuda-jobs=$(cpus)"
export LD_LIBRARY_PATH=$CUDA_HOME/lib64:${LD_LIBRARY_PATH:-}
