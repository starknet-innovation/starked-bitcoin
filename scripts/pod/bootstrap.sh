#!/usr/bin/env bash
# Pod bootstrap for the resident CUDA block prover (docs/design/gpu-cuda.md § Running on a pod).
#   bootstrap.sh <commit>            clone github.com/starknet-innovation/starked-bitcoin (with submodules) at <commit>
#   bootstrap.sh --tarball <file>    use a shipped working tree instead (tar of the repo incl. third_party/stwo-zig)
# Installs Zig 0.15.2 and the build tools, then builds zig-out/bin/cuda-prove against the real CUDA archive
# (NO_BUILD=1 skips that build: cuda-pack / cuda-widenode link stwo-zig's circuit archive instead).
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
mkdir -p "$LOGS"
exec > >(tee -a "$LOGS/bootstrap.log") 2>&1

echo "== host =="
nvidia-smi --query-gpu=name,compute_cap,driver_version,memory.total --format=csv,noheader
nvcc --version | tail -1
nproc; free -g | head -2

echo "== deps =="
apt-get update -qq >/dev/null
apt-get install -y -qq build-essential git python3 xz-utils curl time >/dev/null
ls -l "$CUDA_HOME/lib64/libcudart.so" "$CUDA_HOME/lib64/stubs/libcuda.so"

echo "== zig 0.15.2 =="
if ! /workspace/zig/zig version 2>/dev/null | grep -q '^0.15.2$'; then
  case "$(uname -m)" in
    x86_64) tarball=zig-x86_64-linux-0.15.2.tar.xz; sum=02aa270f183da276e5b5920b1dac44a63f1a49e55050ebde3aecc9eb82f93239 ;;
    aarch64) tarball=zig-aarch64-linux-0.15.2.tar.xz; sum=958ed7d1e00d0ea76590d27666efbf7a932281b3d7ba0c6b01b0ff26498f667f ;;
    *) echo "unsupported arch $(uname -m)"; exit 1 ;;
  esac
  curl -fsSL -o "/tmp/$tarball" "https://ziglang.org/download/0.15.2/$tarball"
  echo "$sum  /tmp/$tarball" | sha256sum -c -
  rm -rf /workspace/zig && mkdir -p /workspace/zig
  tar xf "/tmp/$tarball" -C /workspace/zig --strip-components=1
fi
zig version

echo "== source =="
if [ "${1:-}" = "--tarball" ]; then
  rm -rf "$SRC" && mkdir -p "$SRC" && tar xf "$2" -C "$SRC"
  # The build identity reads `git rev-parse HEAD` and hashes untracked files (stwo-zig
  # build_support/build_identity.zig), so the shipped trees become one-commit repos.
  git config --global --add safe.directory '*'
  git config --global user.email pod@local && git config --global user.name pod
  (cd "$SRC/third_party/stwo-zig" && rm -rf .git && git init -q && git add -A && git commit -q -m "stwo-zig (tarball)")
  (cd "$SRC" && rm -rf .git && git init -q && echo third_party/stwo-zig/ >> .git/info/exclude && git add -A && git commit -q -m "starked-bitcoin (tarball)")
else
  commit=${1:?usage: bootstrap.sh <commit> | --tarball <file>}
  [ -d "$SRC/.git" ] || git clone -q --recurse-submodules https://github.com/starknet-innovation/starked-bitcoin "$SRC"
  git -C "$SRC" fetch -q origin && git -C "$SRC" checkout -q "$commit" && git -C "$SRC" submodule update -q --init --recursive
  git -C "$SRC" log --oneline -1
fi
test -f "$SRC/third_party/stwo-zig/scripts/cuda_build.py" || { echo "stwo-zig submodule missing"; exit 1; }

if [ -n "${NO_BUILD:-}" ]; then echo "== BOOTSTRAP DONE (no build) =="; exit 0; fi
echo "== build (archive: stwo-zig runtime + our 16 kernels for $CUDA_ARCH; first build is the slow part) =="
cd "$SRC"
time zig build cuda-archive-plan -Dcuda=true -Dcuda-arch="$CUDA_ARCH"
# shellcheck disable=SC2086
time zig build install $CUDA_FLAGS
ls -l zig-out/bin/cuda-prove
echo "== BOOTSTRAP DONE =="
