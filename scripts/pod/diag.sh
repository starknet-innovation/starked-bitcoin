#!/usr/bin/env bash
# First-failure triage on the pod (cheap; no proving).
#   diag.sh              device and toolchain facts, archive identity, link of cuda-prove
set -uo pipefail
here=$(cd "$(dirname "$0")" && pwd)
source "$here/env.sh"
nvidia-smi
nvcc --version | tail -2
cd "$SRC"
ldd zig-out/bin/cuda-prove | grep -E "cuda|stdc|gcc" || true
cat zig-out/cuda-archive-plan.json 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print('archive plan:', d['frontend'], 'SMs', d['target_sms'], 'AOT sources', d['aot_source_count'])" || true
# pass 1 only: upload, LDE and Merkle of the preprocessed and main trees vs the CPU roots
zig-out/bin/cuda-prove --small 0 --profile test --pass1-only 2>&1 | tail -8
