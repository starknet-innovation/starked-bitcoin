#!/usr/bin/env bash
# The GPU set-pass drivers' plumbing on any host (no GPU; docs/design/gpu-cuda.md § Set pass):
# `cuda-set --mock` (CPU proofs through the GPU driver's pipeline) and `cuda-set-tree --cpu-prover` must
# write the same files as `chainproof prove-set` (segments, setvk.bin, pass.bin, byte for byte), and
# `chainproof verify-set` must accept the result. Test strength, on the test chain's epoch 4..8 (the set
# after block 8 under its challenge) and on the set after block 170 under the testing challenge (several
# segments: a real tree). Needs `zig build install -Dcuda=true` (stub-linked binaries).
#   scripts/test_cuda_set_mock.sh <scratch-dir>
set -euo pipefail
cd "$(dirname "$0")/.."
W=${1:?usage: test_cuda_set_mock.sh <scratch-dir>}
B=zig-out/bin
T=data/test-chain
LOGS=10,8,6,6,10,8,11,10,11,10,12,13
E8="$T/e8:8:4:$T/e3/set-3.bin"
rm -rf "$W" && mkdir -p "$W"
same() { cmp -s "$1" "$2" && echo "  same: $(basename "$1")" || { echo "  DIFFERENT: $1 $2"; exit 1; }; }

echo "== test chain, set after 8, epoch 4..8's challenge"
$B/chainproof set-challenge "$E8" "$W/ch8.bin"
$B/chainproof prove-set $T/e8/set-8.bin "$E8" "$W/cpu8" --test-strength --logs $LOGS 2>&1 | tail -2
$B/cuda-set $T/e8/set-8.bin "$W/gpu8" --challenge "$W/ch8.bin" --test-strength --logs $LOGS --mock 2>&1 | tail -2
$B/cuda-set-tree "$W/gpu8" --test-strength --cpu-prover 2>&1 | tail -3
for f in "$W"/cpu8/seg/*.sbseg; do same "$f" "$W/gpu8/seg/$(basename "$f")"; done
same "$W/cpu8/setvk.bin" "$W/gpu8/setvk.bin"
same "$W/cpu8/pass.bin" "$W/gpu8/pass.bin"
$B/chainproof verify-set "$W/gpu8" "$E8" --unpinned 2>&1 | grep -E "VERIFIED|coins|error"

echo "== set after 170, testing challenge, several segments"
$B/cuda-set data/epoch/set-170.bin "$W/s170" --testing-challenge --test-strength --logs $LOGS --mock --jobs 3 2>&1 | tail -2
# A stopped run resumes: drop one segment and one tree proof, run both again.
$B/cuda-set-tree "$W/s170" --test-strength --cpu-prover --jobs 3 > "$W/s170.lines" 2> "$W/s170.log"; tail -3 "$W/s170.log"
cp "$W/s170/pass.bin" "$W/pass170.first"
rm "$W/s170/seg/1.sbseg" "$W/s170/stree/0-2.sbproof" "$W/s170/pass.bin"
$B/cuda-set data/epoch/set-170.bin "$W/s170" --testing-challenge --test-strength --logs $LOGS --mock 2>&1 | tail -1
$B/cuda-set-tree "$W/s170" --test-strength --cpu-prover 2>&1 | tail -2
same "$W/pass170.first" "$W/s170/pass.bin"
echo "CUDA SET MOCK TEST DONE"
