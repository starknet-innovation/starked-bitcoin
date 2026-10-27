#!/usr/bin/env bash
# Set-pass proofs on the small test chain (set-pass steps 4–5): each epoch's start and end set proved
# under that epoch's challenge, then verify-chain with --set-proofs (no set files read) against the
# set-file verification; a pass under another epoch's challenge must be rejected.
set -uo pipefail
cd "$(dirname "$0")/.."
B=zig-out/bin/chainproof; V=data/store/mainnet-q70-p26-l20.vk; C=data/store/mainnet-to-970734.sbchain; T=data/test-chain
LOGS=11,8,6,6,11,10,12,11,12
E3="$T/e3:3"; E8="$T/e8:8:4:$T/e3/set-3.bin"; E15="$T/e15:15:9:$T/e8/set-8.bin"
run() { echo "== $*"; /usr/bin/time -l "$@" 2>&1 | grep -vE "^ {6,}[0-9]" | grep -v "^$" | tail -5; }
run $B prove-set $T/e3/set-3.bin $E3 $T/e3/pass-3 --logs $LOGS
run $B prove-set $T/e3/set-3.bin $E8 $T/e8/pass-3 --logs $LOGS
run $B prove-set $T/e8/set-8.bin $E8 $T/e8/pass-8 --logs $LOGS
run $B prove-set $T/e8/set-8.bin $E15 $T/e15/pass-8 --logs $LOGS
run $B prove-set $T/e15/set-15.bin $E15 $T/e15/pass-15 --logs $LOGS
echo "== verify-chain (set files)"; $B verify-chain $V $C $T/out --unpinned $E3 $E8 $E15 2>&1 | grep -E "VERIFIED|balanced|hash_serialized|amount|REJECTED|error"
echo "== verify-chain --set-proofs (must VERIFY)"; $B verify-chain $V $C $T/out --unpinned --set-proofs $E3 $E8 $E15 2>&1 | grep -E "VERIFIED|balanced|hash_serialized|amount|REJECTED|error"
echo "== verify-chain --set-proofs, pinned only (must be REJECTED: test set VK)"; $B verify-chain $V $C $T/out --set-proofs $E3 $E8 $E15 2>&1 | grep -E "set VK|REJECTED|error" | head -3
echo "== the set after 8 proved under epoch 9..15's challenge, given as epoch 4..8's (must be REJECTED)"
mv $T/e8/pass-8 $T/e8/pass-8.good; cp -r $T/e15/pass-8 $T/e8/pass-8
$B verify-chain $V $C $T/out --unpinned --set-proofs $E3 $E8 $E15 2>&1 | grep -E "VERIFIED|REJECTED|error" | head -3
rm -rf $T/e8/pass-8; mv $T/e8/pass-8.good $T/e8/pass-8
echo "SET PASS TEST DONE"
