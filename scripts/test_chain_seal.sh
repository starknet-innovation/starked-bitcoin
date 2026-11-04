#!/usr/bin/env bash
# The chain seal on the small test chain (docs/design/chain-seal.md): one proof over the chain of three
# epochs (0..3, 4..8, 9..15) and their five set passes (scripts/test_chain_set_pass.sh first), verified;
# then three resealed tampers of the seal file, each rejected. About 4 minutes and 15 GB on an M4 Pro.
set -uo pipefail
cd "$(dirname "$0")/.."
B=zig-out/bin/chainproof; V=data/store/mainnet-q70-p26-l20.vk; C=data/store/mainnet-to-970734.sbchain; T=data/test-chain
E3="$T/e3:3"; E8="$T/e8:8:4:$T/e3/set-3.bin"; E15="$T/e15:15:9:$T/e8/set-8.bin"
run() { echo "== $*"; /usr/bin/time -l "$@" 2>&1 | grep -vE "^ {6,}[0-9]" | grep -v "^$" | tail -4; }
run $B prove-seal $V $C $T/out --unpinned $E3 $E8 $E15
echo "== verify-seal (must VERIFY)"; $B verify-seal $V $C $T/out --unpinned $E3 $E8 $E15 2>&1 | grep -E "VERIFIED|REJECTED|error|hash_serialized"
echo "== verify-seal, pinned only (must be REJECTED: test VKs)"; $B verify-seal $V $C $T/out $E3 $E8 $E15 2>&1 | grep -E "REJECTED|error" | head -2
cp $T/out/seal-15.bin $T/out/seal-15.good
python3 - "$T/out" <<'PY'
import hashlib, sys
d = sys.argv[1]; b = open(f"{d}/seal-15.good", "rb").read(); body = b[:-32]
assert hashlib.sha256(body).digest() == b[-32:]
def reseal(name, t): open(f"{d}/{name}", "wb").write(bytes(t) + hashlib.sha256(bytes(t)).digest())
t = bytearray(body); t[-100] ^= 1; reseal("seal-15.proofbyte", t)
# The end set's amount (u128 LE) in its public final state: bound by the output digest.
amt = (75000000000).to_bytes(16, "little"); j = body.find(amt); assert j > 0 and body.find(amt, j + 1) < 0
t = bytearray(body); t[j] ^= 1; reseal("seal-15.amount", t)
# The end set's Merkle root: the last 32 bytes of the last set's public part, before the proof: found
# as the 32 bytes before the proof's request text.
k = body.find(b'{"'); assert k > 32
t = bytearray(body); t[k - 32] ^= 1; reseal("seal-15.mroot", t)
PY
for x in proofbyte amount mroot; do
  cp $T/out/seal-15.$x $T/out/seal-15.bin
  echo "== tampered $x (must be REJECTED)"; $B verify-seal $V $C $T/out --unpinned $E3 $E8 $E15 2>&1 | grep -E "REJECTED|error|VERIFIED" | head -1
done
cp $T/out/seal-15.good $T/out/seal-15.bin; rm -f $T/out/seal-15.proofbyte $T/out/seal-15.amount $T/out/seal-15.mroot $T/out/seal-15.good
echo "SEAL TEST DONE"
