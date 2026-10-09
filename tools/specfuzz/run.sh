#!/bin/sh
# Differential fuzzing of the Lean header and block specs against Bitcoin Core (core_cases.cpp,
# core_block_cases.cpp).
# Usage: tools/specfuzz/run.sh <core src dir> <seed> <cases per kind>
# <core src dir>: a checkout of bitcoin/bitcoin's src/ (e.g. a sparse clone in data/core-src/src).
set -e
CORE="$1"; SEED="$2"; N="$3"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="$ROOT/data/specfuzz"
mkdir -p "$OUT"
: > "$OUT/bitcoin-build-config.h"
( cd "$CORE" && c++ -std=c++20 -O2 -I. -I"$OUT" "$ROOT/tools/specfuzz/core_cases.cpp" pow.cpp chain.cpp \
    arith_uint256.cpp uint256.cpp util/strencodings.cpp crypto/hex_base.cpp -o "$OUT/core_cases" )
( cd "$CORE" && c++ -std=c++20 -O2 -I. -I"$OUT" "$ROOT/tools/specfuzz/core_block_cases.cpp" consensus/merkle.cpp \
    consensus/tx_check.cpp primitives/transaction.cpp script/script.cpp uint256.cpp util/strencodings.cpp \
    crypto/hex_base.cpp crypto/sha256.cpp hash.cpp support/cleanse.cpp crypto/ripemd160.cpp crypto/hmac_sha512.cpp \
    crypto/sha512.cpp -o "$OUT/core_block_cases" )
{ "$OUT/core_cases" "$SEED" "$N"; "$OUT/core_block_cases" "$SEED" "$N"; } > "$OUT/core-$SEED.tsv"
( cd "$ROOT/lean" && lake env lean --run SpecCases.lean < "$OUT/core-$SEED.tsv" > "$OUT/lean-$SEED.tsv" 2>/dev/null )
echo "Core commit: $(git -C "$CORE" rev-parse HEAD 2>/dev/null || echo unknown)"
python3 "$ROOT/tools/specfuzz/compare.py" "$OUT/core-$SEED.tsv" "$OUT/lean-$SEED.tsv"
