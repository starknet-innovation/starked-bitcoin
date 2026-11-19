#!/bin/sh
# Mutation test of the connect-rules fuzzer: each deliberately wrong Spec/ConnectRules.lean must
# disagree with Core on some case. A mutation is applied to both formulations of a rule (so the
# equivalence theorems still build) and the `#guard` examples are removed, so only the fuzzer can
# catch it. Prints one line per mutation; restores the file at the end.
# Usage: tools/specfuzz/mutate_connect.sh <seed> <cases per kind>     (after run.sh has built the tools)
export PATH="$HOME/.elan/bin:$PATH"
SEED="$1"; N="$2"
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="$ROOT/data/specfuzz"; F="$ROOT/lean/StarkedAir/Spec/ConnectRules.lean"
cp "$F" "$F.orig"
trap 'cp "$F.orig" "$F"; rm -f "$F.orig"; ( cd "$ROOT/lean" && lake build StarkedAir.Spec.ConnectRules >/dev/null 2>&1 ); echo restored' EXIT
"$OUT/core_connect_cases" "$SEED" "$N" > "$OUT/mut-core.tsv"
run() { # name, sed expression
  cp "$F.orig" "$F"; sed -i '' "$2" "$F"
  if cmp -s "$F" "$F.orig"; then echo "$1: MUTATION DID NOT APPLY"; return; fi
  sed -i '' '/^\/-! ### Examples -\/$/,/^end StarkedAir/{/^end StarkedAir/!d;}' "$F"
  rm -f "$OUT/mut-lean.tsv"
  ( cd "$ROOT/lean" && lake build StarkedAir.Spec.ConnectRules >/dev/null 2>&1 &&
      lake env lean --run SpecCases.lean < "$OUT/mut-core.tsv" > "$OUT/mut-lean.tsv" 2>/dev/null )
  if [ ! -s "$OUT/mut-lean.tsv" ]; then echo "$1: BUILD FAILED"; return; fi
  echo "$1: $(python3 "$ROOT/tools/specfuzz/compare.py" "$OUT/mut-core.tsv" "$OUT/mut-lean.tsv" |
      grep -v MISMATCH | grep -v '^  ' | sed 's/ cases, / /;s/  */ /g' | tr '\n' ';')"
}
run "none (must show 0 mismatches)" 's/-- 2-of-3 multisig: accurate 3, legacy 20\./-- 2-of-3 multisig/'
run "height lock off by one" 's/decide (coinHeight + lock ≤ c.height)/decide (coinHeight + lock ≤ c.height + 1)/;s/(p.2 : ℤ) + (s % 2 ^ 16 : ℕ) - 1/(p.2 : ℤ) + (s % 2 ^ 16 : ℕ) - 2/'
run "height lock ignores the lock value" 's/decide (coinHeight + lock ≤ c.height)/decide (coinHeight ≤ c.height)/;s/(p.2 : ℤ) + (s % 2 ^ 16 : ℕ) - 1/(p.2 : ℤ) - 1/'
run "time lock from the coin's block, not the one before" 's/c.mtpAt (coinHeight - 1)/c.mtpAt coinHeight/;s/c.mtpAt (p.2 - 1)/c.mtpAt p.2/'
run "time unit 511 s" 's/512 \*/511 */g'
run "version 1 enforced" 's/decide (2 ≤ t.version)/decide (1 ≤ t.version)/g'
run "lock mask 15 bits" 's/sequence % 2 ^ 16/sequence % 2 ^ 15/;s/(s % 2 ^ 16 : ℕ)/(s % 2 ^ 15 : ℕ)/g'
run "type flag at bit 21" 's|/ 2 ^ 22 % 2|/ 2 ^ 21 % 2|g'
run "disable flag at bit 30" 's|/ 2 ^ 31 % 2|/ 2 ^ 30 % 2|g'
run "P2SH without the push-only test" 's/if isP2SH spent \&\& pushOnly scriptSig then sigOpsAccurate/if isP2SH spent then sigOpsAccurate/'
run "P2SH test without the last byte" 's/ \&\& s\[22\]? == some 0x87//'
run "witness script counted with the legacy rule" 's/(witness.getLast?.map sigOpsAccurate).getD 0/(witness.getLast?.map sigOps).getD 0/'
run "witness v1 counted like v0" 's/  if version = 0 then/  if version ≤ 1 then/'
run "P2SH-wrapped witness ignored" 's/match witnessProgram (lastPush scriptSig) with/match (none : Option (ℕ × Bytes)) with/'
run "OP_16 bound off by one" 's/0x51 ≤ last ∧ last ≤ 0x60 then/0x51 ≤ last ∧ last ≤ 0x5f then/'
run "coinbase pays P2SH and witness sigops" 's/if t.isCoinbase || !strict then 0 else/if !strict then 0 else/'
run "flags ignored" 's/if t.isCoinbase || !strict then 0 else/if t.isCoinbase then 0 else/'
