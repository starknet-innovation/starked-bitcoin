#!/bin/sh
# The one place this repository's checks are defined. The commit hook and CI call it.
# Usage: ./scripts/check.sh [--fast]    --fast skips the tests.
# The full run takes about an hour (docs/project/status.md § Verify the current state).
set -eu
cd "$(dirname "$0")/.."

# zig: .
(
    # Turn on once the tree is reformatted with `zig fmt` (deferred so open branches merge cleanly):
    # git ls-files -z '*.zig' '*.zon' | xargs -0 zig fmt --check
    zig build
)

# lean: lean
(
    cd lean
    # Lean accepts these with only a warning, or trusts the compiler; AGENTS.md forbids them.
    if git grep -nwE 'sorry|native_decide|bv_decide' -- '*.lean'; then
        echo 'check: sorry, native_decide or bv_decide in Lean source' >&2
        exit 1
    fi
)
# lean-consensus/ is generated from lean/StarkedAir/Spec and must not drift from it.
python3 scripts/gen_lean_consensus.py --check

if [ "${1:-}" = "--fast" ]; then
    exit 0
fi

# lean: lean
(
    cd lean
    lake exe cache get  # prebuilt Mathlib, instead of hours of compiling
    lake build
    # The main theorems rest only on Lean's standard axioms (AGENTS.md). A renamed theorem fails here too.
    # Fails closed: one matching line per #print, nothing else.
    ax=$(lake env lean ../scripts/axioms.lean)
    printf '%s\n' "$ax"
    std='(propext|Classical\.choice|Quot\.sound)'
    want=$(grep -c '^#print axioms' ../scripts/axioms.lean)
    good=$(printf '%s\n' "$ax" | grep -cE "^'[^']+' (depends on axioms: \[$std(, $std)*\]|does not depend on any axioms)$" || true)
    lines=$(printf '%s\n' "$ax" | grep -c . || true)
    if [ "$good" -ne "$want" ] || [ "$lines" -ne "$want" ]; then
        echo "check: $good of $want main theorems on standard axioms only ($lines lines of output)" >&2
        exit 1
    fi
)

# The slow part stays on developer machines: CI sets CI=true and skips it.
if [ "${CI:-}" != "true" ]; then
    # zig: . (about 45 minutes; large blocks are slow in Debug, hence ReleaseFast)
    (
        out=$(mktemp)
        trap 'rm -f "$out"' EXIT
        status=0
        zig build test -Doptimize=ReleaseFast --summary all >"$out" 2>&1 || status=$?
        cat "$out"
        [ "$status" -eq 0 ] || exit "$status"
        # The tool exits 0 when it finds no tests, so a suite can disappear silently.
        grep -Eq '[1-9][0-9]*/[0-9]+ tests passed' "$out" || { echo "check: no test ran" >&2; exit 1; }
    )
    # Every committed airs/*.json equals its Lean export.
    scripts/check_air_drift.sh
fi
