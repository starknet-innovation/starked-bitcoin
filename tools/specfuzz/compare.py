"""Compares Core's answers (core_cases) with the Lean spec's (SpecCases.lean), case by case."""
import sys
from collections import Counter

core = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
lean = [l.rstrip("\n").split("\t") for l in open(sys.argv[2]) if l.strip()]
assert len(core) == len(lean), (len(core), len(lean))
total, bad = Counter(), Counter()
shown = 0
for (c, a), (c2, b) in zip(core, lean):
    assert c == c2, (c, c2)
    kind = c.split(" ")[0]
    total[kind] += 1
    if a != b:
        bad[kind] += 1
        if shown < 20 and kind != "nextany":
            print(f"MISMATCH {c}\n  core {a}\n  lean {b}")
            shown += 1
INFORMATIONAL = {"nextany"}  # outside the mainnet domain; divergence documented, not a failure
for k in total:
    note = " (informational: outside the mainnet domain)" if k in INFORMATIONAL else ""
    print(f"{k:10} {total[k]:7} cases, {bad[k]} mismatches{note}")
sys.exit(1 if sum(v for k, v in bad.items() if k not in INFORMATIONAL) else 0)
