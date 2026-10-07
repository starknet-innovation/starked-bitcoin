# Decisions

Status: current · Updated: 2026-10-07

Append-only. A reversal is a new entry that says `Supersedes D-NNN`; also
add `Superseded by D-MMM` to the old entry's status field (the only allowed
edit).

- **By** is `owner` (the project owner decided) or `agent` (proposed by the
  implementer and not objected to).
- Agent decisions that change scope, trust model or public statements need
  owner approval first. See [README.md](README.md#escalation-when-to-stop-and-ask-the-owner).

Template:

```
### D-NNN — <title>
Date: YYYY-MM-DD · By: owner|agent · Status: active
Decision: <one or two sentences>
Why: <reasons; alternatives rejected>
```

---

### D-001 — New repo; Raito as reference only
Date: 2026-10-06 · By: owner · Status: active
Decision: Build `starked-bitcoin` from first principles. Raito
(`~/Workshop/raito`) is a reference spec and test oracle, not a fork.
Why: Raito is abandoned and Cairo-based. A from-scratch design can target
native AIRs and exhaustive state.

### D-002 — Prover: stwo-zig
Date: 2026-10-06 · By: owner · Status: active
Decision: Use stwo-zig. Production runs on an H200 (CUDA); local work on an
M4 Pro (Metal).

### D-003 — Native AIRs, not Cairo
Date: 2026-10-06 · By: owner · Status: active
Why: Performance, and AIRs small enough to verify formally.

### D-004 — assumevalid first; pluggable script module later
Date: 2026-10-06 · By: owner · Status: active

### D-005 — Exhaustive UTXO state with inclusion and non-inclusion
Date: 2026-10-06 · By: owner · Status: active
Decision: A canonical sorted Merkle tree. Current UTXO set first, history
later. Matches Bitcoin Core's set exactly; OP_RETURN outputs are tracked
separately.
Why: Utreexo gives membership only; non-inclusion is a requirement.

### D-006 — Parallel per-block proofs plus aggregation
Date: 2026-10-06 · By: owner · Status: active
Decision: A full node supplies root_in/root_out and hints. Blocks are proven
independently and aggregated.

### D-007 — Blake2s for our own commitments
Date: 2026-10-06 · By: owner · Status: active
Why: Owner preference over Poseidon.

### D-008 — Where code lives
Date: 2026-10-06 · By: owner · Status: active
Decision: Bitcoin-specific AIRs live in this repo. Generic prover changes go
to a stwo-zig fork and are upstreamed if useful. The pinned submodule is
never edited in place.

### D-009 — Lean-first single source of truth
Date: 2026-10-06 · By: owner ("do it right"), confirmed by the spike · Status: active
Decision: AIRs are defined and proven in Lean, exported to JSON
(`starked-air-v1`), and interpreted by Zig. Zig never defines constraints.
Why: Soundness proofs must be about exactly what the verifier runs. See the
[spike report](../reports/2026-10-06-lean-first-spike.md).

### D-010 — Formally verify the AIRs
Date: 2026-10-06 · By: owner · Status: active
Decision: Every AIR gets a Lean soundness theorem with standard axioms only.

### D-011 — Proof scope: "a valid chain exists"
Date: 2026-10-06 · By: owner · Status: active
Decision: Choosing the canonical chain is left to verifiers.

### D-012 — Browser verification deferred
Date: 2026-10-06 · By: owner · Status: active

### D-013 — The verifier pins the preprocessed commitment
Date: 2026-10-06 · By: agent · Status: active
Why: Without it, a prover can switch selectors off (reproduced forgery;
stwo-zig#225).

### D-014 — SHA-256 AIR layout: 72-row period, bits plus 16-bit limbs, no lookups
Date: 2026-10-06 · By: agent · Status: active
Why: Keeps soundness to bit-vector lemmas. Lookups can be revisited if
benchmarks demand it. See [airs/sha256.md](../airs/sha256.md).

### D-015 — Header-chain layout: 256 rows per header, consensus checks in scratch rows 216–255
Date: 2026-10-06 · By: agent · Status: active
Why: Constant offsets between a header's three compressions and its checks.
No LogUp needed yet.

### D-016 — Git: commit locally; never push without owner approval
Date: 2026-10-06 · By: owner · Status: active

### D-017 — Documentation and PM structure
Date: 2026-10-07 · By: owner (request), agent (structure) · Status: active
Decision: The README is the map; `docs/{design,airs,reference,guides,reports,project}`;
the PM process lives in [README.md](README.md).

### D-018 — Median time past by counting, not sorting
Date: 2026-10-07 · By: owner · Status: active
Decision: HC-V4 enforces `time_j > MTP` as "at least ⌊k/2⌋+1 of the k ≤ 11 previous times are strictly below `time_j`", with a range-checked difference per comparison. It does not sort inside the circuit.
Why: For a sorted list `s`, `t > s[⌊k/2⌋]` ⟺ `#{i : t_i < t} ≥ ⌊k/2⌋+1`. Counting is cheaper and much easier to prove than an in-circuit sort.

### D-019 — Finish M1 before starting M2
Date: 2026-10-07 · By: owner · Status: active
Decision: Complete HC-V4, HC-V5, HC-TOP, BENCH-RAITO and FV-Z3 before recursion/aggregation work.
