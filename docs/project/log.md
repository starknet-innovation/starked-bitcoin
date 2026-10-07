# Progress log

Append-only, newest first. One entry per work session; a session that spans
midnight goes under its start date. Never edit a past entry: write a
correction in a new one.

Template (copy it to the top):

```
## YYYY-MM-DD — <one-line summary>
Who: <person or agent (model)>
Roadmap: <IDs touched and their new status>
Done:
- <outcome, with commit hash>
Evidence:
- <commands run and their result: tests, lake build, #print axioms, benchmarks>
Problems / lessons:
- <what went wrong, how it was resolved, what to do differently>
Next: <the exact next step; must match status.md>
```

---

## 2026-10-07 — v3b retarget proven; docs and PM process
Who: Claude (agent), with the owner
Roadmap: HC-V3B → done (9a03734); DOCS → done
Done:
- `retarget_sound` proven (9a03734). The new file `RetargetDiv.lean` holds
  `rt_divq`, `rt_rem`, `rt_cap` and the final assembly. `header_pow_ex`
  exports the PoW row's exponent and powLimit facts.
- Documentation tree, README map and PM process (this commit). The old docs
  moved to `docs/design`, `docs/airs` and `docs/reports`.
Evidence:
- `lake build`: all 8724 jobs OK. No `sorry`, `native_decide` or `bv_decide`.
  `#print axioms` on `retarget_sound`, `chain_sound_v2` and `state_sound` →
  `propext, Classical.choice, Quot.sound`.
- `zig build test`: green.
- JSON drift check: all four `airs/*.json` files match the Lean export.
Problems / lessons:
- A single proof took 47 minutes and hit the heartbeat limit. The causes:
  `omega` over a ~70-fact context (including `(by omega : …)` inside a term),
  let-bound `set` variables, and bounds stated about the unfolded expression.
  Fixed with `clear * -`, `clear_value` and top-level helper lemmas; the
  proof now takes 15 s. Bisecting with truncated copies of the module built
  in parallel found the culprit quickly. The rules are recorded in
  [reference/lean.md](../reference/lean.md).
- Retarget soundness depends on the PoW row's powLimit constraints. This is
  recorded in [verification.md](../reference/verification.md).
Next: HC-V4 (median time past). Start with the design section in
`docs/design/consensus-rules.md` and a layout plan in `docs/airs/header-chain.md`.

## 2026-10-06 — Repo bootstrap through header chain v3b (definition)
Who: Claude (agent), with the owner
Roadmap: SPIKE, STWO-225, SHA, IR-V1, HC-V1, HC-V2, HC-V3A → done; HC-V3B definition done
Done:
- Scaffold and Lean-first spike (85507f4); Zig↔Lean differential test (542d834).
- Filed teddyjfpender/stwo-zig#225 (the verifier doesn't pin the
  preprocessed root; forgery reproduced).
- SHA-256 compression AIR (7ba4a21) and its soundness proof (7dc817c,
  f965fca, 9a446cc).
- IR v1 (66703fb). Header chain v1 (82baf06, 6594fd3), v2 (fb5040e,
  74df024), v3a (6a3250e, b1660b5), v3b definition and tests (c52ddcf), and
  the retarget proof groundwork (eaa3a9d, 8ecd353).
Evidence:
- The per-AIR docs list the tests, theorems and benchmarks.
Problems / lessons:
- A claim about stwo-zig's CUDA support taken from its README was wrong.
  Verify upstream claims in source code.
- `lake env lean` ignores `autoImplicit=false`; use `lake build`.
- `norm_num` cannot prove M31 prime; use Lucas–Lehmer.
Next: finish the v3b proof.
