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

## 2026-10-07 (session 3) — HC-V5, HC-TOP, BENCH-RAITO, FV-Z3; version rule found missing
Who: Claude (agent), with the owner
Roadmap: HC-V5, HC-TOP, BENCH-RAITO, FV-Z3 → done. New: HC-V6 (next), HC-AUDIT, HC-FULLRUN.
Decisions: D-020 (exact chainwork, owner), D-021 (s ≥ 16, agent).
Done:
- HC-V5 exact chainwork: definition 1250f02, proof e1353f0 (`work_q`, `work_step`, `work_out`,
  built on the generic `carry_chain`/`shift_sum`/`cauchy`).
- HC-TOP: `Spec/Chain.lean` `SegmentValid` and `header_chain_sound` (c30c715).
- BENCH-RAITO: our SHA AIR is about 250× faster than Raito's Cairo SHA-256 under `scarb prove` (0c7f39c).
- FV-Z3: `scripts/air_z3.py`. Four windows unique, SHA round unknown, control behaves (this commit).
Evidence:
- `lake build` OK (8731 jobs). No sorry/native_decide/bv_decide. `#print axioms header_chain_sound`
  → propext, Classical.choice, Quot.sound.
- `zig build test`: 26/26. JSON drift: in sync. Benchmarks and Z3 runs: see the reports.
Problems / lessons:
- **A consensus rule was missing.** Core rejects low block versions after BIP34/66/65
  ("bad-version"). I had wrongly recorded that version rules never matter. Found while answering
  the owner; now HC-V6, plus HC-AUDIT so that a line-by-line check of Core replaces memory.
- Z3: integer encoding hopeless at this size; cone of influence + bit-vectors made 4/5 tractable.
- Lean: `set` trap again (facts derived after `set` keep the unfolded form); derive first, set last.
Next: HC-V6 (version rule). Q-HEADERS is open for HC-FULLRUN.

## 2026-10-07 (session 2) — HC-V4 median time past: defined, tested, proven
Who: Claude (agent), with the owner
Roadmap: HC-V4 → done; HC-V5 → next. Owner decisions D-018 (counting) and D-019 (M1 before M2).
Done:
- Spec `mtpOk` (Core `GetMedianTimePast`) with `#guard`s, including mainnet height 101982 whose
  time is below two predecessors. Counting equivalence `mtpOk_iff_count` and `sentinel_sound` proven.
- v4 AIR (`Mtp.lean`, rows 229–240, 394 constraints, 52 preprocessed, 88 pubs), Zig witness,
  tests, real pre-history test data (35710cb, ffa4c89).
- Soundness (`MtpSound.lean`): `mtp_window`, `mtp_cmp`, `mtp_count`, `mtp_out`, `mtp_core`.
Evidence:
- `lake build`: OK, 8727 jobs. No sorry/native_decide/bv_decide. `#print axioms` on all 10 main
  theorems → `propext, Classical.choice, Quot.sound`.
- `zig build test`: 23/23 passed. JSON drift: all 4 files in sync.
- Python brute force (200k cases) and a Zig randomized test (100k) agree: the sentinel counting
  rule matches Core's sorted median (sound always, and complete for t > 0).
- Benchmark: 1024 headers at 2^18 rows, Metal, 70 queries/26-bit PoW: 3.65 s prove (≈ 280
  headers/s, down from ≈ 350), 0.13 s verify, 1.07 MB.
Problems / lessons:
- My first `#guard` had the median of 1..11 wrong; the guard caught it. Keep writing guards
  before the circuit.
- The Blockstream API rate-limited after the timestamp scans. Fetched the new test data from
  mempool.space (same Esplora API) and recorded the source.
- The doc-edit script aborted midway but the shell chain still committed. Fixed in ffa4c89.
  Run edit scripts so a failure stops the commit (`&&`, assertions).
- `set` lesson again: facts obtained after `set x := e` mention `e`, not `x`; state them with
  the `set` name.
Next: HC-V5 (chainwork). Start with the design note in `docs/design/consensus-rules.md` § v5.

## 2026-10-07 — v3b retarget proven; docs and PM process
Who: Claude (agent), with the owner
Roadmap: HC-V3B → done (9a03734); DOCS → done
Done:
- `retarget_sound` proven (9a03734). The new file `RetargetDiv.lean` holds
  `rt_divq`, `rt_rem`, `rt_cap` and the final assembly. `header_pow_ex`
  exports the PoW row's exponent and powLimit facts.
- Documentation tree, README map and PM process (97dbca4). The old docs
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
