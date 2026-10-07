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

## 2026-10-07 — M2: plain in-circuit verifier, leaf, node, aggregation (Lean + Zig); headers downloaded
Who: Claude (agent, Opus 5.5), with the owner (Q-MASK choice B)
Roadmap: REC-PROFILE, REC-COMPOSE, REC-MASK, REC-LEAF, REC-FOLD → done; AGG → in-progress (full-chain run); HC-FULLRUN → in-progress (check running)
Done:
- REC-PROFILE (84bfad4), REC-COMPOSE `segment_compose` (f32b6be), `dag_correct` (38f27df).
- D-024 plain in-circuit verifier for multi-offset, no-LogUp proofs (fa7b33d).
- REC-LEAF (1142c8f): leaf circuit, proved and verified natively.
- AGG-LEAN (8c8f662): `pub_compose`, `leaf_valid`, `chain_from_genesis`.
- REC-FOLD (7df4a99, D-025): node circuit with in-circuit `PubLink` and identity key.
- AGG (3233bcd, 7b5b400): fold driver, node identity from topology, `verifyRoot`, `spike chain`.
- All 970,348 mainnet headers (0..970347) downloaded and merged, every link checked.
Evidence:
- `zig build test`: 32/32. Lean builds; new theorems use standard axioms only.
- `spike agg 16 4 70 26`: 1,024 headers → one root proof (0.98 MB), verified in 0.23 s.
- `spike agg 20 2 70 26`: 8,192 headers; leaf 31–33 s + 33 s segment, node 24 s, 13.3 GB peak.
- `spike chain 12 3 10 … 40`: mixed leaf sizes and an odd carry; chainwork 40 × 0x100010001.
Problems / lessons:
- `verifyProofBytes` returns the verifier circuit's own output, not the proven circuit's
  digest; the proven digest is `request.output_digest`, bound by acceptance.
- Adding a package that a dependency already imports creates a duplicate module; use the
  dependency's re-export (`circuit_cpu.verify.Request`).
- Zero component sizes are not a valid padding target; start the fixpoint from a leaf's padded sizes.
Next: finish `spike chain 20 70 26 data/headers.bin` (data/chain_full.log) and `fullrun 16 check`
(data/fullrun_check.log); write the report; close M1 and M2.

## 2026-10-07 (session 4) — HC-V6 proven, Core audit, full-chain tooling; download running
Who: Claude (agent), with the owner
Roadmap: HC-V6, HC-AUDIT → done; HC-FULLRUN → in-progress. Decision D-022 (owner): defer GPU/H200.
Done:
- HC-V6 minimum block version (BIP34/66/65; heights verified in Core `chainparams.cpp`): spec,
  AIR v6, witness, real segment at 400000, `version_sound`, added to `SegmentValid` (b8a2e8c).
- HC-AUDIT against Core master: `SegmentValid` covers every mainnet header rule except
  `time-too-new` (verification.md § Coverage audit).
- `scripts/fetch_headers.py` (verified header download) and `spike fullrun` (a1a0320).
  Heights 0..2047: check mode OK, Metal prove+verify OK, chaining OK, chainwork exact.
Evidence:
- `lake build` OK (8733 jobs); `#print axioms header_chain_sound` → standard axioms only.
- `zig build test`: 27/27.
Problems / lessons:
- Blockstream started returning 429 under 4 parallel workers; the fetcher now puts a failing
  source on cooldown and uses the other.
- An overclaiming test comment ("version 3 refused" may fail on PoW first) was corrected.
Next: when the download finishes, merge the chunks (`fetch_headers.py --merge data/chunk_{0,1,2,3}.bin`)
and run `spike fullrun 16 check data/headers.bin`; then `fullrun 18 metal` to measure the full-chain proving time.

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
