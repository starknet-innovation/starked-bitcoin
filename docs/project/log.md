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


## 2026-10-09 (session 2) — M3a.3: message and SHA components built; component soundness proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: BLOCK-AIR → in progress (M3a.3 BLK-SHA: AIRs, witnesses, component proofs done; linking next)
Done:
- Fields yield each transaction's byte ranges (62f8838). `block_msg` (bf260ea) and `block_sha` (b7b0d3b)
  AIRs, witnesses and tests, plus negative tests (0c1f74d).
- SHA soundness `digest_sound` (37bc8ab..275fc02): a second hash's digest is SHA256d of its message's
  words, read block by block from the first block.
- Message soundness (c129f50..60968c0): `whole_msg`, `split_msg`, `pad_ok`, `pad_bytes`, `belongs`,
  `word_yield`, `len_yield`.
- Soundness fix (1fffa02): the length rows were checked only mod `P`, and a top length byte up to 255
  allowed `8 · len + P`. Bits 3..7 of that byte must now be clear; `top_lt` proves the bound.
- The owner's `bitcoind` node is reachable over SSH and an RPC tunnel. It is a data source only: the
  machine is too small to prove on. Credentials stay in `prove-any-chain/.env.local`, which is gitignored
  here.
Evidence:
- `lake build`: 8,762 jobs, OK. `#print axioms` on `digest_sound`, `whole_msg`, `split_msg`,
  `pad_bytes`, `word_yield`, `len_yield`, `belongs`: only `propext`, `Classical.choice`, `Quot.sound`.
- `zig build test -Dtest-filter=block` passes (exit 0). (bytes, fields, msg, sha) proves and verifies
  on blocks 0, 170 and 91812. Txid digests reproduce the Merkle roots, including on segwit blocks
  481824 and 709632.
Problems / lessons:
- The prover rejects preprocessed columns read at a nonzero offset (`PreprocessedOffsetUnsupported`).
  Use an extra periodic indicator for the shifted row instead (`IS56`, `IS0`).
- Proving the length rows against the spec exposed the mod-`P` gap. Check for wrap-around whenever a
  constraint compares a multi-byte value.
Next: tie the message rows to `Spec.Block.pad`, then link the system's lookups (SHA ↔ msg, msg ↔ byte
table, msg ↔ fields).

## 2026-10-09 — Full chain re-proven with the header tree
Who: Claude (agent, Opus 5.5)
Roadmap: HC-HASHTREE → done
Done:
- `spike chain 20 70 26`: 243 leaves, 242 nodes, root verified with the public-data VK; `T` equals the natively
  recomputed MMR root over 970,348 block hashes ([report](../reports/2026-10-09-full-chain-tree.md)).
Evidence:
- Log `data/chain_full_tree.log`: leaves 45,317 s, fold 5,098 s, verify 1.09 s, root proof 981,000 bytes.
Problems / lessons:
- Leaves cost about 2.5× the previous run: the segment proof now includes the tree component at the same row
  count (no lifting yet).
Next: M3a.3 BLK-SHA.

## 2026-10-08 (session 4) — M3a.1 and M3a.2 done and proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: BLOCK-AIR → in progress (M3a.1 BLK-BYTES, M3a.2 BLK-FIELDS done)
Done:
- M3a.1 block byte table: `bytes_rows`, `read_byte` (33e3237).
- M3a.2 grammar layer `toksBlock_parse` (b898e56); fields AIR, tokenizer and witness (310ab0d); AIR-layer proof
  through `fields_sound` (8bb66a9 … this commit).
- Soundness fix found while proving: bound the 5-byte CompactSize's top byte (95a05bc).
Evidence:
- `zig build -Dtest-filter=block -Doptimize=ReleaseFast test`: 11/11 (6 small samples prove and verify with the byte table;
  5 large ones satisfy the constraints; tampered rows and bytes rejected).
- `lake build` clean, no sorry; `#print axioms fields_sound`: propext, Classical.choice, Quot.sound; JSON drift: ok.
Problems / lessons:
- `set` abbreviations break rewrites against lemma outputs stated on the original terms; state lemmas
  over abstract `M`/`R` with hypotheses instead.
- `by` blocks inside applications elaborate before implicit naturals are unified; use `refine … ?_`.
- `unfold P` inside goals that mention `ZMod P` values creates distinct omega atoms; bound via `lt_P`.
Next: M3a.3 BLK-SHA; the full-chain run with the tree continues (see status).

## 2026-10-08 (session 3) — Prover race fixed; CIRCUIT-GLUE done
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: CIRCUIT-GLUE → done; PROOF-STORE proposed; HC-HASHTREE full run in progress
Done:
- Fixed an intermittent `ConstraintsNotSatisfied` in multi-component proofs (fdd5a03): two components evaluate
  concurrently and allocated from one arena; `system.prove` now wraps the allocator thread-safely.
- Glue defined in Lean, exported, replayed (15b6496); proofs: `blake2s_sound`, `node_sound`, `node_compose`, digests, key.
Evidence:
- Before the fix about 1 in 4-5 runs of `spike chain 16` failed (ReleaseSafe: integer overflow in the accumulator
  merge); after it, 10/10 pass.
- `glue parity` tests: leaf, and node in topology and value mode, gate-identical to the hand-written builders; the
  node proves and verifies.
- `lake build` clean, no sorry; `#print axioms` of the new theorems: propext, Classical.choice, Quot.sound.
Problems / lessons:
- The first full run with the tree died at start (the race); restarted at fdd5a03, running.
- A word-level Blake2s spec with the chaining value as a function evaluated exponentially (16^blocks); materialize lists.
Next: let the full-chain run finish and write its report; then M3a.1.

## 2026-10-08 (session 2) — IR-LOGUP, BLAKE2S, M3a spec, HC-HASHTREE built and proven
Who: Claude (agent, Opus 5.5), with the owner
Roadmap: IR-LOGUP, BLAKE2S, BLOCK-SAMPLES, BLOCK-SPEC, BLOCK-AUDIT → done; HC-HASHTREE → built and proven, full-chain re-run todo
Done:
- Owner decisions D-027..D-033 (multi-component LogUp, spent-output slots, Blake2s commitments, duplicate inputs in M3b, header commitment = MMR).
- Private repo starknet-innovation/starked-bitcoin created; authors rewritten to the GitHub noreply address. Nothing pushed.
- IR-LOGUP (Lean semantics, system prover, in-circuit), BLAKE2S (`compress_sound_air`), block spec and serialization round trip.
- HC-HASHTREE: tree + header-v7 components and `tree_root_sound` (a2066db); leaf over the system with the root entry (bb1a9c0);
  Lean aggregation with `T` (b668b4e); node computes `T` in-circuit, MMR fold, VK sizes, inclusion proofs, native `T` check (this commit).
Evidence:
- `zig build -Dtest-filter=...`: leaf, node (T = perfect root over 32 hashes; node 229–328 s Debug), header tree (MMR, inclusion, blockHash) pass.
- `spike chain 12 3 10 data/headers.bin 53`: 4 segments (16+16+16+4), 3 nodes, root verified; `T` equals the native MMR root over 52 hashes.
- `lake build` clean; `#print axioms` for `pub_compose_T`, `leaf_valid_T`, `chain_from_genesis_T`: propext, Classical.choice, Quot.sound.
Problems / lessons:
- A first background chain run stopped silently after leaf 1 (exit status hidden by a pipe); the direct rerun completed. Not reproduced.
- 1-header segments have no tree node: the plan now uses ≥ 2-header segments and leaves an odd last header out.
Next: full-chain re-run with the tree (`spike chain 20 70 26 data/headers.bin`, about 8 h+), then M3a.1 (block AIR).

## 2026-10-08 — M1 and M2 done: full chain checked and proven to one root
Who: Claude (agent, Opus 5.5)
Roadmap: HC-FULLRUN, AGG, RECURSION, VK → done; IR-LOGUP → moved to M3; REC-STMT-EQ → partly done
Done:
- `fullrun 16 check`: heights 0..970,347, 0 failures; chainwork equals Core's (blockchair).
- `spike chain 20 70 26`: 243 leaves, 242 nodes, root verified; 8.2 h CPU wall.
- `leafIdentity`: the verifier derives leaf identities from public data; drivers use it.
Evidence: [report](../reports/2026-10-08-full-chain.md); `zig build test` 32/32.
Problems / lessons:
- The full run's VK used the leaf proofs' own hashes; fixed afterwards and checked at
  every leaf size used, but the 8 h run was not repeated.
Next: REC-FUZZ, then M3 after the owner's decisions (status.md, Needs owner).
## 2026-10-07 — M2: plain in-circuit verifier, leaf, node, aggregation (Lean + Zig); headers downloaded
Who: Claude (agent, Opus 5.5), with the owner (Q-MASK choice B)
Roadmap: REC-PROFILE, REC-COMPOSE, REC-MASK, REC-LEAF, REC-FOLD → done; AGG → in-progress (full-chain run); HC-FULLRUN → in-progress (check running)
Done:
- REC-PROFILE (ab8d1fc), REC-COMPOSE `segment_compose` (31e1db4), `dag_correct` (1c973bb).
- D-024 plain in-circuit verifier for multi-offset, no-LogUp proofs (089faee).
- REC-LEAF (0eb473a): leaf circuit, proved and verified natively.
- AGG-LEAN (d4b5714): `pub_compose`, `leaf_valid`, `chain_from_genesis`.
- REC-FOLD (2d89e67, D-025): node circuit with in-circuit `PubLink` and identity key.
- AGG (933b7a8, 9267084): fold driver, node identity from topology, `verifyRoot`, `spike chain`.
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
  AIR v6, witness, real segment at 400000, `version_sound`, added to `SegmentValid` (f8dc841).
- HC-AUDIT against Core master: `SegmentValid` covers every mainnet header rule except
  `time-too-new` (verification.md § Coverage audit).
- `scripts/fetch_headers.py` (verified header download) and `spike fullrun` (2873f78).
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
- HC-V5 exact chainwork: definition 5199752, proof 79d2fde (`work_q`, `work_step`, `work_out`,
  built on the generic `carry_chain`/`shift_sum`/`cauchy`).
- HC-TOP: `Spec/Chain.lean` `SegmentValid` and `header_chain_sound` (9a6ea99).
- BENCH-RAITO: our SHA AIR is about 250× faster than Raito's Cairo SHA-256 under `scarb prove` (84a42fe).
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
  tests, real pre-history test data (6fa5376, c903ecb).
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
- The doc-edit script aborted midway but the shell chain still committed. Fixed in c903ecb.
  Run edit scripts so a failure stops the commit (`&&`, assertions).
- `set` lesson again: facts obtained after `set x := e` mention `e`, not `x`; state them with
  the `set` name.
Next: HC-V5 (chainwork). Start with the design note in `docs/design/consensus-rules.md` § v5.

## 2026-10-07 — v3b retarget proven; docs and PM process
Who: Claude (agent), with the owner
Roadmap: HC-V3B → done (5e219bb); DOCS → done
Done:
- `retarget_sound` proven (5e219bb). The new file `RetargetDiv.lean` holds
  `rt_divq`, `rt_rem`, `rt_cap` and the final assembly. `header_pow_ex`
  exports the PoW row's exponent and powLimit facts.
- Documentation tree, README map and PM process (4df8c1e). The old docs
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
- Scaffold and Lean-first spike (9b95bb6); Zig↔Lean differential test (a0e54a5).
- Filed teddyjfpender/stwo-zig#225 (the verifier doesn't pin the
  preprocessed root; forgery reproduced).
- SHA-256 compression AIR (665b732) and its soundness proof (daae642,
  69ba59a, f18e90d).
- IR v1 (1e3a824). Header chain v1 (2fa7211, 69b2335), v2 (829a7e4,
  3323650), v3a (f9f7a95, 508cfd8), v3b definition and tests (b7ab5ce), and
  the retarget proof groundwork (0a808ce, f0297d8).
Evidence:
- The per-AIR docs list the tests, theorems and benchmarks.
Problems / lessons:
- A claim about stwo-zig's CUDA support taken from its README was wrong.
  Verify upstream claims in source code.
- `lake env lean` ignores `autoImplicit=false`; use `lake build`.
- `norm_num` cannot prove M31 prime; use Lucas–Lehmer.
Next: finish the v3b proof.
