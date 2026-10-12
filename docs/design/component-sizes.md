Status: **proposed (2026-10-12), awaiting owner review.** Owner constraint: everything proven today stays proven.
Paths written as `SB/` mean this repo; the row counts came from a throwaway planning-only program (not kept).

# c1: per-component trace sizes — design note

Repo state: starked-bitcoin `m3a5`, stwo-zig `4afa09dbf`. Read-only study. The row counts come from `c1/rows/` (planning only, no witnesses, under 1 GB). Paths: SB = starked-bitcoin, SZ = third_party/stwo-zig/src.

## 1. Facts

**stwo-zig already supports mixed sizes end to end.**
- **Lifting.** Every tree is committed at one height H = max log + blowup (SZ/core/pcs/config_v2.zig:79-125). A column of log n is lifted as f∘π^(H−n), where π is the doubling map (SZ/prover/vcs_lifted/prover.zig:483-509).
- **Composition.** The degree bound is the max over components (SZ/core/air/components.zig:131-137). Per-component quotients are bucketed by size, lifted and summed (SZ/prover/air/accumulation.zig:153-224, 374-423).
- **One OODS point and one FRI** (SZ/prover/prove.zig:604-633; SZ/core/pcs/verifier.zig:271-289).
  - A small component reads its masks at the same point. Row offsets use the max-domain step, because π^k(p+g_N) = π^k(p)+g_n.
- **Vanishing.** V_n(π^k p) = V_N(p), since the canonic vanishing polynomial is x after n−1 doublings (SZ/core/constraints.zig:17-27; I checked this by hand). So one shared 1/Z_N(oods) stays correct. The in-circuit gadget does exactly that (SZ/frontends/circuit/stark_verifier/constraint_eval.zig:276).
- **LogUp shift.** The shift is claimed_sum / 2^(own log) (constraint_eval.zig:142-145).
- **Periodicity samples.** A cumulative-sum column is also sampled at oods + 2^(own log)·g_N (stark_verifier/oods.zig:37-60, 129-133; SZ/core/pcs/quotients/samples.zig:207-224).
- **Native verifier.** Lifted Merkle verification takes per-column logs (SZ/core/vcs_lifted/verifier.zig:96-135).
- **Recursion.** `CircuitStatement` fixes sizes as constants through the preprocessed layout and circuit hash (statements/circuit_statement.zig:44-50, 110-124). The multiverifier pads every child to one `target_sizes` profile per fold tree (statements/multiverifier.zig:60-74). The Cairo statement instead mixes guessed sizes into the transcript (cairo_statement.zig:109-136). stwo-zig therefore favours **one fixed size vector per verifying key**.
- **STWZEVA.** Lowering is per component (SB/src/air/stwzeva.zig:415-447). Lifted reads use `shift = eval_log − col_log + 1` (SZ/frontends/cairo/proving/air/component.zig:429-478).

**What blocks us (all local changes):**
- SB/src/air/system.zig:54-58 rejects mixed sizes with `LiftingUnsupported`. Fix: return the max and build `cfg` from it.
- SB/src/air/component.zig:200/255 has the same guard. Fix: allow `max ≥ log_size`; divide by Z_N(p) (equivalently Z_n(π^k p)).
- stwzeva.zig:556,561,596-602 needs `lifting = max+1` and real per-column preprocessed logs.
- prove_rec `config(max)`.
- SB/src/block/system.zig:168-169, 282: compute one size per part. The generators already take `log_size` per call.
- plain_verifier.zig: `PlainConfig.log_trace_size` (:56-75) stays as the max. Add `PartConfig.log_size`. Use the part's own size in statement mixing (:819, :834) and the LogUp shift (:744, :650). Add the extra periodicity points (:965-979). Sort leaf values by (log, col), a static permutation (:916-930). Regenerate the Lean tables (`st.composition/deep/statement/shifts`).

## 2. Row needs (log2 of `buildFull`'s per-part terms, SB/src/block/system.zig:168)

| comp | cols P+M+I | 0 | 170 | 400000 | 481824 | 709632 | 970347 | 774628 |
|---|---|---|---|---|---|---|---|---|
| bytes | 18 | 9 | 9 | 20 | 20 | 21 | 21 | 22 |
| fields | 264 | 3 | 4 | 14 | 14 | 16 | 16 | 10 |
| msg | 54 | 10 | 11 | 21 | 22 | 22 | 22 | 22 |
| sha | 188 | 11 | 12 | **22** | **22** | **22** | **23** | **23** |
| merkle | 67 | 1 | 2 | 11 | 11 | 11 | 13 | 7 |
| tables | 13 | 8 | 8 | 8 | 8 | 8 | 8 | 8 |
| walk | 65 | 8 | 9 | 20 | 20 | 19 | 19 | 13 |
| ctx | 96 | 8 | 8 | 8 | 8 | 8 | 8 | 8 |
| wmerkle | 37 | 1 | 2 | 11 | 11 | 11 | 13 | 7 |
| undo | 18 | 1 | 7 | 18 | 18 | 19 | 19 | 12 |
| b2msg | 33 | 5 | 6 | 16 | 16 | 17 | 17 | 10 |
| b2s | 406 | 8 | 9 | 19 | 19 | 19 | 19 | 13 |
| fpwalk | 24 | 7 | 9 | 19 | 19 | 19 | 20 | 13 |
| urec | 63 | 1 | 1 | 13 | 13 | 13 | 14 | 7 |
| coin | 354 | 2 | 3 | 14 | 14 | 14 | 15 | 8 |
| anc | 179 | 8 | 8 | 8 | 12 | 12 | 12 | 12 |
| **L today** | 1879 | 11 | 12 | 22 | 22 | 22 | 23 | 23 |

- sha always sets L. Its estimate adds 3·(wnodes+1) compressions even without a witness commitment.
- The heaviest columns sit in components that need few rows: b2s, coin, fields and anc hold 64 % of the cells.

**Peak memory**, using Σ_c w_c·4 B·2^(L_c), with w = 3(P+M+I) in default mode and ≈ 2M+P (scaled to 2.75 k) in compact mode (docs/design/gpu.md:262-264):

| | uniform default / compact | exact per-comp | tiers (below) |
|---|---|---|---|
| L=22 blocks (400000…709632) | 94.6 / 46.1 GB | 14.8–16.2 / 8.6–9.3 | 23.7 / 13.2 |
| L=23 blocks (970347, 774628) | 189 / 92 GB | 22.6–25.9 / 13.1–15.0 | 47.3 / 26.5 |
| L=24 (projected) | 378 / 185 GB | ≈ 45–52 / 26–30 | 94.6 / 52.9 |

- **Tiers:** A = {sha, msg, bytes, walk} at L; B = {fpwalk, b2s, undo, b2msg} at L−2; C = the rest at L−5 (minimum 8); ctx and tables fixed at 8; anc at 12 (with CSV).
- All five large samples fit, with at least one log of slack outside sha and msg.
- A tier is not guaranteed in general. An undo stream can be large relative to the block, and so can scripts. Any block that doesn't fit falls back to uniform.

## 3. Lean impact

The semantics are already per instance: `Inst.logSize`, `sites` over `2^(inst i).logSize` (Lookup.lean:35-67). `used_in_table` and `yields_eq_uses` (LookupCount.lean:33) don't depend on size.

| assumption | where | class |
|---|---|---|
| `hL : ∀ i < 15, (inst i).logSize = L` section variable | Link:76, HashSound:81, MerkleLink:42, WMerkleLink:71, ChkLink, SysLink, BlockSetup:51, BlockTxs, BlockSums, BlockFinal, BlockCommit, ScriptSum:54, B2Link:24, HashPub, CoinLink:98, CoinClaims, CoinEvents, CoinRecs, CoinEpochCore:340, CoinEpochSound:211, BlockSound:31; `<16` in BlockAnc:75 | (i): ≈330 theorems and 578 `2^L` occurrences, each re-indexed to its producer's size |
| `Setup inst pub L` (`m<2^L`, `hN25`, `hidx`) | BlockSetup:20-46 | (i): becomes the fields size L₁ |
| `rows_le`, `len_R ≤ 2^L` | BlockSetup:64-66 | (i): becomes the bytes size L₀ |
| fields/bytes reads share one L | FieldsSound:1682, TxBytes:42 | (i): split into L₀, L₁ |
| `mem_sites`/`link` give `r' < 2^L` | Link:160, 540 | (i): becomes the yielding component's size |
| `pair_sum`, `filter_sites` over `range 2^L` | CoinLink:102-245, ScriptSum:59 | (i) |
| `hash_sites_len = 216·2^L`, `hash_rows_lt_P (L ≤ 23)` | Link:139,150 (+≈15 users) | **(ii)**: Σ_i k_i·2^(L i) ≤ 216·2^23 < P; one new lemma |
| lower bounds `8 ≤ L`, `12 ≤ L` | BlockSound:35, BlockTxs:67, B2Link:502, AncSound:211,491 | (i): become per-component floors (ctx, b2s, anc) |
| `BlockPubOk` (single L, 8 ≤ L ≤ 23) | AggregateBlocks:29-31; users CoinEpochCore:187,258, CoinWFE:181, BlockRec:487, BlockTree:309 | (i)/(ii): existential over a size vector |
| `Shared.logSize`, `ninv L`, `instOf L`, `StarkSound L`, `stmtWords … L` | CompositionLogUp:234-280, EndToEnd:318-472,546, Statement:62-166 | **(ii)**: per-part sizes; a single `invZ` stays valid (§1) |
| `Tree.leaf (L)`, `Trust.leafSound ∀ L`, `htree_sound (hl : ∀ L …)` | BlockRec:321,383; HeaderRec:127 | (i): indexed by size profile |

- **Class (iii), cross-component row alignment: none in the block system.** Every link is a lookup bounded by its producer's rows. I found no shared row variable across two `inst` mains.
- The only alignment is in the header tree (HeaderTreeSound:365-586, root `node(L−8,…)`). It is out of scope.
- **Size of the change:** about 30 Lean files.
  - Block: 22 files, ≈330 mechanical edits, best done through `n i := 2^(inst i).logSize`.
  - Circuit: 7 files, ≈15–20 lemmas.
  - Count bound: 2 new lemmas.
- **Bonus.** The Σ bound lets an L = 24 block pass the count bound. `BlockPubOk` caps L at 23 today even though `Vk` admits 24 (block_forest.zig:113). Lifting L≤23 also means re-checking `rows_le` (2^24) and the 2^26 id spaces; both still hold at 24.

## 4. VK and recursion

- **Exact vectors.** Each component varies on its own, so the number of shapes is unbounded. This needs option (b): sizes as transcript wires. The `sv` gadgets support that (verify.zig:174-177, 292-299), but our Lean-first plain verifier bakes in static tables. That makes (b) the most expensive option.
- **(a) Fixed tiers, sizes = f(L).** The circuit depends only on L, so there are still 17 leaf identities (8..24). Static constants, as stwo-zig's `CircuitStatement` does.
- **(c) A few profiles.** Uniform (today) plus tiered gives `Vk.leaf : [25][2]?Id` (block_forest.zig:46-53). The forest's per-block `logs` byte becomes (L, profile), and `expected` keys on it (:241-249). Nodes are unaffected, because leaves already pad to one shared shape.

## 5. Candidate designs

| | design | memory at L=23 (default/compact) | shapes | effort |
|---|---|---|---|---|
| D1 | Profiles {uniform, tiered}, chosen per block | 47 / 26.5 GB | 2 × 17 VKs | Zig ≈1.5 wk; plain_verifier + regenerated tables ≈1.5 wk; Lean ≈3–4 wk |
| D2 | Exact sizes, dynamic in-circuit (b) | 23–26 / 13–15 GB | 1 generic leaf | D1 + Lean-generated programs parametric in sizes, ≈+4–6 wk |
| D3 | Segments (c2): split a block across proofs | ≈ 1/s of uniform | new segment and joint leaves | Largest: cross-proof LogUp balance, byte positions and SHA messages spanning segments, segmented Merkle; ≈ 8+ wk. Not needed: weight caps L at 24 |

**Recommendation: D1.**
- It gets 4× (189 → 47 GB default; 92 → 26.5 compact at L=23) with few shapes. Today's uniform path survives unchanged as profile 0.
- Write the Lean generalisation for arbitrary size vectors from the start. D1 and D2 need the same Lean work, so D2 later is a Zig/circuit-only step.
- Combine with the compact mode and (a1) from docs/design/gpu.md.

## 6. Acceptance plan: everything proven today stays proven

- **Rule:** each old statement stays, under its old name, as a corollary of the new one at the constant vector `fun _ => L`.
- A `Compat.lean` file restates the old statements verbatim from git, as `example : <old> := …`, and CI builds it.

| old | new | old from new |
|---|---|---|
| section lemmas with `hL`, `hL24` (22 files) | hypotheses `∀ i, (inst i).logSize ≤ 23` plus floors | instantiate; uniform `hL` implies every per-part hypothesis |
| `hash_sites_len`, `hash_rows_lt_P` | Σ form, Σ < P | Σ at constant L = 216·2^L |
| `Setup inst pub L` | `Setup` over L₀, L₁ | `Setup_unif` |
| `block_sound`, coin theorem, `block_mtp`, `anc_sound`, `commit_sound` | same conclusions, weaker hypotheses | direct |
| `BlockPubOk` | `BlockPubOk'` (∃ vector) | lemma `BlockPubOk → BlockPubOk'`. Consumers (`epoch_blocks`, CoinWFE, `tree_sound`, `forest_sound`) take `BlockPubOk'`, so they get stronger with identical conclusions |
| `StarkSound L` (trusted) | `StarkSoundV Lv` | `StarkSoundV (fun _ => L) ↔ StarkSound L` by `rfl`/`simp`. The trust base is unchanged for uniform proofs and new only for lifted ones |
| `plain_sound`, `plain_leaf_valid`, `statement_sound` | per-part sizes | specialise |
| `Tree.leaf L`, `Trust.leafSound`, `htree_sound` | indexed by (L, profile) | profile 0 = today |

Zig side:
- Uniform proofs must stay byte-identical. This needs the existing STWZEVA byte-identity test (system.zig:408) and golden hashes for all samples.
- Small and large sample tests run under both profiles.
- Today's uniform VKs must still verify old forests.

**Flag for review:** the `StarkSoundV` hypothesis for lifted proofs is a new trusted assumption (FRI/DEEP soundness under lifting). It should be checked against Stwo's lifting soundness argument before anyone relies on it.
