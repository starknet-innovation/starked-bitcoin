# Per-component sizes: the Lean-first programs and what Zig must supply (c1, D-045)

Interface between the Lean track (branch `c1/lean`) and the prover track (`c1/prover`, which owns
`src/recursion/plain_verifier.zig` and the generated tables). Read it with
`docs/design/component-sizes.md` (the design) and the prover's `component-sizes-prover-needs.md`
(branch `c1/prover`); §"Resolving the prover's P1–P5" answers it point by point.

**Summary: no exported program has to change.** Every place a size enters the in-circuit verifier is
a host hook or a host-side choice of point. The Lean programs never contain a size. For the
uniform profile, every export stays byte-identical, and what each hook returns is unchanged. What
changes is what Zig returns from hooks 2 and 4, which table entry it picks, and which point it gives a
periodicity response. The Lean side restates the hook hypotheses per part (below).

Notation: part `i` (in component order) has `2^(L i)` rows; `N = max_i L i` is the lifted trace
size (`PlainConfig.log_trace_size`); `g_N` generates the size-`2^N` trace subgroup.

## Program by program

| Program (export) | Where a size enters | Mixed sizes: what Zig does | Export changes? | Lean statement |
|---|---|---|---|---|
| Composition `sysProg` (`composition_*.json`, `sysJson`) | hook 2 (`1/2^L`, the claimed sum's share per row); hook 1 (`1/Z(oods)`) | hook 2: the `k`-th hook-2 call (program order = component order, one per component **with lookups**) returns `1/2^(L i)` for that component `i`. hook 1: `1/Z_N(oods)` at the max size, as stwo-zig's `constraint_eval` does (`V_n(π^k p) = V_N(p)`, so one denominator serves every lifted component). | No (ops don't depend on `logSize`; `sysJson`'s `logSize` field only feeds `Shared`, not the ops) | `sys_soundV`/`plain_soundV` take `HookOk ρ sh Ls parts`: part `i`'s hook-2 register holds `ninv (Ls i)`. At constant sizes this follows from today's `hninv` (`hookOk_of_const`). |
| Statement `stmtOpsH` (`statement_leaf.json`, `stmtJson`) | hook 4 returns a component's 10 header words, word 0 = the log size | The `k`-th hook-4 call returns `[L k, digest_k, n_pubs_k]`, matching the native `mixStatement` with per-component sizes. | No | `statement_soundV`: the words mixed are `stmtWordsV system Ls …` (per-part size word); `stmtWordsV system (fun _ => L) = stmtWords system L`. |
| OODS shifts `shiftP` (`oods_shift_leaf.json`, `shiftJson`) | the table is per `(L, off)` | Mask offsets and the interaction's previous row are at step `g_N` for **every** component (lifting: `π^k(p + g_N) = π^k(p) + g_n`). Use the entries for `L = N`, as today with `log_trace_size`. | No (the export must contain `N`'s entries, which the 8..24 tables do) | `shift_sound` unchanged. |
| DEEP responses `deepList` (`deep_leaf.json`) | none in the table; points are host-built | A component with `L i < N` whose column has two samples (main offsets `{x, 0}` or the last four interaction columns) needs its **periodicity response** at `pt[1] + 2^(L i)·g_N` (stwo-zig `samples.zig:207-224`). That is the first of the column's responses in the table. Zig picks the point by position and part size. When `L i = N` this point is `oods` (today). The value index is unchanged. | No | `deep_sound`/`deep_complete` are label-level and unchanged. That the response points are right is part of what `StarkSoundV` assumes about the samples (as today for all points). |
| Balance `balanceProg` | none | none (claimed sums per part, unchanged) | No | `balance_sound` unchanged. |
| Merkle leaf hashing (`leafhash_*.json`) | column order in a leaf | stwo-zig's lifted trees order a leaf's columns by `(log size, index)` (`vcs_lifted/verifier.zig`). For a fixed profile this is a static permutation of the decommitted values. Zig permutes before hashing. | Per profile, a new `leafhash_<n>` only if a leaf's column **count** changes. It doesn't: counts are per tree. | `leaf_sound` is about the list it is given; the permutation is host-side. |
| Leaf checks / ctx / out glue (`block_leaf_*.json`) | none | none | No | unchanged. |

## Resolving the prover's P1–P5

- **P1 (composition hook 2).**
  - **Prover's proposal:** hook 2 `[i] → [1/2^(L_i)]`, with `i` a constant in the program.
  - **Lean side instead:** keeps hook 2 argument-free and fixes the **call order**: the `k`-th hook-2 call
    belongs to the `k`-th component with lookups, in component order. This is the same convention
    hook 4 already uses (`next_part` in `verifyPlain`).
  - **Why:** `composition_*.json` stay byte-identical, and the uniform path needs no change.
  - **Zig:** keep a counter in the hook-2 handler and serve `config.partLog(i)` for the `i`-th part with
    lookups (parts without lookups have no hook 2).
  - **Lean:** `HookOk` (CompositionSound.lean) is exactly this per-call statement; `sys_soundV` and
    `plain_soundV` take it.
  - **If an index argument is still wanted:** it changes the composition ops of every export. It is a
    small Lean change (`pShOps` with a constant, `HookOk` reading it), but it is not byte-identical.
- **P2 (DEEP `per` field).**
  - **Lean side:** done without touching `deep_leaf.json`.
    - `deepPer tc` gives one flag per response (`deepPer_length`). `colResps_per` proves that a flagged
      response is the periodicity copy (same label and value index as the column's last response).
    - The new export target `deep_leaf_per` (`deepJsonPer`) emits the 5-field rows
      `[tree, col, off, idx, per]` under the same schema. `DeepTable.parse` accepting 4 or 5 fields reads
      both.
  - **Note:** the flags depend only on the shape, not the sizes, so a uniform table read with `per`
    gives the same points (`pt(off) + G_N = pt(off)`).
- **P3 (statement), P4 (leaf hashes), P5 (transcript, shifts): agreed, no change.**
  - **P3:** `statement_soundV`/`Hook4Ok` state the per-part size word; `stmtWordsV (fun _ => L) = stmtWords L`.
  - **P4:** the `(log, column)` sort is a host permutation.

**Wiring facts the hand-written Zig path must match by inspection.** These are what `plain_soundV`
assumes the circuit wires; with the Lean-first programs they are theorems.
1. The statement words are `stmtWordsV`: per component `[L_i, digest_i, n_pubs_i]`, then its public inputs.
2. Each component's LogUp shift is `claimed_i · 1/2^(L_i)` (`starkParts`).
3. The composition is `Σ` (Horner with `coeff`, component order) of every component's terms, times
   `1/Z_N(oods)` at the max size (`sys_soundV`).
4. Mask offsets and the interaction's previous row are at `g_N` for every component.
5. Periodicity responses are at `pt + 2^(L_i)·g_N` (= `pt` when `L_i = N`).
6. Each Merkle leaf's values are sorted by `(log, column)`.

Items 4–6 sit under `StarkSoundV` (points and openings), as the OODS points sit under `StarkSound` today.

## The leaf's identity

Every hook value above is a circuit constant (`ctx.constant`), so a profile's sizes are baked into the
leaf circuit and its circuit hash. One leaf circuit per `(L, profile)` is the VK set of
`component-sizes.md` §4. On the Lean side, `BlockRec.Tree.leaf` and `Trust.leafSound` are keyed by a
profile index instead of `L` (milestone 3). The node circuit doesn't change (leaves are padded to one
shape).

## What `StarkSoundV` assumes (the one new assumption)

`StarkSoundV Ls pub α z coeff invZ C cs` (in `Circuit/EndToEnd.lean`) is `StarkSound` with component `i`'s
rows ranging over `2^(Ls i)` and its row valuation at that size. `StarkSoundV (fun _ => L) = StarkSound L`
(`starkSoundV_const`, `Iff.rfl`).
- Stated, not proven, like `StarkSound`.
- It stands for stwo's lifting soundness: component `i`'s columns are committed lifted (`f ∘ π^(N − L i)`).
  A constraint quotient divided by `Z_N` is low-degree iff the constraint vanishes on the `2^N` lifted
  domain. That domain is a `2^(N − L i)`-to-one image of `i`'s own `2^(L i)` domain, so the constraint
  vanishes on `i`'s own rows.
- **Needs review before anything relies on it** (owner's request); see the docstring of `StarkSoundV`.

## Status

- **Done (milestone 2):**
  - composition: `HookOk`, `partFold_soundV`, `sys_soundV`;
  - statement: `stmtWordsV`, `Hook4Ok`, `statement_soundV`;
  - end to end: `instOfV`, `StarkSoundV`, `plain_soundV`;
  - DEEP periodicity flags: `deepPer`, `deep_leaf_per`.
- **Done (milestone 3): leaf, tree and forest.**
  - **Generic over the per-block statement:** `SumOkP ok`, `LeafOutP ok`, `tree_soundP`,
    `forest_soundP`. `forest_epochV` gives the epoch hypotheses with a size per block and component.
  - **Leaf keys:** `Tree.leaf k` and `leafH : ℕ → …` already take an arbitrary key. A `(L, profile)` key is
    any injective encoding into `ℕ`, e.g. `Nat.pair L profile` or `L + 32·profile`. `block_forest.zig` must
    use the same encoding in `expected`.
  - **Mixing leaf kinds:** uniform leaves (`LeafOut`) and lifted leaves can share one tree under
    `LeafOutP BlockPubOk'` (`LeafOut.toV`, `Trust.mono`).
