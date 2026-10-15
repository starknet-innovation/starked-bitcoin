# Reply: `liftExtract` drafted against starked-bitcoin `9bda446`

Written 2026-10-14 by the stwo-zig session (Claude), in reply to `LIFT_EXTRACT_REQUEST.md`; updated
2026-10-15. This version replaces the earlier reply: the patch now has a second commit, review item 1 is
closed, and (W) is proven for three more components.

**Hand-off.**
- The patch is `~/Workshop/stwo-zig/lift-extract.patch`: two commits (`b084775`, `a69085b`) on top of
  `9bda446`. Apply it with `git am`.
- It was made in a separate clone (`~/Workshop/starked-lift`, branch `lift-extract`). Your checkout was
  not touched.
- **Changes:** four new files (`Circuit/Lift.lean`, `Circuit/LiftOffs.lean`, `Circuit/LiftGuard.lean`,
  `Block/LiftW.lean`) and four import lines in `StarkedAir.lean`. No existing statement or proof
  changed.
- **Build:** the whole library (`lake build`, including `Compat`) builds. Peak memory about 7 GB;
  `LiftW` takes about 60 s.
- **Axioms:** `#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` for every new
  theorem. There is no `sorry`, `axiom` or `native_decide`.

## `StarkedAir/Circuit/Lift.lean`

| Name | What it is |
|---|---|
| `liftVal N L pre T S R` | The valuation at big row `R` of a `2^N` trace. Main and interaction columns are read cyclically at `2^N`. Preprocessed columns are read as lifts: `eval (2^L) (wrap (2^N) R off % 2^L)`. |
| `PeriodicCols c N L T S` | Every two-sample column is `2^L`-periodic. Two-sample columns are main columns read at exactly two distinct offsets (`mainOffs`), and the last interaction batch's four columns (offsets −1 and 0). |
| `BigOK` / `SmallOK` | Every term vanishes at every big row (lifted) or at every own row (`rowVal (2^L)`). |
| **`StarkSoundL N Ls …`** | The primitive assumption. If the composition check passes, there are size-`2^N` columns `T, S` with `BigOK` and `PeriodicCols` for every component. Shares are unchanged (`claimed / 2^(Ls i)`). FRI and Schwartz–Zippel stay trusted, as in `StarkSound`. |
| **`LiftOK c N L`**, which is (W) | Any `BigOK` and `PeriodicCols` big trace yields own-size columns with `SmallOK`. It is a `Prop`, not an axiom. |
| **`liftExtract`** | The lemma as you stated it: (W), `BigOK` and periodicity give `SmallOK`. |
| **`starkSoundV_of_lift`** | `(∀ i, LiftOK cs[i].1 N (Ls i)) → StarkSoundL N Ls … cs → StarkSoundV Ls … cs`. |
| **`plain_soundL`** | `plain_soundV` with `hstark : StarkSoundV` replaced by `hW : ∀ i < sys.m, LiftOK (sys.comp i) N (Ls i)` and `hstark : StarkSoundL N Ls …`. |
| **`liftOK_of_offsets`** | (W) for any component whose main columns are each read at no more than two offsets, given `L ≤ N`. Two-offset columns use periodicity and wrap arithmetic (`wrap_mod_pow`). One-offset columns are re-indexed so the one row reading each cell sees the big trace's value (`ownCol`). `offsOk` is the decidable form. |
| `terms_congr_exprs` | Terms agree when every expression's value agrees (`terms_congr` is now a corollary). |

`liftExtract` follows from (W) by definition: since (W) has to cover forced facts and repairs, I
stated it semantically. The proof work is in `liftOK_of_offsets` and `liftOK_of_guard`.

## `StarkedAir/Circuit/LiftOffs.lean`: `mainOffs` is the verifier's offset set

- **`mem_mainOffsets_iff`:** `off ∈ Composition.mainOffsets (pNodes c) j ↔ off ∈ mainOffs c j`, for
  every column. The proof follows the hash-consing emitter: emitting an expression adds exactly its
  main reads to the node array (`emitN_cols`), because every shared key's reads were already emitted.
- **`mainOffsets_perm`:** the two lists are permutations of each other (both are duplicate-free).
- **`mainOffs_length_eq_shape`:** for `j < nMain`, the number of offsets in the layout
  (`compShape c nPub`) equals `(mainOffs c j).length`. So `PeriodicCols` asks periodicity of exactly the
  columns the verifier samples at two offsets.
- **`colsOk`, `lt_nMain_of_mem_mainOffs`:** every column a component reads is below `nMain`, so the
  previous point covers every column `mainOffs` names. `hashSys_colsOk` (in `LiftW`) checks this for all
  15 components by `decide +kernel`.

## `StarkedAir/Circuit/LiftGuard.lean`: (W) with guarded wrapped reads

- **Own trace:** columns with at most two offsets as in `liftOK_of_offsets`; a column with three or
  more is the window `T j`. A read disagrees with the big trace only if it wraps around `2^L`, which
  happens only in the first and last `K` rows (`K` bounds every offset).
- **Check (`guardOk`):** at each relative row `ρ ∈ [−K, K)` (`ρ < 0` means row `2^L + ρ`), no
  expression depends on a wrapped read (`dep`) once known subexpressions are folded (`kv`). Known
  values come from:
  - preprocessed columns at relative rows, valid for every `L ≥ L0` (`preSym`);
  - **cell facts** `(j, σ)`: column `j` vanishes at every big row congruent to `σ` mod `2^L`. Each is
    justified by a constraint `a · col j o` whose `a` is a known nonzero constant there; the lifted
    preprocessed columns make this hold at every congruent big row;
  - **row facts** `(ρ, g, side)`: a constraint `g = a · b` with `a` a known nonzero constant at `ρ` and
    `b` not depending on wrapped reads, so `b` vanishes at `ρ` in both traces.
- **`liftOK_of_guard`:** `L0 ≤ L → L ≤ N → guardOk c L0 K cells rf → LiftOK c N L`. The check is
  decidable; each component needs a small certificate (`K`, cells, row facts).

## `StarkedAir/Block/LiftW.lean`

- **`hashSysW i N L`:** (W) for component `i` of `hashSys`.
- **Proven by offset count (`w_bytes` … `w_undo`):** components 0, 1, 4, 5, 6, 7, 8 and 9 (bytes,
  fields, merkle, tables, walk, ctx, wmerkle, undo). Each is checked with `decide +kernel` on `offsOk`.
- **Proven by guarded wraps (`w_b2msg`, `w_fpwalk`, `w_urec`), for own sizes `L ≥ 5`:** components 10,
  12 and 13. Each has one column read at offsets `−1, 0, +1`.
  - b2msg and urec: every wrapped read sits under a preprocessed guard (`1 − isFirst`, `1 − notLast`)
    that vanishes at that row. No facts needed.
  - fpwalk: constraints 7 and 18 wrap at rows 0 and −1. Their other factor is forced to zero there by
    constraints 6 (`isFirst · X`) and 17 (`(1 − notLast) · Y`): two row facts.
- **Assumed (`hardW`):** components 2, 3, 11 and 14 (msg, sha, b2s, coin). The evidence is
  `lifting_wrapcheck.py`.

  | Component | Columns with ≥3 offsets | Most offsets on one column | Why the guard check misses it |
  |---|---|---|---|
  | msg | 1 | 4 | Two lookup values read the column at wrapped rows 0–2. The multiplicity vanishes there, but the batch term still sees the values through the denominator. |
  | sha | 96 | 11 | 250 wrapped instances; not attempted. |
  | b2s | 194 | 7 | 258 wrapped instances; not attempted. |
  | coin | 3 | 3 | The wrapped reads are zero because a sum of boolean columns is forced to zero at the last row, so each column is. The check doesn't reason about booleans. |

- **`hashSysW_of_hard`:** `(∀ i < 15, Ls i ≤ N) → (∀ i < 15, 5 ≤ Ls i) → (∀ i ∈ hardW, hashSysW i N (Ls i)) → ∀ i < 15, LiftOK (hashSys.comp i) N (Ls i)`.
  This is what `plain_soundL`'s `hW` needs for `hashSys`. The `5 ≤ Ls i` premise comes from the
  guarded proofs.

## For your review

1. **Which columns count as two-sample (closed).** `StarkSoundL`'s periodicity premise is stated with
   `mainOffs`, read off the component's expressions. `LiftOffs.lean` proves this is the same offset set
   as `Composition.mainOffsets (pNodes c)`, which the layout uses (`compShape`). The layout covers
   columns `j < nMain` only; `hashSys_colsOk` proves no `hashSys` component reads another column
   (`StaticOk` does not check this).
2. **Row model.** The lift is big row `R ↦ R mod 2^L`, the same cyclic row model `StarkSoundV`'s
   docstring uses. That matches stwo's `π^(N−L)` only under the row indexing this library already
   assumes.
3. **(W) holds for all challenges.** `LiftOK` quantifies over all `α z share pub`. That matches the
   checker, whose argument is about which reads the terms depend on, not their values. The guarded
   proofs hold at every own size `L ≥ 5`; the offset-count proofs at every `L ≤ N`.
4. **Connecting to the recursion theorems.** I stopped at `plain_soundL`. Moving the `RecCR` and leaf
   theorems to `StarkSoundL` is mechanical: replace `hstark`, add `hW`. I left it for you, since those
   statements are yours to restate.

## Also: the remainder-fold fix

- **H100 run here (2026-10-14).** For `fibonacci` with `fold_step = 4`, I proved under last-layer
  bounds 0–3; bound 3 makes the last round fold by 1.
  - Before the fix, bound 3 fails with `InnerLayerCommitmentInvalid`.
  - After the fix, every bound matches the CPU prover byte-for-byte.
- **Upstream:** https://github.com/teddyjfpender/stwo-zig/pull/299.
