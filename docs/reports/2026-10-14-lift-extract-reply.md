# Reply: `liftExtract` drafted against starked-bitcoin `9bda446`

Written 2026-10-14 by the stwo-zig session (Claude), in reply to `LIFT_EXTRACT_REQUEST.md`.

**Hand-off.**
- The patch is `~/Workshop/stwo-zig/lift-extract.patch`: one commit (`b084775`) on top of `9bda446`.
  Apply it with `git am`.
- It was made in a separate clone (`~/Workshop/starked-lift`, branch `lift-extract`). Your checkout was
  not touched.
- **Changes:** two new files and two import lines in `StarkedAir.lean`. No existing statement or proof
  changed.
- **Build:** the whole library (`lake build`, including `Compat`) builds.
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
| **`liftOK_of_offsets`** | (W) is proven for any component whose main columns are each read at no more than two offsets, given `L ≤ N`. This is where the real content is. Two-offset columns use periodicity and wrap arithmetic (`wrap_mod_pow`). One-offset columns are re-indexed so the one row reading each cell sees the big trace's value (`ownCol`); this covers a column read only at, say, +1. `offsOk` is the decidable form. |

`liftExtract` follows from (W) by definition: since (W) has to cover forced facts and repairs, I
stated it semantically. The proof work is in `liftOK_of_offsets` and in what is left to prove for the
hard components.

## `StarkedAir/Block/LiftW.lean`

- **`hashSysW i N L`:** (W) for component `i` of `hashSys`.
- **Proven (`w_bytes` … `w_undo`):** components 0, 1, 4, 5, 6, 7, 8 and 9 (bytes, fields, merkle,
  tables, walk, ctx, wmerkle, undo). Each is checked with `decide +kernel` on `offsOk`.
  - Building the file takes about 27 s and about 10 GB of memory, mostly for `block_fields`.
- **Assumed (`hardW`):** components 2, 3, 10, 11, 12, 13 and 14 (msg, sha, b2msg, b2s, fpwalk, urec,
  coin). Each has columns read at three or more offsets:

  | Component | Columns with ≥3 offsets | Most offsets on one column |
  |---|---|---|
  | msg | 1 | 4 |
  | sha | 96 | 11 |
  | b2msg | 1 | 3 |
  | b2s | 194 | 7 |
  | fpwalk | 1 | 3 |
  | urec | 1 | 3 |
  | coin | 3 | 3 |

  The evidence for these is `lifting_wrapcheck.py`.
- **`hashSysW_of_hard`:** `(∀ i < 15, Ls i ≤ N) → (∀ i ∈ hardW, hashSysW i N (Ls i)) → ∀ i < 15, LiftOK (hashSys.comp i) N (Ls i)`.
  This is what `plain_soundL`'s `hW` needs for `hashSys`.

## For your review

1. **Which columns count as two-sample.** `mainOffs` collects the distinct offsets from each
   component's constraints and lookup expressions (`exprs`). The circuit's layout uses
   `Composition.mainOffsets` over the DAG nodes. These should be the same set, but `StarkSoundL`'s
   periodicity premise is only as good as that match. If the verifier ever sees a column at a third
   offset that `exprs` doesn't, that column gets no periodicity check, and the premise claims more than
   the verifier checks. A lemma tying `mainOffs` to `mainOffsets (pNodes c)` would close this; I didn't
   write it.
2. **Row model.** The lift is big row `R ↦ R mod 2^L`, the same cyclic row model `StarkSoundV`'s
   docstring uses. That matches stwo's `π^(N−L)` only under the row indexing this library already
   assumes.
3. **(W) holds for all challenges.** `LiftOK` quantifies over all `α z share pub`. That matches the
   checker, whose argument is about which reads the terms depend on, not their values. The checker was
   run at the own sizes in the 115-run sweep; `hashSysW` is needed at the sizes you actually prove at.
4. **Connecting to the recursion theorems.** I stopped at `plain_soundL`. Moving the `RecCR` and leaf
   theorems to `StarkSoundL` is mechanical: replace `hstark`, add `hW`. I left it for you, since those
   statements are yours to restate.

## Also: the remainder-fold fix

- **H100 run here (2026-10-14).** For `fibonacci` with `fold_step = 4`, I proved under last-layer
  bounds 0–3; bound 3 makes the last round fold by 1.
  - Before the fix, bound 3 fails with `InnerLayerCommitmentInvalid`.
  - After the fix, every bound matches the CPU prover byte-for-byte.
- **Upstream:** https://github.com/teddyjfpender/stwo-zig/pull/299.
