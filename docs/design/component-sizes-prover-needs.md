# c1: what the prover track needs from the Lean track

Status: **2026-10-12**, prover branch `c1/prover`. Written for the Lean track (`c1/lean`); see
[component-sizes.md](component-sizes.md) and D-045.

## Nothing blocks the block leaf today

The block leaf (`src/recursion/block_rec.zig` `buildLeafCircuit`) runs the plain verifier's
**hand-written** path.
- **Not used:** the Lean composition, statement, DEEP, shift, leaf-hash or channel programs.
- **Used:** only the Lean leaf programs that read public inputs (checks, ctx, seed, `blockLeafOut`), and they don't depend on sizes.
- **Already handled in Zig** for mixed sizes:
  - per-part statement words and LogUp shift;
  - 1/Z at the largest size;
  - periodicity points;
  - sorted Merkle leaves.
- **Tested:** "mixed sizes (lifted" in `plain_verifier.zig`; "block leaf (tiered" in `block_rec.zig`.

The header-chain segment leaf (`src/recursion/leaf.zig`) does use the Lean-first programs, but it is uniform (two components at one size), so it is unaffected.

## Needed before a Lean-first verifier can take lifted proofs

`verifyPlain` refuses mixed sizes in these programs (`error.LeanProgramNeedsPerPartSizes`).

### P1. Composition (`Circuit/CompositionLogUp.lean`, export `composition_*`)

**Today:**
- hook 1 is `1/Z(oods)` at L; this stays correct for lifted parts, since Z_n(π^k p) = Z_L(p);
- hook 2 is one constant, `1/2^L`, used for every component's LogUp shift.

**Needed:** hook 2 takes the component's index and returns `1/2^(L_i)`.
- Signature: hook 2 `[i] → [1/2^(L_i)]`, where `i` is a constant in the program, in component order.
- Lean: the shift term becomes `claimed_sum_i · ninv (L_i)` (`CompositionSound` with `Shared.logSize` per part, §3 of the design).
- Zig: `compositionViaProgram` will serve hook 2 from `config.partLog(i)`.

### P2. DEEP table (`Circuit/Deep.lean`, export `deep_*`, `starked-deep-v1`)

**Today:** each response is `(tree, col, off, idx)`. A two-sample column's periodicity response uses its second point, which coincides with the periodicity point only when the column is at L.

**Needed:** a 5th field, `per`, set to 1 on periodicity responses.
- For a column of log l, the point is then `pt(off) + G_l`, with G_l = `CanonicCoset(L).step().repeatedDouble(l)`, a constant of order 2^(L−l).
- Lean: `deep_sound` with that point (stwo's `samples.zig`). A table with `per = 0` everywhere is today's table.
- Zig: `DeepTable.parse` accepts 4 or 5 fields; for `per = 1` it uses the `periodic()` helper `verifyPlain` already has.

### P3. Statement (`Circuit/Statement.lean`)

**No change needed.** Hook 4 already receives each component's header words from Zig, which now sends that part's own log size.

### P4. Merkle leaves (`Circuit/LeafHash.lean`)

**No change needed.** The programs hash the values in the order Zig gives them, and Zig now sorts them by (log, column).

### P5. Transcript and shifts

**No change needed.**
- The transcript order is unchanged.
- Mask shifts use the largest domain's step for every part, so `oods_shift_*` at L stays correct.
