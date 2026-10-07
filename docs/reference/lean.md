# Lean code reference

Status: current · Updated: 2026-10-07 · Owner files: `lean/**`

The Lean project `lean/` (package `StarkedAir`) holds:

- the IR and its semantics;
- the specifications (FIPS 180-4 SHA-256 and Bitcoin Core consensus rules);
- every AIR definition;
- the soundness proofs, which state that a satisfying trace implies the spec.

Toolchain: Lean `v4.33.1` and Mathlib `v4.33.1` (`lean/lean-toolchain`,
`lean/lakefile.lean`). The lakefile sets `autoImplicit = false`.

## File map

Files are listed in dependency order; `lean/StarkedAir.lean` imports all of
them.

| File | Contents |
|---|---|
| `IR.lean` | `F = ZMod P`, `P = 2^31−1`, `P_prime` (Lucas–Lehmer, no `native_decide`); `Expr`, `PreCol`, `Air`, `wrap`, `Expr.eval`, `Air.Satisfied` |
| `Export.lean` | `Air.toJson` (canonical JSON printer). The driver is `lean/Export.lean`. |
| `Bits.lean` | `ofBits`, bit/limb lemmas shared by the gadgets |
| `Testing/Probe.lean` | Generates the `probe_oracle` used to differential-test the Zig interpreter |
| `Spec/Sha256.lean` | FIPS 180-4 SHA-256 over `BitVec 32`, checked against the "abc" vector |
| `Spec/Bitcoin.lean` | `sha256d`, `prevHash`, `hashNat`, `nBitsOf`, `timeOf`, `compactTarget` (SetCompact), `powOk` (CheckProofOfWork, mainnet), `compactValue`, `getCompact`, `nextWork` (GetNextWorkRequired, mainnet), with `#guard`s on genesis and on heights 2016 and 32256 |
| `Spec/RetargetMath.lean` | Pure arithmetic about `getCompact`/`nextWork`: `getCompact_of`, `getCompact_powLimit`, `quot_shift`, `nextWork_eq`, `nextWork_noncap`, `nextWork_cap` |
| `Gadgets/Add32Chain.lean` | Spike gadget and its `sound` theorem |
| `Gadgets/Sha256.lean` | SHA-256 compression AIR (layout: [airs/sha256.md](../airs/sha256.md)) |
| `Gadgets/Sha256Sound.lean` | `ShaSat`, `compress_sound`, `compress_sound_air` |
| `Gadgets/HeaderChain.lean` | Header-chain AIR: SHA256d layout, `powCs` (row 216), chain-state constraints (rows 218–219), 40 preprocessed columns |
| `Gadgets/Retarget.lean` | Retarget constraints (rows 220–228) and the final `constraints` / `air` (`header_chain_v3b`) |
| `Gadgets/HeaderChainSound.lean` | `ChainSat`, `headerWord`, `hashAt`, `pubWord`, `chain_sound` (v1) |
| `Gadgets/PowSound.lean` | `header_pow_ex`, `header_pow`, `chain_sound_v2` (v2) |
| `Gadgets/StateSound.lean` | `heightAt`, `pstAt`, `state_row`, `state_sound` (v3a) |
| `Gadgets/RetargetSound.lean` | Copies (`copy_facts`), evaluation helpers, `rt_core`, `rt_span`, `rt_p0`, `rt_dhead` |
| `Gadgets/RetargetDiv.lean` | `rt_divq`, `rt_rem`, `rt_cap`, `retarget_sound` (v3b) |

## Main theorems

Every theorem below depends only on `propext`, `Classical.choice` and
`Quot.sound`. Check with `#print axioms` (see
[status.md](../project/status.md)).

| Theorem | Statement, informally | Doc |
|---|---|---|
| `Sha256.compress_sound_air` | Every 72-row block of a satisfying trace computes FIPS 180-4 `compress` | [airs/sha256.md](../airs/sha256.md) |
| `HeaderChain.chain_sound` | Every header hashes (SHA256d) to its claimed hash; consecutive headers link; endpoints match the public inputs | [airs/header-chain.md](../airs/header-chain.md) |
| `HeaderChain.chain_sound_v2` | The above, plus `powOk hash nBits` for every header | same |
| `HeaderChain.state_sound` | Height increments from the public start; nBits is constant inside a period; the period-start time is tracked; output public inputs are correct | same |
| `HeaderChain.retarget_sound` | At heights that are positive multiples of 2016: `nBits = nextWork(prev nBits, prev time, period start)` | same |

> There is no single top-level theorem combining these yet. The roadmap
> tracks it as item `HC-TOP`.

## Proof architecture

Every gadget proof uses the same layers:

1. **Evaluation lemmas.** Rewrite `Expr.eval` of a constraint into field
   arithmetic over column values. Use the `rfl` lemmas
   `eval_mul'`/`eval_sub'`/`eval_add'` with `rw`, plus dedicated per-gadget
   lemmas such as `ev_window`, `ev_beByte` and `ev_bitsR`.
2. **Booleanity → `Bool`/`BitVec`.** Columns holding bits become `bit main c r`;
   words become `word main base r`.
3. **Lifting.** An equation in `F` whose sides are both < P becomes an
   equation in ℕ (`natCast_inj_of_lt` with `lt_P_of`).
4. **Arithmetic.** Combine the ℕ/ℤ equations with `omega`,
   `linear_combination` or small pure helper lemmas, then match the spec.

## Rules for writing proofs

These rules are mandatory. Each one cost real time when it was broken.

- **Build with `lake build <Module>`, not `lake env lean <file>`.** Only
  `lake build` applies `autoImplicit = false`.
- **No `sorry`, `native_decide` or `bv_decide` in committed code.** Run
  `#print axioms` on every new main theorem.
- **Never `simp [Expr.eval]` on a large constraint tree.** Rewrite with the
  `rfl` lemmas and dedicated evaluation lemmas instead.
- **Prove membership in big constraint lists with explicit paths**
  (`List.mem_append_left/right`, `List.mem_map`), not `simp`.
- **`omega` sees the whole local context,** including `(by omega : …)` inside
  a term. With dozens of ℕ facts it can blow up exponentially. Use
  `clear * - h₁ h₂; omega`, or move the fact into a top-level helper lemma
  (`digits4`, `digits2`, `divq_arith`, `rem_arith`, `cap_arith`).
- **`clear_value` before arithmetic.** Variables introduced with `set` over
  `(word …).toNat` stay let-bound, and definitional-equality checks will try
  to unfold and evaluate them. Clear their values first and keep the
  `with h` equations.
- **State bounds about the `set` name** (`have l : D0 ≤ 255 := …`), not about
  the original expression.
- **`rw [eval_cst]` rewrites only one instance;** use `simp only [eval_cst]`.
  Use the simprocs `Nat.reduceEqDiff`, `Nat.reduceLT` and `↓reduceIte` to
  reduce literal `if`s.
- **Normalize offset literals** (`-3` vs `-↑3`) with `wrapN` plus
  `simp only [Nat.cast_ofNat]` before rewriting.
- **Avoid name clashes:** Mathlib `round` vs `Spec.Sha256.round`.
- **Large proofs** go in their own file, with
  `set_option maxHeartbeats N in` scoped to the theorem. If a build takes
  more than ~2 minutes, bisect it: copy truncated variants of the file into
  temporary modules and build them in parallel.

## Workflow

- Add or change an AIR: [guides/adding-an-air.md](../guides/adding-an-air.md).
- Build everything: `cd lean && lake build`. The first build downloads the
  Mathlib cache with `lake exe cache get`.
