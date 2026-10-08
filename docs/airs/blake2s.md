# Blake2s compression AIR

Status: current · Updated: 2026-10-08

**What it proves:** in every aligned 88-row period, the output rows hold
RFC 7693's compression `F(h, m, t, f)` of the inputs read from that period.
Theorem `Blake2s.compress_sound_air` (`lean/StarkedAir/Gadgets/Blake2sSound.lean`),
standard axioms only. Spec: `lean/StarkedAir/Spec/Blake2s.lean`, checked against
`hashlib` vectors (including RFC 7693's "abc").

## Layout (`Gadgets/Blake2s.lean`)

| rows | role |
|---|---|
| 0–3 | init: row `k` holds the state slots of diagonal G `4+k` (`h`, IV words, `IV ⊕ t`, `IV ⊕ f`); row 0 also holds `t_lo`, `t_hi`, `f` |
| 4–83 | one G function per row (round `j / 8`, G `j % 8`) |
| 84–87 | final: row `k` outputs words `k` and `b(4+k)` (`h ⊕ v_i ⊕ v_{i+8}`, two xors at a time) |

- 300 main columns: eight 32-bit words as bits per row, 16 message words as
  16-bit limbs (copied down the period), carry bits.
- 50 preprocessed columns: row-type selectors and one-hot σ selectors (`preQ`).
- 1,455 constraints, degree ≤ 3, no lookups.
- A G row reads each input from the row that last wrote that state slot, in the
  same role, at a distance `src g role` that depends only on the G position.

## Proof structure (`Blake2sSound.lean`)

1. `g_step`: a G row's eight words are RFC 7693's `mix` (limb additions with
   carries, xor-rotations on bits; SHA-256 proof lemmas reused).
2. `col_half`, `diag_half`: a half-round maps the diagonal layout of four rows
   to the column layout of the next four, and back (16 concrete slots).
3. `steps_rounds`: after ρ rounds the spec state is the diagonal layout of rows
   `s + 8ρ …`.
4. `msg_copy`, `init_c`, `init_d`, `init_state`, `final_out`: message limbs,
   initial state and outputs.
5. `compress_sound`, `compress_sound_air`.

**Consumer obligation:** message limbs must be 16-bit (`hm`); the AIR does not
range-check them. Producers bind them by lookup to range-checked values.

## Tests

`src/hash/blake2s_air.zig`: the witness satisfies the Lean export; outputs equal
Zig's std Blake2s-256 and the reference compression (counter above 2³², non-final);
flipped output or message bits are rejected; it proves and verifies.
