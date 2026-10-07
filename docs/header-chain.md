# Header-chain AIR

## v3b (2026-10-07): difficulty retarget — proven sound

- **Spec:** `nextWork` (Core `GetNextWorkRequired`, mainnet) and `getCompact`
  in `lean/StarkedAir/Spec/Bitcoin.lean`. Checked against the first real
  retarget at height 32256 (`0x1d00d86a`) and the capped case at 2016.
- **AIR:** `lean/StarkedAir/Gadgets/Retarget.lean` (rows 220–228).
  - Row 220 copies the predecessor's nBits, time and period-start time.
  - At heights that are positive multiples of 2016:
    - clamp the span (branches for below, inside and above the range, with
      exact 16-bit-limb time arithmetic);
    - compute `P0 = mant_prev · span` byte by byte;
    - then either check the quotient
      `div·mant' + ρ = 256·P0` with `ρ < div` and
      `div = 1209600·256^(1+d)`, `d = s' − s_prev ∈ {−1, 0, 1}`, plus a
      canonical mantissa ≥ 0x8000;
    - or take the cap branch: nBits must be `0x1d00ffff`, with
      `P0 ≥ 1209600·256^(28 − s_prev)`.
  - Totals: 307 constraints, degree ≤ 3, 40 preprocessed columns, 48 public
    inputs.
- **Zig:** `src/btc/retarget.zig` holds the witness and an independent
  reference `nextWork`.
- **Tests:**
  - heights 1984..2047 (cap branch at 2016);
  - heights 32192..32319 (the real change at 32256);
  - tampering with the remainder, the d flag or the clamp flag is caught;
  - a wrong period start is refused.
- **Benchmark:** about 350 headers/s on Metal with the CPU constraint
  interpreter.
- **Statement proven** (`retarget_sound`, `lean/StarkedAir/Gadgets/RetargetDiv.lean`).
  - For every header `j` of a satisfying trace whose height is a positive
    multiple of 2016:
    `nBitsOf header_j = nextWork (nBits_{j−1}) (time_{j−1}) (pst_{j−1})`.
  - The predecessor values come from the previous header in the trace, or
    from public inputs for the first header.
  - Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
  - Proof outline:
    - `rt_core`/`rt_span` (RetargetSound) give the previous exponent and the
      clamped span;
    - `rt_p0` gives `P0 = mant_prev · span`;
    - the division branch uses `rt_dhead`, `rt_divq` and `rt_rem`;
    - the cap branch uses `rt_cap`;
    - assembly goes through `nextWork_noncap`/`nextWork_cap` (Spec/RetargetMath).
  - **Soundness depends on the PoW row.** A prover could pick the division
    branch when Core would cap. The quotient would then exceed powLimit. That
    is excluded only by the PoW constraints (`s ≤ 26`, and `s = 26 →
    mant < 2^16`, exported by `header_pow_ex`), not by the retarget rows.
    Keep this coupling in mind if the PoW gadget changes.


## v3a (2026-10-06): chain state — proven sound

- **Rows 218–219** hold the header's height (< 2³⁰) and the boundary flag
  (set iff `height mod 2016 = 0`, via a range-checked
  `height = 2016·q + rem`). They also hold the period-start time and two
  auxiliary selector bits.
- **Constraints:**
  - the height increments by one per header;
  - `nBits` is unchanged inside a period;
  - the period-start time is reset at a boundary and otherwise carried.
- **Public inputs:**
  - 32..37: the segment's first height, and its predecessor's nBits and
    period-start time;
  - 38..43: the last header's height, nBits and period-start time, for
    linking segments.
- **Tests:**
  - heights 1..16 after genesis;
  - heights 1984..2047, which cross the boundary at 2016 (the period-start
    time resets to block 2016's timestamp);
  - a wrong first height or a flipped flag is caught;
  - a mid-period nBits change is refused by the generator.
- **Proof:** `lean/StarkedAir/Gadgets/StateSound.lean`, theorem
  `state_sound`, standard axioms only. For every header, in a satisfying
  trace:
  - the height is the public start height plus its index, and is below 2³⁰;
  - nBits equals the predecessor's (or the public predecessor value)
    whenever the height is not divisible by 2016;
  - the period-start time equals the header's own time at such heights and is
    inherited otherwise;
  - the last header's height, nBits and period-start time are public.
- **Not yet constrained:** the retarget value at a boundary (v3b), median
  time past (v4) and chainwork (v5). See `docs/consensus-rules.md`.


## v2 (2026-10-06): + proof of work — proven sound

- **Definition:** `HeaderChain.powCs`. It runs on each header's row 216 and
  uses the bit columns of rows 216–217 as scratch, so no new columns are
  needed. The AIR now has 218 constraints and 37 preprocessed columns.
- **Proof:** `lean/StarkedAir/Gadgets/PowSound.lean`, theorem `chain_sound_v2`.
  It depends only on `propext`, `Classical.choice` and `Quot.sound`.
- **Statement added:** every header satisfies `powOk (hash_j) (nBits_j)`.
  - `powOk` transcribes Bitcoin Core's `arith_uint256::SetCompact` plus
    `CheckProofOfWork` for mainnet: it rejects negative, overflowing and zero
    targets, requires target ≤ powLimit = 2²²⁴−1, and requires hash ≤ target.
  - The hash is the 32 digest bytes read as a little-endian integer
    (`UintToArith256`).
  - `nBits` is header bytes 72..75 read little-endian.
  - Spec: `lean/StarkedAir/Spec/Bitcoin.lean`, checked on genesis and on a
    too-hard target.
- **How the circuit does it** (the encoding is in the docstrings of
  `HeaderChain.lean`):
  - a one-hot exponent `s = nSize − 3` with `s ≤ 26`;
  - hash bytes above `s+2` must be zero;
  - `mant = mid + lt + D`, where `D` is a 24-bit range check;
  - `lt = 0` forces `D = 0` and all bytes below `s` to be zero;
  - `mant ≥ 1` via a 23-bit range check;
  - the sign bit must be 0;
  - when `s = 26`, `mant < 2¹⁶`, which together with the bound above gives
    target ≤ powLimit.
- **Completeness gap (deliberate):** encodings with `nSize < 3` cannot be
  proven. They describe targets below 2²⁴, which no real block can meet.
  Overflowing encodings are already excluded by `powLimit`.
- **Tests:**
  - mainnet blocks 0..15 satisfy the AIR;
  - a header claiming a harder `nBits` than its hash meets cannot be laid
    out;
  - tampering with `lt`, the exponent one-hot or `D` is caught.
- **Benchmark:** real mainnet headers 0..1023 on Metal run at about 500–640
  headers/s.


## v1 (2026-10-06): SHA256d + linkage — proven sound

- **Definition:** `lean/StarkedAir/Gadgets/HeaderChain.lean`
  (export: `airs/header_chain.json`, 208 constraints, 36 preprocessed columns,
  32 public inputs).
- **Witness:** `src/btc/header_chain.zig`
- **Proof:** `lean/StarkedAir/Gadgets/HeaderChainSound.lean`, theorem
  `chain_sound`. It depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

**Layout:** 256 rows per header.

| Rows | Contents |
|---|---|
| 0–71 | compression 0 (IV, header bytes 0..63) |
| 72–143 | compression 1 (bytes 64..79 + padding) |
| 144–215 | compression 2 (IV, digest + padding) |
| 216–255 | reserved for proof-of-work and difficulty checks |

Because 256 divides the trace length, there are no partial headers.

**Statement proven.** For a trace satisfying the AIR with `2^logSize` rows
(logSize ≥ 8), let `H = 2^logSize/256`. Then:

1. `sha256d(header_j) = hash_j` for every `j < H`. Here `header_j` is the 20
   words read from the trace and `hash_j` is read from compression 2's finalize
   rows. `sha256d` is FIPS 180-4 SHA-256 applied twice
   (`lean/StarkedAir/Spec/Bitcoin.lean`, checked against the genesis block).
2. `prevHash(header_j) = hash_{j−1}` for `1 ≤ j < H` (header words 1..8).
3. `prevHash(header_0)` = public inputs 0..15, as 8 words of (lo, hi) limbs.
4. `hash_{H−1}` = public inputs 16..31.

**What this does not establish yet:**
- **nBits validity** (the difficulty retarget rules), timestamps (median time
  past) and cumulative work. Proof of work is covered by v2 above.
- **The usual trust base:**
  - Zig interpreter ≡ Lean semantics (differential-tested, not proven);
  - the exporter is a faithful printer;
  - the soundness of Stwo itself.

**Tests:** real mainnet blocks 0..15 satisfy the AIR, and the tip hash equals
block 15's. Tampering is caught: a broken link (at the expected row), a wrong
padding word, and a wrong claimed tip.

**Benchmark (M4 Pro, Metal, secure profile):**

| Rows | Headers | Prove | Throughput |
|---|---|---|---|
| 2¹⁴ | 64 | 0.16 s | |
| 2¹⁶ | 256 | 0.33 s | |
| 2¹⁸ | 1,024 | 1.7 s | ≈ 600 headers/s |
