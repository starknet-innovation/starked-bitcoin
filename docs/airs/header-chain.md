# Header-chain AIR

Status: current · Updated: 2026-10-07 · Owner files: `lean/StarkedAir/Gadgets/{HeaderChain,Retarget,*Sound,RetargetDiv}.lean`, `src/btc/`

Versions are listed newest first. The guarantees as a whole are in
[reference/verification.md](../reference/verification.md).

## Top-level guarantee (2026-10-07)

`header_chain_sound` (`lean/StarkedAir/Gadgets/TopSound.lean`, standard axioms
only): any trace satisfying the AIR with `2^logSize` rows proves
`SegmentValid` (`lean/StarkedAir/Spec/Chain.lean`) for its
`H = 2^logSize/256` headers, from `decodeIn pub realWindow` to
`decodeOut pub`. `SegmentValid` is stated over Bitcoin objects only:
- every header meets `CheckProofOfWork`;
- the first prev-hash is the input, consecutive headers link, and the tip
  is the output;
- heights run consecutively from the input height (< 2^30);
- nBits is constant inside a period and equals `GetNextWorkRequired` at every
  boundary above 0;
- every header passes the median-time-past check over its real predecessors;
- the output chainwork is the input plus Σ `GetBlockProof`;
- the output nBits, time, period-start time and window are those of the
  last header.

Obligations on the public inputs, checked by the verifier or aggregator:
- the window inputs equal the real predecessor times padded with
  `sentinel`;
- the input-work limbs are 16-bit;
- for a segment starting at genesis: an empty real window, input work 0, and
  prev-hash 0.

## v6 (2026-10-07): minimum block version — proven sound

Roadmap `HC-V6`. Core `ContextualCheckBlockHeader` "bad-version": `nVersion`
(int32) must be ≥ 2, 3, 4 from heights 227931 (BIP34), 363725 (BIP66) and
388381 (BIP65). These heights were checked against Core's `chainparams.cpp`
on 2026-10-07. Spec: `versionOf`, `versionInt`, `versionOk` in
`Spec/Bitcoin.lean`, with `#guard`s.

- **Layout:** rows 254–255, with constraints at row 254 (selector `VER`,
  preprocessed column 53).
  - Exact flags `f_k = [h ≥ T_k]`: each comes with a 30-bit difference
    (`h = T_k + d` or `h + 1 + d = T_k`).
  - When `f_1 = 1`: `nVersion = m + e` over two 16-bit limbs, with
    `m = 1 + f_1 + f_2 + f_3`, and the int32 sign bit equal to 0.
  - Definition: `lean/StarkedAir/Gadgets/Version.lean` (`header_chain_v6`,
    520 constraints, 54 preprocessed columns).
- **Proof:** `version_sound` (`Gadgets/VersionSound.lean`). It is part of
  `SegmentValid` and `header_chain_sound`.
- **Tests:**
  - a real segment at heights 400000..400063 (versions 4 and 0x30000000)
    satisfies v6;
  - tampering with a flag, the slack or the difference is caught.

## v5 (2026-10-07): exact chainwork — proven sound

Roadmap `HC-V5`. Decisions: D-020 (exact), D-021 (`s ≥ 16`). Spec: `blockProof` in
`lean/StarkedAir/Spec/Bitcoin.lean`, with Core's formula
`(~T / (T+1)) + 1`; `blockProof_eq` proves it equals `⌊2^256 / (T+1)⌋`.

**Enforced per header:** with `T = mant · 256^s` from the proof-of-work row:
- `q = ⌊2^256/(T+1)⌋`, via `R = q·mant`, `R·256^s + q + ρ = 2^256` and
  `ρ + σ = T`. All are byte-column identities with range-checked carries, so
  `0 ≤ ρ ≤ T` and the division is exact.
- `W_j = W_{j−1} + q_j`, as 16-bit limbs.
- The first header takes `W_{−1}` from public inputs 88..97; the last
  header's `W` is public inputs 98..107.

**Statement proven** (`lean/StarkedAir/Gadgets/WorkSound.lean`, standard axioms only):
- `work_q`: each header's `q` digits (`workQ`) equal `blockProof (nBitsOf header)`
  (Core `GetBlockProof`).
- `work_step`: `workAt j = (j = 0 ? pubWork pub 88 : workAt (j−1)) + blockProof(nBits_j)`.
  It assumes the input-work public limbs are 16-bit (a verifier obligation).
- `work_out`: the last header's `workAt` = `pubWork pub 98`.
- The proof rests on three generic column-arithmetic lemmas: `carry_chain`
  (column sums with carries), `shift_sum` (shift by the one-hot exponent)
  and `cauchy` (schoolbook product).

**Layout:** rows 241..253, with all constraints at row 248 (selector
`WORK`, preprocessed column 52). The row map is in the header comment of
`lean/StarkedAir/Gadgets/Work.lean`.

**Completeness bound (D-021):** `s ≥ 16` (target ≥ 2^128), so `q` and `R`
fit in 16 bytes. Mainnet targets have `s ≥ 20`.

**Totals:** 514 constraints, 53 preprocessed columns, 108 public inputs,
2,514 column/offset reads.

**Zig:** `src/btc/work.zig` (`scratch`, `blockProof`); `ChainStart.work`.

**Tests:**
- chainwork after height 15 = `0x1000100010` (Core);
- after height 32319 = `0x7e4c32ec7280` (independent Python reference);
- tampering with `q`, `R`, `ρ`, `W` or a carry is caught;
- a wrong input-work public input is caught;
- `s = 15` is refused.

**Benchmark** (M4 Pro, Metal, 70 queries, 26-bit PoW, 2026-10-07): 1024
headers at 2¹⁸ rows. Proving takes 4.28 s (≈ 239 headers/s), verifying 0.13 s,
and the proof is 1.11 MB.

## v4 (2026-10-07): median time past — proven sound

Roadmap `HC-V4`; counting approach per decision D-018. Spec: `mtpOk` in
`lean/StarkedAir/Spec/Bitcoin.lean`. Counting equivalence: `mtpOk_iff_count` in
`lean/StarkedAir/Spec/MtpMath.lean` (proven).

**Rule enforced.** For every header with time `t` and window `T_1..T_11` (the
previous 11 times, newest first): `#{i : T_i < t} ≥ 6`.

**Layout** (rows of each header; slot `i = row − 228`):

| Row | `a` | `e` | `w` | col 108 | col 109 |
|---|---|---|---|---|---|
| 229..239 (slot 1..11) | `T_i` (raw time word) | `d_i` (numeric, 32 bits) | own time `t` (raw word) | `b_i = [T_i < t]` | lo-limb carry `c_i` |
| 240 | bits 0..2: `r = Σ b_i − 6` | — | — | — | — |

**Constraints:**
- **Own-time copies:** `w@229 = w@77` (offset −152), and `w@r = w@r−1` for rows 230..239.
- **Window.**
  - `T_1 = e@220`, the predecessor's time copy. That copy is already pinned
    to public input 44/45 for the first header.
  - `T_i = a@−257` (the predecessor's `T_{i−1}`) for `i ≥ 2` on non-first
    headers.
  - On the first header, `T_i` = public inputs `48 + 2(i−2) + h`.
- **Comparison** (degree 3, on the 16-bit numeric limbs `timeLimb`):
  - `b = 1`: `T + 1 + d = t`, so `T < t`;
  - `b = 0`: `t + d = T`, so `T ≥ t`.
  - The lo limb carries into the hi limb through `c`, and the hi limb has no
    carry out, so each branch holds exactly over ℕ.
- **Count:** at row 240, `Σ_{i} col108@(i−12) − 6 = r`, where `r` is 3 bits,
  so `Σ ≥ 6`.
- **Outputs (last header):** `T_1..T_10` → public inputs `68..87`. The last
  header's own time is already public input 46/47. The next segment takes
  pubs 44/45 and 48..67 from these.
- **Selectors:** 12 new one-row selectors (rows 229..240), giving 52
  preprocessed columns. Public inputs: 88.

**Heights below 11 (sentinel history).** Core takes the median over the
`k = h` existing predecessors. The circuit always uses 11 slots. The
segment that starts at genesis takes a fixed **sentinel history** as its
public inputs: `T_1 = 0xFFFFFFFF` (pubs 44/45), then
`T_2..T_11 = 0, max, 0, max, 0, max, 0, max, 0, 0` (`max = 0xFFFFFFFF`).
At height `h ≤ 10`, the visible sentinels are the first `11 − h` of that
list. They contain exactly `5 − ⌊h/2⌋` zeros (6 at `h = 0`), so
`count ≥ 6 ⟺ #{real T_i < t} ≥ ⌊h/2⌋ + 1`, which is Core's rule. Genesis
itself (no rule) passes because the 6 zero-sentinels are below any `t > 0`.
**Verifiers must check that a segment starting at height 0 uses exactly this
sentinel history.**

**Definition:** `lean/StarkedAir/Gadgets/Mtp.lean` (`mtpCs`; the file also
assembles the full `constraints` and `air`, now `header_chain_v4`). Totals: 394
constraints, 52 preprocessed columns, 88 public inputs.

**Zig:** `ChainStart.window` (11 raw time words, newest first), `windowFrom`
(pads with `SENTINEL` near genesis). The generator refuses a header that fails
the rule (`error.TimeTooOld`).

**Statement proven** (`lean/StarkedAir/Gadgets/MtpSound.lean`, standard axioms only):
- `mtp_count`: for every header `j`, at least 6 of its window times
  `winAt main j 1..11` are strictly below its own time (numeric, `leN`).
- `mtp_window`: `T_1 = prevTime`; on non-first headers `T_{i+1}(j) = T_i(j−1)`;
  on the first header `T_{i+1} = pubWord pub (48 + 2(i−1))`.
- `mtp_out`: the last header's `T_1..T_10` are public inputs 68..87.
- `mtp_core`: if a header's window is its real predecessors' times padded with
  the sentinel, the header passes Core's `GetMedianTimePast` check
  (`mtpOk`). It rests on `mtpOk_iff_count` and `sentinel_sound`
  (`Spec/MtpMath.lean`).
- Showing along a whole chain that the window *is* the real predecessors'
  times is the job of the top-level theorem (roadmap `HC-TOP`), by induction
  with `mtp_window`.

**Benchmark** (M4 Pro, Metal, 70 queries, 26-bit PoW, 2026-10-07): mainnet
headers 0..1023 at 2¹⁸ rows. Proving takes 3.65 s (≈ 280 headers/s, against
≈ 350 at v3b), verifying 0.13 s, and the proof is 1.07 MB.

**Tests** (`src/btc/header_chain.zig`):
- every existing segment satisfies v4, including the genesis segment with the
  sentinel window and segments at 1984 and 32192 with real 11-block
  pre-histories;
- window outputs equal the last header's predecessor times;
- a window entirely in the future is refused;
- tampering with a comparison bit, a difference bit, a window word or the
  count slack is caught, as is a wrong window public input;
- 100,000 random cases check that the sentinel counting rule matches Core's
  sorted median (sound always, and complete for `t > 0`).

## Earlier versions

v1 (SHA256d and linkage), v2 (proof of work), v3a (chain state) and v3b
(difficulty retarget): [header-chain-history.md](header-chain-history.md).
