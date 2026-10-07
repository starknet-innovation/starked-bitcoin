# Header consensus rules beyond proof of work — design

Status: current · Updated: 2026-10-07

Design for the header rules beyond SHA256d and proof of work. v3a and v3b
are implemented and proven (see [airs/header-chain.md](../airs/header-chain.md)).
v4 and v5 are implemented and proven.

Bitcoin Core's contextual header checks are in `ContextualCheckBlockHeader`
and `GetNextWorkRequired`. For mainnet:

1. **Difficulty.**
   - If `height % 2016 ≠ 0`, `nBits` equals the previous block's.
   - At a boundary, `nBits = GetCompact(min(powLimit, T_prev · clamp(Δt) / 1209600))`.
     - `T_prev = SetCompact(nBits_prev)`.
     - `Δt = time_prev − time_{height−2016}`. This is Core's "2015 intervals"
       off-by-one, preserved.
     - `clamp` bounds Δt to `[302400, 4838400]`.
2. **Median time past:** `time > median(time of the previous 11 blocks)`. For
   heights below 11, fewer blocks are available, and the median index is
   `k/2` of the `k` available.
3. **Cumulative work** (fork choice, not validity): each block adds
   `floor(2²⁵⁶ / (T+1))`.
4. **Not provable:** `time ≤ now + 2h` depends on wall-clock time.
   Version-bit rules (BIP9 and later) do not affect header validity for
   history.

## State carried across headers

A proof covers a segment of consecutive headers. Each header row-block
carries the state needed by the next one. A segment's first-header inputs and
last-header outputs are public, so that segments can be chained during
aggregation.

| State | Width | Where |
|---|---|---|
| hash | 256 | rows 212–215 (existing) |
| height | 32 | row 218 `a` (new) |
| period-start time `pst` (time of the block at `height − height % 2016`) | 32 | row 218 `e` (new) |
| nBits | 32 | header word 18 (existing, row 78) |
| time | 32 | header word 17 (existing, row 77) |
| previous 11 times | — | read from earlier headers with constant offsets. Only a segment's first 11 headers need public inputs for times before the segment. |
| chainwork | 256 | later |

## Plan (each step: Lean AIR → export → Zig witness + tests → Lean proof)

- **v3a.**
  - Height counter: `height_j = height_{j−1} + 1`; the first header's height
    is public.
  - Boundary flag: `height = 2016·q + rem` with range-checked bits; the flag
    is set iff `rem = 0`.
  - `nBits_j = nBits_{j−1}` when not at a boundary. The first header compares
    against a public `nBits_prev`.
  - `pst` carried forward, or reset to `time_j` at a boundary.
- **v3b.** Retarget at boundaries, using 256-bit limb arithmetic in the
  reserved rows:
  - `1209600·T' ≤ T_prev·clamp(Δt) < 1209600·(T' + 256^s')`;
  - `T'` is canonical, i.e. its mantissa is in `[0x8000, 0x7fffff]`;
  - the powLimit cap, via a flag.
- **v4.** MTP: count ≥ 6 of the previous 11 times strictly below
  `time_j`, each with a range-checked difference. Heights < 11 use a fixed
  sentinel history on the genesis segment (see
  [airs/header-chain.md § v4](../airs/header-chain.md)). Implemented and
  proven.
- **v5.** Chainwork as a sound lower bound: `q·(T+1) ≤ 2²⁵⁶`, accumulated.

Scratch space: rows 218–255 of each header (38 rows × 96 bit columns, plus
16 carry bits per row). Every scratch value is held in bit columns.
