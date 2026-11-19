# Block proof cost split per component, and BIP68 frequency (blocks 935,001–972,500)

Status: current · Updated: 2026-11-19 · Owner files: `src/bin/survey.zig`, `src/block/system.zig`

Answers: where a block proof's trace cells go, component by component, over the 37,500 proven blocks;
and how often BIP68 relative locktimes occur there. Asked on Delving (t/3070, ajtowns: would moving
amounts and maturity out of the coin-set layer make it cheaper?) and needed for CONNECT-RULES
([connect-rules.md](../design/connect-rules.md)).

## Method

- Tool: `survey` with `STARKED_SURVEY_NEEDS=1` prints, per block, the rows each of the 16 components
  needs (`system.shape`'s `needs`, before rounding); with `STARKED_SURVEY_BIP68=1`, the BIP68 counts.
  No witness is built and nothing is proven.
- Input: all 37,500 blocks and undo streams on the node (`/data/replay/out935`, `/data/replay/out972`),
  packed by `~/snap/pack.py`. 0 parse errors in either run.
- Cells = rows × columns. Columns per component = preprocessed + main + interaction (4 per pair of
  lookups), from `airs/block_*.json`: 1,879 in all.
- **Exact**: the rows needed. **Proven**: the rows of the size profile the prover picks
  (`sizesAuto`: tiered from 2^12, powers of two; 10 blocks fall back to uniform).
- Cells are a proxy for prover time (commitments and FFTs scale with them), not a timing.

```sh
python3 pack.py | STARKED_SURVEY_NEEDS=1 ./survey > needs.csv   # 37,500 lines, ~23 min on the node
python3 pack.py | STARKED_SURVEY_BIP68=1 ./survey > bip68.csv
```

## Result 1: the split

Trace size L: 34,131 blocks at 2^23, 1,776 at 2^22, 752 at 2^21, 841 below.

| Group (components) | Exact cells | Proven cells |
|---|---|---|
| SHA-256 of the block's bytes: txids, Merkle trees (`sha`, `msg`, `bytes`) | 82.7 % | 55.3 % |
| Commitment to block and undo data, Blake2s (`b2s`, `b2msg`, `undo`) | 13.5 % | 24.3 % |
| Sigop walk over scripts (`walk`) | 1.4 % | 13.8 % |
| Coin set: events, undo records, fingerprints (`coin`, `urec`, `fpwalk`) | 1.4 % | 4.1 % |
| Parsing and checks (`fields`, `ctx`, `tables`) | 0.9 % | 1.8 % |
| Merkle nodes (`merkle`, `wmerkle`) | 0.03 % | 0.7 % |
| Ancestry and MTP (`anc`) | 0.05 % | 0.02 % |

Per component (proven share): sha 40.0, b2s 21.6, walk 13.8, msg 11.5, bytes 3.8, coin 2.4, fields 1.8,
b2msg 1.8, fpwalk 1.3, undo 1.0, the rest below 0.5 each.

- **Amounts and maturity** are constraints of `coin` (0.4 % exact, 2.4 % proven). Moving them to
  another layer would not change the cost measurably.
- **Hashing dominates**: SHA-256 over the block's bytes plus the Blake2s commitment are 96 % of the
  exact cells. Any layering needs the SHA-256 part (txids bind the coins to the block).

## Result 2: padding is 2.6×

Total: 5.37·10^13 exact cells, 1.39·10^14 proven. `sha` is padded 1.5× (it sets L); the other
components together 5.3× (their tiers are L, L−2 or L−5, whatever they need): `walk` sits at L but
needs about L−3; `b2s` at L−2 but needs about L−4.

Tiers closer to the needs cut the proven cells by 40 % (result 4, simulated). Not measured as time. A new
profile changes the block VKs; the Lean theorems already hold for any size vector under `SizeOk`
(D-045). Decided: try it before the next full re-prove (D-055).

## Result 3: BIP68 in these blocks

279,962,123 non-coinbase inputs. Counted: inputs of version ≥ 2 transactions whose sequence has bit 31
clear and a nonzero 16-bit value (a zero value is always satisfied).

| | Inputs | Blocks with any | Max per block |
|---|---|---|---|
| Height-based locks | 1,816,618 (0.65 %) | 36,687 | 13,016 |
| Time-based locks | 6,988 (0.0025 %) | 4,510 | 74 |

The time-based locks refer to 5,626 coin creation heights (distinct per block, summed). So proving the
median time past of old blocks is needed about 0.15 times per block.

## Result 4: a tighter profile would prove 40 % fewer cells (TIERS-2, D-055)

Simulated on the same per-block needs (no proving): a candidate profile is a vector of offsets below
L; a block takes the first profile it fits, then `tiered`, then `uniform`. Offsets found by a
coordinate search on the total proven cells.

Slack below L (log2) of the components that matter, over the 35,907 blocks with L ≥ 22:

| Component | Minimum | 1st percentile | Median | `tiered` offset |
|---|---|---|---|---|
| `msg` | 0 | 0 | 1 | 0 |
| `bytes` | 0 | 1 | 2 | 0 |
| `walk` | 2 | 3 | 4 | 0 |
| `b2s`, `b2msg` | 1 | 3 | 4 | 2 |
| `undo` | 2 | 3 | 4 | 2 |
| `fpwalk` | 2 | 3 | 3 | 2 |
| `fields` | 6 | 6 | 7 | 5 |
| `coin` | 7 | 8 | 8 | 5 |
| `urec` | 7 | 8 | 10 | 5 |
| `merkle`, `wmerkle` | 9 | 10 | 10 | 5 |

| Profiles tried, in order | Proven cells | Against exact | Against current |
|---|---|---|---|
| current: `tiered`, `uniform` | 1.39·10^14 | 2.59× | |
| `walk` at L−2 only | 1.25·10^14 | 2.32× | −10 % |
| one tight profile (below), `tiered`, `uniform` | 8.39·10^13 | 1.56× | −40 % |
| two new profiles, `tiered`, `uniform` | 8.25·10^13 | 1.54× | −41 % |

The tight profile: `sha` L; `msg`, `bytes` L−1; `fpwalk` L−3; `walk`, `b2s`, `b2msg`, `undo` L−4;
`fields` L−7; `coin` L−8; `urec` L−9; `merkle`, `wmerkle` L−10; `ctx`, `tables`, `anc` unchanged. 32,475
blocks (87 %) fit it; 5,015 fall back to `tiered`, 10 to `uniform`.

- One profile gets nearly all of the gain; each profile is a set of block VKs and leaf circuits.
- Not final: CONNECT-RULES adds rows to `walk` (redeem and witness scripts) and columns to `coin`, so
  the offsets are searched again on the new needs.
- Cells, not time: to confirm with a GPU timing of one 2^23 block in both profiles.

```sh
python3 scripts/tier_search.py needs.csv   # ~1 min
```
