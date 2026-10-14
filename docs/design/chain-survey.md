Status: **complete: every block 0–971,297 sized** (full pass collected 2026-10-14; the 1-in-10 sample of 2026-10-13 is kept below).

# Chain survey: trace size and GPU class of every mainnet block

## Question

Which trace size (L, profile) does the block prover choose for each mainnet block, and how much GPU memory does that need? This lets blocks be bucketed by the GPU they need.

## Method

- **Needs without witnesses.** `system.shape` (src/block/system.zig) computes everything `buildFull` sizes by:
  - the tokens, messages and SHA plan (with the txid tree's compressions);
  - the in-circuit undo stream, the trees, the undo records and the fingerprint segments;
  - from these, `needs[C.*]`, the rows each of the 16 components needs.
- **Same code path.** `buildFull` now calls `shape` itself, so the two cannot drift apart. `sizeReport(needs)` gives:
  - `sizesAuto(needs, 0)` (D-046);
  - the uniform L;
  - the binding component (the one whose need sets L);
  - on a fallback, the first component that missed its tier;
  - Lean's `SizeOk`.
- **Agreement test.** "shape's needs give buildFull's (L, profile) on every sample" checks all 11 samples in `checks.zig`. The large ones run with `STARKED_SURVEY_LARGE=1` and ReleaseFast. All agree:
  - 0, 91722 and 91842: 11 uniform;
  - 170, 91812 and 91880: 12 tiered;
  - 400000, 481824 and 709632: 22 tiered;
  - 774628 and 970347: 23 tiered.
- **Golden proofs.** The golden proof hashes and the other `block system` tests still pass after the refactor.
- **Arena per (L, profile).** The CUDA planner gives it: `prover.Prepared.init(..., .device_logup).memory.bytes()` with the production `prove_rec.config(L)`.
  - Run: `STARKED_ARENA_TABLE=1 zig build cuda-test -Dcuda=true -Dtest-filter="chain survey"` on the Mac. No GPU is needed.
  - The table is embedded in `src/bin/survey.zig`.
  - It matches gpu-cuda.md: 26.42 GiB at 2^22 tiered, 52.82 GiB at 2^23 tiered, 98.25 GiB at 2^22 uniform.
- **`survey` binary** (`zig build -Doptimize=ReleaseFast -Dtarget=aarch64-linux-gnu`, CPU only).
  - Input on stdin: records of (height, raw block, fetched undo stream).
  - Output: one CSV line per block: `height,L,profile,block_bytes,undo_bytes,ntx,uniform_L,binding,misfit,covered,arena_gib`.
  - `undo_bytes` is the fetched stream's length (fetch_undo.py's format), not the in-circuit stream's.
- **Node driver** (`scripts/survey_driver.py`, `scripts/survey_run.sh`, in `~/survey` on the node).
  - Reads with read-only RPC only, using the node's cookie (read with `sudo -n cat`, kept in memory).
  - Per height it calls `getblockhash`, then `getblock 0`. It checks that the header hashes to the block hash.
  - For blocks with more than one transaction it also calls `getblock 3`. The undo stream is built from the `prevout`s exactly as `fetch_undo.py` builds it.
  - It scans the verbosity-3 JSON with a regex, without parsing it, to keep memory small. The binary checks that the record count matches the block's inputs.
  - The streams equal `testdata/undo` for 170, 400000, 774628 and 970347.
- **Run settings.** 3 workers under `nice -n 19 ionice -c3`. Each worker appends to its own `out/w{k}.csv`, and a restart skips heights already done.
  - Pass 1 covered every height divisible by 10; pass 2 covers the rest.
  - Our processes use about 100 MB in total. bitcoind's JSON generation is the bottleneck: it uses about 2.2 of the 4 cores, and the load is about 3.4.
  - Throughput is about 15 MB/s of blocks, or 6–10 blocks/s for recent blocks.
  - The node stayed in sync (blocks = headers) and nothing swapped.
- **Summary.** `scripts/survey_summary.py <csv|dir> [headers.bin]` prints every table below.

**GPU classes.** A block fits a device when its planned arena plus 1.5 GiB fits the device's nvidia-smi total. The 1.5 GiB covers the context: the 2^22 tiered run showed 25.6 GiB planned as 26.9 GB in nvidia-smi. The nvidia-smi totals used are:

| Device | nvidia-smi total |
|---|---|
| RTX 4090 | 24,564 MiB |
| L40S | 46,068 MiB |
| A100 / H100 80 GB | 81,559 MiB |
| H100 NVL | 95,830 MiB |
| H200 | 143,771 MiB |

The arena takes only a few distinct values, all far from these limits, so the headroom choice does not change any bucket.

## Arena per (L, profile)

| L | uniform GiB | tiered GiB |
|---|---|---|
| 11 | 0.05 | – |
| 12 | 0.10 | 0.04 |
| 16 | 1.54 | 0.42 |
| 18 | 6.14 | 1.66 |
| 19 | 12.28 | 3.31 |
| 20 | 24.56 | 6.61 |
| 21 | 49.13 | 13.21 |
| 22 | 98.25 | 26.42 |
| 23 | 196.50 | 52.82 |
| 24 | 393.00 (not SizeOk) | 105.64 |

## Results (full pass: all 971,298 blocks, 2026-10-14)

No block errored and every block is covered by `SizeOk`. The sample's estimates hold, with one correction: **3 blocks need 2^24 tiered** (the sample had none).

| GPU class (arena + 1.5 GiB fits) | blocks | share | cumulative |
|---|---|---|---|
| ≤ 24 GB (RTX 4090) | 440,343 | 45.34 % | 45.34 % |
| ≤ 48 GB (L40S / A6000) | 293,900 | 30.26 % | 75.59 % |
| ≤ 80 GB (A100 / H100) | 236,968 | 24.40 % | 99.99 % |
| ≤ 94 GB (H100 NVL) | 0 | 0 | 99.99 % |
| ≤ 141 GB (H200) | 87 | 0.01 % | 100 % |

- **H200 blocks (87).**
  - 84 are 22 uniform (98.25 GiB), the b2msg fallbacks of undo-heavy blocks, for example 491072–491097 and 933734–960848.
  - 3 are **24 tiered** (105.64 GiB): 367851 and 367853 (~1 MB, ~10–12k transactions, 2015) and 836361 (1.72 MB, 8,320 transactions). SHA binds.
  - The owner's decision (2026-10-14): these go to an H200; no third profile.
- **Largest classes.** 22 tiered: 293,847 blocks (30.3 %). 23 tiered: 236,765 (24.4 %). 11 uniform: 86,958 (9.0 %).
- **Uniform fallbacks: 998** (the sample estimated ~870). Of those, 202 are 21 uniform (`fpwalk`, 2012–2015) and 83 are 22 uniform (`b2msg`). The summary script lists every misfit with examples.
- **The size changes from block to block.** Of the aligned groups of 16 consecutive blocks, only 7,906 of 60,706 have one (L, profile): 2,737 of 12,500 in heights 0–199,999, 24 of 12,500 in 200,000–399,999, 1,988 in 400,000–599,999, 434 in 600,000–799,999, and 2,723 of 10,706 after that. This decides aggregation: a circuit that verifies several block proofs depends on the tuple of their sizes. So the aggregation width belongs in the node (`block-rec.md` § Wide nodes), not in the leaf.
- **Data.** `data/chain-sizes.csv` (local, 971,298 lines, from the node's `survey/out/w*.csv`). `scripts/survey_summary.py` regenerates the tables.

## Results (1-in-10 sample: 97,130 blocks, heights ≡ 0 mod 10; multiply by 10 for the chain)

No block errored and every block is covered by `SizeOk`. No sampled block needs L ≥ 24 (the full pass found 3).

### By GPU class

| GPU class | sample | share | ≈ chain |
|---|---|---|---|
| ≤ 24 GB (RTX 4090): L ≤ 21 tiered, L ≤ 19 uniform | 43,928 | 45.2 % | 439k |
| ≤ 48 GB (L40S / A6000): 22 tiered, 20 uniform | 29,503 | 30.4 % | 295k |
| ≤ 80 GB (A100 / H100): 23 tiered, 21 uniform | 23,694 | 24.4 % | 237k |
| ≤ 94 GB (H100 NVL) | 0 | 0 | 0 |
| ≤ 141 GB (H200): 22 uniform (fallbacks) | 5 | 0.005 % | ≈ 50 |
| more | 0 | 0 | 0 |

### By (L, profile)

| L | profile | sample | share |
|---|---|---|---|
| 10–11 | uniform | 8,713 | 9.0 % |
| 12–19 | tiered | 20,979 | 21.6 % |
| 12–19 | uniform (fallbacks) | 61 | 0.06 % |
| 20 | tiered | 7,722 | 7.95 % |
| 21 | tiered | 6,453 | 6.64 % |
| 22 | tiered | 29,497 | 30.37 % |
| 23 | tiered | 23,679 | 24.38 % |
| 20 / 21 / 22 | uniform (fallbacks) | 6 / 15 / 5 | 0.03 % |

### By height (50k ranges; sample counts per GPU class)

| heights | years | modal | ≤ 24 GB | ≤ 48 GB | ≤ 80 GB | H200 |
|---|---|---|---|---|---|---|
| 0–249,999 | 2009–2013 | 11 uniform → 20 tiered | 24,998 | 2 | 0 | 0 |
| 250,000–299,999 | 2013–2014 | 20 tiered | 4,920 | 80 | 0 | 0 |
| 300,000–349,999 | 2014–2015 | 21 tiered | 4,349 | 644 | 7 | 0 |
| 350,000–399,999 | 2015–2016 | 22 tiered | 2,702 | 2,264 | 34 | 0 |
| 400,000–449,999 | 2016–2017 | 22 tiered | 1,230 | 3,622 | 148 | 0 |
| 450,000–499,999 | 2017 | 22 tiered | 358 | 4,531 | 110 | 1 |
| 500,000–549,999 | 2017–2018 | 22 tiered | 1,370 | 3,288 | 342 | 0 |
| 550,000–599,999 | 2018–2019 | 22 tiered | 662 | 2,515 | 1,823 | 0 |
| 600,000–649,999 | 2019–2020 | 22 tiered | 622 | 2,741 | 1,637 | 0 |
| 650,000–699,999 | 2020–2021 | 22 tiered | 415 | 3,274 | 1,311 | 0 |
| 700,000–749,999 | 2021–2022 | 22 tiered | 1,133 | 2,230 | 1,637 | 0 |
| 750,000–799,999 | 2022–2023 | 23 tiered | 575 | 1,672 | 2,753 | 0 |
| 800,000–849,999 | 2023–2024 | 23 tiered | 16 | 903 | 4,079 | 2 |
| 850,000–899,999 | 2024–2025 | 23 tiered | 105 | 962 | 3,932 | 1 |
| 900,000–949,999 | 2025–2026 | 23 tiered | 432 | 734 | 3,833 | 1 |
| 950,000–971,297 | 2026 | 23 tiered | 41 | 41 | 2,048 | 0 |

Since 2023, 72–89 % of blocks per year need an 80 GB card (2^23 tiered), and most of the rest need 48 GB. A 24 GB card proves the chain only up to about 2014.

### What binds

- **SHA always sets L.** It is the binding component of every block above the floors: 88,078 tiered and 8,800 uniform blocks in the sample.
- **Floor blocks.** Another 252 tiered blocks sit at the 2^12 floor.
- **Size tracks bytes only roughly.** SHA rows follow the compressions, so they depend on the transaction count and on witness hashing, not only on bytes:
  - 2^23 tiered starts at 934,503 B (374990);
  - 2^22 tiered reaches 3,449,177 B (896750).

### Uniform fallbacks (tiered refused because a component exceeds its tier)

- **Count.** 87 in the sample, so about 870 in the chain. In the fully done range 0–258,993 there are 507.
- **Small ones don't matter.** About half are below 2^17 (mostly 2009–2012 blocks with large undo streams relative to their size). Those up to 2^19 have an arena of at most 12.3 GiB, so they still fit a 24 GB card.
- **Misfit components.**
  - `b2msg` (tier L−2): the Blake2s message rows of a large undo stream.
  - `fpwalk` (tier L−2): the fingerprint walk over outputs plus spent scripts.
  - `undo`: a few small blocks.
- **Fallbacks that cost a bigger GPU:**
  - **22 uniform, 98.25 GiB, H200 only.** Sample: 491080, 809680, 848170, 881050, 931270, so about 50 in the chain. Each has a 0.69–0.96 MB undo stream (consolidation-heavy blocks), and its b2msg needs more than 2^20 rows. Tiered they would be 2^22 tiered at 26.4 GiB.
  - **21 uniform, 49.13 GiB, 80 GB.** About 150 in the chain, for example 326020, 330270, 337280 and 353630 (2014–2015, `fpwalk`).
  - **20 uniform, 24.56 GiB, 48 GB.** About 60 in the chain, for example 143870, 327950 and 515760.

### Outliers

- **Largest blocks.** They are about 3.99 MB with a few transactions (inscriptions, 2023–2026), for example 931990 (3,991,999 B, 7 txs) and 927410. All are 2^23 tiered (52.8 GiB): none reaches 2^24.
- **Largest undo streams.** 491080 (958,485 B), 881050 (806,378 B) and 809680 (724,460 B): all three are the 22-uniform fallbacks above.
- **L ≥ 24.** None in the sample; 3 in the full pass (above).

## Implications

- **Hardware.** An 80 GB card (A100 or H100) proves every block except 87 (84 fallbacks and 3 blocks at 2^24 tiered). An H200 proves all of them.
- **Cheap fix for the H200 blocks.** A profile with b2msg, b2s and undo at L−1 (or a third profile for undo-heavy blocks) would make the ~50 H200 blocks 2^22 tiered (48 GB class). It would also move the ~150 21-uniform blocks down.
  - This changes the VK set (D-045: one VK per (L, profile)), so it is the owner's decision.
- **Tier headroom.** The tiered profile reaches 2^24 under `SizeOk`; three blocks use it.

## Reproduce, resume, collect

- **Build.** `zig build -Doptimize=ReleaseFast -Dtarget=aarch64-linux-gnu`, then `scp zig-out/bin/survey scripts/survey_driver.py scripts/survey_run.sh node:survey/`.
- **Run.** On the node, `echo <tip> > ~/survey/tip.txt` and `cd ~/survey && (setsid nohup ./survey_run.sh </dev/null >>run.log 2>&1 &)`.
  - To resume, rerun the same command: done heights are skipped and a partial line is dropped.
  - To stop: `pkill -f survey_run.sh; pkill -f 'python3 -I survey_driver'`.
- **Progress.** `tail ~/survey/run.log` shows progress; the run is finished when the log ends with "survey complete".
- **Collect.** `scp 'node:survey/out/w*.csv' data/full/`, then `cat data/full/w*.csv | sort -t, -k1,1n > data/chain-sizes.csv`, then `python3 -I scripts/survey_summary.py data/chain-sizes.csv data/headers.bin`.
- **Data.** The 1-in-10 sample is committed as `data/sample10.csv.gz` (1.1 MB).
