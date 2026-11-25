# Cheaper proving: where the GPU time goes and what to change (GPU-UTIL)

Status: **exploration for the owner**, 2026-11-25. Nothing here is decided; the only code is a
measurement (`cuda-epoch` now prints per-stage device times). Figures marked *measured* come from logs
under `data/store/gpu/` and `data/survey/`; the others are estimates and say from what.

## What the data says today

**The GPU is rarely idle between proofs.** In the 590-block sample (session 48, one H100, 20 vCPUs,
`--jobs 3`): wall 458.6 s, of which the proving call 420.0 s (92 %), file writing about 8 s, and the
rest, about 30 s (6 %), the proving thread waiting for a witness. `nvidia-smi` reported 84 % busy.
*Measured.* So "keep the GPU busy" is worth at most 6–8 %. The cost is inside the proofs.

**`nvidia-smi` utilization is the wrong measure.** It is the share of time any kernel ran, not how
much of the card a kernel used. It cannot tell a saturated card from 13,000 small launches in a row.

**Hashing is 92 % of what is proven.** Share of proven cells over the whole chain under `sizesAuto`
(needs of every block to 492,992 and from 935,001, 1 block in 10 between; 1.170e15 cells; *measured*
needs, computed sizes):

| Part | Components | Share of cells |
|---|---|---|
| SHA-256 of the block's bytes (txid, wtxid, Merkle trees) | sha 56.2, msg 13.0, bytes 2.9, merkle, wmerkle 0.1 | 72.3 % |
| The undo commitment (Blake2s over the spent coins) | b2s 16.5, b2msg 1.3, fpwalk 1.0, undo 0.7 | 19.6 % |
| Parsing and the block checks | walk 6.2, fields 1.0, anc, ctx, tables | 7.2 % |
| Coin events, amounts, maturity, BIP68, sigop cost | coin 0.8, urec 0.1 | 0.9 % |

**41 % of the proven cells are padding.** Proven cells are 1.70 times the cells the blocks need
(sha 1.45, b2s 2.09, msg 2.04, walk 2.43), because every component's size is a power of two.

**Inside one proof** (block 970,347, 2^23 `tight`, single run, *measured*): constraint evaluation
868 ms, ingress 337 ms, trace commit with LogUp 331 ms, OODS 120 ms, quotient 54 ms, the rest under
20 ms; 13,259 kernel launches. The stage clock sums to 1.77 s of a 2.37 s proving call. In batch mode
the same class takes 1.44 s per proof, and no stage breakdown was recorded: that is the first gap.

**A fixed cost per proof.** The smallest blocks take 0.075 s on the device whatever their size
(the fit's constant is 0.082 s): 22 of the 262 H100-hours. Likely the launches; not yet attributed.

**SHA rows cost more than other rows.** From the three profiles at 2^22 and 2^23 (they differ in
which components shrink), the marginal device cost is about 0.26 s per 10^9 cells for msg and walk,
about 0.45 for the Blake2s group, and by difference about 0.6 for sha. Rough: three classes, not a fit.

**One old data point on a cheaper card.** On 2026-10-13 block 400,000 (2^22) ran on an L40S:
constraint evaluation 0.57 s. On the H100 the same stage took 1.15 s at 2^23, so about 0.58 s at 2^22
(inferred by halving, not measured at 2^22). Half of the device time may not need an H100 at all.

## Measured on three cards (2026-11-25)

The 590-block sample of session 48, `cuda-epoch` with the stage output, `--jobs 3` then `--jobs 8`,
`nvidia-smi` at 100 ms. Logs in `data/store/gpu/2026-11-25-gpu-util/` (local). *All measured.*

| Card (RunPod, per hour) | Proofs | Wall, 8 workers | Device time, same 587 blocks | Busy / memory / power |
|---|---|---|---|---|
| H100 SXM 80 GB ($4.39 secure) | 590 | 474.2 s | 410.3 s | 82 % / 18 % / 283 W |
| L40S 48 GB ($1.09 secure, $0.79 community) | 587 | 512.7 s | 476.7 s | 88 % / 62 % / 272 W |
| RTX 4090 24 GB ($0.89 secure, $0.34 community) | 408 | 224.4 s | (408 blocks) 161.9 s; H100 164.6 s, L40S 180.9 s | 66 % / 37 % / 215 W |

- **The L40S is at 92 % of the H100's speed on this sample at a quarter of the price**, and the 4090
  equals the H100 on every class it fits. The 587 proofs made on both the H100 and the L40S are
  **byte-identical** (sha256 of each file). The 4090's proofs were not hash-checked (the pod was gone).
- **What fits.** L40S: everything but 2^23 `tiered` and the uniform blocks (4 of the sample deferred).
  4090: to 2^22 `tight` and `early` and 2^21 `tiered` (183 deferred, from 2^22 `tiered` up).
- **Weighted by the chain's classes** (mean seconds per block of each (L, profile) class, 8 workers,
  times the class's blocks; 99.4 % of blocks are in measured classes): H100 267 hours; L40S 287 hours
  for 99.2 % of blocks; the 68 % of blocks a 4090 fits take 108.5 hours on it (H100 111.3, L40S 107.6),
  and the remaining L40S classes 180 hours. About 2 hours stay on an H100 (2^23 `tiered`).
- **Block proofs, priced:** H100 only $1,170 (secure). L40S for all it fits: **about $315** (secure),
  $230 (community). 4090s for what they fit and L40S for the rest: about $295 (secure). Add the 10 %
  margin of genesis-run.md.
- **Stages** (ms per proof, H100 | L40S | 4090):

| Stage | 2^12 `tight` | 2^22 `early` | 2^23 `tight` |
|---|---|---|---|
| ingress | 4.9, 4.9, 5.8 | 55, 53, 59 | 69, 74, – |
| trace generation | 0.5, 0.4, 0.5 | 17, 47, 40 | 39, 96, – |
| trace commit (with LogUp) | 4.0, 3.1, 3.0 | 168, 242, 202 | 323, 499, – |
| constraint evaluation | 8.7, 5.4, 5.5 | 403, 413, 370 | 787, 823, – |
| OODS | 46, 36, 33 | 93, 79, 71 | 121, 104, – |
| quotient | 3.7, 2.6, 2.5 | 29, 53, 44 | 53, 106, – |
| the rest | 13, 10, 10 | 19, 18, 16 | 22, 23, – |
| outside the stage clock | 1.7, 2.5, 2.6 | 5.3, 3.2, 2.6 | 5.1, 2.4, – |
| **proving call** | **83, 65, 63** | **789, 908, 804** | **1,420, 1,726, –** |

  What it shows: constraint evaluation is 51–55 % of a large proof and runs at the same speed on all
  three cards (arithmetic-bound). The H100 gains only in trace commit, trace generation and the
  quotient (1.5–2.5 times), which move memory. Its memory controller is 18 % busy: its bandwidth is
  mostly unused. **The fixed cost per proof is OODS**: 33–46 ms whatever the size, more than half of a
  small block's proof. Ingress is 5–7 % in batch mode, not the 19 % of the single run. Nothing
  measurable happens outside the stage clock.
- **Witness workers.** With 8 instead of 3 the proving thread waited 5.3 s instead of 14.5 s on the
  H100 (wall 493.8 s to 474.2 s, 4 %); L40S 23.4 s to 12.9 s; 4090 59.4 s to 31.1 s (there the
  deferred blocks' witnesses are built for nothing).
- **A bug found and fixed.** Under 8 workers every run failed at once with random plan errors
  (`ReadBeforeWrite`, `CudaCatalogBodyMismatch`, `ParameterOutOfBounds`, …): the workers admitted
  programs through the catalog, whose allocator was the run's arena (not thread-safe). The catalog now
  uses `std.heap.smp_allocator`: 3 of 3 short runs and every full run passed. Session 48's failure of
  the forced `--tiered` run shows the same errors and is very likely the same race (not re-run).
- Cost of the three pods: about $4.6 (4090 0.70 h, L40S 0.88 h, H100 0.75 h; estimate, not from billing).

**Not measured:** the trees, the set passes and the uniform blocks on these cards (other circuits,
other memory needs); 2^23 on any 24 GB or 32 GB card; a community L40S against a secure one.

## Levers, by expected saving

**Revised after the measurement:** lever 1 is confirmed and is the largest by far (block proofs from
about $1,170 to about $315). In lever 3, ingress drops out, the workers are worth 4 %, and the fixed
cost has a name (OODS, about 40 ms of every proof: about 10 of the 267 hours).

## Levers as written before the measurement

Baseline (genesis-run.md, secure prices): block proofs $1,270, trees $480–570, set passes $490.

### 1. A cheaper GPU class. No redesign; a few dollars to measure

RunPod prices on 2026-11-25, secure / community per hour (stock changes by the hour):

| GPU | Memory | Price | Fits |
|---|---|---|---|
| H100 SXM | 80 GB | $4.39 / $2.69 | all but about 130 blocks |
| A100 | 80 GB | $2.09–2.19 / $1.19–1.39 | the same |
| RTX 5090 | 32 GB | $1.39 / $0.69 | to 2^22 (all profiles but uniform) |
| L40S, RTX 6000 Ada | 48 GB | $1.09 / $0.74–0.79 | to 2^23 `tight` and `early` (34.9, 39.4 GiB): 99 % of cells |
| RTX 4090 | 24 GB | $0.89 / $0.34 | to 2^22 `tight` and `early` (about 17.5, 19.7 GiB, by halving): about 36 % of cells, most blocks |
| A40 | 48 GB | $0.59 / – | as the L40S; an older, slower chip |

An L40S pays off if it runs at more than a quarter of the H100's speed; a 4090 at more than a fifth.
The kernels are integer arithmetic and hashing, which do not use what makes an H100 expensive
(memory bandwidth, tensor cores), so I expect well above that, and the one data point agrees.
**Unknown until measured.** If an L40S reaches 60 % of the H100, block proofs drop from about $1,270
to about $525.

To measure: the same 590-block sample (the blocks that fit) on a 4090 and on a 48 GB card, with the
new stage output. About an hour each. Risks: the AOT kernels are built per architecture on the pod
(sm_89 worked in October); the 24 GB fit is computed, not tried.

### 2. Less padding

Two designs, both change the block system and its Lean statements:

- **Split sizes.** Let a component be two instances (2^(l−1) + 2^(l−2)) when its need is at most
  three quarters of 2^l. On sha alone: 9.3 % fewer cells. On the eight row-heavy components
  (sha, msg, bytes, b2s, walk, undo, b2msg, fpwalk): **19.3 % fewer**. *Computed from the needs.*
  Cost: more components per proof, more profiles and leaf VKs, a system statement over a variable
  number of instances.
- **Several blocks per proof.** Pack consecutive blocks until sha fills 2^23: 6.7 % fewer cells
  (9.7 % at 2^24, which needs an H200), but **388,833 proofs instead of 972,503** (163,308 at 2^24).
  That removes about 13 H100-hours of fixed cost and, more important, most tree leaves: the trees
  cost 0.40 s per block proof whatever the block's size. If the leaf's cost stays near that, trees
  fall from about 120 to about 50 H100-hours. Cost: the largest redesign here (public inputs per
  block inside one proof, the leaf's interface, every statement that says "one proof, one block").

The two overlap (both remove padding); together they would not add up.

### 3. Inside the pipeline. Needs the stage breakdown first

- More witness workers (`--jobs 3` on 20 vCPUs): up to the 6 % the proving thread waits. Free.
- The fixed 0.075 s per proof: fewer launches (OODS runs one cohort per mask offset, 4,837 samples;
  gpu-cuda.md lists batching by column), or two small proofs at once on one card. Up to 8 %.
- Ingress: 337 ms for 0.34 GiB in the single run is far below what the bus carries. If batch mode
  shows the same, pinned buffers or an upload during the previous proof's tail are worth up to 15 %
  of a large proof. Unknown until measured.
- Constraint evaluation is half of the device time. Per-component times would show whether a few
  constraints dominate (b2s has 2,286 constraints on 406 columns, sha 213 on 188). No data yet.

### 4. Fewer SHA cells per compression

`block_sha` uses 72 rows of 188 columns per compression. A denser AIR would cut the largest share
directly, at the price of redoing its Lean proof (SHA-256 against FIPS 180-4). Not estimated.

### Not a saving

Moving amounts, maturity or the lock checks to another layer (asked on Delving): they are under 1 %
of the cells. A set-update proof fed only by cheap-hash commitments would skip the 72 %, but then it
proves a statement about those commitments, and something else must tie them to the blocks.

## How to measure, in order

1. **Stage breakdown in batch mode** (built: `cuda-epoch` prints, per (L, profile), the device's
   stage clock in ms per proof, the part of the proving call outside it, launches, syncs, H2D bytes,
   and the total time the proving thread waited for witnesses). Compiles and runs under `--mock`;
   the device lines are untested until a GPU run.
2. **The same sample on two cheaper cards**, same output. Gives price per proof per card and, from
   which stages slow down, whether a stage is bound by arithmetic or by memory.
3. `nvidia-smi dmon` at 100 ms (sm, mem, power) next to the run: power draw separates a saturated
   card from a launch-bound one better than the busy flag.
4. One `nsys profile` of about 20 blocks: the kernel timeline with its gaps, to attribute the fixed
   0.075 s and the 25 % of a proving call outside the stage clock.
5. `--jobs 6` and `--jobs 10` on the sample: the witness wait.

Steps 1, 2, 3 and 5 fit one session of about two hours of cheap cards and half an hour of H100:
about $5.

## What I would do

Measure first (above), because lever 1 may be worth more than every redesign and costs nothing to
build. Then choose between the two padding designs with the tree figure from the rehearsal in hand:
several blocks per proof is worth its cost only if the trees stay a third of the bill.
