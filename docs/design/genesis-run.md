# The run from genesis: plan and cost (GENESIS-PLAN)

Status: **proposal for the owner**, 2026-11-24. Nothing here is started. Figures marked *measured* come
from runs in the log (sessions 46b, 47, 48); the others are estimates and say from what.

## What the run produces

One sealed proof that blocks 0 to 972,500 connect as Bitcoin Core connects them (with the rules of
[connect-rules.md](connect-rules.md), now including BIP68 and the full sigop cost), ending in the coin set
after block 972,500 with Core's `hash_serialized`. It starts from the empty set, so the snapshot limit of
D-059 (coin times taken from a set file) does not apply. The limit of D-060 stays: coins created at heights
0–10 carry time 0.

## Cost in one table

GPU prices are RunPod's on 2026-11-24: H100 $2.69/h (community) or $4.39/h (secure); H200 $3.59/h or
$5.29/h. The community cloud had no H100 on each of the last four tries, so the right-hand column is the
one to plan on.

| Part | Work | Community | Secure | From |
|---|---|---|---|---|
| Block proofs, 972,501 blocks | 262 H100-hours, +10 % for retries and the ~130 blocks that need an H200 | $780 | $1,270 | *measured* model, below |
| Block trees (one leaf per block, nodes) | 110–130 H100-hours | $300–350 | $480–570 | 0.40 s per block *measured* on 10,000 blocks in October, with the old AIRs; not re-measured |
| Set passes, 6 boundary sets twice and the final set | about 92 H200-hours | $330 | $490 | about 16 M coins per H200-hour (October's passes); set sizes partly estimated |
| Epoch roots, joins, seal | a few GPU-hours and one large-memory CPU pod | $30 | $50 | October's runs |
| Data: replay of the chain, transfer, storage | CPU pod with 64 GB for a day, AWS egress of about 800 GB, volumes | $150 | $200 | AWS's public egress price; see "Data" |
| Rehearsal first (one epoch end to end on the new AIRs) | | $40 | $60 | October's rehearsal cost $51 |
| **Total** | | **about $1,650** | **about $2,650** | |

I would plan on **$2,500–3,000** and treat anything under $2,000 as luck with the community cloud.
Wall-clock: the block proofs and trees are about 400 GPU-hours and split across machines, so about 4–5
days on four H100s, plus the set passes (they can overlap), plus the preparation below.

What could move the total: the tree figure (the leaf circuit verifies a block proof whose AIRs grew since
October; I have not re-timed it); the set sizes at the boundaries; failures that need reruns.

## Where the block-proof figure comes from (measured)

- Needs of every block to 492,992 and from 935,001, and of 1 block in 10 between
  (`data/survey/`, log session 47).
- An H100 run of 590 blocks spread over every era (`cuda-epoch --heights`, log session 48): 459 s,
  0.78 s per block, GPU 84 % busy. Fit: **time per block = 0.082 s + 0.738 s per 10^9 proven cells**
  (pipeline wall time per block on one H100 with 20 vCPUs; residual 0.29 s rms).
- Applied to every measured block under `sizesAuto` (tight, early, tiered, uniform):

| Heights | GPU-hours, four profiles | with `tiered` only |
|---|---|---|
| 0–99,999 | 2.3 | 2.3 |
| 100,000–199,999 | 3.4 | 4.0 |
| 200,000–299,999 | 7.7 | 10.2 |
| 300,000–399,999 | 16.8 | 23.1 |
| 400,000–499,999 | 29.2 | 41.3 |
| 500,000–599,999 | 34.2 | 47.9 |
| 600,000–699,999 | 40.0 | 54.3 |
| 700,000–799,999 | 42.0 | 58.5 |
| 800,000–899,999 | 50.6 | 78.5 |
| 900,000–972,500 | 35.4 | 56.7 |
| **Chain** | **262** | **377** |

The fixed part (0.082 s on every block) is 22 hours of the 262. About 130 blocks need the uniform profile
at 2^22 (a 108 GiB arena): they go to an H200, as six did in October.

## Epochs

An epoch is a range of blocks proven under one challenge. The seal's statement bounds an epoch: its input
count plus the coin counts of its start and end sets must stay below 2^30 (`EpochOk`), and its coin events
below 2^31. Inputs per 100,000 blocks, from the needs: about 0.3 billion in all below 400,000, then 409 M,
444 M, 553 M, 578 M, 732 M, and 527 M for 900,000–972,500.

Proposed: seven epochs, `[0, 500,000)`, three of 100,000 blocks to 800,000, `[800,000, 850,000)`,
`[850,000, 900,000)`, `[900,000, 972,500]`. Six boundary sets (about 60 M, 62 M, 75 M, 110 M, 175 M and
170 M coins; the first is near a measured 53.6 M at 492,992, the last three are estimated from set-file
sizes), each proven under two challenges, and the final set once: about 1.47 billion coin records.
Fewer epochs would save set passes but do not fit the 2^30 bound; more epochs cost about $50–110 each.

## What must be built or checked first

1. **A rehearsal on the new AIRs.** Since CONNECT-RULES only block proofs have run. The leaf circuits for
   the four profiles, the tree, the epoch root, the join, a set pass in the new set-file format and the seal
   have not been proved with these AIRs. One small epoch end to end, on a GPU, before anything else.
2. **Epoch loading that fits in memory.** `cuda-epoch` loads an epoch's blocks to derive the challenge;
   October's 10,000 recent blocks took 27 GB. A 100,000-block epoch of recent blocks would take about
   270 GB. Either stream the commitments (a code change) or use smaller epochs at more set-pass cost.
3. **The chain's data at the provers.** See "Data".
4. **Driving several GPUs** for days: resumable per-epoch runs exist (`--resume`, `--only`, deferred
   lists, `scripts/pod/node_run.sh`); running four at once over one epoch's heights is not scripted.
5. **Open defects to look at before the run:** a forced `--tiered` run failed at its first block with
   `CudaCatalogBodyMismatch` (session 48; the automatic choice proved 590 blocks without it); the set-pass
   driver's test-strength decode error (session 45b).

## Data

Every block, its undo data and the boundary sets must reach the provers: about 700 GB of blocks plus the
undo streams.
- **Making it:** `replay` from genesis writes blocks, undo, `.ctx` and the sets. The node (16 GB) cannot
  replay past about height 490,000; a CPU pod with 64 GB can ($0.44/h).
- **Moving it:** uploads into a pod through its SSH port are capped near 1 MB/s (log, the set-pass runs of late October), which
  would take over a week. The pods download at about 90 MB/s, so the data should sit somewhere they can
  pull from: an object store (the project already uses Cloudflare R2, which does not charge for downloads),
  filled once from the node. That one upload leaves AWS and is billed by AWS: about $0.09 per GB, so
  roughly $70 for 800 GB. *This is a charge on the node's AWS account, not RunPod's.*
- An alternative with no AWS egress: a pod syncs its own Bitcoin Core (about a day on a fast machine) and
  replays there. More pod time, no transfer.

## What the owner decides

- Go or no go on the rehearsal (about $40–60), which is the next step either way.
- The data route: R2 with a one-time AWS egress charge, or a Core sync on a pod.
- A budget for the run itself, once the rehearsal has re-timed the trees.
