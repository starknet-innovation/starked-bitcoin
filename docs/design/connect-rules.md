# CONNECT-RULES: BIP68 relative locktimes and the full sigop cost (design)

Status: current · Updated: 2026-11-23 · Owner files: `lean/StarkedAir/Block/TimeLock.lean`, `lean/StarkedAir/Spec/ConnectRules.lean`, `src/block/connect_rules.zig`, `tools/specfuzz/core_connect_cases.cpp`, `lean/StarkedAir/Block/Coin.lean`, `lean/StarkedAir/Block/Walk.lean`, `src/block/coin.zig`, `src/block/walk.zig`, `src/block/anc.zig`

Answers: which `ConnectBlock` rules outside scripts the block proof does not enforce, what Core
checks exactly, how to add them, and how far that is. The design is accepted (D-054). Steps 1–3 of 5 are
done: the rules are specified and checked natively; the height-based half of BIP68 and the full sigop
cost are enforced by the block AIRs and proven in Lean. Step 4 (time-based BIP68) is built and proven
too: every coin carries the median time past of the block before its creating block, and the coin balance
makes the time a lock is checked against the coin's own (D-058, resolution R5; "Step 4" below, with its
limits). No proof has been made with the new AIRs: the proofs of 935,001–972,500 use the AIRs before
step 2. Roadmap item CONNECT-RULES.

## The gap

`Spec/Block.lean:6` leaves "fees, subsidy, BIP30, BIP68, full sigop cost, scripts" to M3b/M3c. M3b
proved fees, subsidy and BIP30 ([utxo.md](utxo.md) rules 1–7). Two rules remain that are not script
validation, and that Core enforces even under assumevalid:

| Rule | Core (`consensus/tx_verify.cpp`, `validation.cpp ConnectBlock`) | 2026-11-19 |
|---|---|---|
| BIP68, height-based locks | `SequenceLocks`: reject `bad-txns-nonfinal` | enforced by the AIRs of step 2 (no proof made with them yet) |
| BIP68, time-based locks | same | enforced by the AIRs of step 4 (no proof made with them yet) |
| Sigop cost | `GetTransactionSigOpCost` summed ≤ 80,000: `bad-blk-sigops` | legacy sigops only (`Spec/BlockFlat.lean:149`) |

Until both are proven the guarantee is weaker than assumevalid (said on the site and on Delving t/3070).

## BIP68, exactly

Active when the CSV flag is set (height ≥ 419,328; public input 5 already) and the transaction's
version ≥ 2. Per input with sequence bit 31 clear, with `lock = sequence & 0xffff`, `c` the spent
coin's height and `h` the block's:

- bit 22 clear (height): valid iff `h ≥ c + lock`;
- bit 22 set (time): valid iff `MTP(h − 1) ≥ MTP(max(c − 1, 0)) + 512·lock`.

Core takes the maximum over a transaction's inputs and compares once; that is the same as every input
passing. `MTP(k)` is the median of the times of blocks `k − 10 … k` (fewer near genesis).

Frequency in 935,001–972,500 ([report](../reports/2026-11-19-block-cost-split.md)): height locks on
0.65 % of inputs, time locks on 6,988 inputs in 37,500 blocks.

### Height-based: decoded in `block_fields`, compared in `block_coin` (built, step 2)

An input row of `block_coin` already holds the spent coin's code (`2·c + coinbase`, from undo record
`J`) and checks coinbase maturity against `h` (public 2) with a range check. As built:

- **`block_fields`** (`Fields.lockC`, 13 columns, 15 constraints, 4 byte reads): a transaction head
  reads its 4 version bytes; `V2 = [version ≥ 2]` is carried down the transaction's rows. An input row
  splits bytes 2 and 3 of its sequence into bit 22 (`T22`), bit 23 and bit 31 (`D31`), the remainders in
  range slots that were free on input rows. `LKH = pub5 · V2 · (1 − D31) · (1 − T22)` says a height
  lock is enforced; `LKT` (the same with `T22`) is the time lock, for step 4.
- **The input relation** `in` grows from `(tx, start)` to `(tx, start, lock, LKH, LKT)`, with `lock` the
  sequence's low 16 bits.
- **`block_coin`** (`Coin.lockC`, 6 columns, 2 constraints, 3 range lookups): on a non-coinbase input
  with `LKH = 1`, `h − c − lock` is three range-checked bytes. The coinbase's input is not checked.

Sizes: `block_fields` 190 → 203 main columns and 36 → 40 lookups; `block_coin` 164 → 170 and 94 → 97;
the block system's lookup sites per row 216 → 223 (the bound for 2^23 rows is 255). Lean: next section.

### Time-based: a claim per input, resolved by one small proof per epoch (superseded)

**Superseded 2026-11-23** by "Step 4" below (D-058, R5: the coin carries its time). Kept as the record
of option A and of why a claim must be committed.

`MTP(h − 1)` is in the block proof already (`block_anc`, public 3 and 7). `MTP(k)` for an old `k` is
not: the block proof does not see old headers, and linking by previous hash across thousands of
blocks is out of the question.

Recommended (option A):

1. **The claim is committed.** For each time-locked input the undo stream carries `m`, the claimed
   `MTP(k)` (4 bytes). The stream is under the block commitment `C_h`, so the claim `(k, m)` is fixed
   before the epoch challenge. `block_coin` checks `MTP(h − 1) ≥ m + 512·lock` and adds
   `+1/(z − φ(k, m))` to the block's partial sum, under a relation id of its own.
2. **A resolver proof per epoch** consumes each claim once: for `(k, m)` it holds the headers
   `k − 10 … k`, hashes and links them and takes the median (the layout and the median gadget of
   `block_anc`), binds header `k`'s hash to the chain's `T` with an MMR path (the seal's path gadget),
   and adds `−1/(z − φ(k, m))`. Its sum joins the epoch balance next to the set passes'.
3. The balance being zero then says every claimed `m` is the chain's `MTP(k)`: the same LogUp
   argument as the coins (`epoch_sound`), with multiplicities ±1 on both sides.

Why the claim must be committed: the block proofs are made after the challenge is known. A claim
whose `m` is a free trace value could be chosen against the known `z`; with many claims that is a
generalized-birthday problem, not a negligible probability. `LogUpSZ` only covers tuples fixed
before the challenge (the reason for D-041's committed indices).

Consequence: **the commitment changes**, so the epoch challenges change and the set passes are redone.
Step 3 of the plan (a canonical snapshot hash) redoes them anyway, and so does a run from genesis; all
of it is one re-prove.

Rejected:
- (B) A digest of the claims per block, folded by the tree and opened by the resolver: no commitment
  change, but every leaf and node circuit carries one more digest and the resolver rebuilds the tree.
- (C) Per-height MTP in the header tree: re-proves the frozen chain VK (D-036), as in D-043.
- (D) Height-based only, time-based left unproven: leaves a stated gap; acceptable only as an
  intermediate state.

Open points for the build:
- claims near genesis (`k < 10`): fewer than 11 headers, as Core's `GetMedianTimePast`;
- a zero time lock: `MTP` is non-decreasing on a valid chain, so no claim is needed; either prove
  that from the header rules or emit the claim anyway;
- the resolver as an AIR system (reusing `block_anc`) or as a circuit program (reusing the seal's
  paths): decide when costing; about 7,000 claims per 37,500 blocks, so the cost is negligible
  either way.

## Sigop cost, exactly

Per non-coinbase transaction: `4·legacy + 4·P2SH + witness`, summed over the block with the
coinbase's `4·legacy`, at most 80,000.

- **legacy**: `GetSigOpCount(false)` over every scriptSig and scriptPubKey (proven, `block_walk`).
- **P2SH** (per input whose spent script is P2SH): walk the scriptSig; if any opcode is above
  `OP_16` the count is 0; else the last pushed item is the redeem script, counted *accurately*
  (`OP_CHECKMULTISIG` after `OP_1 … OP_16` counts that number, else 20).
- **witness** (`CountWitnessSigOps`): the witness program is the spent script, or the redeem script
  when the spent script is P2SH and the scriptSig is push-only. Version 0 with a 20-byte program: 1.
  Version 0 with a 32-byte program: the accurate count of the last witness item (0 if the stack is
  empty). Other versions (taproot): 0.

Design sketch:

- **Classify the spent script** where its bytes are already walked (`block_fpwalk` over the undo
  record's `serTxOut`): P2SH (`a9 14 … 87`, 23 bytes), witness program (version, length).
- **A second mode of the sigop walker**, accurate counting (one more state: the previous opcode),
  over two new kinds of spans: the redeem script (the last push of a scriptSig, bytes the walker
  already visits) and the last witness item of a P2WSH spend (bytes not walked so far).
- **The push-only test and the last push** come from the walker's pass over the scriptSig.
- The block total becomes `4·(legacy + P2SH) + witness ≤ 80,000`.

Rows: `walk` grows by the redeem and witness script bytes. It is proven at 2^L while needing about
2^(L−3) (report, result 2), so the extra rows fit in the current padding for typical blocks. *Est.*, to
confirm with a survey mode before building.

This is the larger half of the work: the walker's second mode and its Lean proof (`walk_eq_sigOps`
is the pattern), and the classification.

## Step 1 (done 2026-11-19): the spec, fuzzed against Core, and a native check

- **Lean** (`Spec/ConnectRules.lean`, executable): `txSigOpCost` and `SigOpCostOK`
  (`GetTransactionSigOpCost` and the block bound), `seqLocksOk` and `SeqLocksOK` (the per-input rule
  above). `seqLockPair` transcribes Core's maximum-then-compare; `seqLockPair_eval` proves the two
  agree, so the AIR may check inputs one by one.
- **`strict`**: the P2SH and witness parts apply under `SCRIPT_VERIFY_P2SH | SCRIPT_VERIFY_WITNESS`,
  which Core sets for every mainnet block but the BIP16 exception at height 170,060
  (`script_flag_exceptions`). The spec takes it as a parameter; a run from genesis needs it false there.
- **Fuzzing** (`tools/specfuzz/core_connect_cases.cpp`): Core's own `GetSigOpCount(true)`,
  `GetTransactionSigOpCost` through a `CCoinsViewCache`, and `CalculateSequenceLocks` with
  `EvaluateSequenceLocks` over a `CBlockIndex` chain, linked from `data/core-src` at `c067aa71` with
  stubs for what those functions never call (`core_stubs.cpp`).
- **Result:** 20,000 cases of each of the three kinds (seed 2026), 0 mismatches.
- **Mutation test** of the fuzzer (`tools/specfuzz/mutate_connect.sh 5 5000`): 16 deliberately wrong
  specs (a lock off by one, the wrong time base, a 511 s unit, wrong bits and masks, version 1, P2SH
  and witness variants, the flags), each applied to both formulations with the `#guard`s removed. All
  16 disagree with Core on 27 to 1,610 of 5,000 cases. The first run missed three (lock boundaries,
  lock values above 2^15), which the generator now produces on purpose.
- **Native reference** (`src/block/connect_rules.zig`), answering the same cases as Core
  (`STARKED_CONNECT_CASES`), run over blocks 935,001–972,500 on the node
  (`survey`, `STARKED_SURVEY_RULES=1`):

| Check | Result |
|---|---|
| Blocks, parse errors | 37,500, 0 |
| Sigop cost over 80,000 | 0 blocks; highest 79,599 (block 961,121: legacy 18,767, P2SH 213, witness 3,679) |
| Sigops in all | legacy 22,345,192; P2SH 2,737,002; witness 232,767,938 |
| Height-based locks (version ≥ 2, bit 31 clear, any value) | 5,120,340 inputs, 0 not met |
| Time-based locks | 6,988 inputs, 0 not met against the node's `mediantime`; the tightest is met with 0 s to spare (block 937,433, coin height 933,116, lock 5,063) |

The legacy bound, the only one the proof enforces as of 2026-11-19, would not catch block 961,121 going over: its legacy part
alone is 75,068.

```sh
sh tools/specfuzz/run.sh data/core-src/src <seed> <cases>          # all kinds, Lean against Core
tools/specfuzz/mutate_connect.sh <seed> <cases>                    # ~30 min: wrong specs must fail
STARKED_CONNECT_CASES=$PWD/data/specfuzz/core-<seed>.tsv zig build test -Dtest-filter="Core does"
python3 pack.py | STARKED_SURVEY_RULES=1 ./survey > rules.csv      # on the node, ~45 min
python3 check_time_locks.py                                         # scripts/, on the node: time locks against bitcoin-cli
```

## Step 2 (done 2026-11-19): height-based BIP68 in the AIRs, proven

- **Spec** (`Spec/Coins.lean`): `heightLockOk h version sequence coinHeight`, and `connectTxL`, Core's
  connect of a transaction (`connectTx`) with that check on each input against the coin it finds.
  `connectTxsL_connectTxs`: the stricter connect implies the plain one. `Spec/ConnectRules.lean`,
  `seqLocksOk_split`: Core's `SequenceLocks` is every input passing `heightLockOk` and `timeLockOk`, so
  what is left is exactly the time half.
- **Soundness** (Lean, standard axioms):
  - `Block.in_lock` (`Block/CoinClaims.lean`): for a non-coinbase input of a satisfied block system
    whose `pub 5` is the CSV bit, `heightLockOk` holds against the claimed coin's height. It rests on
    `Block/FieldsLock.lean` (`v2_head`, `seq_bits`, `lkh_of`, `row_in_tx`) and `Coin.lock_row`.
  - `Block.epoch_systems_coreL` (`Block/CoinEpochCore.lean`): a balanced epoch connects as
    `connectTxsL`, so each height lock is checked against the coin actually spent.
  - The earlier theorems (`tx_claims_ok`, `block_facts`, `epoch_systems_core`, and all 100 statements
    of the `Compat.lean` gate) keep their statements; the lock arrives in theorems with an `L` suffix
    beside them (D-056). Six pins of the gate are re-pinned: the AIR definitions themselves changed.
- **Open in Lean:** `epoch_systems_coreL` takes `pub 5 = [CSV_HEIGHT ≤ height]` per block as a
  hypothesis. The block leaf circuit pins that bit from the height (`Circuit.BlockCtx.ctx_sound`), but
  the leaf's guarantee carried through the recursion (`LeafOut`, `BlockAt`) names the BIP30 flag only,
  not the CSV bit, so `forest_epoch` does not hand it to the epoch theorem. The finality rule's cutoff
  has the same dependency (`final_ok`). To close: add the bit to `LeafOut` and `BlockAt`.
- **Tests** (`src/block/negative.zig`, synthetic blocks at height 500,000, coins from 499,999):

| Case | Verdict |
|---|---|
| lock 0; lock 1 | accepted |
| lock 2; lock 65,535; lock 2 with the unused bits 16–21 and 23–30 set | rejected (`block_coin` constraint 114) |
| lock 2 with bit 31 set; version 1; version 0 | accepted |
| lock 2, version 256; version 0xffffffff | rejected |
| time lock 2 (bit 22) | accepted: not enforced before step 4 |
| coinbase of version 2 with sequence 2; lock 2 at height 1,000 (before CSV) | accepted |

  Forgeries: a coin row that clears its lock bit leaves the input relation unbalanced; clearing the
  bit on both sides and withdrawing the range uses balances every lookup and is rejected by the
  fields' definition of the bit alone.
- **Not done here:** the GPU prover has no kernel for `block_fields` or `block_coin` (their witness is
  built on the CPU), so step 5 has nothing to add for this step beyond new VKs and a parity run.

```sh
zig build test -Doptimize=ReleaseFast -Dtest-filter="BIP68"     # ~20 s
(cd lean && lake build StarkedAir.Block.CoinEpochCore)
```

## Step 3 (2026-11-20): the full sigop cost in the AIRs, proven

Status: the AIRs enforce `4·legacy + 4·P2SH + witness ≤ 80,000`, are tested against the native
reference, and are **proven sound in Lean** (2026-11-20, `block_sigop_cost`, `epoch_systems_coreS`; see
"Lean soundness" below for the statement and its hypotheses). Not in the published proofs (branch
`connect-rules`).

**Rows first (survey, 37,500 blocks, 0 errors).** `survey` with `STARKED_SURVEY_SIGOPS=1` on the node:

| | Value |
|---|---|
| Rows `block_walk` needs today (script bytes) | 1.136·10^10 |
| Redeem scripts to count accurately | 14,189,109 spans, 4.09·10^8 bytes (+3.6 %) |
| Witness scripts to count accurately | 8,504,590 spans, 8.22·10^8 bytes (+7.2 %) |
| Extra rows per block, against its need | median +9.7 %, 99th percentile +43.5 %, largest ×11.8 (block 950,125) |
| Blocks whose walker still fits at L / L−2 / L−3 / L−4 | 37,500 / 37,493 / 37,242 / 35,776 (before: 37,500 / 37,500 / 37,319 / 36,316) |

So the walker fits the current profile for every block; TIERS-2 picks its offset on the new needs.

**As built.**

- **`block_urec`** classifies the spent script from the record's `serTxOut`: it reads the script's
  length byte (`S + 17`), then two bytes and, for P2SH, the last one. `CP`: `17 a9 14 … 87`; `C20`:
  `16 00 14`; `C32`: `22 00 20`. The class travels in the record tuple to `block_coin`, and in the
  input tuple to the input's row in `block_fields`.
- **`block_walk`** has two kinds of spans. A *script* (`AC = 0`) is walked as before; it now also
  outputs `PO` (it parses and no opcode is above `OP_16`: `IsPushOnly`) and `(RS, RL)`, the data of its
  last operation, in the script tuple. An *accurate span* (`AC = 1`, tuple `aspan(start, len, W4)`)
  is counted accurately: a multisig counts the previous opcode's value (`PV`: 1 … 16 after
  `OP_1 … OP_16`, else 20), with weight 4 (`W4`, a redeem script) or 1 (a witness script). Two sums:
  `SUMS` (legacy, scripts only) and `SUMA` (weighted accurate counts).
- **`block_fields`**, per non-coinbase input: `AR0` = P2SH spent by a non-empty push-only scriptSig.
  Then the last push is the redeem script: it is requested as an accurate span of weight 4 (if not
  empty, and below 2^24 bytes), and if it is 22 or 34 bytes its first two bytes are read to see a
  version 0 witness program (`RWA`, `RW32`). `W20S` counts the inputs whose program, native or
  wrapped, is version 0 with 20 bytes. An input whose program is version 0 with 32 bytes (`N32`)
  sends `wreq(tx, inputs left)` to its witness stack's row in a segwit transaction; the stack's last
  item, if not empty, is requested as an accurate span of weight 1.
- **`block_ctx`** checks `2·ACC + PAR = 80,000 − 4·SIGS − SIGA − W20T` with `ACC` two range bytes and
  `PAR` a bit (the bound needs 17 bits).
- **The opcode table** gains three columns (above `OP_16`, multisig, the value a following multisig
  takes). The set-pass system shares `block_tables`, so the block system uses a copy,
  `block_tablesb` (`Tables.tablesB`); the set-pass AIRs and keys do not change.
- **`strict`** (the P2SH and witness flags) is always on in the AIR. Core turns it off for one block
  (height 170,060); counting more there can only reject, and that block's cost stays far below the
  limit. To state in Lean when the from-genesis run is prepared.
- Columns: walk 51 → 71, fields 203 → 229, urec 21 → 39, coin 170 → 173, ctx 41 → 44. Lookups per
  row: fields 40 → 46, walk 5 → 6, urec 20 → 24 (`hashRows`: 223 → 234 sites; `SizeOk` still covers
  uniform 2^23).

**Tests.**

| Test | Result |
|---|---|
| Real blocks 400,000; 481,824; 709,632; 970,347 (`large samples`) | constraints hold, lookups balance |
| The walker's, fields' and records' counts against the native reference, 11 samples | equal (e.g. block 709,632: cost 13,143 = 4·1,611 + 4·268 + 5,627) |
| 22 synthetic inputs in one transaction (P2SH with multisigs, PUSHDATA1/2, two pushes, not push-only, truncated push, empty last push, `OP_RESERVED`; P2SH-P2WPKH, P2SH-P2WSH, 22 and 34 bytes that are not version 0 programs; P2WPKH with and without witness; P2WSH with one item, empty stack, empty last item; taproot) | AIRs hold; cost 9,480 as the native reference counts |
| Cost exactly 80,000 through two redeem scripts, through one witness script, through both (legacy count 0) | accepted |
| Cost 80,001 (one more P2WPKH input); 120,000 | rejected (`block_ctx` constraint 48) |
| Forgeries: the record, the coin row or the fields deny the P2SH class; the fields drop a P2WPKH class; the walker denies push-only; a witness stack ignores its request; the walker counts a redeem script with weight 1 | each rejected (a constraint, or an unbalanced lookup) |

The native reference (`connect_rules.zig`) is the one fuzzed against Core in step 1.

**Lean, done** (standard axioms, `lake build` 8930 jobs):

- Every earlier theorem holds on the new AIRs, including `sigops_ok` (legacy sigops × 4 ≤ 80,000),
  now derived from the new check: `Block.sigops_nat` gives `4·legacy + A + w + D = 80,000` over the
  naturals, with `A` the walker's `SUMA` and `w` the fields' `W20S`.
- `Walk.total`: the legacy sum is over the scripts only. `Walk.pv_le`, `row_cost`, `sums_nat`: each row
  adds at most 80 to `4·SUMS + SUMA`, so the check cannot wrap. `Fields.w20_nat`: `W20S` is a natural
  of at most two per row. `walk_rem`: every span, script or accurate, is 1 to 2^25 bytes long.
- Sixteen pins of the `Compat.lean` gate re-pinned (D-056); no `compat_*` statement changed.

**Lean soundness (2026-11-20, standard axioms, `lake build` 8938 jobs).**

Statement, block level (`Block.block_sigop_cost`, `Block/SigCost.lean`): for a satisfied, balanced block
system whose context component has at least 2^8 rows, with `claim t k` the undo record the coin
component uses for input `k` of transaction `t ≥ 1`: if every such claim is some output's `serTxOut`,
then `SigOpCostOK true` holds for the block's transactions with the claims' scripts as the spent
scripts (`Spec/ConnectRules.lean`: `GetTransactionSigOpCost` summed, at most 80,000).

Statement, epoch level (`Block.epoch_systems_coreS`, `Block/SigEpoch.lean`): `epoch_systems_coreL`
with one more hypothesis (each initial coin's value is a serialized output) and one more conclusion:
for every block of a balanced epoch, `SigOpCostOK true` on
`(blockTxC N B).map fun x => (x.t, x.claims.map (·.1.script))`, the scripts of the coins that the same
theorem's `connectTxsL` finds in the view. In a balanced epoch every spent claim is an initial or a
created coin, which is why the claims are serialized outputs there.

| Part | Theorems | File |
|---|---|---|
| The walker automaton with a decoration equals a fold over Core's `GetOp` parse; its instances: accurate count, `IsPushOnly`, last push | `runG_opsD`, `acc_run`, `po_run`, `last_run`, `lastPush_suffix`, `acc_le` | `Spec/SigWalk.lean` |
| `CountWitnessSigOps` as two flags; the classes read from a `serTxOut` | `countWitness_eq`, `count_split`, `ser_p2sh`, `ser_w` | `Spec/SigClass.lean` |
| A span's rows carry any decoration; `SUMA` is the sum over the spans of weight × `sigOpsAccurate`; a script's `PO` is `pushOnly` and `(RS, RL)` its last push | `seg_gen`, `seg_acc`, `total_acc`, `total_acc_nat`, `span_out` | `Block/WalkAcc.lean` |
| The records' class flags are `isP2SH`, `isW 20`, `isW 32` of the spent script | `URec.class_spec`, `urec_class_bytes`, `claim_class` | `Block/CoinClass.lean` |
| Witness stacks: a marked stack requests its last item; a stack row names its input; an input row's place | `stack_q`, `wq_sum`, `wits_rows`, `row_tx`, `wcnt_tx`, `in_tx` | `Block/FieldsWits.lean` |
| A non-coinbase input row's flags are `p2shSigOps` and the two flags of `CountWitnessSigOps` | `in_cost`, `w20_sum`, `nongin` | `Block/FieldsSig.lean` |
| The relations (accurate spans, witness requests, script tuples), the context's check by rows, rows to `(t, k)`, the block statement | `aspan_sum`, `wreq_sum`, `sig_out`, `rdf_read`, `wq_total`, `cost_rows`, `in_rows`, `in_row_cost`, `gin_sum`, `block_sigop_cost` | `Block/SigCost.lean` |
| The epoch | `block_factsS`, `epoch_core_runS`, `epoch_coreS`, `epoch_blocksS`, `txc_scripts`, `epoch_systems_coreS` | `Block/SigEpoch.lean` |

All of it is additive (D-056): no earlier statement changed, `Compat.lean` is untouched.

**What the statement does not cover.**

- `strict` is `true` for every block: the P2SH and witness parts are counted at every height (D-057).
  Core turns them off for block 170,060 only; counting more can only reject.
- The two hypotheses of `epoch_systems_coreS` beyond `epoch_systems_coreL`'s: the context component has
  at least 2^8 rows (true of every size profile in use), and the epoch's initial coins are serialized
  outputs (true of a set built from Core's coins; not yet derived from the set proof in Lean).
- Like the CSV bit of step 2, the new epoch theorem is not yet carried into the recursion's guarantee
  (`LeafOut`, `BlockAt`, `forest_epoch`): the chain proof's composed Lean statement still ends in
  `epoch_systems_core`.

**Not done here:** the GPU walker kernel (`src/gpu/cuda/witness.zig`) builds the old 51 columns; the
CPU path is the reference until step 5.

```sh
python3 pack.py | STARKED_SURVEY_SIGOPS=1 ./survey > sigops.csv   # on the node, ~40 min
zig build test -Doptimize=ReleaseFast -Dtest-filter="sigop cost"  # ~1 min
(cd lean && lake build StarkedAir.Block.SigEpoch)   # block_sigop_cost, epoch_systems_coreS
```

## Step 4 (2026-11-23): time-based BIP68 — the coin carries its time (D-058, R5)

Status: built, tested on the host and **proven in Lean** for the block AIRs and the epoch
(`Block.in_time_lock`, `Block.epoch_systems_coreS`). Not in the published proofs (branch `connect-rules`),
not run on the node's blocks, GPU parity of the changed AIRs not run. The design of 2026-11-20 (a claim
per time-locked input in the block's public sum, resolved by a per-epoch proof) is replaced: the owner
chose R5 (D-058), and the claim sum, its tuple and the "net of claims" statements are gone.

**The rule.** `MTP(h − 1) ≥ MTP(c − 1) + 512·lock`, with `c` the spent coin's height. The block proof has
`MTP(h − 1)` (public inputs 3 and 7, `block_anc`). It does not see block `c − 1`.

**The idea.** A coin's **time** is `MTP(c − 1)`: what the block that creates the coin has as *its own*
previous median time past. So the creating block writes it into the coin, and the spending block reads
it from the coin:

| Where | What |
|---|---|
| A coin's bytes | `serTxOut ‖ time`, the time 4 bytes little-endian (`Spec.CoinEpoch.coinBytes`, `coin.coinBytes`) |
| The coin tuple (26 entries, unchanged layout) | the fingerprint slots hold the fingerprint of `serTxOut ‖ time`; the length slot is `|serTxOut| + 4` |
| An output row of `block_coin` | time bytes `TB` = the bytes of public inputs 3 and 7 (range-checked); fingerprint `EX = (((FH·γ + TB0)·γ + TB1)·γ + TB2)·γ + TB3` |
| An undo record (in-circuit format v2) | `code(4) ‖ ctx(3) ‖ tl(2) ‖ serTxOut(tl) ‖ time(4)`: every record carries the spent coin's time |
| An input row of `block_coin` | `TB` = the record's four time bytes (through `block_urec`); the same `EX`; for an enforced time lock, `pub(3,7) − TB − 512·lock ≥ 0` as a two-limb subtraction |
| The set file | a record's `ser` is `serTxOut ‖ time`, `len = |serTxOut| + 4` (at least 12) |
| The set pass | fingerprints `ser` whole (no change), hashes it whole into the file digest and the Merkle leaf; Core's `hash_serialized` stream leaves the 4 time bytes out (`set_tmsg`: `RLEN = len − 4`) |

**Why it is sound.** The coin balance already forces every spent tuple to equal a created or an initial
one (`epoch_sound`: fixed before the challenge by the commitments, D-041). The time is now inside the
tuple, so the time an input checks its lock against **is** the time its coin was created with. No new
relation, no new public input, no change to the seed or to the recursion's logic.

**As built.**

- **`block_urec`** (43 columns, 28 lookups): reads the four time bytes at `S + 9 + tl + i` and passes them
  in the record tuple (`REL_UREC`, 13 entries).
- **`block_coin`** (191 columns, 108 lookups), `Coin.timeC`:
  - `EX` (4 columns) is the segment's fingerprint `FH` extended by `TB 0..3`, on every row (`Coin.extQ`);
    the tuple uses `EX` and `SLEN + 4`;
  - output rows: `TB0 + 256·TB1 = pub 3`, `TB2 + 256·TB3 = pub 7`, four range lookups;
  - time-locked input rows (`TM = KI·LKT`): the lock `SQL = SA + 128·(SH0 + 256·SHB)` and the two-limb
    subtraction with borrow `BW0 + BW1` and result bytes `TQ` (as on 2026-11-20, against `TB`).
  - A zero time lock is enforced like any other.
- **`set_rec`**: `len ≥ 12`. **`set_tmsg`**: looks its record up with `RLEN + 4`.
- Site counts: `urec` 28, `coin` 108; `Link.hashRows` 249 sites per row (the bound for 2^23 rows is 255).
- **The public input layout and the recursion circuits do not change.**

**Below the CSV height** a block's previous median time past is not proven and its public limbs are 0
(D-043 part 3), so a coin created below height 419,328 has time 0 (`coin.coinTime`). For the proven range
(935,001 on) this gives Core's verdict: such a coin is more than 9 years old and a time lock is at most
388 days. For a run from genesis it does not, for spends between the CSV height and about a year later:
`block_anc` must then run below the CSV height too (roadmap).

**The honest times** come from the header file the provers already load: `system.timeClaims`
(`coin.timeClaims`) gives every undo record its coin's time. `prove-epoch`/`cuda-epoch`
(`epoch_run.zig`), `chainproof prove-block` and the replay (`replay.Set.apply`, which stores the time
with the coin and writes it to the set file) use it.

**Tests** (`zig build test -Doptimize=ReleaseFast`): 17 time-lock cases against the record's time
(`negative.zig`: met exactly at `time = prev − 512·lock`, rejected one second later, both limbs, locks 1,
2, 65,535 and 0, the unused sequence bits, the disabled cases); every record's honest time on a
synthetic chain, 0 below the CSV height; blocks 9 and 170 balance across blocks with the times in the
tuples; the set pass and the set file on the regenerated test sets (Core's `hash_serialized`
unchanged).

**Lean** (`lake build` passes; axioms `propext`, `Classical.choice`, `Quot.sound`):

| Statement | File | Says |
|---|---|---|
| `Spec.CoinEpoch.coinBytes`, `serOf`, `coinBytes_inj` | `Spec/CoinEpoch.lean` | a coin's bytes are `serTxOut ‖ le4(time)`; they determine both |
| `Spec.Coins.timeLockOk` | `Spec/Coins.lean` | the time half of `SequenceLocks` for one input |
| `Block.coin_out_tuple` | `Block/CoinEvents.lean` | an output row's tuple is the created coin's, its bytes `coinBytes (serTxOut o) (pubMtp pub)` |
| `Block.coin_in_tuple`, `ClaimAt` | `Block/CoinEvents.lean`, `CoinEpochSound.lean` | an input row's tuple is its claim's: code, `serTxOut`, index and time are the undo record's committed bytes |
| `Block.in_time_lock` | `Block/TimeLock.lean` | for a non-coinbase input with claim `c`: `timeLockOk h version sequence c.mtp (pubMtp pub)` |
| `Block.epoch_systems_coreS` | `Block/SigEpoch.lean` | for a balanced epoch, outside the bad set: every non-coinbase input has `timeLockOk B.h version sequence c.mtp B.mtp`, and its spent coin is an initial one or was created by a block `B′` of the epoch with `B′.h = c.code / 2` and **`c.mtp = B′.mtp`** |
| `SetFile.txOutSer`, `SetPass.sha_side` | `Spec/SetFile.lean`, `SetPass/Sound.lean` | Core's `TxOutSer` is the record without its time; the pass hashes exactly that |

Limits of what is proven:
- `B.mtp` is `pubMtp (pub i)`, the block's public inputs 3 and 7. That they are the chain's `MTP(h − 1)` is
  `block_anc`'s statement (D-043), for blocks at or above the CSV height only (above).
- **A coin of the initial set** has the time its set file gives it. Core's `hash_serialized` does not
  cover the time, so for a proof that starts from a snapshot the times of the coins older than the start
  are an input, not a proven fact. A run from genesis has no initial coins. *(A security limit; to be
  checked by the owner. R2, the resolver, would not have had it, at the cost of a proof system inside the
  recursion.)*
- Not in the recursion's guarantee, like steps 2 and 3 (`BlockOK′` is not `BlockOK`; the circuits are
  unchanged and still attest the block system's satisfiability).
- The gate (`Compat.lean`): five statements change (`URec.rows_sound`, `epoch_coin_run`, `epoch_blocks`,
  `epoch_systems_core`, `epoch_systems_wf`: a spent value is `(code, coinBytes ser mtp)`, the length bound
  is `+ 4`, an initial coin is `RealCoin`), 14 pins are re-pinned and 9 added (D-058).

**Not done in step 4:** a run over the node's blocks with time locks; `block_anc` below the CSV height;
binding the initial set's times for a snapshot start; GPU parity on a device (step 5).

## Order of work

1. **Spec first, no proving cost.** Done, above.
2. Height-based BIP68 (AIR, witness, Lean, negative tests). Done, above.
3. Sigop cost (walker mode, classification, negative tests): built, tested and proven, above.
4. Time-based BIP68: the coin carries its time (D-058, R5). **Built and proven 2026-11-23**, above.
5. GPU witness kernels for the changed components (`gpu-cuda.md`), new VKs, one re-prove.

Each of 2–4 changes the block AIRs, hence every block VK. Nothing is re-proven until all are in,
together with the snapshot hash of step 3 if the owner wants it in the same run.

## Decided (owner, 2026-11-19)

- **The commitment change** (option A) is accepted: D-054. The set passes are redone (about $75 each at
  the 972,500 set's size).
- **A tighter size profile before the re-prove** (TIERS-2): D-055. Simulated at 40 % fewer cells
  ([report](../reports/2026-11-19-block-cost-split.md), result 4). Its offsets are searched again once
  steps 2–4 fix the new needs of `walk` and `coin`.
