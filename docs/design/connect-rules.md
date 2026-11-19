# CONNECT-RULES: BIP68 relative locktimes and the full sigop cost (design)

Status: draft · Updated: 2026-11-19 · Owner files: `lean/StarkedAir/Block/Coin.lean`, `lean/StarkedAir/Block/Walk.lean`, `src/block/coin.zig`, `src/block/walk.zig`, `src/block/anc.zig`

Answers: which `ConnectBlock` rules outside scripts the block proof does not enforce, what Core
checks exactly, and how to add them. Nothing here is built. Roadmap item CONNECT-RULES.

## The gap

`Spec/Block.lean:6` leaves "fees, subsidy, BIP30, BIP68, full sigop cost, scripts" to M3b/M3c. M3b
proved fees, subsidy and BIP30 ([utxo.md](utxo.md) rules 1–7). Two rules remain that are not script
validation, and that Core enforces even under assumevalid:

| Rule | Core (`consensus/tx_verify.cpp`, `validation.cpp ConnectBlock`) | 2026-11-19 |
|---|---|---|
| BIP68 | `SequenceLocks`: reject `bad-txns-nonfinal` | not checked |
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

### Height-based: in `block_coin`

An input row of `block_coin` already holds the spent coin's code (`2·c + coinbase`, from undo record
`J`) and checks coinbase maturity against `h` (public 2) with a range check. Add:

- the input's sequence (4 bytes) and its transaction's `version ≥ 2` bit, carried by the `in(tx,
  start)` relation that `block_fields` yields (it reads both already, for finality);
- bits 31 and 22 and the 16-bit lock decomposed and range-checked;
- when active and bit 22 is clear: `h − c − lock` is a 24-bit value.

Cost: a few columns on rows that exist (the component is 0.4 % of the cells). Lean: `Spec.Coins`
gains the rule; `in_maturity`'s proof is the pattern.

### Time-based: a claim per input, resolved by one small proof per epoch

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

## Order of work

1. **Spec first, no proving cost.** `Spec`: `seqLocksOk` and `sigOpCost` in Lean, executable;
   differential fuzzing against Core (`tools/specfuzz`: `CalculateSequenceLocks`,
   `EvaluateSequenceLocks`, `GetTransactionSigOpCost`); the Zig replay checks both natively on all
   37,500 blocks (they must all pass, as Core accepted them).
2. Height-based BIP68 in `block_coin` (AIR, witness, Lean, negative tests).
3. Sigop cost (walker mode, classification, Lean, negative tests).
4. Time-based BIP68 (the committed claim, the resolver, the balance; the epoch root and seal take one
   more child).
5. GPU witness kernels for the changed components (`gpu-cuda.md`), new VKs, one re-prove.

Each of 2–4 changes the block AIRs, hence every block VK. Nothing is re-proven until all are in,
together with the snapshot hash of step 3 if the owner wants it in the same run.

## Needs the owner

- **The commitment change** (option A): accepted cost is redoing the set passes (about $75 each at
  the 972,500 set's size).
- **Finer size tiers before the re-prove** (TIERS-2): about a third fewer cells (*est.*), more Lean
  side conditions.
