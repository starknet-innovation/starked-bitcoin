# UTXO module (M3b) — design proposal

Status: approach B approved by the owner (2026-10-10, D-040); epochs end at Core's assumeUTXO heights.
Figures marked *est.* are rough.

## What M3b must prove

For every block, given its proof (M3a: `block_sound`, `commit_sound`, `hash_pub`):

1. **Spends exist:** every input after the coinbase spends a coin that was created earlier (in an
   earlier block, or earlier in the same block) and not spent since. This includes D-031: no outpoint
   is spent twice, inside one transaction or across transactions.
2. **Undo records are those coins:** record `j` of the block's undo stream (D-038) is the spent coin's
   height, coinbase flag, amount and script (D-029).
3. **Coinbase maturity:** a coinbase coin is spent at least 100 blocks after its creation.
4. **Amounts:** a transaction's inputs sum to at least its outputs (the fee), and the block's
   coinbase claims at most the subsidy plus fees. Inputs' amounts come from the undo records.
5. **Unspendable outputs never enter the set:** `OP_RETURN` scripts and scripts over 10,000 bytes
   (Core's `IsUnspendable`).
6. **BIP30 history:** the two duplicate coinbase pairs (91722/91880 and 91812/91842) overwrite, as
   Core did; all later txids are unique (BIP34).
7. **The set itself, at chosen heights:** its `HASH_SERIALIZED` equals Core's pinned assumeUTXO
   constant (D-037), and its total amount is within the subsidy schedule (no inflation).

Script validity (signatures) is M3c, not M3b.

## Two ways to keep the set

### A. A sorted Merkle tree updated per block (the roadmap's current wording)

Each block proves its spends by inclusion paths and deletes them, then inserts its new coins with
non-inclusion paths, so the root moves from `R_{h-1}` to `R_h`.

- **Cost per coin event:** about three paths of ~28 levels (180 M leaves), with one Blake2s
  compression (88 rows) per level: about 7,400 rows. *est.*
- **Whole history:** about 6 × 10⁹ coin events (outputs created plus inputs spent), so about
  4 × 10¹³ rows. *est.* That is about 40× the block proofs themselves (next section).
- **For:** each block's statement is self-contained (`R_{h-1} → R_h`); following the tip is natural.
- **Against:** the cost; sequential root updates inside a block make the AIR long and serial.

### B. A chain-wide multiset argument (recommended)

Treat the UTXO set as offline memory checked by LogUp over the whole history:
- every created coin contributes `+1/(z − enc(coin))`;
- every spent coin contributes `−1/(z − enc(coin))`;
- the set at the end contributes `−1/(z − enc(coin))` for each remaining coin;
- the total must be zero.

A coin's tuple is its outpoint, height, coinbase flag, amount and script digest. To keep the spending
order, it also carries a position: `(height, transaction index)`.

- **Created coins** come from the block proof's parsed outputs (the fields component already reads
  every output's amount and script range).
- **Spent coins** come from the inputs' outpoints plus the undo records. So requirement 2 holds by
  construction: the tuple subtracted is the undo record's.
- **Order:** each spend checks that its coin's position is strictly earlier than the spending
  transaction's. This covers same-block spends and spending an output created later.
- **Duplicates (D-031):** a coin spent twice subtracts its tuple twice against one creation, so the
  sum is not zero. The set at the end is sorted strictly by outpoint, so it holds each coin once.
- **The challenge `z`:** it must be drawn after every tuple is fixed. History is known before proving,
  so:
  1. compute every block's commitment `C_h` (D-038) natively;
  2. derive `z` from the MMR of the `C_h`;
  3. prove each block with `z` as a public input;
  4. the final aggregation checks that `z` is the hash of the MMR of the proven `C_h`.

  This is commit-then-challenge, with the commitment checked at the end. Each epoch of history (for
  example, up to an assumeUTXO height) uses one `z`.
- **The set at the end** is the sorted coin list. The pass that subtracts it also computes
  `HASH_SERIALIZED` in Core's order and the total amount, so requirement 7 comes from the same pass.
  Chaining epochs means the next epoch starts by adding this list.
- **Cost:** a few LogUp columns per coin event inside each block proof: about one row per event, so
  about 10¹⁰ rows over history, plus the final sorted pass (about 2 × 10⁸ SHA-256 compressions, about
  1.5 × 10¹⁰ rows, *est.*, already scoped in [utxo-hash-scope.md](utxo-hash-scope.md)).
- **For:**
  - two to three orders of magnitude cheaper than A;
  - no per-block tree;
  - the undo records are checked for free;
  - `HASH_SERIALIZED` and no-inflation share the final pass.
- **Against:**
  - a statement holds only for a whole epoch: a single block's proof alone says nothing about its
    spends;
  - following the tip needs either short epochs (each paying a sorted pass over the set) or approach A
    for the last stretch;
  - the soundness argument is global, so the Lean proof is about a system of all blocks, not one.

## Soundness argument, in detail (2026-10-10)

**Spec theorem (proven, `Spec/UtxoMultiset.lean`, `run_of_balance`).** Model each transaction as its
claimed inputs `(outpoint, coin, creation index)` and its outputs. Core's update runs the transactions in
order: each input must find exactly the claimed coin, which is removed; then each output is added and may
not overwrite. The theorem assumes three things:
- every claimed creation index is earlier than the spending transaction;
- the created outpoints are distinct;
- `created = spent + final` as multisets.

Under those, Core's update never fails and ends holding exactly `final`. So the undo records are the
removed coins (D-029), and no outpoint is spent twice, in one transaction or across transactions (D-031).

**From field sums to multisets.** The epoch's sum `Σ_created 1/(z − φ) − Σ_spent 1/(z − φ) − Σ_final
1/(z − φ) = 0` over QM31 gives, outside a small set of bad `(α, z)`, per-fingerprint balance *in the
field* (`LogUpSZ.logup_sz`). Counts are only known mod p (≈ 2³¹):
- a created tuple occurs at most once (distinct outpoints);
- a final tuple occurs at most once (the final set is strictly sorted);
- a spent tuple's count is at most the epoch's number of inputs.

So **each epoch must have fewer than p − 1 inputs**. Each block proof makes its input count public, and
the aggregator checks the epoch total; an epoch that would exceed it is split. Bitcoin's total inputs to
~840k are roughly 2–3 × 10⁹ (*est.*), near p, so the first epoch may need a split.

**Distinct created outpoints.** A txid is SHA256d of the transaction. Assuming no SHA256d collision on the
chain's data (a stated cryptographic assumption), equal txids mean equal transactions:
- **coinbases after BIP34 (height 227,931)** commit to their height (proven in `block_sound`), so they
  are distinct;
- **a repeated non-coinbase transaction** would spend its inputs twice, which the balance rejects; this
  argument is well-founded on positions, since the earliest repeat would be a coinbase;
- **pre-BIP34 coinbases:** the only repeats in history are the two BIP30 pairs. The two earlier
  coinbases' outputs (heights 91,722 and 91,812) are treated as never created. Core overwrote them
  unspent at 91,880 and 91,842, so the views agree from 91,880 on, and every snapshot height is later.
  The heights are constants the verifier knows. A one-off sorted check over the ~228k pre-BIP34 coinbase
  txids shows there are no other repeats.

**The challenge.** `(α, z)` is drawn from the MMR root of the epoch's block commitments (D-038) and the
header MMR, computed natively before proving. Each block proof takes `(α, z)` as public inputs and outputs
its partial sum (a QM31) and its input count. The aggregator recomputes the challenge from the proven
commitments.

**Coin tuple.** `φ` combines, with powers of `α`:
- the txid's 16 limbs and the output index;
- `2·height + coinbase`;
- the amount's limbs;
- a fingerprint of the script, `Σ_j γ^j b_j` over QM31 with `γ` derived like `z`. That costs one row per
  script byte, on the walker that already reads script bytes.

**Build order.**
1. QM31 is a field (Lean);
2. the external-challenge running-sum gadget and its soundness;
3. the epoch theorem (sums → multisets → `run_of_balance`);
4. the undo-record parser component;
5. the coin-event component linked to the fields' outputs and inputs;
6. the final sorted pass, with `HASH_SERIALIZED`;
7. the aggregator.

## The coin-event component, as designed (2026-10-10)

One row per input and per output token of the block, **ordered by position** (strictly increasing
start, range-checked). Every fields token is consumed exactly once, so the rows are the block's inputs and
outputs in order. That fixes:
- the output index (`vout`), which restarts after each transaction's inputs;
- the record index `j` (the count of earlier non-coinbase inputs), which pairs input `j` with undo
  record `j` canonically.

The canonical pairing matters: the commitment must be the undo stream in input order.

**Kinds.** `KO` (output), `KI` (non-coinbase input), `CBI` (the coinbase input: consumed, no event).

**Tuple** (`w = 26` elements):
- txid's 16 limbs;
- `vout` as two limbs;
- `code = 2h + cb` as two limbs;
- the `serTxOut` fingerprint (4 coordinates);
- its length;
- the creation transaction index.

**Creations (`KO`):**
- txid from SHA's digest of message `1 + 2·tx`;
- `code` from `pub 2` and `tx = 0`;
- the segment `(0, row, start, len)` is offered to the fingerprint walker;
- `m = 1` unless the script is unspendable (first byte `0x6a`, or longer than 10,000 bytes) or this is a
  BIP30-lost coinbase (a public bit the verifier sets at 91,722 and 91,812).

**Spends (`KI`):**
- txid and `vout` limbs from the 36 prevout bytes;
- `code`, the amount and the creating transaction's index from undo record `j` (D-041), and the
  fingerprint from the undo segment `(1, j)`;
- the claimed creation `(height, tx)` must be lexicographically before `(pub 2, tx)`;
- a coinbase coin must be at least 100 blocks old;
- `m = −1`.

**Public inputs** (after the block's 41):
- `γ` (4);
- `z` (4);
- `αₖ` (26 × 4), with `αₖ = αᵏ` (`α₀ = 1`) for one drawn `α` (the epoch theorem's `tuplePoly`; before
  2026-10-11 the implementation drew the 26 weights independently, which is also sound but not what the
  proof covers);
- the partial sum (4);
- the input count;
- the BIP30-lost bit.

**Lookup sites:** 211 per row in the system, so the bound is `L ≤ 23` (`211·2^23 < P`). That costs
nothing in practice: a `2^24`-row block is beyond memory anyway.

**Amounts (built):** per-transaction input and output sums as 24-bit limbs (inputs ≤ `MAX_MONEY`, inputs
≥ outputs), the fees summed over the block, and the coinbase's outputs at most subsidy plus fees. Each
comparator is a difference written as a three-byte low limb and a four-byte high limb. **The high
limb's top byte is bounded by 7** (`H1C = 7 − H1 3`, `H2C = 7 − H2 3`, range-checked), so the high
limb is below `2^27 < P` and the equation cannot wrap modulo `P`. Without that bound (the AIR before
2026-10-10), a wrapped difference such as `P − 1` fits four bytes, and a transaction could output more
than its inputs or a coinbase claim more than subsidy plus fees. The block's accumulated fees are
checked within `MAX_MONEY` after each non-coinbase transaction (Core's
`bad-txns-accumulated-fee-outofrange`), which also keeps the fee accumulator from wrapping. Proven at the
natural-number level in `Block/CoinSound.lean` (`in_nat`, `out_nat`, `tend_nat`, `fee_acc`,
`coinbase_nat`), given the byte ranges from the lookups.

**The fingerprint step (closed 2026-10-10, `Spec/UtxoFingerprint.lean`).** `epoch_sound` assumed an
injective tuple encoding; the fingerprint makes it injective only for good `γ`.
- `fp_separates`: outside `fpBad` (at most `N²·(L + 1)` values of `γ`, `N` distinct byte strings, `L`
  their maximum length), equal lengths and equal fingerprints give equal bytes.
- `epoch_sound_on`: the epoch theorem needs injectivity only on the epoch's own events.
- `epoch_sound_fp`: both steps. For `γ ∉ fpBad`, then `(α, z)` outside the LogUp bad set, a zero sum
  gives Core's coins view, for any encoding that records a coin's other fields, its byte length and its
  fingerprint (`Separates`), with a coin determined by its fields and bytes.
`γ` must be drawn after the epoch's bytes are fixed: it comes from the seed over the block hashes and
commitments, which bind the raw blocks and undo data. QM31 (`|K| ≈ 2^124`), `N ≈ 2·10⁹`, `L ≤ 10⁴`: the
`γ` step's bad fraction is about `2^-50` (*est.*).

**Challenge binding (D-041, 2026-10-11).** Both bounds hold only for events fixed before `(γ, z, α)`. So
every value behind a tuple is: block bytes (block hash), undo records with their codes, amounts,
scripts **and creating-transaction indices** (the undo commitment), and the initial and final sets
(their full encodings' Blake2s in the seed). Before D-041 the final set, the initial set's indices and
each input's `CTX` were chosen after the challenge; with hundreds of free choices a generalized-birthday
search can balance a false epoch (*est.*: practical). The in-circuit undo record is now
`code (4) ‖ index (3) ‖ serTxOut`; URec reads the index bytes and yields them in `urec`, and the coin
row's `CTX` must equal them (`coin_urec`, `coin_in_tuple`). The index is below `2^24`, so it never
wraps.

## The coin proof, plan and progress (2026-10-11)

Layers (Lean):
1. **Rows** (`Block/CoinSound.lean`, done): kinds, prefix, starts, coinbase flag, record and output
   indices, tuple fields, unspendable, multiplicity, input count; running sum (`coin_runsum`, via
   `Block/RunSum.lean`); amounts at the natural-number level (`in_nat`, `out_nat`, `tend_nat`,
   `fee_acc`, `coinbase_nat`).
2. **Tokens** (`Block/CoinLink.lean`, done): `outt_sum`/`int_sum` (yields = uses), `coin_align` and
   `coin_row_tok` (coin row `j` is the block's `j`-th input or output token, same tuple), `coin_bytes`
   (every coin range check is a byte), `coin_txid` (an output's txid limbs are its transaction's
   txid).
3. **Fingerprints and claims** (done: `coin_fp_out`, `coin_urec`, `coin_fp_in`, `coin_prevout`,
   `coin_script_byte`, `urec_bytes`), existence links only, each pinned by its tuple:
   - an output's `FP(0, START, LEN, FH)` is a walker segment `(0, START)`, whose `SEG` use can only be
     the coin's own `SEG(0, START, START, LEN)` yield (undo segments have stream 1), so the walk reads
     the block bytes `[START, START + LEN)`: `FH` is their Horner fingerprint (`seg_sound`);
   - an input's `UREC(J, …)` is URec row `J` (its `J` is the row index): the code and amount bytes
     are undo bytes at `S_J`, `S_J + 7` and the creating-transaction index the bytes at `S_J + 4`
     (D-041); its `FP(1, J, SLEN, FH)` is the walker segment `(1, J)` started by URec's
     `SEG(1, J, S_J + 7, TL_J)`: `FH` is the fingerprint of undo bytes `[S_J + 7, S_J + 7 + TL_J)`;
   - the prevout bytes and an output script's first byte are block bytes (`REL_BYTE`).
4. **Events** (done 2026-10-11, `Block/CoinEvents.lean`, `Spec/BlockIo.lean`): each coin row is its
   transaction's input or output (`coin_row_tx`, `coin_kind_pos`), with its output index (`coin_vout`)
   and record index (`coin_J`); its tuple is its event's encoding (`coin_out_tuple`, `coin_in_tuple`);
   an output's multiplicity is Core's (`coin_out_mm`, `coin_unsp`); and **`coin_block_sum`**: the
   block's public partial sum is its created outputs' `1/(z − φ)` minus its spends'. Per block, the spec events (created outputs with txid, vout, `2h + cb`, `serTxOut`,
   creation index `h·2^24 + tx`; spends with the prevout and the claimed record `(code, serTxOut,
   claimed index)`), the claims being some split of the undo bytes into records (the undo component
   parses no CompactSize; the epoch balance fixes each claim to a created coin). The coin partial sum
   is the events' fractions (`coin_runsum` + the links), and the encoding satisfies `Separates`.
5. **Epoch** (next): `epoch_sound_fp` / `epoch_from_sound` on the events, then `connect_of_run` with
   `ClaimsOK` from the amounts (layer 1), and `block_sound`'s no-repeated-prevout hypothesis from the
   run (D-031).

## Recommendation (D-040, proposed)

B for catch-up and for the assumeUTXO statement. Revisit A (or a hybrid) only for tip following. Lean:
- a spec of Core's coins view as a fold over blocks;
- the multiset lemma: with zero total and strictly sorted final set, the spend multiset is the
  creation multiset minus the final set;
- per-block links to M3a's parsed outputs and undo records.

## What changes in M3a

Nothing in proven M3a statements. M3b adds to the block system:
- a coin-event component: one row per created or spent coin, its tuple, and its position check;
- a public `z` and the block's partial LogUp sum.

The block commitment (D-038) already fixes the undo format, so existing block proofs keep their
meaning. They are not reused, though: blocks are re-proved with `z`, so catch-up should wait for M3b.

## Compute wall (CATCHUP)

Block proofs alone: about 970k blocks. A recent full block is about 2²¹–2²² rows across ~900 columns
at one size, and needs 13–20 GB in the in-memory check on this laptop. *Measured on block 400000:
see status.md.* Even at a few minutes per block, that is years of single-laptop CPU time. Catch-up
needs a proving cluster (or GPU) and lifting (per-component trace sizes). It is not a laptop job.
