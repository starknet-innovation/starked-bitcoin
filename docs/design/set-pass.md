# The coin-set pass: a set file's facts proved, so a verifier needs no set

Status: current · Updated: 2026-10-27 (accepted as D-048; steps 1–5 done on small sets; step 6, the real sets on GPU, next)

Figures marked *est.* are rough; the native model (step 1) measures them.

## Why

`verify-chain` checks blocks 935,001–972,500 as one proof, but it still reads three coin-set files
(the sets after blocks 935,000, 945,000 and 972,500: 14.2 GB each) and scans them natively:

- **the balance:** each epoch's proof outputs the summed coin events under its challenge; the
  verifier adds the fractions of the epoch's start set and compares them with its end set's, under
  that challenge (`SF.sum`);
- **the binding:** the challenge is derived in-circuit from the sets' Blake2s file digests, so the
  scanned files must have those digests (`SF.scan`);
- **the facts:** Core's `hash_serialized`, the count and the amount of the final set (and the start
  set's, compared with Core's pinned assumeUTXO value at 935,000), and that the start set holds no coin
  created at or after the epoch's first block.

The set pass proves all of these per set file, so a verifier checks a few proofs and compares public
values: no set file, seconds instead of 33 minutes.

## Fixed by what is already proved

The owner's rule: anything proven stays proven. The block proofs and epoch roots already bind:

- **the digest:** Blake2s-256 of the whole set file (`epoch.setDigest`, `SF.Reader`): one sequential
  hash over the 4-byte count, then each record `txid(32) ‖ vout(4) ‖ height(4) ‖ cb(1) ‖ txi(4) ‖
  len(4) ‖ ser(len)`;
- **the fraction:** `coinFrac(ch, …) = 1/(z − φ)`, `φ = Σ αᵢ·tᵢ` over 26 terms: the txid's 16 limbs,
  `vout` and `2·height + cb` as u16 limbs, the script bytes folded by Horner at `γ` (4 M31), `len`,
  `txi` (`coin.coinFrac`).

The pass must compute exactly these. Changing either (a cheaper digest, say) would change every
challenge, hence every block proof.

`hash_serialized` (Core, `kernel/coinstats.cpp`) is SHA256d over a different stream, per coin
`txid ‖ vout ‖ (2·height + cb) as u32 LE ‖ ser`, byte-reversed at the end (`SF.scan`).

## The statement, per set file B

For challenges `ch₁ … ch_k` (public; k = 1 for a chain's end sets, 2 for a boundary between epochs,
whose set closes one epoch and opens the next under another challenge):

- B parses as the reader parses it: count n, n records, no trailing bytes; `cb ≤ 1`,
  `height < 2³¹`, `len < 2³¹ − 1`; outpoints strictly increasing (txid bytes, then `vout`);
- `digest = Blake2s(B)`, `hash = SHA256d(TxOutSer stream)` reversed;
- `count = n`, `amount = Σ` the first 8 bytes of each `ser` (each `len ≥ 8`), `maxHeight`;
- `sumⱼ = Σ coinFrac(chⱼ, coin)` for each j.

The verifier then checks natively, per epoch i under its challenge `chᵢ`:
`blocksᵢ + sum(startᵢ, chᵢ) = sum(endᵢ, chᵢ)`; the digests are the ones the epoch root bound;
`maxHeight(startᵢ) < fromᵢ`; the chain's start set has Core's pinned 935,000 `hash_serialized`.

## Segments and carried state

The pass is one long sequential computation, so it splits like the header chain:

- **Segment:** a run of whole records, ~2²³ rows (~70k coins, *est.*). The file's 4-byte count and
  the hash finalizations are the verifier's (§ What the circuit leaves to the verifier).
- **Carried (public in, public out):** the Blake2s state (8 words, the byte counter, the up-to-64
  bytes not yet compressed); the SHA-256 state (8 words, the length, the pending bytes); the k
  fraction sums; the amount and count; the last outpoint (sortedness across the boundary); the
  maximum height.
- **Aggregation:** a tree of segment proofs, as the block forest: a node checks the left child's
  outgoing state equals the right's incoming one and passes the outer states up. The root's public
  values are the statement's. Recursion and the GPU prover are reused.

## Components

Surveyed against the block system (2026-10-27): no block component starts from a carried state
(`b2s` fixes `h0` and a counter below 2^25, `sha` loads the IV and outputs only SHA256d, `coin`
accumulates from 0). The compression gadgets hold for any init rows, so the segment system copies the
block components' edges and keeps the gadgets.

### What the circuit leaves to the verifier

The pass's two ends are pure functions of public values, so they are computed natively:

- **The start:** `begin(n)` (Lean `SetFile.begin`): the count's 4 bytes are Blake2s pending bytes,
  everything else zero. The verifier builds it and compares the first segment's incoming state.
- **The end:** `finish`: one Blake2s compression of the pending bytes (counter `64·nb + plen`, last
  flag), SHA-256's padding and the second hash, and `i = n`.

A segment then proves only `s' = seg.foldl step s` for its records. Counters are block counts: the
pass only ever compresses whole 64-byte blocks, so Blake2s's `t = 64·nb` and SHA-256's
`len = 64·nb + plen`, and `nb < 2^28` fits a field element.

### One challenge per pass

A pass carries one fraction sum. The set after block 945,000, which needs two challenges (D-048),
is proved twice, once per challenge: four passes instead of three (~+$15–20 *est.*), but the
fingerprint walker (`block_fpwalk`, `γ` at public input 41) and the accumulator are reused as they
are, with their proofs.

### The segment system

Nine components. Reused unchanged (same AIR, same JSON, same proofs): `block_bytes` (the segment's
file bytes, `pub 0` = length), `block_fpwalk` (Horner over each `ser`), `block_tables` (`r8`). New:

| Component | Rows | Role |
|---|---|---|
| `set_pend` | 64 | yields the four pending-byte tables from public inputs: Blake2s in/out, SHA-256 in/out |
| `set_rec` | one per record | reads the 49-byte head and the 8 amount bytes; checks `cb ≤ 1`, `h < 2^24`, `8 ≤ len < 2^24`, sortedness against the previous record (the first against the public `last`); the code bytes `2h + cb`; the fraction `1/(z − φ)` (the coin tuple) accumulated from the public incoming sum; the amount (12 bytes, carries), the maximum height, the count; yields `rec(r, start, len)` and `code(r, i, byte)`, the `ser` segment; uses its fingerprint |
| `set_b2w` | one per word of `P_in ‖ S` | Blake2s message words over the incoming pending bytes then the segment's bytes; the last block is held back (its bytes are the outgoing pending bytes); yields words and `(block, nb_in + block + 1, last)` |
| `set_b2c` | 88 per block | the Blake2s gadget: period 0 chains from the public `h_in`, the rest from the previous period; counter `64·G`, never final; the last used period's output is the public `h_out` |
| `set_tmsg` | one per byte of `Q_in ‖ TxOutSer` | SHA-256's message, byte per row like `block_msg`: the pending bytes, then per record the outpoint (file bytes), the 4 code bytes, the `ser` (file bytes); yields big-endian words for whole blocks; the bytes after the last whole block are the outgoing pending bytes |
| `set_shac` | 72 per block | the SHA-256 gadget: period 0 from the public `H_in`, the rest chained; the last used period's output is the public `H_out` |

The lookups bind them: every record's head and amount bytes, outpoint and `ser` are read from the
byte table by position; `rec` and `code` are yielded once per record and consumed once each by
`set_tmsg`, so its records are `set_rec`'s; words and block tuples are yielded once and consumed once,
so each compression component compresses exactly the walker's blocks. Membership alone would let a
compression component stop early and leave the outgoing chaining value free, so each yields an end
token at its last block (`m − 1`) that its walker consumes once. The token is on the period's last row:
the trace's last period may be cut short (`2^L` is not a multiple of 88 or 72), and a cut period has no
output rows, so a token there would leave the output free. `set_tmsg`'s last record is
`i_out − i_in − 1`, so it walks every record.

### Public inputs

550, laid out so the reused components find theirs (`pub 0` length, `γ` at 41, the coin
challenge's `z` at 45 and `α` at 49–152 as in `block_coin`):

| Index | Value |
|---|---|
| 0 | segment length (file bytes) |
| 1, 2 | records before and after the segment (`i`) |
| 3, 4–39 | has-last flag, incoming last key (txid bytes, then `vout` big-endian) |
| 40 | incoming maximum height |
| 41–44, 45–48, 49–152 | `γ`, `z`, `α₀…α₂₅` |
| 153–156, 157–160 | incoming and outgoing sums |
| 161 | outgoing maximum height |
| 162–173, 174–185 | incoming and outgoing amount (12 bytes, little-endian) |
| 186–221 | outgoing last key |
| 222–303, 304–385 | Blake2s in, out: `h` (16 limbs), `nb`, pending length, 64 pending bytes |
| 386–467, 468–549 | SHA-256 in, out: the same layout |

### Sizes

Per record (86 file bytes, 77 `TxOutSer` bytes on average over the set after block 972,500):
`set_b2c` ~119 rows, `set_shac` ~87, `bytes` 86, `set_tmsg` 77, `fpwalk` ~37, `set_b2w` ~22,
`set_rec` 1. One profile: `set_b2c`, `set_shac`, `bytes`, `set_tmsg` at L; `fpwalk` at L − 1;
`set_b2w` at L − 2; `set_rec` at L − 6; `set_pend` at 6; `tables` at 8. At L = 23, about 70,000
records per segment and ~2,400 segments per set *est.*

### Soundness (the obligation)

`set_seg_sound`: a satisfied, balanced segment system whose incoming public state encodes a
reachable `St` (limbs and bytes in range, `t = 64·nb`) has outgoing public values encoding
`seg.foldl step s` for the records `seg` its bytes parse to, with every record well formed and
sorted. Its parts: the byte table and `set_rec` parse the segment (`encSet`'s records);
`set_b2w`/`set_b2c` give `b2Feed`, `set_tmsg`/`set_shac` give `shaFeed` (both streamed:
`b2Feed_append`, `shaFeed_append`); `set_rec` gives the rest.

### The tree

Built 2026-10-27 (`Circuit/SetTree.lean`, `src/recursion/set_tree.zig`). A segment's summary is 32
limbs: the 16-bit halves of the Blake2s digests of its **incoming and outgoing state vectors** (331
limbs each: the challenge `(γ, z, α)`, then `i`, `HASLAST`, the last key, the height, the sum, the
amount, the Blake2s and SHA-256 states; the outgoing `HASLAST` is the constant 1). The challenge is in
both vectors, so linked segments share it with no separate check, and a node checks only 16 limbs.

- **Leaf** (`setLeafOut`): the plain verifier over the segment proof, then the two digests and
  `pubsDigest(0, summary)`.
- **Node** (`setNodeProgram`): two children verified at hooks; the right one's incoming digest is the
  left one's outgoing digest; the output is (left's incoming, right's outgoing) under the key of the
  children's circuit hashes and keys. Binary; the tree over `k` leaves splits at the largest power of
  two below `k` (`set_tree.split`), so the key the verifier expects follows from `k` alone.
- **One leaf identity per pass:** every segment of a pass is built at the same component logs
  (`set_seg.buildAt`; the cutter `set_seg.cut` fills each segment to them, assuming full pending
  buffers), so the VK is (circuit FRI, segment FRI, logs, leaf identity, node identity).
- **The verifier** (`set_tree.verifyRoot`, `verifyPass`) rebuilds the start state `begin(n)` and takes
  the final state from the pass file, compares the root's summary with their digests under the
  epoch's challenge, then computes `finish` natively: digest, `hash_serialized`, count (`i = n`),
  amount, highest height, sum.
- **Lean:** `leafOut_sound`, the node's digests/key/link, `stree_sound` (a root with the expected hash
  and key is a chain of proven, linked segments, or a Blake2s collision, under the same `Trust`
  hypotheses as the block and header trees), and `SetPass.set_root_sound` (`PassChain.lean`): with
  `set_seg_sound` per segment, the root gives a record list folding the pass from the start state to
  the final state, the checks holding iff they held before (standard axioms).
- **SHA-256 length:** the pass's SHA-256 block count is a field element, but it cannot wrap: the
  Blake2s block count is checked below `2^30` in-circuit, so the file is under `2^36 + 64` bytes, and
  the `TxOutSer` stream (`40 + len` per record against the file's `49 + len`) is shorter.

## Cost

Measured by the native model (`chainproof set-pass-model`) on the set after block 972,500 (164,539,066
coins; 14,203,071,164 file bytes; 12,722,219,566 `TxOutSer` bytes): 221,922,987 Blake2s blocks and
198,784,682 SHA-256 blocks. Rows per component are *est.* until the segment system exists:

| Part | Rows |
|---|---|
| Blake2s over the file: 2.22·10⁸ compressions × 88 | ~2.0·10¹⁰ |
| SHA-256 over the `TxOutSer` stream: 1.99·10⁸ × 72 | ~1.4·10¹⁰ |
| bytes, parser, fractions (~2 rows per byte) | ~2.8·10¹⁰ |
| **total** | **~6·10¹⁰** |

At the block run's H100 rate (2²³ rows in ~1.9 s), about 4 H100-hours per set, ~$15–20. The three
sets of the current chain: ~$50–60. For scale, the chain's 37,500 block proofs were ~3·10¹¹ rows.

## Plan

1. **Native model** (`src/block/set_pass.zig`): the segment step on the carried state. **Done
   (2026-10-26):** any segmentation of `set-170` and `set-1000` gives `SF.scan`/`SF.sum`'s values
   (two challenges); over the real set after block 972,500 in 7,154 segments of 23,000 records it
   gives the epoch root's digest `77a0de28…` and Core's `hash_serialized` `9f92d143…` (15 min on the
   node, 3.8 MB).
2. **Lean spec and statement.** **Done (2026-10-27):** `lean/StarkedAir/Spec/SetFile.lean`.
   - `parseSet` is the reader; it accepts exactly the encodings of well-formed record lists
     (`parseSet_encSet`, `encSet_of_parseSet`), so the bytes fix the records (`encSet_inj`).
   - `facts`: count, amount, highest height, Blake2s digest, `hash_serialized`, one sum per challenge.
   - The pass is a per-record `step` on a carried state; Blake2s and SHA-256 are streamed (chaining
     value plus pending bytes: `b2Feed_rep`, `shaFeed_rep`), so a segment may end anywhere.
   - `pass_sound`: `finish` accepts the fold exactly when the records are well formed, strictly sorted
     and as many as declared, and then returns `facts`. `pass_segments`: any segmentation folds to
     the same state. Standard axioms only.
   - `#guard`s check a two-coin file against Python's `hashlib` and `chainproof set-pass-model`.
   Step 3's obligation: a segment proof with public states `(s, s')` implies `s' = seg.foldl step s`
   for some records `seg` (as field encodings of `St`).
3. **The segment system** (Zig witness, Lean export, soundness), small sets on the Mac.
   **Circuit done (2026-10-27):** `lean/StarkedAir/SetPass/` (six new components, `airs/set_*.json`),
   `src/block/set_seg.zig` (witnesses, `begin`, `finish`). Every segment of the sets after blocks 170
   and 1000 satisfies and balances, the first proves and verifies, and the chained public states give
   the native model's digest, `hash_serialized`, count, amount, height and sum; 21 tampered public
   values are each rejected. **Soundness done (2026-10-27):** `SetPass.set_seg_sound`
   (`SetPass/Sound.lean`, standard axioms): a satisfied, balanced segment system below the size bound
   (`SegSizeOk`) whose incoming public state encodes `s` (`EncIn`) proves records `seg` its bytes
   encode (nonempty, `RecOk`), its outgoing state encodes `seg.foldl step s` (`EncOut`), and the checks
   hold after it iff before (the records are sorted after `s`'s last). Parts: the system link
   (`Link`, `LinkUse`, `Facts`), `RecSound`, `B2wSound`/`B2cSound`/`B2Spec`, `TMsgSound`/`ShaCSound`/
   `ShaSpec`, `Fold` (`fold_step`). Review found one hole, fixed before the proof: the end tokens moved
   to the period's last row (f7caac7). Two things the tree and verifier must carry: `EncIn` asks the
   incoming state's ranges (`nb_b2 < 2^30`, key and amount bytes, height `< 2^24`, `HASLAST` 0/1), which
   `EncOut` gives back; the SHA-256 block count is a field element, so the final length
   `64·nb + plen` is exact only below `64·P` bytes (~137 GB), which the verifier should check.
4. **The set tree** (node circuit over segments, root VK pinned in `vk/`). **Built (2026-10-27):**
   § The tree. `chainproof prove-set <set.bin> <epoch> <work-dir>` proves a whole pass under the
   epoch's challenge (from its forest and its sets' digests, as the epoch root derives it):
   `<work-dir>/seg/*.sbseg`, `setvk.bin`, `pass.bin` (segment count, the count bytes, the final state,
   the root). `verify-set` checks one. Tested: three segments of `set-170` proved, folded and verified
   (swapped children unsatisfiable; a wrong final state, segment count or non-root proof rejected),
   and the test chain's five passes (one with five segments). The set VK is pinned after the real runs
   (step 6; `chainproof` has the `set` kind, empty until then).
5. **`verify-chain` without set files:** **Built (2026-10-27):** `verify-chain --set-proofs` reads each
   epoch's passes (`<dir>/pass-<to>` for its final set, `<dir>/pass-<from−1>` for its start set, both
   under its challenge) instead of set files: the digests the joins bind come from the passes' final
   states, each pass is then verified under the epoch's derived challenge, the balance is checked on
   the passes' sums, the start set's highest coin height is below the epoch's first block, consecutive
   epochs' sets have equal digests, and the chain's start set matches Core's assumeUTXO
   `hash_serialized` when one is pinned for it (935,000). On the test chain (blocks 0..15, three
   epochs) it gives the set-file path's balances and final facts (15 coins, `hash_serialized
   d6ab257d…`); the set after block 8 proved under epoch 9..15's challenge and given as epoch 4..8's is
   rejected (`scripts/test_chain_set_pass.sh`; the test chain is `data/test-chain/build.sh`'s).
6. **The real sets** on GPU pods (three sets, ~12 H100-hours *est.*).
7. Later: the balance folded into the join, so one proof covers everything.

## Decisions (D-048, owner, 2026-10-27)

1. **Scope:** all three boundary sets now, the 945,000 one under two challenges.
2. **Balance:** natively on the set-pass roots' public values first (step 5); folded into the join
   later (step 7).
3. **Anchor:** the start set's `hash_serialized` checked against Core's pinned 935,000 assumeUTXO value,
   built into the binary with the source line cited: `e4b90ef9eae834f56c4b64d2d50143cee10ad87994c614d7d04125e2a6025050`
   for block `0000000000000000000147034958af1652b2b91bba607beacc5e72a56f0fb5ee`
   (`src/kernel/chainparams.cpp:211` at Core commit `c067aa71`, the copy in `data/core-src`).
