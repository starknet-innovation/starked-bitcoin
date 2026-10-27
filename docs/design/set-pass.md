# The coin-set pass: a set file's facts proved, so a verifier needs no set

Status: current · Updated: 2026-10-27 (accepted as D-048; steps 1–2 done)

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

- **Segment:** a run of whole records, ~2²³ rows (~23k coins, *est.*), plus the file's 4-byte count
  in the first segment and the hash finalizations in the last.
- **Carried (public in, public out):** the Blake2s state (8 words, the byte counter, the up-to-64
  bytes not yet compressed); the SHA-256 state (8 words, the length, the pending bytes); the k
  fraction sums; the amount and count; the last outpoint (sortedness across the boundary); the
  maximum height.
- **Aggregation:** a tree of segment proofs, as the block forest: a node checks the left child's
  outgoing state equals the right's incoming one and passes the outer states up. The root's public
  values are the statement's. Recursion and the GPU prover are reused.

## Components

Surveyed against the block system (2026-10-27). No block component can start from a carried state:
`b2s` fixes the chaining value to `h0` on its first period and its counter below 2^25, `sha` loads
the IV from preprocessed constants and outputs only SHA256d, and `coin`'s accumulator starts at 0 under
one challenge. The compression gadgets and their row proofs (`period_compress`, `compress_sound_air`)
hold for any init rows, so the changes are at the edges.

- **As is:** the byte table (`block_bytes`, positions local to the segment), `fpwalk` (Horner over
  `ser`), `tables`/`R8`, the ExtSum builders (`phi`, `fracC`, `accC`), the System/LogUp framework.
- **Modified:** Blake2s (start `(h, t)` from public inputs, a two-limb counter up to ~2^34, no final
  block except in the last segment, the outgoing state public; the message side takes the counter
  offset and the pending bytes); SHA-256 (chaining value from public inputs, no `DBL`/length check
  inside a segment, the outgoing state public; padding and the second hash in the last segment).
- **New:** the record parser (49-byte head, `cb ≤ 1`, `h < 2^31`, `8 ≤ len < 2^31 − 1`); the
  `TxOutSer` message stream (file bytes plus the code bytes); a coin-fraction component with two
  accumulators (two `(z, α)`), seeded from the incoming sums; amount, count and maximum height; the
  36-byte outpoint comparison against the incoming `last`; the first segment's count bytes.
- **Tree:** the header chain's `linkChecks`/`combine` (right's input = left's output) for the hash
  states, `last`, `i`, `n`, `ok`; the block node's challenge equality and range checks for the sums.

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
4. **The set tree** (node circuit over segments, root VK pinned in `vk/`).
5. **`verify-chain` without set files:** the set-pass roots in the chain file; the balance and
   anchors compared on public values.
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
