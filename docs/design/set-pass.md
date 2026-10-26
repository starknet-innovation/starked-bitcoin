# The coin-set pass: a set file's facts proved, so a verifier needs no set

Status: proposal (2026-10-26). Figures marked *est.* are rough; the native model (step 1) measures them.

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

Reused from the block system (proven gadgets, Lean models exist): the byte stream, SHA-256
compression, Blake2s message words and compression, the coin fraction (Horner over `ser`, the
26-term fingerprint, the inverse). New: the set-record parser (the field layout above, the range
checks), the 36-byte outpoint comparison, the carried-state boundary rows.

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
2. **Lean spec and statement:** the set file's parse, `digest`, `hash`, `sum` as Lean functions
   over bytes; the segment relation; composition by induction over segments.
3. **The segment system** (Zig witness, Lean export, soundness), small sets on the Mac.
4. **The set tree** (node circuit over segments, root VK pinned in `vk/`).
5. **`verify-chain` without set files:** the set-pass roots in the chain file; the balance and
   anchors compared on public values.
6. **The real sets** on GPU pods (three sets, ~12 H100-hours *est.*).
7. Later: the balance folded into the join, so one proof covers everything.

## Questions for the owner

1. **Scope:** prove all three boundary sets now (the 945,000 one under two challenges), as above?
2. **Balance:** first natively on the set-pass roots' public values (step 5), the join folding it in
   later (step 7)?
3. **Anchor:** the start set's `hash_serialized` checked against Core's pinned 935,000 value built
   into the binary (as `nMinimumChainWork` is), with the source line cited?
