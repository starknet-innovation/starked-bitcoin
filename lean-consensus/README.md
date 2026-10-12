# Bitcoin consensus in Lean 4

Executable specifications of Bitcoin Core's mainnet consensus rules, with machine-checked proofs.

The files are generated from this repository's `lean/StarkedAir/Spec/` by
`scripts/gen_lean_consensus.py` (namespace `StarkedAir.Spec` → `BitcoinConsensus`). Don't edit them here;
`python3 scripts/gen_lean_consensus.py --check` fails if they drift. starked-bitcoin is a STARK prover for
Bitcoin built on stwo-zig. These files contain nothing specific to it: no AIRs, no circuits, no field
arithmetic. They are plain Lean statements about Bitcoin objects.

- **Size:** 21 files, about 4,200 lines and 163 theorems.
- **Proof hygiene:** no `sorry`, no `axiom` declarations, no `native_decide`. The main theorems depend
  only on `propext`, `Classical.choice` and `Quot.sound`.
- **Toolchain:** Lean `v4.33.1`, Mathlib `v4.33.1`.

## Contents

| File | What it specifies or proves |
|---|---|
| `Sha256`, `Sha256Fast` | SHA-256 per FIPS 180-4, over 32-bit words; `compress_eq_fast`, a fast schedule that equals the spec |
| `Bitcoin` | Header words, `sha256d` of an 80-byte header, `prevHash`, `timeOf`; proof of work (`powOk`, compact target decoding); Core's `GetMedianTimePast` (`medianTimePast`, `mtpOk`); retarget (`GetNextWorkRequired`); minimum block versions (BIP34/66/65, `versionOk`); chainwork (`blockProof`); `#guard` checks on mainnet headers |
| `MtpMath` | The MTP rule in counting form (`mtpOk_iff_count`); sentinel padding near genesis (`sentinel_sound`) |
| `RetargetMath` | Compact target encoding facts used by retarget proofs (`getCompact_of`, `nextWork_eq`, the cap cases) |
| `Chain` | `SegmentValid`: what a valid run of consecutive headers is, as input/output chain state (height, nBits, period start, MTP window, chainwork) |
| `Compose` | `segment_compose`: two valid segments whose states link form one valid segment, the basis for aggregating header chains |
| `Block`, `BlockSer` | Block and transaction deserialization (`ReadCompactSize`, segwit); txid and wtxid; Merkle root with the CVE-2012-2459 mutation flag; Core's `CheckBlock` and `ContextualCheckBlock` (sizes, weight, coinbase position, `CheckTransaction`, legacy sigops, finality, BIP34 height push, witness commitment). `checkBlock` returns Core's reject reason |
| `BlockFlat` | `checkBlock_none_iff`: `checkBlock` passes iff a conjunction of the rules holds, in any order; per-rule iff lemmas |
| `BlockTokens`, `BlockIo`, `TxSplit`, `TxFields`, `TokSums` | A block as a token stream, with round-trip lemmas between tokens, parsed transactions, inputs/outputs and sigop and witness sums |
| `SigBound`, `PushHeight`, `MerkleLevels` | Sigop bounds; the BIP34 height push; Merkle tree levels by index |
| `Coins` | Core's coins view, transaction by transaction (`CheckTxInputs` + `UpdateCoins`: coinbase maturity, `MAX_MONEY`, fees); `connect_of_run` |
| `UtxoMultiset`, `UtxoMap` | A multiset ("created = spent + remaining") characterization of connecting transactions in order, including BIP30 non-overwrite (`run_of_balance`), and its invariance under value maps (`run_map`) |

## Scope and caveats

- **Mainnet only.** Script execution (signatures), BIP68 relative locktime and the full sigop cost are
  not specified. The UTXO-dependent checks covered are those in `Coins`.
- **Fidelity to Bitcoin Core** comes from close transcription plus `#guard` tests on mainnet data. It is
  not a proof against Core's C++. Review before relying on it.
- Comments mention starked-bitcoin's internal milestones (`M3a`, `D-035`, …). They are historical
  references only.
- Built and checked on Lean `v4.33.1`. Older toolchains, e.g. `v4.29`, are untested.

## Build

```
lake exe cache get   # optional: fetch Mathlib's prebuilt oleans
lake build
```

## License

Apache License 2.0, see [LICENSE](../LICENSE).
