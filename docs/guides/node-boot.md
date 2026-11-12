# Checking a Core UTXO snapshot against the seal (NODE-BOOT)

Answers: how a node operator checks that a UTXO snapshot received from anyone is the proven coin set,
before loading it into Bitcoin Core.

Status: current · Updated: 2026-11-12 · Owner files: `src/block/snapshot.zig`, `src/bin/chainproof.zig` (`verifySnapshot`, `setToSnapshot`)

## What is checked

`chainproof verify-snapshot` does three things:

1. **Verifies the seal**, exactly as `verify-seal` does: one proof for blocks 935,001–972,500 and their
   coin sets, with every VK pinned. The start set is Core's assumeUTXO set after 935,000.
2. **Binds the snapshot's base block to the proven chain.** Under SEAL-T, the headers from the base
   block to the proven tip must link by hash and end at the tip. Under the D-051 seal, the base block's
   hash must be in the verified `T`. The headers file is untrusted: every header used is checked
   against the proof.
3. **Reads the snapshot as Core's loader does** (`node/utxo_snapshot.h` v2, `compressor.cpp`,
   `PopulateAndValidateSnapshot`). The coin count, total amount, highest coin height and
   `hash_serialized` must equal the proven ones. The coins must also be strictly sorted, with no
   trailing bytes.

What is not proven: scripts and signatures (assumevalid-like, see
[overview.md](../design/overview.md)), and blocks before 935,001 (Core's assumeUTXO hash is trusted
there). The trusted items are listed in [verification.md](../reference/verification.md).

## Steps (mainnet, after block 972,500)

```sh
# On a synced Core node (v28 or later), about 20 minutes; the node rolls back, then reconnects.
bitcoin-cli -rpcclienttimeout=0 -named dumptxoutset /data/bitcoin/utxo-972500.dat rollback=972500
# Expect: "coins_written": 164539066, "txoutset_hash": "9f92d143…"

chainproof verify-snapshot utxo-972500.dat headers-972501.bin data/store/mainnet-q70-p26-l20.vk \
  data/store/mainnet-to-972502.compact.sbchain data/seal972/outT \
  data/seal972/e945:945000:935001:none data/seal972/e972:972500:945001:none
# Expect, last line: "VERIFIED: utxo-972500.dat is the proven coin set after block 972500 (00000000000000000001f945…)"
```

`headers-972501.bin` holds raw 80-byte headers from height 0 to the proven tip, 972,501.

Measured on the node (m7g, 2026-11-12): 71.6 s and 0.5 GB RSS for the 9.39 GB snapshot. Reading
the snapshot takes 70.7 s of that.

## Loading it into Core

Stock Core loads only snapshots at heights listed in its `chainparams`, and 972,500 is not one of
them. Loading this snapshot needs a Core patch: it would accept a base block whose set a verified
seal attests to. Whether that node keeps validating the old chain in the background is an open
decision for the owner (roadmap NODE-BOOT).

## Tests

- `zig build test -Dtest-filter=snapshot` covers four things:
  - amount and VARINT encodings, checked against the examples in Core's tests;
  - the special script templates;
  - a set file written as a snapshot, which must scan to the set file's facts;
  - tampers (a coin above the base height, a trailing byte, a short count, unsorted coins).
- Test chain: `chainproof set-to-snapshot data/test-chain/e15/set-15.bin data/headers.bin 15 snap15.dat`.
  Then `verify-snapshot` with `--unpinned` against `data/test-chain/out` (D-051) and `outT` (SEAL-T)
  must VERIFY. Each of these must be rejected:
  - a wrong base block (`BaseMismatch`);
  - another set (count, amount and height `MISMATCH`);
  - a flipped script byte (`hash_serialized` `MISMATCH`);
  - a forged header (`HeadersNotLinked`).
