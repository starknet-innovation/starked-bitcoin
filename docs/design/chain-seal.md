# The chain seal: one proof for the chain of epochs and its coin sets

Status: current · Updated: 2026-11-04 · Owner files: `lean/StarkedAir/Circuit/ChainSeal.lean`, `src/recursion/chain_seal.zig`, `src/bin/chainproof.zig` (`prove-seal`, `verify-seal`)

This document answers: what the seal circuit checks, what it outputs, what its verifier still does
natively, how it is proved and verified, and what its soundness statement is.

## Why

`verify-chain --set-proofs` (set-pass.md step 5) checks blocks 935,001–972,500 and their coin sets
with no set file, but as **six proofs and native glue**: the header chain root, the epoch join, four
set-pass roots, and in Zig the balance equations, the set-digest links, the count and height ranges.
That is fine for this binary and awkward for anyone else: a Starknet verifier or a Bitcoin Core fork
wants one proof whose public values say "from this start set, following these blocks, the coin set is
this", not our glue. D-048 and D-049 deferred the fold ("later"); the seal is that fold.

## The statement

One circuit, the Lean program `chainSeal ms gen` (`Circuit/ChainSeal.lean`; `ms` the epochs' child
counts, `gen` whether the first epoch starts from genesis), verifies in-circuit:

- **hook 0: the last join** (`EpochJoin.joinChild`), opened to `key ‖ start ‖ end ‖ a ‖ b ‖ acc`;
- **hooks `1 … S`: the set-pass roots** (`setChild`, as `SetTree.schild`), each opened to its 48
  summary limbs and key; `S = 2n` set children for `n` epochs (`2n − 1` from genesis): child
  `2i − g` is epoch `i`'s start set under epoch `i`'s challenge, `2i + 1 − g` its end set.

And checks, on values it opens itself (every opening is a Blake2s preimage of something a child
proof binds):

| Check | Gadget | Replaces (native, before) |
|---|---|---|
| `acc` opened epoch by epoch: each epoch root's output `key ‖ fin ‖ prev ‖ from ‖ to ‖ rest` recomputed, `acc₁ = H(out₀ ‖ out₁)`, `accᵢ = H(accᵢ₋₁ ‖ outᵢ)`, the last equal to the join's | `rootOpen`, `accChain` | `EJ.replay` (`verifyChain`'s `acc`) |
| each `rest` opened to `s` (4), `nin`, the challenge (12), each child's block-hash root (16 limbs) | `restOpen` (`EpochRoot.restOut`) | the head's public values |
| the join's `a`, `b`, `start`, `end` are epoch 0's `from`, the last's `to`, `prev₀` (zero words from genesis), `finₙ₋₁`; consecutive epochs link (`toᵢ + 1 = fromᵢ₊₁`, `finᵢ = prevᵢ₊₁`) | `checksOps` | `EJ.expected` |
| each set root's summary: its second digest is `Blake2s` of the outgoing state vector (331 limbs: the challenge's 112 from the epoch's `(γ, z, α)` with `α^0 … α^25` by coordinates, then `i`, 1, the last key, the highest height, the sum, the amount, the Blake2s and SHA-256 states); its first digest is that of the start vector `begin(count)` under the same challenge | `chal`, `stateOpen`, `outVec`, `inVec`, `pubsDigest`, `packEq` | `ST.verifyRoot` (`stateVec`, `outStateVec`) |
| the file's count from its 4 bytes (`c₃ < 64`) equals the final `i` | `count` | `ST.factsOf` |
| the Blake2s state finishes to the digest the epoch root bound: one compression from the chaining value, the pending bytes masked past `plen` (65-way one-hot), counter `64 nb + plen` as two u32 words, the last flag; the end set's to `fin`, the start set's to `prev` | `oneHot65`, `ltMask`, `mask`, `packBytes`, `counter`, `compressFinal` | `SS.finish` (Blake2s half), `passFacts` |
| the balance: `sᵢ + sum(startᵢ) = sum(endᵢ)` limb by limb (from genesis: `s₀ = sum(end₀)`) | `checksOps` | `verifyChainSetProofs` |
| the ranges: `ninᵢ + count(endᵢ) + count(startᵢ) < 2^30`; `maxHeight(startᵢ) < fromᵢ` | `lt30` | same |
| the key: `Blake2s` over every child's circuit hash and key | `blake2s` | `wk.key` |

**The output digest** is `Blake2s` of 63 words: `key ‖ a ‖ b ‖ start ‖ end ‖ acc ‖ count ‖ amount
(3 words) ‖ maxHeight ‖ Merkle root (8) ‖ shaEnd (8) ‖ shaStart (8)`, where `shaEnd`/`shaStart` are
the Blake2s digests of the end and start sets' SHA-256 states (82 limbs each; zero words for the
start of a chain from genesis). The verifier finishes those natively to Core's `hash_serialized`
(SHA-256 is not in the glue language: no gadget, and the Lean spec's `finish` is two more
compressions over public bytes). The Merkle root is the end set's (D-050), for membership proofs.

## What stays native

`verify-seal` (`chain_seal.verify`) still does, on public data:

1. the header chain root (`store.verifyChain`), as every verifier;
2. each epoch head opened as `verify-chain` does (`ER.openHead`): the children's identities from the
   pinned tree VKs into the root's key, the block-hash roots' inclusion paths against the chain's `T`;
   the joins replayed natively for the join's key and `acc` (`EJ.replay`);
3. the set keys from the pinned set VK and each pass's segment count (`ST.expected`);
4. the facts from the public final states: `SS.finish` for `hash_serialized`, the digests the join must
   open to, `shaDigest`;
5. Core's assumeUTXO anchor for the chain's start set;
6. the one proof against the pinned seal identity with the digest of 1–4 (`expected`, the same
   function the prover checks its circuit against).

So after the seal, the native part is hashing of public data plus one STARK verification; the
arithmetic of the statement (balance, links, finish, ranges) is in-circuit. The header root and the
`T` paths are the next fold (below).

## Files and commands

- `chainproof prove-seal <vk> <file.sbchain> <out-dir> [--unpinned] <epoch>...`: reads
  `<out>/chain-<to>.bin` (the last join and the heads), `<out>/joinvk.bin`, each epoch's tree VK and
  passes (`<dir>/pass-<to>`, `<dir>/pass-<from−1>`, each verified under its epoch's challenge first),
  builds the seal, checks it is satisfied with the native output, proves it at its natural size on the
  CPU, and writes `<out>/seal-<to>.bin` and `<out>/sealvk.bin`. The children's verifier
  configurations come from their proofs' requests (`sharedOf`): a child of another shape changes the
  seal's circuit, which the pinned seal VK rejects.
- `chainproof verify-seal <vk> <file.sbchain> <out-dir> [--min-work …] [--unpinned] <epoch>...`.
- `chainproof setup-seal-vk <out-dir> <chain-<to>.bin> <joinvk> <pass-dir>`: the seal VK remade from
  public inputs (the heads' child counts, the join's and the set tree's configurations from their proofs'
  requests, each accepted only under its pinned VK), no proof made; says whether it is the pinned one.
  Mainnet: equals `vk/epoch/seal-935001-972500.vk` (8.9 s, 6.3 GB).
- **The seal file** (`SBSEAL01`): the heads (as the chain file), the set VK the passes were proved
  under (accepted only when pinned), per set child its segment count, count bytes, final state and
  Merkle root, the seal proof.
- **The seal VK** (`SBSEALVK`): the configuration, `ms`, `gen`, the trace log, the identity.
- Exported programs: `airs/chain_seal_1_2_3_genesis.json` (the test chain: epochs 0..3, 4..8, 9..15)
  and `airs/chain_seal_16_16.json` (mainnet 935,001–945,000 and 945,001–972,500). Another chain shape
  needs an export (`lake env lean --run Export.lean chain_seal <m,m,…> [genesis]`) and a `build.zig`
  entry.

## Measured

| Seal | Variables | Trace | Prove (CPU) | Peak RSS | File |
|---|---|---|---|---|---|
| test chain 0..15 (3 epochs, 5 set children; M4 Pro, 2026-11-04) | 69,078,170 | 2^24 | 214 s | 14.4 GB | 583,149 bytes |

The program for the test chain is 42,375 ops (24,000 Blake2s G gates: 300 blocks, mostly the two
331-limb state digests per set child); mainnet's is 37,228 ops.

## Soundness

All on standard axioms (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`:

- **Per gadget** (`Circuit/ChainSealSound.lean`, 27 theorems): the children's digests and hooks, `rest`,
  `acc`, the constants, the challenge expansion, bytes and the count, packing, the one-hot and mask, the
  counter, `compressFinal_sound` (RFC 7693 `F`), the program's key and output digest, and the checks.
- **A set child as a pass** (`Circuit/ChainSealSet.lean`): the seal's registers read as the segment
  system's public inputs, `pbOf` (the start vector) and `pfOf` (the final vector). `setOpen_summ`: the
  child's 48 limbs are `summ2 pb pf R`; `setOpen_begin`: `pb` encodes `begin 1 count` (`EncIn`), the
  count from its 4 bytes below `2^30`; `setOpen_finish`: for any final state `pf` encodes, the in-circuit
  compression is Blake2s's `hashBlocks` of its Blake2s state; `setOpen_i`, `setOpen_cntW`,
  `setOpen_maxhW`, `setOpen_amtW`, `setOpen_shaDg`, `setOpen_mroot`: the end facts' words.
- **The set tree with a named collision** (`SetPass/PassChainW.lean`): `set_root_sound` concludes
  `… ∨ Collision`, which is vacuous (`RecCR.collision_true`: 9-word messages outnumber digests);
  `set_root_soundW` restates it as `RecCR` does the block trees: the segment tree is computed from the
  witnesses (`segOf`) and the conclusion is `… ∨ Collides (setPairs …)`.
- **The seal, composed: `seal_soundW`** (`Circuit/ChainSealCompose.lean`). Hypotheses: the chain's
  `TrustEW`, the set trees' `TrustW`, the seal's `TC` (a proof accepted under `sealH` with output `d`
  runs `chainSeal ms gen` with the witness `sealW d`), the verifier's own checks on its chain of epoch
  openings `c` (as `chain_verifyW` takes them), and `Acc sealH (H (sealMsg …))`, the message the
  verifier recomputes. Conclusion: `c` is valid; per epoch `EpochOk` (the table above, as statements
  about records: the passes fold from `begin 1 count` under the fractions of the epoch's challenge,
  `SE.sums = s + SB.sums`, the finishes are `fin` and `prev`, the ranges); `EndOk` (the end facts in `W`
  are the last end set's); or two of `sealPairs` collide.

What the theorem does not cover: the header root and `T` (native, SEAL-T); `hash_serialized` (the
verifier finishes the SHA-256 state whose digest `EndOk` names); that the pinned seal VK is
`chainSeal ms gen` (remade by `setup-seal-vk`, not proven); that Zig's `expected` is Lean's `sealMsg` (tested).

## Next fold: the header root and `T`

The seal still trusts the verifier to check each epoch child's block-hash root against the header
chain's `T` (paths in the heads). Folding it: the header chain root as one more child (its 124
public inputs opened, the genesis checks as 50 constant equalities, `T` and the height read from
them), and per epoch child an MMR inclusion of its root at its aligned position: ~60 conditional
Blake2s compressions per child with sides computed from the bits of the position and the leaf count
(`HTree.sides`), about 2^20 more G gates. The canonical decomposition of `[from, to]` into aligned
subtrees must then be computed in-circuit too (the roots' children are not bound to positions by
`rest`). Planned as SEAL-T.
