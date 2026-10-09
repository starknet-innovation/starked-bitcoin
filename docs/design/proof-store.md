# Proof store (PROOF-STORE): a saved, verifiable, extendable chain proof — design

Status: current (implemented) · Updated: 2026-10-10 · Decision: D-036

## Goal

The 2026-10-09 full-chain run kept nothing but a log ([review](../reports/2026-10-09-proof-review.md)).
Before the next full run, the chain proof becomes a file that:

1. **Verifies standalone**, without proving anything and without re-deriving circuit identities.
2. **Extends at the tip:** new headers are proven and folded in, without re-proving the stored part.
3. **Survives crashes:** a long run resumes from its last checkpoint.

## What makes a proof extendable

`mmrFold` keeps a stack of peaks (perfect, aligned subtrees, sizes strictly decreasing) and then *bags*
them right to left into the root. Extending means pushing new segments onto the **peaks**, so the file
stores the peaks, not only the bagged root. The root is stored too, for verification.

**Segments must stay aligned.** A segment of `n` headers starting at height `h0 > 0` needs
`n ≤ lowbit(h0)` (and `n` a power of two). Then every stack entry is an aligned perfect subtree, and the
bagged root equals the canonical MMR root over the block hashes (`mmrRoot`), however the chain was cut
into segments. The planner (`nextSegment`) picks the largest such `n`, at most `2^(maxLog−8)`, at
least 2. From height 0 it gives exactly today's greedy plan. The verifier checks the segment list
(`validPlan`), since the root key `K` commits to it.

**The node circuit must not depend on the run.** Today `spike chain` sizes the node circuit to the
largest padded leaf among the segment sizes that run uses. A later extension using another size
could change the node's identity, and stored peaks would no longer fold. The shape is now frozen: it
covers leaves of **every** segment log size in `[9, 20]` (2 to 4096 headers). The VK follows:

- the node identity (preprocessed root, circuit hash);
- the node proof's expected `pcs_config` and preprocessed column log sizes (pinned);
- one leaf circuit hash per segment log size.

`chainproof setup` computes the VK once (about 20 min at production parameters). The production VK
is then committed as constants (`src/recursion/vk_mainnet.zig`), so verification never re-derives it.

## Verification (`chainproof verify`)

Given a proof file and the pinned VK (constants, or a VK file for test parameters):

1. **Config pinned:** the root request's `pcs_config` and column log sizes must equal the VK's. Nothing
   security-relevant is read from the file without comparison. (Fixes review finding 2.)
2. **Identity:** the request's preprocessed root is the node's.
3. **Shape:** the segment list passes `validPlan` and sums to the header count. The expected root key
   follows from it (`expectedRoot`).
4. **Proof:** the native circuit verifier accepts, and the output digest is `pubsDigest(K, pubs)`.
5. **Genesis state:** prev-hash 0, height 0, sentinel window, work 0 (as today).
6. **Genesis block (new):** an inclusion proof shows that leaf 0 of `T` is Bitcoin's genesis hash
   `000000000019d6…8ce26f`. The path must be the leftmost one, of the depth the header count implies.
   With prev-hash 0 at height 0, this pins the chain's first block to Core's genesis.
7. **Report:** tip hash, height, chainwork, `T`. The verifier must compare chainwork with a trusted
   minimum (`--min-work`): it is the only defence against a cheap low-difficulty chain (review
   finding 3); the genesis check does not replace it.

The stored peaks are also checked: each is verified natively against the VK, and bagging them must
give the stored root's public inputs. So a file whose peaks do not match its root is rejected, and an
extension never builds on unchecked data.

## File format (`.sbchain`, version 1)

Little-endian, length-prefixed, sections in this order:

| Section | Content |
|---|---|
| header | magic `SBCHAIN\0`, version `u32` |
| params | FRI config (`log_blowup`, `n_queries`, `pow_bits`, `log_last_layer`, fold step), min/max segment log size |
| vk digest | Blake2s of the VK it was proven under (the verifier compares it with the pinned VK) |
| segments | count, then `(h0, log_size)` per segment |
| peaks | count, then per peak: `Proved` (below) and its header count |
| root | `Proved` |
| genesis | the inclusion steps of leaf 0 in `T` |
| provenance | text: repo commit (and dirty flag), stwo-zig commit, SHA-256 of the proven headers, timestamps |
| trailer | SHA-256 of everything before (corruption check only; soundness comes from verification) |

A `Proved` is: the request as stwo-zig's `writeVerifyRequest` text, length-prefixed; the circuit
hash; the key; the 124 public inputs; the proof bytes (`VerifierProof.serialize`). Loading rebuilds
the in-circuit verifier's view with stwo-zig's `deserializeProof` under
`proofConfig(n_preprocessed, pcs_config)`, and requires all bytes to be consumed. A reloaded proof
re-serializes to the same bytes (tested).

Writes go to a temporary file in the same directory, are flushed and synced, and then renamed. A
crash never leaves a half-written proof.

## Commands

- `chainproof setup <params> <out.vk>`: the frozen shape and the VK; prints the Zig constants.
- `chainproof prove <params> <headers.bin> <to> <out.sbchain>`: proves `[0, to)`. After each leaf
  (and the merges it triggers) it writes a checkpoint, `<out>.ckpt`, containing the segments and
  peaks so far. It resumes from the checkpoint if one exists. At the end it bags, **writes the file,
  then verifies it** by reloading it from disk.
- `chainproof extend <in.sbchain> <headers.bin> <to> <out.sbchain>`: loads and verifies the input,
  checks that the stored headers' hashes match `headers.bin` (via `T`), proves `[N, to)`, folds and
  saves as above.
- `chainproof verify <file> [--min-work X]`: standalone verification, as above.
- `chainproof inclusion <file> <headers.bin> <height>`: an MMR inclusion proof of a block hash.

`prove` is `extend` from an empty store: one code path.

## Memory (measured 2026-10-10)

| Phase | Footprint |
|---|---|
| Leaf of 4,096 headers (log 20) | peaks at 34–37 GB |
| Leaf of 2,048 headers (log 19) | about 22 GB |
| Node | about 19 GB |
| Between segments | falls back to about 11 GB, then lower |

There is no steady leak; the peaks are transient. On a 24 GB machine, log-20 leaves swap heavily: the
first two full-run attempts were stopped at footprints of 36–38 GB with about 22 GB of swap. So long
runs use:

- `--max-log 19`: any segment size up to the VK's is valid, and the plan stays aligned. A log-19 leaf
  took 68 s, against 125–190 s for log 20 while swapping.
- `tools/prove_loop.sh`, which runs one `prove --segments K` process per K segments. Each step resumes
  from the checkpoint, so nothing can accumulate across the run.

Release builds use libc malloc instead of `DebugAllocator`, and checkpoints no longer allocate in the
prover's long-lived arena.

## Tests before any long run

On mainnet headers 0–1023 with test-strength FRI and log sizes `[9, 12]`:

1. Prove 0–51 and save; reload in a fresh process; verify.
2. Extend to 100 from the file. The root `T` must equal a from-scratch `mmrRoot` over 0–99, and
   verify.
3. A checkpoint resume gives the same file.
4. Rejected:
   - a flipped proof byte;
   - a lowered query count or other `pcs_config` field in the file;
   - one changed public input;
   - a misaligned segment list;
   - a swapped peak;
   - a genesis path that is not leftmost;
   - a truncated file.

Only then the full chain (about 14 h), then a timed extension by a few hundred real headers.

## Out of scope here

- Lean statement of the verifier's checks (review §5 item 1, the Lean half): later.
- Automatic header fetching, a service, scheduling.
- Changing circuits invalidates stored proofs: the VK digest in the file makes that an explicit error.
