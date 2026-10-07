# What is proven, what is trusted

Status: current · Updated: 2026-10-07

This is the project's assurance ledger. **Update it in the same commit as
any change to a theorem, an AIR or the trust base.** A claim about what the
system guarantees that doesn't appear here is not a claim the project makes.

> Formal statements are summarized informally here. The Lean theorem is
> authoritative. Have security-relevant claims reviewed before relying on
> them externally.

## Proven in Lean (standard axioms only)

**Headline:** `HeaderChain.header_chain_sound` (`Gadgets/TopSound.lean`). A
satisfying trace proves `SegmentValid` (`Spec/Chain.lean`), the whole
segment's validity under Core's mainnet header rules, from decoded public
inputs to decoded public outputs. The rows below are the per-rule theorems it
is built from.

| Property | Theorem | AIR version |
|---|---|---|
| SHA-256 compression = FIPS 180-4 | `Sha256.compress_sound_air` | sha256_compress v1 |
| Header hash = SHA256d(header) | `HeaderChain.chain_sound` | header_chain v1+ |
| prev-hash linkage; first prev-hash and tip hash = public inputs | `chain_sound` | v1+ |
| Proof of work (Core `CheckProofOfWork`, mainnet; target ≤ powLimit) | `chain_sound_v2`, `header_pow` | v2+ |
| Height counter, nBits constant inside a period, period-start time | `state_sound` | v3a+ |
| Difficulty retarget at positive multiples of 2016 (Core `GetNextWorkRequired`, mainnet, including the powLimit cap) | `retarget_sound` | v3b |
| Exact chainwork: per-header `q = GetBlockProof(nBits)`; `W_j = W_{j−1} + q_j`; last `W` public | `work_q`, `work_step`, `work_out` | v5 |
| Minimum block version (Core "bad-version", BIP34/66/65 heights) | `version_sound` | v6 |
| Median time past: ≥ 6 of the 11 window times are below the header's time; the window shifts along the chain and is public at segment ends; equals Core's `GetMedianTimePast` rule given the window form | `mtp_count`, `mtp_window`, `mtp_out`, `mtp_core` (with `mtpOk_iff_count`, `sentinel_sound`) | v4 |

## Coverage audit against Bitcoin Core (2026-10-07)

Bitcoin Core `master`, fetched 2026-10-07:
- `CheckBlockHeader` (`validation.cpp`) checks `CheckProofOfWork` →
  covered (`powOk`; `DeriveTarget` rejects negative, zero, overflow and
  `> powLimit`).
- `ContextualCheckBlockHeader` checks, in order:
  - `bad-diffbits` (`GetNextWorkRequired`, `pow.cpp`): mainnet has
    `fPowAllowMinDifficultyBlocks = false` and `enforce_BIP94 = false` →
    covered (continuity plus `nextWork`);
  - `time-too-old` (MTP) → covered;
  - `time-timewarp-attack` (BIP94) → testnet4/regtest only, not mainnet;
  - `time-too-new` → out of scope (wall-clock time);
  - `bad-version` → covered (v6).
- `AcceptBlockHeader` adds only `duplicate-invalid`, `prev-blk-not-found`
  and `bad-prevblk` (chain structure, covered by linkage plus validity of
  every earlier header in the chain), and `too-little-chainwork` (anti-DoS,
  not validity).
- `GetBlockProof` / `GetBitsProof` (`chain.cpp`): `(~T / (T+1)) + 1`, or 0 for
  a negative, overflowing or zero target → matches `blockProof`.

Result: `SegmentValid` covers every mainnet header-validity rule except
`time-too-new`.

## Not yet constrained (header chain)

- Wall-clock time: `time ≤ now + 2h` is out of scope by design.
- Version-bit signalling (BIP9) does not affect header validity. (The
  minimum-version rule does, and is enforced; see the table above.)
- Testnet and regtest rules: the specs are mainnet only.

**Aggregation soundness (spec level):** `segment_compose` (`Spec/Compose.lean`).
Two valid segments, the second starting where the first ends (`Link`), form
one valid segment. By induction, any number of linked segments from genesis
form a valid chain.

**Independent check:** Z3 witness-uniqueness on four gadget windows (MTP flag,
height decomposition, retarget clamp, PoW one-hot). See the
[Z3 report](../reports/2026-10-07-z3-uniqueness.md).

## Trusted, not proven

| Assumption | Mitigation |
|---|---|
| Stwo protocol soundness (circle FRI, Fiat–Shamir, Blake2s channel) | Upstream; out of scope |
| stwo-zig implements Stwo correctly | Upstream tests. We pin the preprocessed root ourselves (stwo-zig#225). |
| The Zig interpreter matches Lean `Expr.eval` | Differential test against `probe_oracle` (`src/air/interp.zig`) |
| The JSON exporter is a faithful printer | Small and reviewed; drift check in [status.md](../project/status.md) |
| Committed `airs/*.json` equals the current Lean definitions | Drift check (regenerate and `cmp`) |
| The specs in `Spec/*.lean` match Bitcoin Core | `#guard`s on real mainnet values, and Zig tests on mainnet headers. Not proven against Core's C++. |
| Lean kernel, Mathlib, toolchain | Pinned versions |
| **(M2, planned)** The recursive verifier circuit: stwo-zig's port of StarkWare's circuit recursion (PR #204) correctly implements Stwo verification in-circuit | Not formally verified anywhere, as of 2026-10-07; stwo-zig's Lean work is RISC-V-only. Byte-parity tests against StarkWare's Rust; audit; independent native check of the final root. The composition (`REC-COMPOSE`) and our in-circuit statement (`REC-STMT-EQ`) are to be proven in Lean. |
| **Verifier obligation:** a segment starting at height 0 uses exactly the sentinel window (pubs 44/45 = `0xffff,0xffff`; pubs 48..67 as in `SENTINEL`), and later segments' input windows equal the previous segment's outputs. Also: the input-work public limbs 88..97 are 16-bit, and a genesis segment's input work is 0. | Checked by whoever verifies or aggregates segments. To be enforced in aggregation (roadmap `AGG`). |

## Known completeness gaps

These are deliberate: valid blocks that cannot be proven, not invalid blocks
that can.

- nBits with `nSize < 3` (targets < 2²⁴) cannot be laid out by the PoW
  gadget. No real block can meet such a target.
- A retarget whose previous exponent is outside 3..29 is rejected by the
  witness (`UnsupportedTargetEncoding`). This doesn't occur on mainnet.
- A header whose target is below 2^128 (exponent `s < 16`) cannot be proven
  (D-021). Mainnet targets have `s ≥ 20`; `s < 16` needs about 2^128 hashes.
- At heights below 11, a header with time 0 cannot be proven: the zero
  sentinels are not below 0. Core would reject it anyway, because the
  genesis time is above 0.

## Cross-gadget dependencies

These are soundness couplings. Re-check them whenever either side changes.

- `mtp_window` takes `T_1` from the row-220 copy of the predecessor's time
  (`copy_facts`), which the retarget also uses. Changing that copy affects both.
- `retarget_sound` relies on the PoW row: it uses `header_pow_ex` for
  `s ≤ 26` and `s = 26 → mant < 2^16`. Without those, the division branch
  could claim a target above powLimit.
