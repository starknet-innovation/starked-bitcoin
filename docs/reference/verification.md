# What is proven, what is trusted

Status: current · Updated: 2026-10-07

This is the project's assurance ledger. **Update it in the same commit as
any change to a theorem, an AIR or the trust base.** A claim about what the
system guarantees that doesn't appear here is not a claim the project makes.

> Formal statements are summarized informally here. The Lean theorem is
> authoritative. Have security-relevant claims reviewed before relying on
> them externally.

## Proven in Lean (standard axioms only)

| Property | Theorem | AIR version |
|---|---|---|
| SHA-256 compression = FIPS 180-4 | `Sha256.compress_sound_air` | sha256_compress v1 |
| Header hash = SHA256d(header) | `HeaderChain.chain_sound` | header_chain v1+ |
| prev-hash linkage; first prev-hash and tip hash = public inputs | `chain_sound` | v1+ |
| Proof of work (Core `CheckProofOfWork`, mainnet; target ≤ powLimit) | `chain_sound_v2`, `header_pow` | v2+ |
| Height counter, nBits constant inside a period, period-start time | `state_sound` | v3a+ |
| Difficulty retarget at positive multiples of 2016 (Core `GetNextWorkRequired`, mainnet, including the powLimit cap) | `retarget_sound` | v3b |

## Not yet constrained (header chain)

- Median time past (v4).
- Cumulative chainwork (v5).
- Wall-clock time: `time ≤ now + 2h` is out of scope by design.
- Version-bit rules do not affect historical header validity.
- Testnet and regtest rules: the specs are mainnet only.

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

## Known completeness gaps

These are deliberate: valid blocks that cannot be proven, not invalid blocks
that can.

- nBits with `nSize < 3` (targets < 2²⁴) cannot be laid out by the PoW
  gadget. No real block can meet such a target.
- A retarget whose previous exponent is outside 3..29 is rejected by the
  witness (`UnsupportedTargetEncoding`). This doesn't occur on mainnet.

## Cross-gadget dependencies

These are soundness couplings. Re-check them whenever either side changes.

- `retarget_sound` relies on the PoW row: it uses `header_pow_ex` for
  `s ≤ 26` and `s = 26 → mant < 2^16`. Without those, the division branch
  could claim a target above powLimit.
