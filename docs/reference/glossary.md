# Glossary

Status: current · Updated: 2026-10-07

**Rule:** add a term the first time a doc uses it without explaining it.
Keep each entry to one or two lines.

| Term | Meaning |
|---|---|
| **AIR** | Algebraic Intermediate Representation: a trace layout plus polynomial constraints that must vanish on every row |
| **M31, P** | The field of integers mod `P = 2^31 − 1`; Stwo's base field |
| **QM31** | The degree-4 extension of M31, used for out-of-domain sampling |
| **Stwo / stwo-zig** | StarkWare's circle-STARK prover, and the Zig implementation we build on (`third_party/stwo-zig`) |
| **Circle STARK** | A STARK over the circle group of M31; Stwo's proof system |
| **LogUp** | A lookup argument based on logarithmic derivatives. Not used in our IR yet. |
| **Preprocessed column** | A column fixed by the AIR (selectors, constants). Committed and pinned by the verifier. |
| **Main trace** | Columns filled by the prover (the witness) |
| **Offset** | Reading a column at row `r + k` (cyclic) |
| **Selector** | A 0/1 preprocessed column that switches a constraint on for certain rows |
| **Period** | The number of rows one repeated unit occupies (SHA: 72, header: 256) |
| **IR** | Our constraint format, `starked-air-v1` ([ir.md](ir.md)) |
| **AIR digest** | Hash of the canonical IR, bound into the transcript |
| **Soundness (of an AIR)** | Every satisfying trace encodes a computation that meets the spec. Proven in Lean. |
| **Completeness (of an AIR)** | Every valid input has a satisfying trace. Tested, not proven. |
| **Witness generator** | Zig code that builds the main trace for a given input |
| **Tamper test** | Change one cell of a valid trace; the AIR must reject it |
| **nBits / compact target** | 32-bit encoding of the PoW target: `mantissa · 256^(exponent − 3)` |
| **powLimit** | Maximum mainnet target, `2^224 − 1` (nBits `0x1d00ffff`) |
| **Retarget** | Recomputing the target every 2016 blocks (`GetNextWorkRequired`) |
| **pst** | Period-start time: the timestamp of the first block of the current 2016-block period |
| **span** | `time_prev − pst`, clamped to `[302400, 4838400]` seconds |
| **MTP** | Median time past: the median timestamp of the previous 11 blocks |
| **Chainwork** | Cumulative work, `Σ ⌊2^256 / (target + 1)⌋` |
| **assumevalid** | Not checking scripts/signatures; trusting PoW for them (current trust model) |
| **Segment** | A run of consecutive headers proven in one trace; segments chain together through public inputs |
| **`leN`** | Lean: the little-endian value of a field stored in a raw big-endian header word |
