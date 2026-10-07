# Agent guide

Read in this order:
1. [docs/project/status.md](docs/project/status.md): current state, next step, verify commands. **Always first when resuming work.**
2. [docs/project/README.md](docs/project/README.md): session checklists, definition of done, escalation.
3. [README.md § Where to find things](README.md#where-to-find-things): the map to every other doc.

Non-negotiable:
- The repo is the source of truth for project state. Write durable knowledge into the doc that owns it ([placement rules](README.md#documentation-rules)).
- Docs change in the same commit as the code they describe.
- AIRs are defined only in Lean (`lean/StarkedAir/`). Never hand-edit `airs/*.json`; regenerate it ([docs/reference/ir.md](docs/reference/ir.md#regenerating-airsjson)).
- Never commit `sorry`, `native_decide` or `bv_decide`. Main theorems use only `propext, Classical.choice, Quot.sound`.
- Build Lean with `lake build`, never `lake env lean`; only `lake build` applies `autoImplicit=false`. Follow the proof rules in [docs/reference/lean.md](docs/reference/lean.md#rules-for-writing-proofs).
- Never edit `third_party/stwo-zig` in place. Verify claims about stwo-zig in its source code, not its README.
- Never push, open PRs or file upstream issues without the owner's approval (decision D-016).
- End every session with the [end-of-session checklist](docs/project/README.md#ending-a-session-log-progress).

Build / test / verify (from the repo root):
```sh
zig build test                    # expect: no output, exit 0
(cd lean && lake build)           # expect: "Build completed successfully"
```
Full verification (axioms, JSON drift): [docs/project/status.md § Verify the current state](docs/project/status.md#verify-the-current-state).
