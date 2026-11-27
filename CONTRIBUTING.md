# Contributing

## Set up

Install the tool versions this repository pins (see `build.zig.zon`, `lean-toolchain`), then turn on the commit hook
once per clone:

```sh
git config core.hooksPath .githooks
```

## Check your change

```sh
./scripts/check.sh          # build, forbidden Lean tactics, generated files, Lean proofs and axioms, tests, AIR drift
./scripts/check.sh --fast   # build, forbidden Lean tactics, generated files; this is what the commit hook runs
```

CI runs `./scripts/check.sh` on every pull request, without the Zig test suite and the AIR drift
check: those take about an hour, so run the full script locally before you merge. A change is ready
when it passes.

## Where things go

- `./`: tests are `test` blocks beside the code they cover.
- `lean/`: Lean proofs; `lake build` checks every theorem.

## Pull requests

Keep each pull request to one purpose. Say what changed, why, and which checks you ran.
