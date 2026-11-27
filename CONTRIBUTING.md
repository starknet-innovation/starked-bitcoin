# Contributing

## Set up

Install the tool versions this repository pins (see `build.zig.zon`, `lean-toolchain`), then turn on the commit hook
once per clone:

```sh
git config core.hooksPath .githooks
```

## Check your change

```sh
./scripts/check.sh          # format, lint, build and tests
./scripts/check.sh --fast   # the same without tests; this is what the commit hook runs
```

CI runs `./scripts/check.sh` on every pull request, without the Zig test suite and the AIR drift
check: those take about an hour, so run the full script locally before you merge. A change is ready
when it passes.

## Where things go

- `./`: tests are `test` blocks beside the code they cover.
- `lean/`: Lean proofs; `lake build` checks every theorem.

## Pull requests

Keep each pull request to one purpose. Say what changed, why, and which checks you ran.
