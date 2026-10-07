# Setup

Status: current · Updated: 2026-10-07

## Requirements

| Tool | Version | Notes |
|---|---|---|
| Zig | 0.15.2 | `minimum_zig_version` in `build.zig.zon` |
| Lean (elan) | v4.33.1 | Pinned by `lean/lean-toolchain`; elan installs it automatically |
| Mathlib | v4.33.1 | Fetched by lake. Needs several GB of disk space for the cache. |
| macOS + Metal | — | Only needed for the `spike` binary's Metal backend. Tests run on CPU. |

## First checkout

```sh
git clone <repo> starked-bitcoin && cd starked-bitcoin
git submodule update --init third_party/stwo-zig
zig build test                       # Zig: parse the AIRs, check witnesses, prove/verify on CPU

cd lean
lake exe cache get                   # download prebuilt Mathlib
lake build                           # check every definition and proof (several minutes the first time)
```

When both commands succeed, the checkout is healthy. To check the full
project state, run the verification commands in
[project/status.md](../project/status.md#verify-the-current-state).

## Benchmarks (macOS)

```sh
zig build -Doptimize=ReleaseFast
zig-out/bin/spike sha 16 metal
zig-out/bin/spike headers 18 metal testdata/mainnet_headers_0_1024.hex
```

**Rule:** record each benchmark result in the relevant `docs/airs/*.md` file.
Include the machine, backend, security profile, row count and date.
Results that leave any of these out are not comparable.
