#!/usr/bin/env bash
# Source tarball for `bootstrap.sh --tarball` (local; for unpushed branches): the committed tree of
# this checkout plus third_party/stwo-zig at its checked-out commit, without stwo-zig's report
# evidence and research notes (2.6 GB → ~0.3 GB).
#   bundle.sh <out.tar.gz>
set -euo pipefail
out=${1:?usage: bundle.sh <out.tar.gz>}
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
git -C "$root" archive HEAD | tar x -C "$tmp"
mkdir -p "$tmp/third_party/stwo-zig"
git -C "$root/third_party/stwo-zig" archive HEAD -- . ':(exclude)vectors/reports' ':(exclude)autoresearch' | tar x -C "$tmp/third_party/stwo-zig"
COPYFILE_DISABLE=1 tar czf "$out" -C "$tmp" .
echo "$out: $(du -h "$out" | cut -f1) (starked-bitcoin $(git -C "$root" rev-parse --short HEAD), stwo-zig $(git -C "$root/third_party/stwo-zig" rev-parse --short HEAD))"
