#!/usr/bin/env python3
"""Bucket the chain survey (docs/design/chain-survey.md) by trace size and GPU class.

Usage: python3 -I scripts/survey_summary.py <sizes.csv | dir of w*.csv> [headers.bin]
Prints Markdown tables. `headers.bin` (raw 80-byte headers from height 0) dates the height ranges.

GPU classes: a block fits a device when its planned arena plus HEADROOM_GIB (CUDA context, cuBLAS-free
runtime and driver reservations; the 2^22 tiered run showed 25.6 GiB planned as 26.9 GB in nvidia-smi)
fits the device's total memory as nvidia-smi reports it.
"""
import collections, os, struct, sys, time

HEADROOM_GIB = 1.5
# (label, total MiB per nvidia-smi)
GPUS = [
    ("<= 24 GB (RTX 4090)", 24564),
    ("<= 48 GB (L40S 46068 MiB / A6000)", 46068),
    ("<= 80 GB (A100 / H100 80 GB)", 81559),
    ("<= 94 GB (H100 NVL)", 95830),
    ("<= 141 GB (H200)", 143771),
]
MORE = "> 141 GB (none single-GPU)"
COLS = ["height", "L", "profile", "block_bytes", "undo_bytes", "ntx", "uniform_L", "binding", "misfit", "covered", "arena_gib"]


def gpu_class(arena):
    if arena is None:
        return "no plan"
    for label, mib in GPUS:
        if arena + HEADROOM_GIB <= mib / 1024:
            return label
    return MORE


def load(path):
    files = [os.path.join(path, f) for f in sorted(os.listdir(path)) if f.endswith(".csv")] if os.path.isdir(path) else [path]
    rows, errors = {}, {}
    for f in files:
        for line in open(f):
            p = line.rstrip("\n").split(",")
            if p[0] == "height":
                continue
            h = int(p[0])
            if p[1] == "error":
                errors[h] = p[2]
                continue
            r = dict(zip(COLS, p))
            for k in ("L", "block_bytes", "undo_bytes", "ntx", "uniform_L", "covered"):
                r[k] = int(r[k])
            r["height"] = h
            r["arena_gib"] = float(r["arena_gib"]) if r["arena_gib"] else None
            rows[h] = r
    return rows, errors


def main():
    rows, errors = load(sys.argv[1])
    hdr = open(sys.argv[2], "rb").read() if len(sys.argv) > 2 else None
    nh = len(hdr) // 80 if hdr else 0

    def year(h):
        if not hdr:
            return "?"
        h = min(h, nh - 1)
        return time.gmtime(struct.unpack_from("<I", hdr, 80 * h + 68)[0]).tm_year

    hs = sorted(rows)
    top = max(list(rows) + list(errors)) if rows or errors else -1
    missing = top + 1 - len(rows) - len(errors)
    print(f"Heights 0..{top}: {len(rows)} sized, {len(errors)} errors, {missing} missing.\n")

    print("### By (L, profile)\n")
    print("| L | profile | arena GiB | GPU class | blocks | share |")
    print("|---|---|---|---|---|---|")
    byp = collections.Counter((r["L"], r["profile"]) for r in rows.values())
    arena = {(r["L"], r["profile"]): r["arena_gib"] for r in rows.values()}
    for (L, prof), n in sorted(byp.items()):
        a = arena[(L, prof)]
        print(f"| {L} | {prof} | {a if a is not None else '-'} | {gpu_class(a)} | {n:,} | {100 * n / len(rows):.2f} % |")

    print("\n### By GPU class\n")
    print("| GPU class (arena + 1.5 GiB fits) | blocks | share | cumulative |")
    print("|---|---|---|---|")
    byg = collections.Counter(gpu_class(r["arena_gib"]) for r in rows.values())
    cum = 0
    for label in [g[0] for g in GPUS] + [MORE, "no plan"]:
        n = byg.get(label, 0)
        if n == 0 and label in (MORE, "no plan"):
            continue
        cum += n
        print(f"| {label} | {n:,} | {100 * n / len(rows):.2f} % | {100 * cum / len(rows):.2f} % |")

    print("\n### By height range (50k blocks)\n")
    labels = [g[0].split(" (")[0] for g in GPUS] + ["> 141 GB"]
    print("| heights | years | blocks | L range | modal (L, profile) | " + " | ".join(labels) + " |")
    print("|---|---|---|---|---|" + "---|" * len(labels))
    for lo in range(0, top + 1, 50_000):
        rs = [rows[h] for h in range(lo, min(lo + 50_000, top + 1)) if h in rows]
        if not rs:
            continue
        c = collections.Counter(gpu_class(r["arena_gib"]) for r in rs)
        modal = collections.Counter((r["L"], r["profile"]) for r in rs).most_common(1)[0][0]
        y0, y1 = year(lo), year(min(lo + 49_999, top))
        cells = [f"{c.get(g[0], 0):,}" for g in GPUS] + [f"{c.get(MORE, 0):,}"]
        print(f"| {lo:,}–{min(lo + 49_999, top):,} | {y0}–{y1} | {len(rs):,} | {min(r['L'] for r in rs)}–{max(r['L'] for r in rs)} | {modal[0]} {modal[1]} | " + " | ".join(cells) + " |")

    if hdr:
        print("\n### By year\n")
        print("| year | blocks | " + " | ".join(labels) + " |")
        print("|---|---|" + "---|" * len(labels))
        byy = collections.defaultdict(collections.Counter)
        for r in rows.values():
            byy[year(r["height"])][gpu_class(r["arena_gib"])] += 1
        for y in sorted(byy):
            c = byy[y]
            print(f"| {y} | {sum(c.values()):,} | " + " | ".join(f"{c.get(g, 0):,}" for g in [g[0] for g in GPUS] + [MORE]) + " |")

    print("\n### Binding component\n")
    print("| profile | binding | blocks |")
    print("|---|---|---|")
    for (p, b), n in sorted(collections.Counter((r["profile"], r["binding"]) for r in rows.values()).items()):
        print(f"| {p} | {b} | {n:,} |")

    fb = [r for r in rows.values() if r["profile"] == "uniform" and r["uniform_L"] >= 12]
    print(f"\n### Uniform fallbacks (uniform L >= 12 but a component missed its tier): {len(fb):,}\n")
    if fb:
        print("| misfit | blocks | L | example heights |")
        print("|---|---|---|---|")
        g = collections.defaultdict(list)
        for r in sorted(fb, key=lambda r: r["height"]):
            g[(r["misfit"], r["L"])].append(r["height"])
        for (m, L), v in sorted(g.items(), key=lambda kv: -len(kv[1])):
            print(f"| {m} | {len(v):,} | {L} | {', '.join(map(str, v[:8]))}{' …' if len(v) > 8 else ''} |")

    nc = [r for r in rows.values() if not r["covered"]]
    print(f"\n### Not covered by SizeOk (buildFull refuses): {len(nc)}\n")
    for r in nc[:20]:
        print(f"- {r['height']}: L {r['L']} {r['profile']}, {r['block_bytes']:,} B")
    big = [r for r in rows.values() if r["L"] >= 24]
    print(f"\n### L >= 24: {len(big)}\n")
    for r in sorted(big, key=lambda r: r["height"])[:30]:
        print(f"- {r['height']}: L {r['L']} {r['profile']}, {r['block_bytes']:,} B, {r['ntx']} txs, binding {r['binding']}")

    print("\n### Largest blocks (bytes)\n")
    print("| height | bytes | undo bytes | txs | L | profile | binding | arena GiB |")
    print("|---|---|---|---|---|---|---|---|")
    for r in sorted(rows.values(), key=lambda r: -r["block_bytes"])[:12]:
        print(f"| {r['height']} | {r['block_bytes']:,} | {r['undo_bytes']:,} | {r['ntx']:,} | {r['L']} | {r['profile']} | {r['binding']} | {r['arena_gib']} |")
    print("\n### Largest undo streams\n")
    print("| height | bytes | undo bytes | txs | L | profile | binding |")
    print("|---|---|---|---|---|---|---|")
    for r in sorted(rows.values(), key=lambda r: -r["undo_bytes"])[:8]:
        print(f"| {r['height']} | {r['block_bytes']:,} | {r['undo_bytes']:,} | {r['ntx']:,} | {r['L']} | {r['profile']} | {r['binding']} |")
    # The smallest block at each L of the tiered profile: how close to the next step.
    print("\n### Smallest and largest block per (L, profile)\n")
    print("| L | profile | smallest (height: bytes) | largest (height: bytes) |")
    print("|---|---|---|---|")
    for key in sorted(byp):
        rs = [r for r in rows.values() if (r["L"], r["profile"]) == key]
        lo = min(rs, key=lambda r: r["block_bytes"])
        hi = max(rs, key=lambda r: r["block_bytes"])
        print(f"| {key[0]} | {key[1]} | {lo['height']}: {lo['block_bytes']:,} | {hi['height']}: {hi['block_bytes']:,} |")
    if errors:
        print(f"\n### Errors: {len(errors)}\n")
        for h, e in sorted(errors.items())[:20]:
            print(f"- {h}: {e}")


if __name__ == "__main__":
    main()
