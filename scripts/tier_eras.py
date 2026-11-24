"""Size profiles per era of the chain (TIERS-GEN; docs/project/roadmap.md).

Reads per-block component needs (`survey` with STARKED_SURVEY_NEEDS=1, or `replay --needs`: `height,` then
the 16 needs in `system.names` order) from one or more csv files, and for each era of heights reports the
proven cells under: tiered or uniform only; tight, then tiered, then uniform (`system.sizesAuto` today);
and one more profile fitted to that era by coordinate search, tried first. Cells are columns x rows,
columns read from `airs/block_*.json`. A sampled file (every k-th height) is fine: eras are compared by
ratio. No proving.

Usage: python3 scripts/tier_eras.py [--era 100000] [--weight k:file ...] needs.csv [more.csv ...]
"""
import sys, json, os, collections

names = "bytes fields msg sha merkle tables walk ctx wmerkle undo b2msg b2s fpwalk urec coin anc".split()
I = {n: i for i, n in enumerate(names)}
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def ncols(n):
    j = json.load(open(os.path.join(ROOT, "airs", f"block_{n}.json")))
    return j["n_preprocessed"] + j["n_main"] + 4 * ((len(j.get("lookups", [])) + 1) // 2)


cols = [ncols(n) for n in names]
FIXED = {I["ctx"]: 8, I["tables"]: 8, I["anc"]: 12}
TOP = [I[n] for n in ("sha", "msg", "bytes", "walk")]
TIGHT = dict(msg=1, bytes=1, fpwalk=3, b2s=3, undo=3, b2msg=3, walk=4, fields=7, coin=8, urec=9, merkle=10, wmerkle=10)
TIERED = dict(fpwalk=2, b2s=2, undo=2, b2msg=2, fields=5, coin=5, urec=5, merkle=5, wmerkle=5)
FREE = [n for n in names if I[n] not in FIXED and n != "sha"]


def cl(n):
    return max(0, (n - 1).bit_length())


def off_vec(off):
    return [off.get(n, 0) for n in names]


def cells_of(L, ov):
    return sum(c << (FIXED[i] if i in FIXED else max(L - o, 8)) for i, (c, o) in enumerate(zip(cols, ov)))


def fits(need_log, L, ov):
    return all(nl <= (FIXED[i] if i in FIXED else max(L - o, 8)) for i, (nl, o) in enumerate(zip(need_log, ov)))


def uniform_cells(uL):
    return sum(cols) << uL


class Blocks:
    """Blocks grouped by their vector of ceil-log needs (few distinct vectors), with counts."""

    def __init__(self):
        self.groups = collections.Counter()
        self.exact = 0

    def add(self, need, w=1):
        self.groups[tuple(cl(x) for x in need)] += w
        self.exact += w * sum(c * n for c, n in zip(cols, need))

    def total(self, profiles):
        """Cells with `profiles` (offset vectors) tried in order, then uniform; and how many blocks each took."""
        tot = 0
        used = collections.Counter()
        for nl, w in self.groups.items():
            uL = max(max(nl), 8)
            if uL < 12:
                tot += w * uniform_cells(uL)
                used["uniform"] += w
                continue
            L = max(max(nl[i] for i in TOP), 12)
            for k, ov in enumerate(profiles):
                if fits(nl, L, ov):
                    tot += w * cells_of(L, ov)
                    used[k] += w
                    break
            else:
                tot += w * uniform_cells(uL)
                used["uniform"] += w
        return tot, used


def search(blocks, rest):
    """One profile, tried before `rest`: coordinate search on the offsets, from tiered's."""
    off = dict(TIERED)
    best, _ = blocks.total([off_vec(off)] + rest)
    improved = True
    while improved:
        improved = False
        for n in FREE:
            for d in (1, -1):
                o = off.get(n, 0) + d
                if o < 0 or o > 14:
                    continue
                trial = dict(off)
                trial[n] = o
                t, _ = blocks.total([off_vec(trial)] + rest)
                if t < best:
                    best, off, improved = t, trial, True
    return off, best


def main():
    args = sys.argv[1:]
    era = 100000
    files = []
    while args:
        a = args.pop(0)
        if a == "--era":
            era = int(args.pop(0))
        else:
            files.append(a)
    if not files:
        sys.exit(__doc__)
    eras = collections.defaultdict(Blocks)
    for f in files:
        for line in open(f):
            if "error" in line:
                continue
            r = list(map(int, line.split(",")))
            eras[r[0] // era].add(r[1:])
    tiered, tight = off_vec(TIERED), off_vec(TIGHT)
    print("era (heights)        blocks   exact cells   tiered  +tight  +fitted   fitted profile's offsets below L (and its share of blocks)")
    for k in sorted(eras):
        b = eras[k]
        n = sum(b.groups.values())
        t0, _ = b.total([tiered])
        t1, _ = b.total([tight, tiered])
        off, _ = search(b, [tight, tiered])
        t2, used = b.total([off_vec(off), tight, tiered])
        show = " ".join(f"{n_}:{off[n_]}" for n_ in names if off.get(n_, 0))
        print(f"{k * era:>7}-{(k + 1) * era - 1:<7} {n:>8}   {b.exact:.3e}   {t0 / b.exact:5.2f}x  {t1 / b.exact:5.2f}x  {t2 / b.exact:5.2f}x   {show}  ({100 * used[0] / n:.0f} %)")
        print(f"{'':>16} cells: tiered {t0:.3e}; with tight {100 * (1 - t1 / t0):.1f} % fewer; with the fitted profile too {100 * (1 - t2 / t0):.1f} % fewer")


main()
