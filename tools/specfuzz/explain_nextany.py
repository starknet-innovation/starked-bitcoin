"""Every `nextany` divergence must be a 256-bit wrap in Core (the shifted mantissa or its product
with the timespan reaches 2^256), which cannot happen in the mainnet domain (target <= powLimit)."""
import sys
core = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.startswith("nextany")]
lean = [l.rstrip("\n").split("\t") for l in open(sys.argv[2]) if l.startswith("nextany")]
unexplained = 0
n_bad = 0
for (c, a), (_, b) in zip(core, lean):
    if a == b:
        continue
    n_bad += 1
    _, nb, prev, pst = c.split(" ")
    nb, prev, pst = int(nb), int(prev), int(pst)
    size, word = nb >> 24, nb & 0x7FFFFF
    value = word >> (8 * (3 - size)) if size <= 3 else word << (8 * (size - 3))
    span = max(302400, min(4838400, prev - pst))
    if value < 2**256 and value * span < 2**256:
        unexplained += 1
        print("UNEXPLAINED", c, a, b)
print(f"nextany: {n_bad} divergences, {unexplained} not explained by a 256-bit wrap")
sys.exit(1 if unexplained else 0)
