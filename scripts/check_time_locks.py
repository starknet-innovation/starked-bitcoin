# Run on the node, next to rules.csv. Checks the time-based BIP68 locks listed by `survey` (STARKED_SURVEY_RULES=1, lines `tl,h,c,lock`)
# against the node: valid iff MTP(h-1) >= MTP(max(c-1,0)) + 512*lock (Core, EvaluateSequenceLocks).
import subprocess, json, sys
CLI = ["sudo", "-n", "bitcoin-cli", "-conf=/etc/bitcoin/bitcoin.conf", "-datadir=/data/bitcoin"]
locks = [tuple(map(int, l.split(",")[1:])) for l in open("rules.csv") if l.startswith("tl,")]
heights = sorted({h - 1 for h, c, l in locks} | {max(c - 1, 0) for h, c, l in locks})
mtp = {}
for i in range(0, len(heights), 200):
    chunk = heights[i:i + 200]
    for k in chunk:
        bh = subprocess.run(CLI + ["getblockhash", str(k)], capture_output=True, text=True, check=True).stdout.strip()
        mtp[k] = json.loads(subprocess.run(CLI + ["getblockheader", bh], capture_output=True, text=True, check=True).stdout)["mediantime"]
bad = 0; tight = None; zero = 0
for h, c, l in locks:
    slack = mtp[h - 1] - (mtp[max(c - 1, 0)] + 512 * l)
    if l == 0: zero += 1
    if slack < 0: bad += 1; print("FAIL", h, c, l, slack)
    if tight is None or slack < tight[0]: tight = (slack, h, c, l)
print(f"time locks {len(locks)} (lock 0: {zero}), heights queried {len(heights)}, failed {bad}, tightest slack {tight[0]} s at block {tight[1]} (coin height {tight[2]}, lock {tight[3]})")
