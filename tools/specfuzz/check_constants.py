"""Checks the mainnet constants the Lean specs and the Zig verifier use against Bitcoin Core's
kernel/chainparams.cpp (CMainParams) and chain.h.
Usage: check_constants.py <core src dir>"""
import re, sys, pathlib
core = pathlib.Path(sys.argv[1])
root = pathlib.Path(__file__).resolve().parents[2]
cp = (core / "kernel/chainparams.cpp").read_text()
main = cp[cp.index("class CMainParams"):cp.index("class CTestNetParams")]
def core_int(name):
    return int(re.search(rf"consensus\.{name} = (\d+);", main).group(1))
spec_bitcoin = (root / "lean/StarkedAir/Spec/Bitcoin.lean").read_text()
spec_block = (root / "lean/StarkedAir/Spec/Block.lean").read_text()
store = (root / "src/recursion/store.zig").read_text()
checks = []
def check(what, ok):
    checks.append((what, ok)); print(("ok   " if ok else "FAIL ") + what)
vo = spec_bitcoin[spec_bitcoin.index("def versionOk"):spec_bitcoin.index("#guard versionOk 0 1")]
for name in ["BIP34Height", "BIP66Height", "BIP65Height"]:
    check(f"{name} = {core_int(name)} in versionOk", f"height < {core_int(name)}" in vo)
for name, lean in [("BIP34Height", "BIP34_HEIGHT"), ("CSVHeight", "CSV_HEIGHT"), ("SegwitHeight", "SEGWIT_HEIGHT")]:
    check(f"{name} = {core_int(name)} as {lean}", f"def {lean} : ℕ := {core_int(name)}" in spec_block)
pl = re.search(r'consensus\.powLimit = uint256\{"([0-9a-f]{64})"\}', main).group(1)
check("powLimit = 2^224 - 1", int(pl, 16) == 2**224 - 1 and "def powLimit : ℕ := 2 ^ 224 - 1" in spec_bitcoin)
check("nPowTargetTimespan = 14 days", "consensus.nPowTargetTimespan = 14 * 24 * 60 * 60;" in main and "def targetTimespan : ℕ := 1209600" in spec_bitcoin)
check("no min-difficulty, retargeting on, no BIP94", all(s in main for s in
      ["fPowAllowMinDifficultyBlocks = false", "fPowNoRetargeting = false", "enforce_BIP94 = false"]))
check("nMedianTimeSpan = 11", "nMedianTimeSpan = 11;" in (core / "chain.h").read_text() and "prev.take 11" in spec_bitcoin)
g = re.search(r'hashGenesisBlock == uint256\{"([0-9a-f]{64})"\}', main).group(1)
internal = bytes.fromhex(g)[::-1]
words = [int.from_bytes(internal[4*i:4*i+4], "big") for i in range(8)]
zig = re.search(r"GENESIS_HASH: HT.Words = \.\{ ([^}]*) \}", store).group(1)
check(f"genesis hash {g[:16]}… = store.GENESIS_HASH", [int(x.strip(), 16) for x in zig.split(",")] == words)
sys.exit(0 if all(ok for _, ok in checks) else 1)
