#!/usr/bin/env python3
"""Regenerate lean-consensus/ (the standalone BitcoinConsensus Lean package) from lean/StarkedAir/Spec.

The package holds the Bitcoin consensus specifications and their proofs, with nothing specific to the
proof system. Files are copied with the namespace `StarkedAir.Spec.` renamed to `BitcoinConsensus.`.
Run from the repository root; `--check` exits non-zero if lean-consensus/ is out of date.
"""
import pathlib, sys

FILES = ["Sha256", "Sha256Fast", "Bitcoin", "MtpMath", "RetargetMath", "Chain", "Compose", "Block",
         "BlockSer", "BlockTokens", "BlockFlat", "BlockIo", "TxSplit", "TxFields", "TokSums", "SigBound",
         "PushHeight", "MerkleLevels", "Coins", "UtxoMultiset", "UtxoMap"]
SRC = pathlib.Path("lean/StarkedAir/Spec")
DST = pathlib.Path("lean-consensus")

def wanted():
    out = {}
    for f in FILES:
        text = (SRC / f"{f}.lean").read_text()
        if "import StarkedAir." in text.replace("import StarkedAir.Spec.", ""):
            sys.exit(f"{f}.lean imports outside the spec layer")
        out[DST / "BitcoinConsensus" / f"{f}.lean"] = text.replace("StarkedAir.Spec.", "BitcoinConsensus.")
    out[DST / "BitcoinConsensus.lean"] = (
        "-- Bitcoin consensus specifications and proofs, generated from starked-bitcoin's lean/StarkedAir/Spec\n"
        "-- by scripts/gen_lean_consensus.py. Do not edit here.\n" + "".join(f"import BitcoinConsensus.{f}\n" for f in FILES))
    return out

def main():
    check = "--check" in sys.argv
    stale = []
    for path, text in wanted().items():
        if not path.exists() or path.read_text() != text:
            stale.append(str(path))
            if not check:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text)
    if check and stale:
        sys.exit("lean-consensus/ is out of date: " + ", ".join(stale))

main()
