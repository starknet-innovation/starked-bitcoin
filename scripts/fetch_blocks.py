#!/usr/bin/env python3
"""Fetch sample raw mainnet blocks from public Esplora APIs into testdata/blocks/ (roadmap BLOCK-SAMPLES).

A block is accepted only if its first 80 bytes equal the header at that height in
data/headers.bin (the header file every proof was built from), so each sample is bound to
the proven chain. Files: testdata/blocks/<height>.bin (raw serialized block, as Core stores it).

Usage:
    python3 -I scripts/fetch_blocks.py HEIGHT...
"""
import sys, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADERS = ROOT / "data" / "headers.bin"
OUT = ROOT / "testdata" / "blocks"
SOURCES = ["https://mempool.space/api", "https://blockstream.info/api"]


def get(path):
    last = None
    for attempt in range(6):
        base = SOURCES[attempt % len(SOURCES)]
        try:
            req = urllib.request.Request(base + path, headers={"User-Agent": "starked-bitcoin-block-samples"})
            return urllib.request.urlopen(req, timeout=60).read()
        except Exception as e:
            last = e
            time.sleep(5 * (attempt + 1))
    raise RuntimeError(f"{path}: {last}")


def main():
    headers = HEADERS.read_bytes()
    OUT.mkdir(parents=True, exist_ok=True)
    for arg in sys.argv[1:]:
        h = int(arg)
        out = OUT / f"{h}.bin"
        if out.exists():
            print(f"{h}: present ({out.stat().st_size} bytes)")
            continue
        block_hash = get(f"/block-height/{h}").decode().strip()
        raw = get(f"/block/{block_hash}/raw")
        if raw[:80] != headers[80 * h:80 * h + 80]:
            raise SystemExit(f"{h}: header differs from data/headers.bin; refusing")
        out.write_bytes(raw)
        print(f"{h}: {len(raw)} bytes, {block_hash}")


if __name__ == "__main__":
    main()
