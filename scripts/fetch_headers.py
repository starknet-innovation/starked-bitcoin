#!/usr/bin/env python3
"""Fetch all mainnet block headers from public Esplora APIs into data/headers.bin (roadmap HC-FULLRUN).

Each header is rebuilt from the block-list endpoints' fields (version, prev hash, merkle root,
time, bits, nonce) and accepted only if SHA256d(header) equals the block id and its prev hash
links to the previous header, so the file is self-verifying (genesis hash is pinned).
Resumable: the file length / 80 is the next height.

Usage:
    python3 scripts/fetch_headers.py [--to HEIGHT]                  # sequential, into headers.bin
    python3 scripts/fetch_headers.py --from LO --to HI --out FILE   # one chunk (heights LO..HI)
    python3 scripts/fetch_headers.py --merge FILE...                # verify links, append to headers.bin
"""
import argparse, hashlib, json, struct, sys, time, urllib.request
from pathlib import Path

OUT = Path(__file__).resolve().parent.parent / "data" / "headers.bin"
GENESIS = "000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f"
SOURCES = [("https://mempool.space/api/v1/blocks/{}", 15), ("https://blockstream.info/api/blocks/{}", 10)]

def get(url):
    for attempt in range(8):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "starked-bitcoin-header-index"})
            return json.loads(urllib.request.urlopen(req, timeout=30).read())
        except Exception as e:
            time.sleep(min(120, 5 * 2 ** attempt))
    raise RuntimeError(f"giving up on {url}")

def header(b):
    return (struct.pack("<i", b["version"]) + bytes.fromhex(b["previousblockhash"] or "00" * 32)[::-1] +
            bytes.fromhex(b["merkle_root"])[::-1] + struct.pack("<III", b["timestamp"], b["bits"], b["nonce"]))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--to", type=int, default=None, help="last height (default: current tip)")
    ap.add_argument("--from", dest="lo", type=int, default=0, help="first height (chunk mode)")
    ap.add_argument("--out", default=None, help="chunk file (chunk mode)")
    ap.add_argument("--merge", nargs="+", default=None, help="chunk files to verify and append, in order")
    a = ap.parse_args()
    if a.merge:
        return merge(a.merge)
    tip = a.to if a.to is not None else int(urllib.request.urlopen("https://mempool.space/api/blocks/tip/height").read())
    out = Path(a.out) if a.out else OUT
    out.parent.mkdir(exist_ok=True)
    data = out.read_bytes() if out.exists() else b""
    assert len(data) % 80 == 0
    h = a.lo + len(data) // 80
    prev = hashlib.sha256(hashlib.sha256(data[-80:]).digest()).digest()[::-1].hex() if data else None
    first = prev is None and h > 0  # chunk start: link checked at merge time
    turn, t0, h0 = 0, time.time(), h
    with out.open("ab") as f:
        while h <= tip:
            url, per = SOURCES[turn % len(SOURCES)]
            turn += 1
            top = min(h + per - 1, tip)
            blocks = sorted((b for b in get(url.format(top)) if b["height"] >= h), key=lambda b: b["height"])
            if not blocks or blocks[0]["height"] != h:
                raise RuntimeError(f"unexpected response at height {h}")
            for b in blocks:
                raw = header(b)
                bid = hashlib.sha256(hashlib.sha256(raw).digest()).digest()[::-1].hex()
                if bid != b["id"] or (prev is None and not first and bid != GENESIS) or (
                        prev is not None and b["previousblockhash"] != prev):
                    raise RuntimeError(f"verification failed at height {b['height']}")
                f.write(raw)
                prev, h = bid, h + 1
            f.flush()
            if turn % 200 == 0:
                rate = (h - h0) / (time.time() - t0)
                print(f"height {h - 1} / {tip}  {rate:.0f} headers/s  eta {(tip - h) / max(rate, 1) / 3600:.1f} h", flush=True)
            time.sleep(0.25)
    print(f"done: heights {a.lo}..{h - 1} in {out}", flush=True)


def merge(files):
    """Appends chunks to headers.bin after checking every header's link to its predecessor."""
    data = bytearray(OUT.read_bytes() if OUT.exists() else b"")
    for fn in files:
        chunk = Path(fn).read_bytes()
        assert len(chunk) % 80 == 0
        for i in range(0, len(chunk), 80):
            raw = chunk[i:i + 80]
            if data:
                want = hashlib.sha256(hashlib.sha256(bytes(data[-80:])).digest()).digest()
                if raw[4:36] != want:
                    raise RuntimeError(f"link broken at height {len(data) // 80} ({fn})")
            data += raw
        print(f"merged {fn}: now {len(data) // 80} headers", flush=True)
    OUT.write_bytes(bytes(data))

if __name__ == "__main__":
    sys.exit(main())
