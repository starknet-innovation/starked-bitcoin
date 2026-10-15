#!/usr/bin/env python3
"""Fetch blocks' undo streams from a Bitcoin Core node (BLOCK-DATA, D-038).

The undo stream is the version byte 0x01, then one record per input after the coinbase, in block
order: LE32(2 * height + coinbase) ++ LE64(value in satoshis) ++ CompactSize(len) ++ scriptPubKey
(Core's TxOutSer without the outpoint; Spec/BlockCommit.lean `undoRecord`). It is read from
`getblock <hash> 3` (each input's `prevout`), so the node needs no txindex.

Checks: the node's block hash at each height equals the hash of data/headers.bin's header there,
and the node's raw block equals testdata/blocks/<height>.bin when that file exists.

RPC over a local tunnel (the node binds 127.0.0.1 only):
    ssh -i <key> -f -N -L 18332:127.0.0.1:8332 <node>
Credentials: BITCOIN_RPC_USER (default `application`) and BITCOIN_RPC_PASSWORD from the environment
or from the file given with --env (KEY=VALUE lines). The password is never printed.

Usage:
    python3 -I scripts/fetch_undo.py [--env FILE] [--url http://127.0.0.1:18332] [--out DIR] [--blocks]
        [--blocks-dir DIR] [--ctx] HEIGHT|FROM-TO...
`--blocks` also saves the raw block (to testdata/blocks/, or `--blocks-dir`) when missing. `--ctx` also
writes <out>/<height>.ctx: per record, the creating transaction's index in its block (LE32), from the
prevout's height and the creating block's transaction list (`getblock <hash> 1`, batched; no txindex).
Writes <out>/<height>.undo (default out: testdata/undo).
"""
import base64, hashlib, json, os, sys, urllib.request
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from decimal import Decimal
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADERS = ROOT / "data" / "headers.bin"
BLOCKS = ROOT / "testdata" / "blocks"


def load_env(path):
    env = {}
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            env[k.strip()] = v.strip().strip('"').strip("'")
    return env


class Rpc:
    def __init__(self, url, user, password):
        self.url = url
        self.auth = "Basic " + base64.b64encode(f"{user}:{password}".encode()).decode()

    def __call__(self, method, *params):
        body = json.dumps({"jsonrpc": "1.0", "id": "fetch_undo", "method": method, "params": list(params)}).encode()
        req = urllib.request.Request(self.url, data=body, headers={"Authorization": self.auth, "Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=300) as r:
            resp = json.loads(r.read(), parse_float=Decimal)
        if resp.get("error"):
            raise RuntimeError(f"{method}: {resp['error']}")
        return resp["result"]

    def batch(self, calls):
        """Several calls in one JSON-RPC request (results in order)."""
        body = json.dumps([{"jsonrpc": "1.0", "id": k, "method": m, "params": list(ps)} for k, (m, ps) in enumerate(calls)]).encode()
        req = urllib.request.Request(self.url, data=body, headers={"Authorization": self.auth, "Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=600) as r:
            resps = sorted(json.loads(r.read(), parse_float=Decimal), key=lambda x: x["id"])
        for (m, _), resp in zip(calls, resps):
            if resp.get("error"):
                raise RuntimeError(f"{m}: {resp['error']}")
        return [resp["result"] for resp in resps]


def compact_size(n):
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xffffffff:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


class Creators:
    """Transaction index within its block, for the blocks that created a block's inputs. The creating
    height is the prevout's (`getblock <hash> 3`), the block hash is data/headers.bin's, and each
    creating block's txid list is read once (`getblock <hash> 1`, batched, several requests at a time)
    and kept in a bounded cache: no `getrawtransaction` per input."""

    def __init__(self, rpc, headers, keep=4096, chunk=16, workers=4):
        self.rpc, self.headers, self.keep, self.chunk, self.workers = rpc, headers, keep, chunk, workers
        self.cache = OrderedDict()

    def ensure(self, heights):
        missing = sorted(set(h for h in heights if h not in self.cache))
        chunks = [missing[k:k + self.chunk] for k in range(0, len(missing), self.chunk)]
        def fetch(hs):
            res = self.rpc.batch([("getblock", (block_hash(self.headers, h), 1)) for h in hs])
            for h, b in zip(hs, res):
                if b["height"] != h:
                    raise SystemExit(f"{h}: node's block at this hash has height {b['height']}; refusing")
            return [(h, {t: i for i, t in enumerate(b["tx"])}) for h, b in zip(hs, res)]
        with ThreadPoolExecutor(self.workers) as pool:
            for part in pool.map(fetch, chunks):
                for h, idx in part:
                    self.cache[h] = idx
        for h in heights:
            self.cache.move_to_end(h)
        while len(self.cache) > max(self.keep, len(set(heights))):
            self.cache.popitem(last=False)

    def index(self, height, txid):
        return self.cache[height][txid]


def block_hash(headers, h):
    return hashlib.sha256(hashlib.sha256(headers[80 * h:80 * h + 80]).digest()).digest()[::-1].hex()


def undo_stream(block):
    out = bytearray([1])
    for tx in block["tx"][1:]:
        for vin in tx["vin"]:
            p = vin["prevout"]
            sats = p["value"] * Decimal(100_000_000)
            if sats != sats.to_integral_value():
                raise SystemExit(f"non-integral satoshi value {p['value']}")
            script = bytes.fromhex(p["scriptPubKey"]["hex"])
            out += (2 * p["height"] + (1 if p["generated"] else 0)).to_bytes(4, "little")
            out += int(sats).to_bytes(8, "little")
            out += compact_size(len(script)) + script
    return bytes(out)


def main():
    args = sys.argv[1:]
    env_file, url, out = None, "http://127.0.0.1:18332", ROOT / "testdata" / "undo"
    save_blocks = False
    blocks_dir = BLOCKS
    want_ctx = False
    heights = []
    i = 0
    while i < len(args):
        if args[i] == "--env":
            env_file = args[i + 1]; i += 2
        elif args[i] == "--url":
            url = args[i + 1]; i += 2
        elif args[i] == "--blocks":
            save_blocks = True; i += 1
        elif args[i] == "--blocks-dir":
            blocks_dir = Path(args[i + 1]); save_blocks = True; i += 2
        elif args[i] == "--ctx":
            want_ctx = True; i += 1
        elif args[i] == "--out":
            out = Path(args[i + 1]); i += 2
        elif "-" in args[i]:
            a0, a1 = args[i].split("-"); heights.extend(range(int(a0), int(a1) + 1)); i += 1
        else:
            heights.append(int(args[i])); i += 1
    env = dict(os.environ)
    if env_file:
        env.update(load_env(env_file))
    if "BITCOIN_RPC_PASSWORD" not in env:
        raise SystemExit("BITCOIN_RPC_PASSWORD not set (environment or --env FILE)")
    rpc = Rpc(url, env.get("BITCOIN_RPC_USER", "application"), env["BITCOIN_RPC_PASSWORD"])
    headers = HEADERS.read_bytes()
    out.mkdir(parents=True, exist_ok=True)
    creators = Creators(rpc, headers)
    for h in heights:
        header = headers[80 * h:80 * h + 80]
        if len(header) != 80:
            raise SystemExit(f"{h}: beyond data/headers.bin")
        want = hashlib.sha256(hashlib.sha256(header).digest()).digest()[::-1].hex()
        got = rpc("getblockhash", h)
        if got != want:
            raise SystemExit(f"{h}: node hash {got} differs from data/headers.bin ({want}); refusing")
        local = blocks_dir / f"{h}.bin"
        rawb = bytes.fromhex(rpc("getblock", got, 0))
        if rawb[:80] != header:
            raise SystemExit(f"{h}: node's block header differs from data/headers.bin; refusing")
        if local.exists() and rawb != local.read_bytes():
            raise SystemExit(f"{h}: node's raw block differs from {local}; refusing")
        if save_blocks and not local.exists():
            blocks_dir.mkdir(parents=True, exist_ok=True)
            local.write_bytes(rawb)
        block = rpc("getblock", got, 3)
        n_in = sum(len(tx["vin"]) for tx in block["tx"][1:])
        u = undo_stream(block)
        (out / f"{h}.undo").write_bytes(u)
        if want_ctx:
            ins = [vin for tx in block["tx"][1:] for vin in tx["vin"]]
            creators.ensure([vin["prevout"]["height"] for vin in ins])
            ctx = bytearray()
            for vin in ins:
                ctx += creators.index(vin["prevout"]["height"], vin["txid"]).to_bytes(4, "little")
            (out / f"{h}.ctx").write_bytes(bytes(ctx))
        print(f"{h}: {n_in} spent outputs, undo stream {len(u)} bytes")


if __name__ == "__main__":
    main()
