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
    python3 -I scripts/fetch_undo.py [--env FILE] [--url http://127.0.0.1:18332] [--out DIR] HEIGHT...
Writes <out>/<height>.undo (default out: testdata/undo).
"""
import base64, hashlib, json, os, sys, urllib.request
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


def compact_size(n):
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xffffffff:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


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
    heights = []
    i = 0
    while i < len(args):
        if args[i] == "--env":
            env_file = args[i + 1]; i += 2
        elif args[i] == "--url":
            url = args[i + 1]; i += 2
        elif args[i] == "--out":
            out = Path(args[i + 1]); i += 2
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
    for h in heights:
        header = headers[80 * h:80 * h + 80]
        if len(header) != 80:
            raise SystemExit(f"{h}: beyond data/headers.bin")
        want = hashlib.sha256(hashlib.sha256(header).digest()).digest()[::-1].hex()
        got = rpc("getblockhash", h)
        if got != want:
            raise SystemExit(f"{h}: node hash {got} differs from data/headers.bin ({want}); refusing")
        local = BLOCKS / f"{h}.bin"
        if local.exists() and bytes.fromhex(rpc("getblock", got, 0)) != local.read_bytes():
            raise SystemExit(f"{h}: node's raw block differs from {local}; refusing")
        block = rpc("getblock", got, 3)
        n_in = sum(len(tx["vin"]) for tx in block["tx"][1:])
        u = undo_stream(block)
        (out / f"{h}.undo").write_bytes(u)
        print(f"{h}: {n_in} spent outputs, undo stream {len(u)} bytes")


if __name__ == "__main__":
    main()
