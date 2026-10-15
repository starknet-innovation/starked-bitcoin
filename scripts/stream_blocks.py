#!/usr/bin/env python3
"""Stream raw blocks from a Bitcoin Core node to stdout, in height order, as `replay`'s records
(src/bin/replay.zig): LE32 height, LE32 n, n raw block bytes. Block hashes come from data/headers.bin
(`--headers`), so the only call is `getblock <hash> 0`, batched (`--batch` heights per request) with
`--workers` requests in flight; `replay` checks every block against its pinned header.

RPC over a local tunnel (as scripts/fetch_undo.py; the node binds 127.0.0.1 only):
    ssh -i <key> -f -N -L 18332:127.0.0.1:8332 <node>
Credentials: BITCOIN_RPC_USER (default `application`) and BITCOIN_RPC_PASSWORD from the environment or
the file given with --env; or `--cookie-stdin`: the node's cookie (`user:password`) on stdin, kept in
memory only (on the node, as scripts/survey_driver.py). The password is never printed.

Usage:
    python3 -I scripts/stream_blocks.py [--env FILE | --cookie-stdin] [--url http://127.0.0.1:18332]
        [--headers data/headers.bin] [--batch 8] [--workers 4] FROM TO | ./zig-out/bin/replay ...
Progress (height, MB/s) goes to stderr every 30 s.
"""
import base64, http.client, json, os, struct, sys, time, urllib.parse
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib, threading

ROOT = Path(__file__).resolve().parent.parent


def load_env(path):
    env = {}
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if line and not line.startswith("#") and "=" in line:
            k, v = line.split("=", 1)
            env[k.strip()] = v.strip().strip('"').strip("'")
    return env


class Rpc:
    """One keep-alive connection per thread."""

    def __init__(self, url, auth):
        u = urllib.parse.urlparse(url)
        self.host, self.port = u.hostname, u.port or 8332
        self.auth = "Basic " + base64.b64encode(auth.encode()).decode()
        self.local = threading.local()

    def batch(self, calls):
        body = json.dumps([{"jsonrpc": "1.0", "id": k, "method": m, "params": list(ps)} for k, (m, ps) in enumerate(calls)])
        for attempt in range(10):
            try:
                conn = getattr(self.local, "conn", None)
                if conn is None:
                    conn = self.local.conn = http.client.HTTPConnection(self.host, self.port, timeout=600)
                conn.request("POST", "/", body=body, headers={"Authorization": self.auth, "Content-Type": "application/json"})
                r = conn.getresponse()
                data = r.read()
                if r.status == 401:
                    raise SystemExit("RPC 401: wrong credentials")
                resps = sorted(json.loads(data), key=lambda x: x["id"])
                for (m, _), resp in zip(calls, resps):
                    if resp.get("error"):
                        raise RuntimeError(f"{m}: {resp['error']}")
                return [resp["result"] for resp in resps]
            except (OSError, http.client.HTTPException) as e:
                self.local.conn = None
                print(f"stream_blocks: RPC retry {attempt + 1} after {type(e).__name__}", file=sys.stderr)
                time.sleep(min(60, 2 ** attempt))
        raise SystemExit("stream_blocks: RPC failed 10 times")


def main():
    args = sys.argv[1:]
    env_file, url, headers_path, cookie_stdin = None, "http://127.0.0.1:18332", ROOT / "data" / "headers.bin", False
    batch, workers = 8, 4
    pos = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "--env":
            env_file = args[i + 1]; i += 2
        elif a == "--url":
            url = args[i + 1]; i += 2
        elif a == "--headers":
            headers_path = Path(args[i + 1]); i += 2
        elif a == "--cookie-stdin":
            cookie_stdin = True; i += 1
        elif a == "--batch":
            batch = int(args[i + 1]); i += 2
        elif a == "--workers":
            workers = int(args[i + 1]); i += 2
        else:
            pos.append(int(a)); i += 1
    if len(pos) != 2:
        raise SystemExit(__doc__)
    lo, hi = pos
    if cookie_stdin:
        auth = sys.stdin.readline().strip()
    else:
        env = dict(os.environ)
        if env_file:
            env.update(load_env(env_file))
        if "BITCOIN_RPC_PASSWORD" not in env:
            raise SystemExit("BITCOIN_RPC_PASSWORD not set (environment or --env FILE)")
        auth = f"{env.get('BITCOIN_RPC_USER', 'application')}:{env['BITCOIN_RPC_PASSWORD']}"
    rpc = Rpc(url, auth)
    headers = headers_path.read_bytes()
    if 80 * (hi + 1) > len(headers):
        raise SystemExit(f"{hi}: beyond {headers_path}")

    def block_hash(h):
        return hashlib.sha256(hashlib.sha256(headers[80 * h:80 * h + 80]).digest()).digest()[::-1].hex()

    def fetch(hs):
        return hs, rpc.batch([("getblock", (block_hash(h), 0)) for h in hs])

    out = sys.stdout.buffer
    chunks = [list(range(s, min(s + batch, hi + 1))) for s in range(lo, hi + 1, batch)]
    t0 = last = time.time()
    total = 0
    with ThreadPoolExecutor(workers) as pool:
        # A bounded window of requests in flight, written in order.
        pending = []
        it = iter(chunks)
        for c in it:
            pending.append(pool.submit(fetch, c))
            if len(pending) >= 2 * workers:
                break
        while pending:
            hs, res = pending.pop(0).result()
            nxt = next(it, None)
            if nxt is not None:
                pending.append(pool.submit(fetch, nxt))
            for h, hexraw in zip(hs, res):
                raw = bytes.fromhex(hexraw)
                out.write(struct.pack("<II", h, len(raw)))
                out.write(raw)
                total += len(raw)
            now = time.time()
            if now - last > 30:
                last = now
                print(f"stream_blocks: {hs[-1]}, {total / 1e6 / (now - t0):.1f} MB/s", file=sys.stderr)
    out.flush()
    print(f"stream_blocks: {lo}..{hi} done, {total / 1e6:.0f} MB in {time.time() - t0:.0f} s", file=sys.stderr)


if __name__ == "__main__":
    main()
