#!/usr/bin/env python3
"""Chain survey driver (docs/design/chain-survey.md): feeds every block and its undo stream to the
`survey` binary and appends its CSV lines, one file per worker. Runs on the node.

Usage (on the node; the RPC cookie arrives on stdin and is kept in memory only):
    sudo -n cat /data/bitcoin/.cookie | nice -n 19 ionice -c3 python3 -I survey_driver.py \
        --bin ./survey --out out --to 971296 [--from 0] [--workers 3] [--chunk 500] [--stride 1]

Heights [from, to] are cut into chunks; chunk c goes to worker c % workers. Restarting skips the
heights already in out/w*.csv (resumable). `--stride S` does only heights divisible by S (a
sample of the whole range first; the full pass then skips them). Progress goes to stdout (redirect it to a log).

Per height: getblockhash, getblock 0 (raw block, checked against the hash), and for blocks with
more than one transaction getblock 3, whose `prevout`s give the undo stream exactly as
scripts/fetch_undo.py builds it (version 0x01; per non-coinbase input LE32(2*height + coinbase),
LE64 satoshis, CompactSize length, scriptPubKey). The verbosity-3 JSON is scanned with a regex rather
than parsed (memory); the survey binary checks the record count against the block's inputs.
"""
import base64, hashlib, http.client, json, os, re, struct, subprocess, sys, time
from multiprocessing import Process

PREVOUT = re.compile(rb'"prevout":\{"generated":(true|false),"height":(\d+),"value":(\d+)(?:\.(\d+))?,"scriptPubKey":\{"asm":"[^"]*",(?:"desc":"[^"]*",)?"hex":"([0-9a-f]*)"')


class Rpc:
    def __init__(self, cookie):
        self.auth = "Basic " + base64.b64encode(cookie.encode()).decode()
        self.conn = None

    def raw(self, body):
        for attempt in range(20):
            try:
                if self.conn is None:
                    self.conn = http.client.HTTPConnection("127.0.0.1", 8332, timeout=600)
                self.conn.request("POST", "/", body=body, headers={"Authorization": self.auth, "Content-Type": "application/json"})
                r = self.conn.getresponse()
                data = r.read()
                if r.status == 401:
                    raise SystemExit("RPC 401 (cookie changed? restart the driver)")
                return data
            except (OSError, http.client.HTTPException) as e:
                self.conn = None
                print(f"rpc retry {attempt}: {e!r}", flush=True)
                time.sleep(min(60, 2 ** attempt))
        raise SystemExit("RPC unreachable")

    def call(self, method, *params):
        body = json.dumps({"jsonrpc": "1.0", "id": "survey", "method": method, "params": list(params)}).encode()
        resp = json.loads(self.raw(body))
        if resp.get("error"):
            raise RuntimeError(f"{method}: {resp['error']}")
        return resp["result"]

    def batch(self, calls):
        body = json.dumps([{"jsonrpc": "1.0", "id": i, "method": m, "params": list(p)} for i, (m, p) in enumerate(calls)]).encode()
        out = sorted(json.loads(self.raw(body)), key=lambda x: x["id"])
        for x in out:
            if x.get("error"):
                raise RuntimeError(f"batch: {x['error']}")
        return [x["result"] for x in out]


def compact_size(n):
    if n < 0xfd:
        return bytes([n])
    if n <= 0xffff:
        return b"\xfd" + n.to_bytes(2, "little")
    if n <= 0xffffffff:
        return b"\xfe" + n.to_bytes(4, "little")
    return b"\xff" + n.to_bytes(8, "little")


def read_varint(b, i):
    x = b[i]
    if x < 0xfd:
        return x
    return int.from_bytes(b[i + 1:i + 1 + {0xfd: 2, 0xfe: 4, 0xff: 8}[x]], "little")


def undo_stream(rpc, h):
    """The undo stream from getblock <h> 3, scanned (not parsed)."""
    body = json.dumps({"jsonrpc": "1.0", "id": "survey", "method": "getblock", "params": [h, 3]}).encode()
    data = rpc.raw(body)
    if not data.startswith(b'{"result":{') or not data.rstrip().endswith(b'"error":null,"id":"survey"}'):
        raise RuntimeError(f"getblock 3: unexpected response {data[:200]!r}...{data[-200:]!r}")
    out = bytearray([1])
    for m in PREVOUT.finditer(data):
        gen, height, whole, frac, script = m.groups()
        frac = (frac or b"").ljust(8, b"0")
        if len(frac) != 8:
            raise RuntimeError(f"value precision {whole}.{frac}")
        sats = int(whole) * 100_000_000 + int(frac)
        s = bytes.fromhex(script.decode())
        out += (2 * int(height) + (1 if gen == b"true" else 0)).to_bytes(4, "little")
        out += sats.to_bytes(8, "little")
        out += compact_size(len(s)) + s
    return bytes(out)


def done_heights(out_dir):
    done = set()
    for f in os.listdir(out_dir):
        if f.startswith("w") and f.endswith(".csv"):
            with open(os.path.join(out_dir, f)) as fh:
                for line in fh:
                    if line.endswith("\n") and "," in line:
                        done.add(int(line.split(",", 1)[0]))
    return done


def worker(k, args, cookie, done):
    rpc = Rpc(cookie)
    surv = subprocess.Popen([args["bin"]], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    path = os.path.join(args["out"], f"w{k}.csv")
    # Drop a partial last line from an interrupted run.
    if os.path.exists(path):
        with open(path, "rb+") as fh:
            data = fh.read()
            if data and not data.endswith(b"\n"):
                fh.truncate(data.rfind(b"\n") + 1)
    fh = open(path, "a")
    lo, hi, chunk, W = args["from"], args["to"], args["chunk"], args["workers"]
    t0 = time.time()
    n = 0
    nbytes = 0
    for c, start in enumerate(range(lo, hi + 1, chunk)):
        if c % W != k:
            continue
        todo = [h for h in range(start, min(start + chunk, hi + 1)) if h not in done and h % args["stride"] == 0]
        if not todo:
            continue
        hashes = rpc.batch([("getblockhash", (h,)) for h in todo])
        for h, bh in zip(todo, hashes):
            raw = bytes.fromhex(rpc.call("getblock", bh, 0))
            if hashlib.sha256(hashlib.sha256(raw[:80]).digest()).digest()[::-1].hex() != bh:
                raise SystemExit(f"{h}: raw header does not hash to {bh}")
            ntx = read_varint(raw, 80)
            undo = undo_stream(rpc, bh) if ntx > 1 else b"\x01"
            surv.stdin.write(struct.pack("<II", h, len(raw)) + raw + struct.pack("<I", len(undo)) + undo)
            surv.stdin.flush()
            line = surv.stdout.readline().decode()
            if not line.startswith(f"{h},"):
                raise SystemExit(f"{h}: survey said {line!r}")
            fh.write(line)
            fh.flush()
            n += 1
            nbytes += len(raw)
        dt = time.time() - t0
        print(f"w{k} {time.strftime('%H:%M:%S')} chunk {start}-{start + chunk - 1} done; {n} blocks, {nbytes / 1e6:.0f} MB in {dt:.0f} s ({n / dt:.2f} blk/s, {nbytes / 1e6 / dt:.2f} MB/s)", flush=True)
    surv.stdin.close()
    surv.wait()
    print(f"w{k} finished", flush=True)


def main():
    argv = sys.argv[1:]
    args = {"bin": "./survey", "out": "out", "from": 0, "to": None, "workers": 3, "chunk": 500, "stride": 1}
    i = 0
    while i < len(argv):
        key = argv[i].lstrip("-")
        if key not in args:
            raise SystemExit(f"unknown option {argv[i]}")
        args[key] = argv[i + 1] if key in ("bin", "out") else int(argv[i + 1])
        i += 2
    if args["to"] is None:
        raise SystemExit("--to required")
    cookie = sys.stdin.readline().strip()
    if ":" not in cookie:
        raise SystemExit("expected the RPC cookie on stdin")
    os.makedirs(args["out"], exist_ok=True)
    done = done_heights(args["out"])
    print(f"start {time.strftime('%F %T')}: heights {args['from']}..{args['to']}, {len(done)} already done, {args['workers']} workers", flush=True)
    ps = [Process(target=worker, args=(k, args, cookie, done)) for k in range(args["workers"])]
    for p in ps:
        p.start()
    for p in ps:
        p.join()
    print(f"all done {time.strftime('%F %T')}", flush=True)


if __name__ == "__main__":
    main()
