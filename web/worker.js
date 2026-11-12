// Runs webverify.wasm off the main thread. Messages in: {op:"seal", chain, seal}, {op:"member", bytes},
// {op:"index", bytes}, {op:"locate", outpoint}, {op:"segment", outpoint, seg, bytes},
// {op:"pickseg", r}, {op:"pickin", bytes, r}; out: {op, result}
// with the wasm's JSON result, or {op, error}.
let wasm = null;
const log = [];

// webverify.wasm is built for wasm32-wasi only for its C library; it reads no files. Every WASI call
// is a stub, except fd_write (debug prints go to the console) and random_get.
function wasiImports(memory) {
  const u8 = () => new Uint8Array(memory().buffer);
  const dv = () => new DataView(memory().buffer);
  const base = {
    fd_write(fd, iovs, n, nwritten) {
      let total = 0;
      for (let i = 0; i < n; i++) {
        const p = dv().getUint32(iovs + 8 * i, true), l = dv().getUint32(iovs + 8 * i + 4, true);
        log.push(new TextDecoder().decode(u8().subarray(p, p + l)));
        total += l;
      }
      dv().setUint32(nwritten, total, true);
      return 0;
    },
    random_get(p, l) { crypto.getRandomValues(u8().subarray(p, p + l)); return 0; },
    clock_time_get(id, prec, out) { dv().setBigUint64(out, BigInt(Math.round(performance.now() * 1e6)), true); return 0; },
    proc_exit(code) { throw new Error("wasm exited " + code); },
  };
  return new Proxy(base, { get: (t, k) => (k in t ? t[k] : () => 52 /* ENOSYS */) });
}

async function load() {
  if (wasm) return wasm;
  let inst;
  const imports = { wasi_snapshot_preview1: wasiImports(() => inst.exports.memory) };
  const res = await WebAssembly.instantiateStreaming(fetch("webverify.wasm"), imports);
  inst = res.instance;
  if (inst.exports._initialize) inst.exports._initialize();
  wasm = inst.exports;
  return wasm;
}

function put(w, buf) {
  const bytes = new Uint8Array(buf);
  const p = w.wv_alloc(bytes.length);
  if (!p) throw new Error("out of memory");
  new Uint8Array(w.memory.buffer).set(bytes, p);
  return [p, bytes.length];
}

function json(w, p) {
  return JSON.parse(new TextDecoder().decode(new Uint8Array(w.memory.buffer, p, w.result_len())));
}

onmessage = async (e) => {
  const { op } = e.data;
  try {
    const w = await load();
    const t0 = performance.now();
    let result;
    if (op === "seal") {
      const [cp, cl] = put(w, e.data.chain);
      const [sp, sl] = put(w, e.data.seal);
      result = json(w, w.verify_seal(cp, cl, sp, sl));
      w.wv_free(cp, cl);
      w.wv_free(sp, sl);
    } else if (op === "member") {
      const [mp, ml] = put(w, e.data.bytes);
      result = json(w, w.verify_member(mp, ml));
      w.wv_free(mp, ml);
    } else if (op === "index") {
      const [ip, il] = put(w, e.data.bytes);
      result = json(w, w.load_index(ip, il));
      w.wv_free(ip, il);
    } else if (op === "locate") {
      const [op_p, op_l] = put(w, new TextEncoder().encode(e.data.outpoint));
      result = json(w, w.locate(op_p, op_l));
      w.wv_free(op_p, op_l);
    } else if (op === "pickseg") {
      result = json(w, w.pick_segment(e.data.r >>> 0));
    } else if (op === "pickin") {
      const [sp, sl] = put(w, e.data.bytes);
      result = json(w, w.pick_in_segment(sp, sl, e.data.r >>> 0));
      w.wv_free(sp, sl);
    } else if (op === "segment") {
      const [op_p, op_l] = put(w, new TextEncoder().encode(e.data.outpoint));
      const [sp, sl] = put(w, e.data.bytes);
      result = json(w, w.verify_segment(op_p, op_l, e.data.seg, sp, sl));
      w.wv_free(op_p, op_l);
      w.wv_free(sp, sl);
    } else throw new Error("unknown op " + op);
    result.ms = Math.round(performance.now() - t0);
    if (log.length) console.debug(log.splice(0).join(""));
    postMessage({ op, result });
  } catch (err) {
    postMessage({ op, error: String(err) });
  }
};
