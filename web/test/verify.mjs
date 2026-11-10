// Node check of webverify.wasm: node web/test/verify.mjs <wasm> <chain.sbchain> <seal.bin> [member.sbmember | --range <set.segindex> <set.bin> <txid:vout>...]
import { readFileSync, openSync, readSync } from "node:fs";
const [wasmPath, chainPath, sealPath, memberPath, ...rest] = process.argv.slice(2);
let inst;
const log = [];
const mem = () => inst.exports.memory.buffer;
const wasi = new Proxy({
  fd_write(fd, iovs, n, nw) { const dv = new DataView(mem()); let t = 0;
    for (let i = 0; i < n; i++) { const p = dv.getUint32(iovs + 8 * i, true), l = dv.getUint32(iovs + 8 * i + 4, true);
      log.push(Buffer.from(mem(), p, l).toString()); t += l; }
    dv.setUint32(nw, t, true); return 0; },
  random_get(p, l) { crypto.getRandomValues(new Uint8Array(mem(), p, l)); return 0; },
  clock_time_get(id, prec, out) { new DataView(mem()).setBigUint64(out, process.hrtime.bigint(), true); return 0; },
  proc_exit(c) { throw new Error("exit " + c); },
}, { get: (t, k) => (k in t ? t[k] : () => 52) });
({ instance: inst } = await WebAssembly.instantiate(readFileSync(wasmPath), { wasi_snapshot_preview1: wasi }));
const w = inst.exports;
if (w._initialize) w._initialize();
const put = (b) => { const p = w.wv_alloc(b.length); new Uint8Array(mem()).set(b, p); return [p, b.length]; };
const out = (p) => JSON.parse(Buffer.from(mem(), p, w.result_len()).toString());
let t = performance.now();
const r = out(w.verify_seal(...put(readFileSync(chainPath)), ...put(readFileSync(sealPath))));
console.log(JSON.stringify(r), `${Math.round(performance.now() - t)} ms`);
if (log.length) console.error(log.join(""));
const str = (x) => Buffer.from(x);
if (memberPath === "--range") {
  // As the page does: the index once, then per outpoint its segment by byte range.
  const [ixPath, setPath, ...ops] = rest;
  console.log(JSON.stringify(out(w.load_index(...put(readFileSync(ixPath))))));
  const fd = openSync(setPath, "r");
  let bad = 0;
  for (const op of ops) {
    const loc = out(w.locate(...put(str(op))));
    if (!loc.ok) { console.log(op, JSON.stringify(loc)); bad++; continue; }
    const seg = Buffer.alloc(loc.end - loc.start);
    readSync(fd, seg, 0, seg.length, loc.start);
    t = performance.now();
    const r = out(w.verify_segment(...put(str(op)), loc.seg, ...put(seg)));
    console.log(`seg ${loc.seg} (${seg.length} B):`, JSON.stringify(r), `${Math.round(performance.now() - t)} ms`);
    if (!r.ok) bad++;
  }
  if (bad) process.exit(2);
} else if (memberPath) {
  t = performance.now();
  console.log(JSON.stringify(out(w.verify_member(...put(readFileSync(memberPath))))), `${Math.round(performance.now() - t)} ms`);
}
process.exit(r.ok ? 0 : 1);
