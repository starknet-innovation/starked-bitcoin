// WEB-MEMBER page logic. Config (config.json): {"set": "<URL of the set file>", "index": "<URL of its
// segment index>"} for lookups by byte range from object storage (default), or {"member": "<base URL of
// chainproof serve-member>"} for a proof server.
const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const pending = {};
worker.onmessage = (e) => { const r = pending[e.data.op]; delete pending[e.data.op]; r && r(e.data); };
const call = (msg, transfer) => new Promise((res) => { pending[msg.op] = res; worker.postMessage(msg, transfer); });

let config = {};
const configReady = fetch("config.json").then((r) => (r.ok ? r.json() : {})).then((c) => { config = c; }).catch(() => {});
let indexLoaded = null; // a promise, once per verified seal

const SAT = 100_000_000n;
const btc = (sat) => {
  const s = BigInt(sat);
  return `${(s / SAT).toLocaleString("en-US")}.${(s % SAT).toString().padStart(8, "0")} BTC`;
};
const num = (n) => Number(n).toLocaleString("en-US");

function setStatus(el, cls, text) { el.className = "status " + cls; el.textContent = text; }

function rows(dl, pairs) {
  dl.replaceChildren();
  for (const [k, v, mono] of pairs) {
    const dt = document.createElement("dt"); dt.textContent = k;
    const dd = document.createElement("dd"); dd.textContent = v; if (mono) dd.className = "mono";
    dl.append(dt, dd);
  }
  dl.hidden = false;
}

async function fetchBytes(url) {
  const r = await fetch(url);
  if (!r.ok) throw new Error(`${url}: HTTP ${r.status}`);
  return r.arrayBuffer();
}

$("seal-btn").onclick = async () => {
  const st = $("seal-status");
  $("seal-btn").disabled = true;
  try {
    setStatus(st, "run", "Downloading the proof files…");
    const [chain, seal] = await Promise.all([fetchBytes("data/chain.sbchain"), fetchBytes("data/seal.bin")]);
    setStatus(st, "run", "Verifying in your browser…");
    const m = await call({ op: "seal", chain, seal }, [chain, seal]);
    if (m.error) throw new Error(m.error);
    const r = m.result;
    if (!r.ok) { setStatus(st, "bad", `REJECTED: ${r.error}`); return; }
    setStatus(st, "ok", `Verified in ${(r.ms / 1000).toFixed(1)} s`);
    rows($("seal-out"), [
      ["Header chain", `genesis to height ${num(r.tip_height)} (${num(r.headers)} headers)`],
      ["Tip hash", r.tip_hash, true],
      ["Chainwork", r.chainwork, true],
      ["Blocks checked", `${num(r.from)} to ${num(r.to)}`],
      ["Start set", `after block ${num(r.from - 1)}: Bitcoin Core's assumeUTXO set (hash_serialized ${r.start_hash.slice(0, 16)}…)`],
      ["Coin set after " + num(r.to), `${num(r.coins)} coins, ${btc(r.amount)}`],
      ["Merkle root", r.merkle_root, true],
      ["hash_serialized", r.hash_serialized, true],
    ]);
    indexLoaded = null;
    $("op-btn").disabled = false;
    $("pick-btn").disabled = false;
    $("file").disabled = false;
  } catch (err) {
    setStatus(st, "bad", String(err.message || err));
  } finally {
    $("seal-btn").disabled = false;
  }
};

function showCoins(r) {
  const out = $("op-out");
  out.replaceChildren();
  for (const c of r.coins) {
    const div = document.createElement("div"); div.className = "coin";
    const dl = document.createElement("dl");
    const pairs = [["Outpoint", c.outpoint, true]];
    if (c.present) {
      pairs.push(["Status", "UNSPENT after block 972,500"], ["Amount", btc(c.amount)],
        ["Created at height", num(c.height) + (c.coinbase ? " (coinbase)" : "")], ["scriptPubKey", c.script, true]);
    } else pairs.push(["Status", "NOT in the set after block 972,500 (spent, or never existed)"]);
    pairs.push(["Merkle path", `${c.path} steps, checked against the seal's root`]);
    rows(dl, pairs);
    div.append(dl);
    out.append(div);
  }
}

function report(results) {
  const st = $("op-status");
  const bad = results.find((r) => !r.ok);
  if (bad) {
    const why = bad.error === "NotBracketed" ? "NotBracketed (no proof of absence for this outpoint)" : bad.error;
    setStatus(st, "bad", `REJECTED: ${why}`); $("op-out").replaceChildren(); return;
  }
  const coins = results.flatMap((r) => r.coins);
  const n = coins.filter((c) => c.present).length;
  setStatus(st, "ok", `${coins.length} proof(s) verified: ${n} unspent, ${coins.length - n} absent`);
  showCoins({ coins });
}

async function checkMember(bytes) {
  setStatus($("op-status"), "run", "Checking the path against the seal's root…");
  const m = await call({ op: "member", bytes }, [bytes]);
  if (m.error) throw new Error(m.error);
  report([m.result]);
}

async function wasmCall(msg, transfer) {
  const m = await call(msg, transfer);
  if (m.error) throw new Error(m.error);
  return m.result;
}

// Lookups by byte range: the segment index once (its roots must fold to the seal's root), then one
// segment (~2 MB) per outpoint; the proof is built and checked in the worker.
function ensureIndex(st) {
  config.set ||= "data/set.bin";
  config.index ||= "data/set.segindex";
  if (!indexLoaded) {
    indexLoaded = (async () => {
      setStatus(st, "run", "Downloading the segment index (0.5 MB)…");
      const bytes = await fetchBytes(config.index);
      const r = await wasmCall({ op: "index", bytes }, [bytes]);
      if (!r.ok) throw new Error(`segment index rejected: ${r.error}`);
      return r;
    })();
    indexLoaded.catch(() => { indexLoaded = null; });
  }
  return indexLoaded;
}

// The last segment downloaded, kept so that checking a randomly picked coin does not fetch it again.
// Untrusted like any download: the worker hashes it against the seal's root on every check.
let segCache = null;
async function fetchSegment(st, loc) {
  if (segCache && segCache.seg === loc.seg) return segCache.bytes.slice(0);
  setStatus(st, "run", `Downloading segment ${loc.seg.toLocaleString("en-US")} (${((loc.end - loc.start) / 1e6).toFixed(1)} MB)…`);
  const r = await fetch(config.set, { headers: { Range: `bytes=${loc.start}-${loc.end - 1}` } });
  if (r.status !== 206) throw new Error(`${config.set}: expected 206 Partial Content, got HTTP ${r.status}`);
  const bytes = await r.arrayBuffer();
  if (bytes.byteLength !== loc.end - loc.start) throw new Error("segment: wrong length");
  segCache = { seg: loc.seg, bytes: bytes.slice(0) };
  return bytes;
}

async function checkByRange(ops) {
  const st = $("op-status");
  await ensureIndex(st);
  const results = [];
  for (const op of ops) {
    const loc = await wasmCall({ op: "locate", outpoint: op });
    if (!loc.ok) { results.push(loc); break; }
    const bytes = await fetchSegment(st, loc);
    setStatus(st, "run", "Hashing the segment and checking the path against the seal's root…");
    results.push(await wasmCall({ op: "segment", outpoint: op, seg: loc.seg, bytes }, [bytes]));
  }
  report(results);
}

$("op-btn").onclick = async () => {
  const st = $("op-status");
  const ops = $("op").value.split(/[\s,]+/).filter(Boolean).map((o) => o.toLowerCase());
  if (!ops.length || !ops.every((o) => /^[0-9a-f]{64}:\d+$/.test(o))) {
    setStatus(st, "bad", "Use txid:vout (64 hex characters, a colon, the output index)."); return;
  }
  if (ops.length > 16) { setStatus(st, "bad", "At most 16 outpoints at a time."); return; }
  $("op-btn").disabled = true;
  try {
    await configReady;
    if (config.member) {
      setStatus(st, "run", "Fetching the Merkle path…");
      await checkMember(await fetchBytes(`${config.member}/member?op=${ops.join(",")}`));
    } else {
      await checkByRange(ops);
    }
  } catch (err) {
    setStatus(st, "bad", String(err.message || err));
  } finally {
    $("op-btn").disabled = false;
  }
};
// A random coin of the set: a random byte of the set file picks a segment (segments are picked in
// proportion to their size), then a random record of that segment. Only fills the box; Check proves it.
const rand32 = () => crypto.getRandomValues(new Uint32Array(1))[0];
$("pick-btn").onclick = async () => {
  const st = $("op-status");
  $("pick-btn").disabled = true;
  try {
    await configReady;
    if (config.member) throw new Error("Random picks need the set file (byte-range mode).");
    await ensureIndex(st);
    const loc = await wasmCall({ op: "pickseg", r: rand32() });
    if (!loc.ok) throw new Error(loc.error);
    const bytes = await fetchSegment(st, loc);
    const p = await wasmCall({ op: "pickin", bytes, r: rand32() }, [bytes]);
    if (!p.ok) throw new Error(p.error);
    $("op").value = p.outpoint;
    $("op-out").replaceChildren();
    setStatus(st, "", "");
  } catch (err) {
    setStatus(st, "bad", String(err.message || err));
  } finally {
    $("pick-btn").disabled = $("op-btn").disabled;
  }
};
$("op").addEventListener("keydown", (e) => { if (e.key === "Enter" && !$("op-btn").disabled) $("op-btn").click(); });

$("file").onchange = async (e) => {
  const f = e.target.files[0];
  if (!f) return;
  try { await checkMember(await f.arrayBuffer()); } catch (err) { setStatus($("op-status"), "bad", String(err.message || err)); }
};

// Verify on load: ~1.6 MB and under a second; the button re-runs it.
$("seal-btn").click();
