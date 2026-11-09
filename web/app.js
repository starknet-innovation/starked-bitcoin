// WEB-MEMBER page logic. Config (config.json, optional): {"member": "<base URL of serve-member>"};
// default: the same origin's /member.
const $ = (id) => document.getElementById(id);
const worker = new Worker("worker.js");
const pending = {};
worker.onmessage = (e) => { const r = pending[e.data.op]; delete pending[e.data.op]; r && r(e.data); };
const call = (msg, transfer) => new Promise((res) => { pending[msg.op] = res; worker.postMessage(msg, transfer); });

let memberBase = "";
fetch("config.json").then((r) => (r.ok ? r.json() : {})).then((c) => { memberBase = c.member || ""; }).catch(() => {});

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
    $("op-btn").disabled = false;
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

async function checkMember(bytes) {
  const st = $("op-status");
  setStatus(st, "run", "Checking the path against the seal's root…");
  const m = await call({ op: "member", bytes }, [bytes]);
  if (m.error) throw new Error(m.error);
  const r = m.result;
  if (!r.ok) { setStatus(st, "bad", `REJECTED: ${r.error}`); $("op-out").replaceChildren(); return; }
  const n = r.coins.filter((c) => c.present).length;
  setStatus(st, "ok", `${r.coins.length} proof(s) verified: ${n} unspent, ${r.coins.length - n} absent`);
  showCoins(r);
}

$("op-btn").onclick = async () => {
  const st = $("op-status");
  const ops = $("op").value.split(/[\s,]+/).filter(Boolean);
  if (!ops.length || !ops.every((o) => /^[0-9a-fA-F]{64}:\d+$/.test(o))) {
    setStatus(st, "bad", "Use txid:vout (64 hex characters, a colon, the output index)."); return;
  }
  $("op-btn").disabled = true;
  try {
    setStatus(st, "run", "Fetching the Merkle path…");
    await checkMember(await fetchBytes(`${memberBase}/member?op=${ops.join(",").toLowerCase()}`));
  } catch (err) {
    setStatus(st, "bad", String(err.message || err));
  } finally {
    $("op-btn").disabled = false;
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
