// Headless Chrome check of the built site: node web/test/browser.mjs <url> [<member-file-url> | --ops <txid:vout,...> | --pick <n>]
// Waits for step 1's status, then checks a .sbmember file fetched from <member-file-url>, or looks up
// outpoints through the page's own form (byte-range lookups), or presses "Pick a random UTXO" n times and
// checks each pick (it must be present, and its segment must be downloaded once, not again by Check).
import { spawn } from "node:child_process";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
const [url, memberUrl] = process.argv.slice(2);
// A fresh profile per run: a profile left locked by an earlier run made every lookup come back undefined.
const chrome = spawn("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  ["--headless=new", "--disable-gpu", "--remote-debugging-port=9333", "--user-data-dir=" + mkdtempSync(join(tmpdir(), "wm-chrome-")), "about:blank"], { stdio: "ignore" });
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
let ws;
for (let i = 0; i < 50 && !ws; i++) {
  await sleep(200);
  try { const t = await (await fetch("http://127.0.0.1:9333/json")).json(); const p = t.find((x) => x.type === "page"); if (p) ws = new WebSocket(p.webSocketDebuggerUrl); } catch {}
}
await new Promise((r) => (ws.onopen = r));
let id = 0; const wait = {};
ws.onmessage = (e) => { const m = JSON.parse(e.data); if (wait[m.id]) { wait[m.id](m); delete wait[m.id]; } };
const send = (method, params = {}) => new Promise((r) => { const i = ++id; wait[i] = r; ws.send(JSON.stringify({ id: i, method, params })); });
const ev = async (expr) => (await send("Runtime.evaluate", { expression: expr, awaitPromise: true, returnByValue: true })).result.result.value;
await send("Page.navigate", { url });
let st = "";
for (let i = 0; i < 100; i++) { await sleep(300); st = await ev("document.getElementById('seal-status')?.className + ' ' + document.getElementById('seal-status')?.textContent"); if (/ (ok|bad) /.test(" " + st + " ") || /status (ok|bad)/.test(st)) break; }
console.log("seal:", st);
console.log(await ev("[...document.querySelectorAll('#seal-out dt')].map(d => d.textContent + ': ' + d.nextSibling.textContent).join('\\n')"));
if (memberUrl === "--ops") {
  const ops = process.argv[4];
  await ev(`document.getElementById('op').value = ${JSON.stringify(ops)}; document.getElementById('op-btn').click()`);
  let m = "";
  for (let i = 0; i < 200; i++) { await sleep(300); m = await ev("document.getElementById('op-status').className + ' ' + document.getElementById('op-status').textContent"); if (/status (ok|bad)/.test(m)) break; }
  console.log("lookup:", m);
  console.log(await ev("[...document.querySelectorAll('#op-out .coin')].map(c => c.innerText.split('\\n').filter((_, i) => i % 2).slice(0, 3).join(' | ')).join('\\n')"));
  if (!/status ok/.test(m)) st = "lookup failed";
} else if (memberUrl === "--pick") {
  const n = +process.argv[4] || 5;
  const segs = "performance.getEntriesByType('resource').filter(e => /set(-972500)?\\.bin/.test(e.name)).length";
  let fails = 0;
  for (let k = 0; k < n; k++) {
    const before = await ev(segs), prev = await ev("document.getElementById('op').value");
    await ev("document.getElementById('pick-btn').click()");
    let op = prev;
    for (let i = 0; i < 200; i++) { await sleep(200); op = await ev("document.getElementById('pick-btn').disabled ? '' : document.getElementById('op').value"); if (op && op !== prev) break; if (/bad/.test(await ev("document.getElementById('op-status').className"))) break; }
    const t0 = Date.now();
    await ev("document.getElementById('op-btn').click()");
    let m = "";
    for (let i = 0; i < 200; i++) { await sleep(200); m = await ev("document.getElementById('op-status').className + ' ' + document.getElementById('op-status').textContent"); if (/status (ok|bad)/.test(m)) break; }
    const coin = await ev("[...document.querySelectorAll('#op-out .coin')].map(c => c.innerText.split('\\n').filter((_, i) => i % 2).slice(1, 3).join(' | ')).join('')");
    const fetched = (await ev(segs)) - before;
    const good = /1 unspent/.test(m) && fetched === 1;
    if (!good) fails++;
    console.log(`pick ${k + 1}: ${op} | ${coin} | segment downloads ${fetched} | check ${Date.now() - t0} ms | ${good ? "OK" : "FAIL: " + m}`);
  }
  if (fails) st = "pick failed";
} else if (memberUrl) {
  await ev(`fetch(${JSON.stringify(memberUrl)}).then(r => r.arrayBuffer()).then(checkMember)`);
  console.log("member:", await ev("document.getElementById('op-status').textContent"));
  console.log(await ev("[...document.querySelectorAll('#op-out .coin')].slice(0,1).map(c => c.innerText).join('')"));
}
chrome.kill();
process.exit(/status ok/.test(st) ? 0 : 1);
