// Headless Chrome check of the built site: node web/test/browser.mjs <url> [<member-file-url> | --ops <txid:vout,...>]
// Waits for step 1's status, then checks a .sbmember file fetched from <member-file-url>, or looks up
// outpoints through the page's own form (byte-range lookups).
import { spawn } from "node:child_process";
const [url, memberUrl] = process.argv.slice(2);
const chrome = spawn("/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
  ["--headless=new", "--disable-gpu", "--remote-debugging-port=9333", "--user-data-dir=" + process.env.TMPDIR + "/wm-chrome", "about:blank"], { stdio: "ignore" });
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
} else if (memberUrl) {
  await ev(`fetch(${JSON.stringify(memberUrl)}).then(r => r.arrayBuffer()).then(checkMember)`);
  console.log("member:", await ev("document.getElementById('op-status').textContent"));
  console.log(await ev("[...document.querySelectorAll('#op-out .coin')].slice(0,1).map(c => c.innerText).join('')"));
}
chrome.kill();
process.exit(/status ok/.test(st) ? 0 : 1);
