// Static server with HTTP Range and CORS, like the object store the site uses (tests only):
// node web/test/serve.mjs <dir> <port> [<url-path>=<file>...]
import { createServer } from "node:http";
import { createReadStream, statSync } from "node:fs";
import { join, extname, normalize } from "node:path";
const [dir, port, ...maps] = process.argv.slice(2);
const mapped = Object.fromEntries(maps.map((m) => m.split("=")));
const types = { ".html": "text/html", ".js": "text/javascript", ".wasm": "application/wasm", ".json": "application/json" };
createServer((req, res) => {
  const path = decodeURIComponent(new URL(req.url, "http://x").pathname);
  const file = mapped[path] ?? join(dir, normalize(path === "/" ? "/index.html" : path));
  let st;
  try { st = statSync(file); } catch { res.writeHead(404); return res.end(); }
  const h = { "access-control-allow-origin": "*", "access-control-expose-headers": "content-range", "accept-ranges": "bytes",
    "content-type": types[extname(file)] ?? "application/octet-stream" };
  if (req.method === "OPTIONS") { res.writeHead(204, { ...h, "access-control-allow-headers": "range" }); return res.end(); }
  const m = /^bytes=(\d+)-(\d+)$/.exec(req.headers.range ?? "");
  if (m) {
    const a = +m[1], b = Math.min(+m[2], st.size - 1);
    res.writeHead(206, { ...h, "content-length": b - a + 1, "content-range": `bytes ${a}-${b}/${st.size}` });
    return createReadStream(file, { start: a, end: b }).pipe(res);
  }
  res.writeHead(200, { ...h, "content-length": st.size });
  createReadStream(file).pipe(res);
}).listen(+port, "127.0.0.1");
