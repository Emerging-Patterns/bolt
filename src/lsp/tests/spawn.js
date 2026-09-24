// lsp over real stdio, launched the way an editor launches it: spawned by
// node, whose child stdio are sockets, not pipes (a pipe-only test once hid
// that the server could not open /dev/stdin). Usage: node spawn.js <bolt.bin>
const { spawn } = require("child_process");
const path = require("path");

const server = spawn(process.argv[2], ["lsp", "--gpu", "off"],
  { stdio: ["pipe", "pipe", "inherit"] });
let buf = Buffer.alloc(0);
const waiting = [];
server.stdout.on("data", (chunk) => {
  buf = Buffer.concat([buf, chunk]);
  for (;;) {
    const head = buf.indexOf("\r\n\r\n");
    if (head < 0) return;
    const len = Number(/Content-Length: (\d+)/.exec(buf.subarray(0, head).toString())[1]);
    if (buf.length < head + 4 + len) return;
    const msg = JSON.parse(buf.subarray(head + 4, head + 4 + len).toString());
    buf = buf.subarray(head + 4 + len);
    waiting.shift()(msg);
  }
});
const send = (o) => {
  const body = Buffer.from(JSON.stringify(o));
  server.stdin.write(Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`), body]));
};
const recv = () => new Promise((ok) => waiting.push(ok));
const fail = (why) => { console.error("FAIL: " + why); server.kill(); process.exit(1); };
setTimeout(() => fail("timed out"), 20000);

(async () => {
  const fixture = path.join(__dirname, "..", "fixtures", "mistyped.bend");
  const uri = "file://" + fixture;
  send({ jsonrpc: "2.0", id: 1, method: "initialize", params: { note: "é€😀" } });
  const init = await recv();
  if (!init.result.capabilities.hoverProvider) fail("no hover capability");
  send({ jsonrpc: "2.0", method: "textDocument/didOpen",
    params: { textDocument: { uri, text: require("fs").readFileSync(fixture, "utf8") } } });
  const diags = (await recv()).params.diagnostics;
  if (diags.length !== 1 || diags[0].range.start.line !== 4) fail("diagnostics: " + JSON.stringify(diags));
  send({ jsonrpc: "2.0", id: 2, method: "textDocument/hover",
    params: { textDocument: { uri }, position: { line: 3, character: 5 } } });
  const hover = (await recv()).result;
  if (!hover || !hover.contents.value.includes("def f(xx: U32) -> String:")) fail("hover: " + JSON.stringify(hover));
  send({ jsonrpc: "2.0", id: 3, method: "shutdown" });
  await recv();
  send({ jsonrpc: "2.0", method: "exit" });
  server.on("exit", (code) => { console.log(code === 0 ? "ok" : "FAIL: exit " + code); process.exit(code === 0 ? 0 : 1); });
})();
