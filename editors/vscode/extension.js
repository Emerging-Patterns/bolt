// The VS Code client for Bend: starts bolt's language server (`bolt lsp`) on
// stdio for .bend files. All the language work is in the server (../../bolt/lsp).
const fs = require("fs");
const os = require("os");
const path = require("path");
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");

let client;

// The server runs `bend`, and bend's launcher runs `bun`: an extension host
// started from a desktop or over SSH often lacks the shell's PATH.
function serverEnv() {
  const home = os.homedir();
  const extra = [".local/bin", ".bend/bin", ".bun/bin", ".nix-profile/bin"].map((d) => path.join(home, d));
  return { ...process.env, PATH: [...extra, process.env.PATH ?? ""].join(path.delimiter) };
}

function serverPath() {
  const set = vscode.workspace.getConfiguration("bend").get("server.path");
  if (set) {
    return set.replace(/^~(?=$|\/)/, os.homedir());
  }
  const local = path.join(os.homedir(), ".local/bin/bolt");
  return fs.existsSync(local) ? local : "bolt";
}

async function start() {
  // `bolt lsp`: the bolt script runs the binary with --gpu off. No
  // `transport`: stdio is the default for a command, and naming it makes the
  // client append `--stdio`, which the binary refuses as an unknown option.
  const run = { command: serverPath(), args: ["lsp"], options: { env: serverEnv() } };
  client = new LanguageClient("bend", "Bend", { run, debug: run },
    { documentSelector: [{ scheme: "file", language: "bend" }] });
  await client.start();
}

async function activate(context) {
  context.subscriptions.push(vscode.commands.registerCommand("bend.restartServer", async () => {
    // a server that already died cannot be stopped; start a fresh one anyway
    try {
      if (client) {
        await client.stop();
      }
    } catch (e) {
      console.error("bend: stopping the old server failed", e);
    }
    await start();
  }));
  await start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
