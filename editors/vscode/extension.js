// The VS Code client for Bend: starts bolt's language server (`bolt lsp`) on
// stdio for .bend files. All the language work is in the server (../../src/lsp),
// and finding the binary is in locate.js, which knows nothing of vscode so a
// test can drive it (tests/locate.js).
const os = require("os");
const vscode = require("vscode");
const { LanguageClient } = require("vscode-languageclient/node");
const { locate, serverEnv } = require("./locate.js");

let client;

async function start() {
  // `bolt lsp --gpu off`: the server stays on the cores, where this work is
  // 2-5x faster than on the GPU (src/lsp/bench); bend's runtime takes
  // `--gpu off` out of the line before the program reads it. No `transport`:
  // stdio is the default for a command, and naming it would only make the
  // client append a `--stdio` the server has no use for.
  const setting = vscode.workspace.getConfiguration("bend").get("server.path");
  const run = {
    command: locate({ setting }),
    args: ["lsp", "--gpu", "off"],
    options: { env: serverEnv(process.env, os.homedir()) },
  };
  client = new LanguageClient("bend", "Bend", { run, debug: run },
    { documentSelector: [{ scheme: "file", language: "bend" }] });
  await client.start();
}

// start, and put a bolt that is missing or wrongly configured in front of the
// user rather than in a log they have no reason to open: locate's message
// names every path it tried.
async function launch() {
  try {
    await start();
  } catch (e) {
    vscode.window.showErrorMessage("bend: " + e.message);
  }
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
    await launch();
  }));
  await launch();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
