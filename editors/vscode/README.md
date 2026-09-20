# bolt for VS Code

Bend 2 in VS Code: syntax highlighting for `.bend`, and through `bolt lsp`
(`bolt/lsp/` in this repo) the checker's errors on open and save, bolt's
findings as you type at the levels the project's `bolt.bend` sets, hover,
definition, completion, references, rename and semantic tokens.

Install `bolt` first (repo root: `bend bolt/main.bend -o bin/bolt.bin`, then
`ln -sfn "$PWD/bin/bolt.bin" ~/.local/bin/bolt`), then the extension from a
VSIX:

```
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bolt-0.3.0.vsix       # or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install the VSIX from the remote window, so it lands on the
machine where `bend` and `bolt` are. `bend.server.path` overrides where bolt
is; `Bend: Restart Language Server` picks up a rebuilt one.
