# Bend for VS Code

Syntax highlighting for `.bend`, and the checker's errors on open and save
through bend-lsp (`lsp/` in this repo).

```
./build.sh                                   # repo root: builds bin/bend-lsp, links ~/.local/bin/bend-lsp
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bend-lsp-0.1.1.vsix   # or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install the VSIX from the remote window, so it lands on the
machine where `bend` and `bend-lsp` are. `bend.server.path` overrides where the
server is; `Bend: Restart Language Server` picks up a rebuilt one.
