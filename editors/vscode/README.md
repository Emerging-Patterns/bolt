# Bend for VS Code

Syntax highlighting for `.bend`, and through `bolt lsp` (`bolt/lsp/` in this
repo): the checker's errors on open and save, bolt's findings as you type at
the levels the project's `bolt.bend` sets, hover, definition, completion,
references, rename and semantic tokens.

```
./build.sh                                   # repo root: builds bin/bolt.bin, links ~/.local/bin/bolt
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bolt-0.3.0.vsix       # or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install the VSIX from the remote window, so it lands on the
machine where `bend` and `bolt` are. `bend.server.path` overrides where bolt
is; `Bend: Restart Language Server` picks up a rebuilt one.
