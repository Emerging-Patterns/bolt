# bolt for VS Code

Bend 2 in VS Code: syntax highlighting for `.bend`, and through `bolt lsp`
(`src/lsp/` in this repo) the checker's errors on open and save, bolt's
findings as you type at the levels the project's `bolt.bend` sets, hover,
definition, completion, references, rename and semantic tokens.

Install `bolt` first. Use `nix profile install github:Emerging-Patterns/bolt`,
or, with any installed Bend 2 (no nix or ez needed), run
`bend main.bend -o bin/bolt.bin` at the repo root (see the root
README's Install). Then install the extension from a VSIX:

```
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bolt-1.10.0.vsix       # x-release-please-version or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install the VSIX from the remote window, so it lands on the
machine where `bend` and `bolt` are. `Bend: Restart Language Server` picks up
a rebuilt one.

## Where it looks for bolt

`locate.js`, in this order, and no symlink is part of it:

1. `bend.server.path`, when the user set it. A leading `~` is their home. If
   it names nothing runnable the extension says so and stops, rather than
   quietly searching on -- a setting that is being ignored is worse than an
   error.
2. `bolt` on the PATH, with `~/.local/bin`, `~/.bend/bin`, `~/.bun/bin` and
   `~/.nix-profile/bin` put in front of it. An extension host started from a
   desktop or over SSH often has none of the shell's PATH, and the server
   runs `bend`, whose launcher runs `bun`, so the same list is the PATH the
   server is started with. A `nix profile install` is found here.
3. `bin/bolt.bin` two levels above the extension, which is a checkout the
   extension is being run out of with nothing installed.

Nothing found is an error message naming every directory it looked in and the
checkout binary it looked for. `tests/locate.js`, off the repo root, drives
all of this with a made-up home and PATH and then starts a real session on
what it resolved; `tests/bare.bend` runs it in the gate.
