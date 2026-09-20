# bolt

A linter, checker and language server for [Bend 2](https://github.com/bendlang/bend),
written in Bend, with a VS Code extension.

- `bolt` lints: comments on every def, unused names, the binder-vs-def trap,
  leftover holes, whitespace, double recursion under `Bool.pick`, and laws
  that reach every pure def. A `bolt.bend` at the project root says which
  rules, and how hard (off, warn, error), oxlint-style by group.
- `bolt check file..` runs Bend's checker and prints its errors in the same
  shape, `path:line:col: error: message`.
- `bolt lsp` is the language server: the checker's errors on open and save,
  bolt's findings as you type, hover, go-to-definition, symbols, completion,
  references, rename and semantic tokens.
- [editors/vscode](editors/vscode/) is the VS Code extension: highlighting,
  plus everything above through `bolt lsp`.

## Install

You need `bend` (`curl -fsSL https://bend-lang.com/install.sh | sh`):

```
bend 0x…/bolt/main.bend
bend 0x…/bolt/main.bend check a.bend
bend 0x…/bolt/main.bend lsp
```

`0x…` is written by the GitHub Release after it publishes `bolt/main.bend`
to the hub.

To build the native binary (clang 14+):

```
git clone https://github.com/Emerging-Patterns/bolt
cd bolt
./build.sh          # builds bin/bolt.bin and links ~/.local/bin/bolt
bolt                # lints every .bend file under the current directory
```

Or with nix:

```
nix profile install github:Emerging-Patterns/bolt   # bolt, with bend on its PATH
nix run github:Emerging-Patterns/bolt               # or just run it, here
```

The VS Code extension, from a checkout:

```
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bolt-0.3.0.vsix   # or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install it from the remote window, so it lands on the
machine where `bend` and `bolt` are. The extension finds `~/.local/bin/bolt`
(or `bolt` on PATH; `bend.server.path` overrides). After rebuilding bolt,
run `Bend: Restart Language Server`.

## Use

```
bend 0x…/bolt/main.bend                 every .bend file under the current directory
bend 0x…/bolt/main.bend a.bend b.bend   the files given
bend 0x…/bolt/main.bend check a.bend    the checker's errors, in the same shape
bend 0x…/bolt/main.bend lsp             the language server, over stdio
```

A native `bolt` (`./build.sh`) is the same words without the hub path.

Each finding is one line, `path:line:col: level: rule: message`, then
`clean` or the counts; the exit code is 1 when anything was an error.

A project sets its rules in a `bolt.bend` at its root, plain Bend a def a
setting; the nearest one above a file wins:

```
# every rule an error
def correctness() -> String:
  "error"
def style() -> String:
  "error"
# but width is advice here
def space() -> String:
  "warn"
```

The groups are `correctness` (`shadow`, `hole`, `pick`; error by default),
`suspicious` (`unused`), `style` (`doc`, `space`) and `laws` (`law`), the
rest warn by default. Every rule, and the config in full, is in
[bolt/README.md](bolt/README.md).
