# bolt

A linter, checker and language server for [Bend 2](https://github.com/bendlang/bend),
written in Bend, with a VS Code extension.

- `bolt` lints: comments on every def, unused names, the binder-vs-def trap,
  leftover holes, whitespace, double recursion under `Bool.pick`, and laws
  that reach every def (IO included). A `bolt.bend` at the project root says
  which rules, and how hard (off, warn, error), oxlint-style by group.
- `bolt check file..` runs Bend's checker and prints its errors in the same
  shape, `path:line:col: error: message`.
- `bolt lsp` is the language server: the checker's errors on open and save,
  bolt's findings as you type, hover, go-to-definition, symbols, completion,
  references, rename and semantic tokens.
- [editors/vscode](editors/vscode/) is the VS Code extension: highlighting,
  plus everything above through `bolt lsp`.

## Install

You need [Bend](https://github.com/bendlang/bend), built from source, and
clang 14+, since bolt is one native binary:

```
git clone https://github.com/Emerging-Patterns/bolt
cd bolt
bend bolt/main.bend -o bin/bolt.bin      # the whole build
bin/bolt.bin                             # lints every .bend under the current directory
```

Run and install with [ez](https://github.com/Emerging-Patterns/ez):

```
ezx Emerging-Patterns/bolt
# or
ez tool install Emerging-Patterns/bolt
bolt
```

Or with nix, nothing else is needed: the flake takes bend 2 from its own
flake (`github:bendlang/bend`: the release archive, patched for nix) and
builds bolt from it.

```
nix profile install github:Emerging-Patterns/bolt   # bolt, with bend on its PATH
nix run github:Emerging-Patterns/bolt               # or just run it, here
```

The VS Code extension, from the same checkout:

```
cd editors/vscode && npm install && npx --yes @vscode/vsce package
code --install-extension bolt-1.3.1.vsix   # x-release-please-version or: Extensions > ... > Install from VSIX
```

Over Remote-SSH, install it from the remote window, so it lands on the
machine where `bend` and `bolt` are. The extension finds `bolt` on the PATH --
`~/.nix-profile/bin`, `~/.local/bin`, `~/.bend/bin` and `~/.bun/bin` included,
since an extension host often has none of the shell's PATH -- and failing that
the `bin/bolt.bin` of a checkout it is run from; `bend.server.path` overrides
both (editors/vscode/README.md). After rebuilding bolt, run
`Bend: Restart Language Server`.

## Use

```
bolt                   every .bend file under the current directory
bolt a.bend b.bend     the files given
bolt check a.bend      the checker's errors, in the same shape
bolt lsp               the language server, over stdio, on the cores
bolt --version         the release, and the short commit when the build has one
bolt help              usage
```

Each finding is one line, `path:line:col: level: CODE: message`, then
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

The groups are `correctness` (`hole`, `pick`, `put`; error by default),
`suspicious` (`unused`), `style` (`doc`, `space`, `wrap`, `param`) and `laws` (`coverage`), the
rest warn by default. Every rule, and the config in full, is in
[bolt/README.md](bolt/README.md).

## Develop

The gate is [ez](https://github.com/Emerging-Patterns/ez), a separate binary
from a separate repo:

```
ez test                  every */tests/*.bend on both lanes, every PROOF.bend
ez build bin/bolt.bin    the binary people run
```

`ez test` checks every `PROOF.bend`, then runs each stay-list
host/integration test on the JS lane and the native lane against the `#|`
trailer the file ends in, caps each `bend` at `EZ_CAP` gigabytes, and caches
a lane on the content of everything it reads, so a second run over an
unchanged tree is seconds. There is no shell script in this repo. If Bend
can state a claim as a quantified law, it goes in `LAWS.bend` /
`PROOF.bend`; a law with no binder is a `closed` finding. `tests/*.bend` / `#|` exist only for claims
Bend cannot prove.

ez is a convenience, not a requirement: it buys the ledger above, the cache and
the caps. bolt itself has no dependency on it, and `tests/bare.bend` proves that
on every run by building bolt with bare `bend` from the git-pinned shake
and ezjson revs.
