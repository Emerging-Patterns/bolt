# lint

A linter for Bend, written in Bend, over the `syntax/` tree and binder. It
enforces what the checker does not: comments, unused names, the binder-vs-def
trap, leftover holes, whitespace, double recursion under `Bool.pick`, and
laws that reach every pure def.

    bend-lint                       every .bend file under the current directory
    bend-lint a.bend b/             the files given
    bend-lint --skip doc,space ..   without those rules

Each finding is one line, `path:line:col: rule: message`, with line and
column 1-based so a terminal can jump to it. The exit code is 1 when anything
was found. `./build.sh` puts `bend-lint` on `~/.local/bin`.

## Rules

Each rule is a module under `rules/` with `check(path, text) -> List<Finding>`,
listed in `rules.bend`. Adding a rule is adding a file and a line. A project
rule has `check(files) -> List<Finding>` instead and sees every file the
linter read at once (`rules.bend`'s `project`).

- `doc` — every top-level def, type and law has a comment block right above
  it. Helpers (dotted names like `show.go`) ride on their parent's, `main`
  needs none, PROOF.bend fills laws that LAWS.bend documents, and a test
  (under `tests/`) is documented by its header and its check names.
- `unused` — a name bound by a let, a do-bind, a lambda or as a parameter is
  never used. Exempt: pattern binders (naming every field of `Tok{k, t, l, c}`
  reads better than `_`), names starting with `_`, erased parameters (`-x`),
  a law's `for` names, and the parameters of a foreign def (its C and JS read
  them).
- `shadow` — a let or a pattern binds a name that a def above it in the file
  already has. When the file is imported, Bend reads the name as the def and
  the binder fails ("a pattern (a binder or a constructor)"). Parameters and
  `for` names are declared, not parsed as terms, and are safe.
- `hole` — a `?TODO` left in code (LAWS.bend is exempt: its laws are open
  claims by convention, filled by PROOF.bend).
- `space` — trailing whitespace, a tab, or a line over 120 wide. Width counts
  a string literal as two characters: a long fixture or message does not make
  a line hard to read, code does. `#|` trailers are data and exempt.
- `pick` — a def calls itself in both branches of a `Bool.pick`. Bool.pick is
  a function: both branches run whatever the condition, so two recursive
  calls a step is 2^n work (a per-token scan took 20 s this way and 20 ms as
  one pass). Bind the call once above the pick (`+more = go(rest)`) and pick
  between `x <> more` and `more`.
- `law` (project) — in a project that states laws (a directory with a
  LAWS.bend), a pure def that no law names. A law names a def when its
  statement mentions it, through the law file's import alias (`M.join` in
  `wire/LAWS.bend` names `join` of `wire/monoid/service.bend`); laws in any
  file count, PROOF.bend's lemmas included. A type is covered once any law
  reaches its module: a law about an instance names the accessors, never the
  service type. Out of scope: helpers (dotted names), `main`, tests, the law
  files, and a module that touches IO (a law cannot state it). A project
  without a LAWS.bend is not under law.

## How it takes its arguments

A native Bend binary rejects arguments it does not know, so `lint/bend-lint`
is a script: it puts the file list in `BEND_LINT_FILES` (one path a line) and
the skipped rules in `BEND_LINT_SKIP`, then runs `bin/bend-lint.bin`.

## In the editor

[lsp](../lsp/) runs every rule on each edit and publishes the findings as
warnings, so they show in VS Code as you type.

## In the gate

`./gate.sh` ends by linting the whole repo with every rule and must see
`clean`.
