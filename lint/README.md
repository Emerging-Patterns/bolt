# lint

A linter for Bend, written in Bend, over the `syntax/` tree and binder. It
enforces what the checker does not: comments, unused names, the binder-vs-def
trap, leftover holes, and whitespace.

    bend-lint                       every .bend file under the current directory
    bend-lint a.bend b/             the files given
    bend-lint --skip doc,space ..   without those rules

Each finding is one line, `path:line:col: rule: message`, with line and
column 1-based so a terminal can jump to it. The exit code is 1 when anything
was found. `./build.sh` puts `bend-lint` on `~/.local/bin`.

## Rules

Each rule is a module under `rules/` with `check(path, text) -> List<Finding>`,
listed in `rules.bend`. Adding a rule is adding a file and a line.

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

## How it takes its arguments

A native Bend binary rejects arguments it does not know, so `lint/bend-lint`
is a script: it puts the file list in `BEND_LINT_FILES` (one path a line) and
the skipped rules in `BEND_LINT_SKIP`, then runs `bin/bend-lint.bin`.

## In the gate

`./gate.sh` ends by linting the whole repo with every rule and must see
`clean`.
