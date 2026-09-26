# lsp

A language server for Bend, written in Bend: the real checker's errors on open
and save, and hover, go-to-definition, document symbols and completion as you type.

```
bend main.bend -o bin/bolt.bin   # from the repo root; clang 14 is enough
bolt lsp                              # speaks LSP on stdio, on the cores
bolt lsp --gpu on                     # the same, on the device
```

It is one command of [bolt](../)'s binary (`lsp/run.bend` is its
entry). `bolt lsp` with no `--gpu` is `--gpu off`: a native binary takes
the device when the line asks and one is present, and a language server
stays on the cores unless the line says `--gpu on` or a size (`--gpu 4GB`).
The runtime takes `--gpu` out of the line, so `IO.args()` still reads just
`lsp`. It ships native only: the JS lane overflows its stack on a large
message. Idle it costs no CPU.

## How it is wired

`server.bend` is the loop. Two of the things outside the process are
records the loop takes as parameters: `LAWS.bend` quantifies over every
`Files`, and `tests/checker.bend` drives the loop over the `script`
transport:

| record | real | fake |
|--------|------|------|
| `transport/` — one message body in, one out | `stdio`: Content-Length framing over bytes | `script`: a list of bodies in; every body sent is printed |
| `files/` — a file's text by path; where Base lives; the working directory | `disk` | any `Files` record |

The checker, a path's diagnostics, has one implementation and the loop calls
it directly: `checker/bend.bend`, a foreign effect (`exec.c`, `exec.js`)
running `bend <path> --check-only`.

The pure parts: `frame.bend` (framing, UTF-8 both ways — Content-Length counts
bytes and a read may end inside a char, so the transport reads bytes and
decodes itself; the length is kept as its decimal digits, so `LAWS.bend`
proves BOLT-LSP-1 over every body: the count is the body's UTF-8 bytes, every
proper prefix of a message waits, and a message cuts back to its body),
`report.bend` (the checker's text to diagnostics),
`proto.bend` (the JSON the server sends; URI to path), `docs.bend` (the open
documents, the loop's state), `path.bend`, and `nav.bend`: a use is answered
as [syntax](../syntax/)'s binder resolves it (BOLT-SYN-5): a binder of the
document, else an item of the document (`def Lib.f` wins over the import
`Lib`), else `rest` in the file behind the import `Alias` of `Alias.rest`,
else Base (BOLT-LSP-6 in `LAWS.bend`). Items come from [syntax](../syntax/)'s outline,
so navigation works in files that do not check, and sees unsaved edits.

## What the checker gives

- `bend <path> --check-only` checks the file and its imports and never runs
  `main`. The server must not execute the file being edited. Which runs the
  checker makes is data (`checker/argv.bend`), so `LAWS.bend` proves every
  one carries `--check-only` (BOLT-LSP-5); that bend honours the flag is
  BOLT-TRUST-5, and `tests/checker.bend` runs a live `bend --check-only`.
- The report is text for people, parsed from bend's output
  (BOLT-TRUST-5 in SPEC.md): an update that changes the format breaks it.
- A `LAWS.bend` alone always has open laws, since `PROOF.bend` beside it fills
  them: its TODOs are reported only while that `PROOF.bend` does not check clean.
- One error per run, a line and no columns: a diagnostic covers its line. An
  error inside an import lands on line 0, naming where it is.
- The checker reads the file and its imports from disk, so its errors follow
  open and save, not unsaved edits.

[bolt](../)'s findings ride along, source `bolt(group:slug)` and code the
stable id (`bolt(style:wrap)`, `S003`),
each at the level the nearest `bolt.bend` gives its rule: errors as severity
1, warnings as 2, off ones dropped. The linter is pure, so it runs on the
text the editor shows: findings follow every edit, and each publish carries
the checker's last errors with the linter's current findings. The bolt.bend
candidates are the CLI's for the same path and working directory, so the
findings are exactly what `bolt <path>` grades for that file and text
(BOLT-LSP-2, `LAWS.bend` `lint_is_cli`). What open, change, save and close
publish is decided by server.bend's `pub.*`, pure over the checker's errors and
the texts the files hold, and `LAWS.bend` states it (BOLT-LSP-4).

Positions follow LSP 3.17's `positionEncoding`: initialize answers `utf-32`
when the client offers it and `utf-16` otherwise, and `enc.bend` converts
every character offset read or sent between bolt's code-point columns and
the negotiated encoding (a char past U+FFFF is two UTF-16 units). On a line
with no such char the two agree (BOLT-LSP-8 in `LAWS.bend`), so a document
with none converts as utf-32 and never looks a line up.

Completion offers what could finish the name being typed: `Alias.pre` from the
file behind the alias; anything else from the document, its aliases and (once
a char is typed) Base. The server filters by prefix and each candidate replaces
the whole typed name, dots included, as the editor's own word stops at a dot.

A name that a binder of the document binds (a parameter, a let, a pattern, a
field, ..) resolves to that binder first ([syntax](../syntax/)'s bind): hover
shows the declaration or the line that bound it, definition lands exactly on
the binder, completion offers the visible names first. An item's own name (a
def, a law, a type) is that binder too, and its hover is the outline item:
the signature, then the comment above it, the same text a use of the name
gets. A proof `def Alias.law` hovers as the law in the file behind `Alias`,
which is where that comment is written. The server knows
binding sites, not types: a parameter has its annotation, a pattern binder has
its pattern.

References and rename work within a document: a binder's every use, or an
item's declaration and its uses in the file. Only a name bound in the
document renames (a Base name, or one behind an alias, is refused with a
message); uses of the item from other files through an alias are not touched.
Semantic tokens (`semantic.bend`) classify every name by what it refers to,
so a parameter stays a parameter at each use and a constructor of the file
is one wherever it appears; a name from elsewhere is read by its shape
(`Bool.pick` a function, `U32` a type, `Nil{` a constructor). Comments,
strings and numbers are left to the editor's grammar.

Not yet: exact ranges for top-level items (an item is its line), rename
across files, percent-encoded URIs when matching open documents.
