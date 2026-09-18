# lsp

A language server for Bend, written in Bend: the real checker's errors on open
and save, and hover, go-to-definition, document symbols and completion as you type.

```
bend lsp/main.bend -o bin/bend-lsp     # from the repo root; clang 14 is enough
bin/bend-lsp --gpu off                 # speaks LSP on stdio
```

Run it with `--gpu off`: a native Bend binary takes the GPU when there is one,
and a language server has no use for a CUDA context. It ships native only: the
JS lane overflows its stack on a large message. Idle it costs no CPU.

## How it is wired

`server.bend` is the loop; everything outside the process is a
[wire](../wire/) service, so a test is a whole session over fakes:

| service | real | fake |
|---------|------|------|
| `transport/` — one message body in, one out | `stdio`: Content-Length framing over bytes | `script`: a list of bodies in; every body sent is printed |
| `files/` — a file's text by path; where Base lives | `disk` | any `Files` record (see `tests/nav.bend`) |
| `checker/` — a path's diagnostics | `bend`: a foreign effect (`exec.c`, `exec.js`) running `bend <path> -o <tmp>.js` | `fake`: canned |

The pure parts: `frame.bend` (framing, UTF-8 both ways — Content-Length counts
bytes and a read may end inside a char, so the transport reads bytes and
decodes itself), `report.bend` (the checker's text to diagnostics),
`proto.bend` (the JSON the server sends; URI to path), `docs.bend` (the open
documents, the loop's state), `path.bend`, and `nav.bend`: a name `Alias.rest`
is `rest` in the file behind the import `Alias`; any other name is an item of
the document, or else of Base. Items come from [syntax](../syntax/)'s outline,
so navigation works in files that do not check, and sees unsaved edits.

## What the checker gives

- `bend <path> -o <tmp>.js` checks and emits but never runs `main`. The server
  must not execute the file being edited; `tests/checker.bend` holds that.
- The report is text for people: `tests/report.bend` pins bend 2.0.3's format
  and fails when an update changes it.
- A `LAWS.bend` alone always has open laws, since `PROOF.bend` beside it fills
  them: its TODOs are reported only while that `PROOF.bend` does not check clean.
- One error per run, a line and no columns: a diagnostic covers its line. An
  error inside an import lands on line 0, naming where it is.
- The checker reads the file and its imports from disk, so its errors follow
  open and save, not unsaved edits.

[bolt](../bolt/)'s findings ride along (source `bolt`, the rule as the code),
each at the level the nearest `bolt.bend` gives its rule: errors as severity
1, warnings as 2, off ones dropped. The linter is pure, so it runs on the
text the editor shows: findings follow every edit, and each publish carries
the checker's last errors with the linter's current findings.

Completion offers what could finish the name being typed: `Alias.pre` from the
file behind the alias; anything else from the document, its aliases and (once
a char is typed) Base. The server filters by prefix and each candidate replaces
the whole typed name, dots included, as the editor's own word stops at a dot.

A name that a binder of the document binds (a parameter, a let, a pattern, a
field, ..) resolves to that binder first ([syntax](../syntax/)'s bind): hover
shows the declaration or the line that bound it, definition lands exactly on
the binder, completion offers the visible names first. The server knows
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
