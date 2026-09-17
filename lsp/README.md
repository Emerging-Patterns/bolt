# lsp

A language server for Bend, written in Bend: the real checker's errors on open
and save, and hover, go-to-definition and document symbols as you type.

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
- The checker reads the file and its imports from disk, so diagnostics follow
  open and save, not unsaved edits.

Not yet: parameters and locals (hover knows top-level names: defs, laws, types,
constructors), completion, exact ranges (an item is its line), percent-encoded
URIs when matching open documents.
