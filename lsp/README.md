# lsp

A language server for Bend, written in Bend. Milestone 1: open or save a
`.bend` file and see the real checker's errors.

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
| `checker/` — a path's diagnostics | `bend`: a foreign effect (`exec.c`, `exec.js`) running `bend <path> -o <tmp>.js` | `fake`: canned |

The pure parts: `frame.bend` (framing, UTF-8 both ways — Content-Length counts
bytes and a read may end inside a char, so the transport reads bytes and
decodes itself), `report.bend` (the checker's text to diagnostics),
`proto.bend` (the JSON the server sends; URI to path).

## What the checker gives

- `bend <path> -o <tmp>.js` checks and emits but never runs `main`. The server
  must not execute the file being edited; `tests/checker.bend` holds that.
- The report is text for people: `tests/report.bend` pins bend 2.0.3's format
  and fails when an update changes it.
- One error per run, a line and no columns: a diagnostic covers its line. An
  error inside an import lands on line 0, naming where it is.
- The checker reads the file and its imports from disk, so diagnostics follow
  open and save, not unsaved edits (`change: 0`).

Next: `syntax/`, an error-tolerant lossless parser, for unsaved text, exact
ranges, symbols; then definition, hover, completion.
