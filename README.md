# bend

A monorepo of [Bend 2](https://github.com/bendlang/bend) projects. A project is
a directory; projects import each other by relative path
(`import ../wire/check/kit.bend as Check`).

| project | what |
|---------|------|
| [wire](wire/) | dependency injection by templates: services, containers, laws; runs on the GPU |
| [json](json/) | a JSON parser, printer and path accessors |
| [syntax](syntax/) | a tolerant lexer, outline, syntax tree and binder for Bend sources |
| [lsp](lsp/) | a language server for Bend: diagnostics, navigation, completion, rename, semantic tokens |
| [lint](lint/) | `bend-lint`: comments, unused names, the binder-vs-def trap, holes, whitespace; warnings in the editor |

[editors/vscode](editors/vscode/) is the VS Code client for the language server;
`./build.sh` builds `bin/bend-lsp` and `bend-lint` and links them into
`~/.local/bin`.

## The gate

```
./gate.sh            # laws + every test on JS, native CPU and GPU
./gate.sh --js-only  # laws + the JS lane only (no toolchain needed)
```

Every project keeps its laws in `LAWS.bend` and their proofs in `PROOF.bend`;
the gate fails while any law is open. Every `tests/*.bend` ends in the `#|`
lines its run must print, and must print them on each lane. A test with a `!`
call also runs on the GPU (capped at 1GB). The gate ends by linting the repo
with `bend-lint`, every rule on.

## Toolchain

`bend` itself: `curl -fsSL https://bend-lang.com/install.sh | sh`. Native
builds need clang, GPU builds clang 19+ and CUDA 12 at `/usr/local/cuda`;
`flake.nix` provides that clang as `bend-cc`, and `gate.sh` enters the dev shell
on its own. To build by hand: `nix develop`, then `bend x.bend -o x`.
