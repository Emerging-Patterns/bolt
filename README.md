# bend

A monorepo of [Bend 2](https://github.com/bendlang/bend) projects. A project is
a directory; projects import each other by relative path
(`import ../core/check/kit.bend as Check`).

| project | what |
|---------|------|
| [core](core/) | dependency injection by templates: services, containers, laws; runs on the GPU |
| [json](json/) | a JSON parser, printer and path accessors |
| [syntax](syntax/) | a tolerant lexer, outline, syntax tree and binder for Bend sources |
| [bolt/lsp](bolt/lsp/) | a language server for Bend: diagnostics, navigation, completion, rename, semantic tokens |
| [bolt](bolt/) | `bolt`: comments, unused names, the binder-vs-def trap, holes, whitespace, double recursion, law coverage; levels per project in `bolt.bend`; in the editor too |

Everything people run is one binary behind one script: `bolt` lints, `bolt
check` runs the checker, `bolt lsp` serves an editor. `./build.sh` builds it
and links `bolt` into `~/.local/bin`; [editors/vscode](editors/vscode/) is the
VS Code client.

## The gate

```
./gate.sh            # laws + every test on JS and native CPU
./gate.sh --js-only  # laws + the JS lane only (no toolchain needed)
```

Every project keeps its laws in `LAWS.bend` and their proofs in `PROOF.bend`;
the gate fails while any law is open. Every `tests/*.bend` ends in the `#|`
lines its run must print, and must print them on each lane. A `!` call runs
on the GPU when the binary is run with one (`bin --gpu 1GB`); the gate does
not, as a GPU run is slower than the CPU cores here. The gate ends by running `bolt`
over the repo; [bolt.bend](bolt.bend) makes every rule an error.

## Toolchain

`bend` itself: `curl -fsSL https://bend-lang.com/install.sh | sh`. Native
builds need clang, GPU builds clang 19+ and CUDA 12 at `/usr/local/cuda`;
`flake.nix` provides that clang as `bend-cc`, and `gate.sh` enters the dev shell
on its own. `nix flake check` builds and runs, in the sandbox, a C program
that needs what bend's generated C needs (C11 atomics, pthreads, libm,
mmap) with the same clang 19; the gate runs it first. To build by hand:
`nix develop`, then `bend x.bend -o x`.
