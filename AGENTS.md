# AGENTS

Read `bend guide` before writing Bend. Then this.

## Layout

    gate.sh            the gate; green before every commit
    flake.nix          bend-cc: clang 19 for native and GPU builds
    build.sh           the binaries people run: bend-lsp, bend-lint -> ~/.local/bin
    editors/vscode/    the VS Code client (not Bend; never publish it unasked)
    <project>/         one dir per project
      LAWS.bend        the claims: human-owned, do not edit to make a proof pass
      PROOF.bend       the proofs; `bend PROOF.bend` prints "All terms check."
      tests/*.bend     each ends in the `#|` lines its run must print
                       (LAWS/PROOF are optional; a project needs tests)
      README.md

Design specs and plans are not kept in this repo; they live under
`~/.superpowers/projects/bend/`.

## Conventions

- New code comes test-first: write `tests/x.bend` with its `#|` trailer, watch
  the gate fail, then implement.
- `bend-lint` (lint/README.md) runs at the end of the gate: keep it clean.
  Every top-level def, type and law gets a comment right above it (helpers
  named `x.go` ride on x's); a parameter that is there to be ignored starts
  with `_`; no let or pattern binder may share a name with a def above it;
  a project with a LAWS.bend has every pure def named by some law.
- Dependencies are injected the `wire` way (see wire/README.md): a service is
  a folder, `x/service.bend` plus one file per implementation exporting
  `new()`. Tests use `wire/check/kit.bend`.
- A service file's header says whether it is pure (GPU-safe) or an effect
  (CPU event loop only). Only pure code may sit under a `!` call.
- Never `bend --publish` without asking: it uploads to the public hub.

## Bend gotchas (each one cost a failed check here)

- A template cannot destructure its own `~` argument ("an undestructed
  scrutinee"): pass it to a plain accessor def that destructures it.
- A pattern binder may not share a name with a top-level def of the module:
  in a module that defines `now`, write `Clock{f} = c`, not `Clock{now} = c`.
- Argument quantities are part of a function type: a field typed
  `@+i:U32 -> U32` only takes defs declared `(+i: U32)`.
- A template is not checked until something instantiates it: every template
  needs a test that calls it.
- User code may not call a law before its def is filled, so Base's mutually
  recursive arm/go lemma shape does not work here. Give the arm the induction
  hypothesis as a parameter, and erase its other arguments (`for -at`) so the
  caller can still recurse on them (see wire/PROOF.bend, Word.xor_assoc).
- `match` takes parameters and pattern-bound variables only, in binder order;
  to branch on a computed value, pass it to a helper (see `report` in
  wire/check/service.bend).
- No mutual recursion, and a def must be defined above its use. A loop that
  branches on a computed value either folds the branch into a non-recursive
  helper that returns the next state (json/lex.bend), or hands the helper a
  continuation closure `rest` (Base's App.loop).
- A self-call must shrink one argument, the same one every time: a rose tree
  over `List<T>` does not pass. Keep the cells inside the type (json/value.bend).
- A big `Nat` literal expands in unary and overflows the stack: write
  `U32.to_nat(100000)`.
- The argument that shrinks must be the first live (non-template) one:
  `send_all(replies, h)` passes, `send_all(h, replies)` does not.
- `Bool.pick` evaluates both branches: never put a different recursive call in
  each (that is exponential; `bend-lint`'s `pick` rule catches it). Bind the
  one recursive call with `+rest = ..` and pick between values built from it. The same goes for any expensive
  expression in a branch: a scan of the whole token list inside a per-token
  pick runs for every token (bind's notes were 20 s that way, 20 ms as one
  pass).
- A destructure or a `match` needs a variable, never a call:
  `Out{a, b} = f(x)` is "a match cannot scrutinize a computed value"; bind the
  call first, or take it apart in a helper that receives it as a parameter.
- `+x` on a pattern variable that a later row refines can fail with "an
  annotated term (cannot infer)": alias it, `+r = {rest : Tree.Node}`, and
  use `r`. A record literal in a `+` let may need the same: `{R{..} : R}`.
- Only a do-block has typed lets (`x : T = v`); elsewhere annotate with
  braces, `{v : T}`. A typed do-bind may be reusable: `+n : U32 <- m`.
- `Kind` is a keyword: no type of that name.
- Binders and defs share a namespace per *imported* module: a let or a pattern
  binder named like a def defined above it in the file parses as a reference
  to the def once the file is imported ("a pattern (a binder or a
  constructor)"), though the same file runs fine as a main. Parameters and
  `for` names are safe. `bend-lint`'s `shadow` rule catches it.
- `bend x.bend` runs main after checking. To check only, `bend x.bend -o t.js`.
- A foreign effect `def a.b(..) -> IO(T)` with `import "./x.c"` and
  `import "./x.js"` bodies is `a_b_run` + `io_eff(CID_A_B, ..)` in C and
  `function a_b(..)` in JS (lsp/checker/exec.*).
- A server's stdin and stdout may be sockets (node spawns children that way),
  and no path opens a socket: wrap descriptors 0 and 1 (lsp/transport/fd.c),
  never `File.open("/dev/stdin")`. Test a server spawned from node
  (lsp/tests/spawn.js), not only through pipes.
- A native Bend binary exits on an option it does not know, and takes no
  positional arguments at all: a launcher must not add flags
  (vscode-languageclient's `transport: stdio` adds `--stdio`), and a CLI
  takes its arguments through the environment (lint/bend-lint).
- A pair `A & B` is never `Data`: a list of pairs is `List<&1, A & B>`.
- The JS lane overflows its stack on long strings (~65KB). Head such a test
  `# lanes: native`; anything long-running ships as the native binary.
- The GPU is on by default in a native binary: the CPU lane is `--gpu off`.
- Link native binaries with `bend-cc` only. The wrapped nix clang links nix's
  glibc and nvrtc then fails to load `libnvrtc-builtins`.
