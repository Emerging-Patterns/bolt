# AGENTS

This is bolt: a linter, checker and language server for Bend 2, and its VS
Code extension, written in Bend (README.md). Read `bend guide` before
writing Bend. Then this.

## Hard rule

If Bend can state it as a law (including an IO equality
`{main() == IO.print("…") : IO(Unit)}`), it goes in `LAWS.bend` /
`PROOF.bend`.

`tests/*.bend` and `#|` exist only for claims Bend cannot prove:
host/integration (bend, nix, node, disk, process). The stay list is
`tests/bare.bend`, `tests/flake.bend`, `bolt/lsp/tests/checker.bend`,
`syntax/tests/lex_files.bend`, `syntax/tests/tree_files.bend`,
`bolt/lsp/tests/levels.bend`, plus companions
(`bolt/lsp/tests/spawn.js`, `tests/locate.js`) and
`lazy/tests/lazy.bend` (a thunk that must not run: Bend cannot state
“this side was skipped”).

A `#|` equality for a proveable claim is a bug. A directory with
`LAWS.bend` and `PROOF.bend` is complete. Do not add `tests/`.

## Layout

    ez.toml            the ledger: bolt's name, its entry `bolt/main.bend`, and
                       shake v0.1.1 (`0x65bf91e14c96bf0c25491d716ec9f68c`),
                       ezjson v0.1.0 (`0xa3c2445eb44c5d8406e6229be518fccb`)
                       and snap v0.1.0 (`0x29fbb19f01e963cc6271864b7e442159`)
                       as git-backed deps
    ez.lock.toml       the resolved pin: rev, narHash, and file digests
    flake.nix          bolt via ez's nix lib (bend follows bendlang/bend; bend-cc,
                       BEND_LIB from ez.lock.toml, and the package build come from ez);
                       `nix flake check` builds the bolt package and runs
                       checks.test (`ez test --unit-only` through mkProofs)
                       (nix sees tracked files only: git add first)
    tests/*.bend       stay-list host/integration only (bare, flake).
                       `ez test` runs each on its own, and caches none of them
    .github/workflows/ ci: `nix flake check`, on a pull request and on a push to main.
                       release-please: on push to main, conventional commits open a
                       release PR; merging it tags `vX.Y.Z` and opens the GitHub Release.
                       Merge release-please PRs (do not squash) so the action can
                       cut the tag/GitHub Release.
                       tag: workflow_dispatch escape hatch (rewrites the version
                       files, then tags).
                       publish: `ez publish`, the hub upload, workflow_dispatch
                       only, on an existing tag -- a person running it is the ask.
                       do not also run github-release for release-please tags.
    editors/vscode/    the VS Code extension (not Bend; never publish it to the marketplace unasked)
    <project>/         one dir per project
      LAWS.bend        the claims: human-owned, do not edit to make a proof pass.
                       Closed equalities (including `IO(T)`) live here.
      PROOF.bend       the proofs; `bend PROOF.bend` prints "All terms check."
                       (every one in the tree is gated, so a fixture holding a
                       proof that is meant to fail cannot live here)
                       no `tests/` unless the claim is on the stay list
      README.md

Anything under a `tests/` directory is a test. Fixtures a test reads are not
tests, so they live beside the project rather than under it --
`bolt/lsp/fixtures/`, not `bolt/lsp/tests/fixtures/`.

## The gate

    nix flake check                the bolt package and checks.test
                                   (mkProofs runs `ez test --unit-only`)
    nix develop                    bend 2, bend-cc and node, with CC=bend-cc set
    ez test                        every lane, every proof, and the top-level tests/
    ez test --js-only              skip the native lanes
    ez test --full                 ignore the cache
    ez build bin/bolt.bin          the binary people run

Run all of it from the repo root. `gate.sh` used to re-exec itself under
`nix develop` when `bend-cc` was missing; nothing does that for you now, so
enter the shell first. `ez build` takes the output path because its default is
still `bin/ez.out`.

[ez](https://github.com/Emerging-Patterns/ez) is the gate. It finds every
`*/tests/*.bend`, runs it on both lanes -- JS, where `bend` interprets it, and
native, where it is compiled first -- against the `#|` trailer the file ends
in, checks every `PROOF.bend` in the tree, runs each `bend` inside a memory
cgroup (`EZ_CAP` gigabytes, 8 by default, which this repo has never needed
raising), compiles a project's
tests into one binary rather than one
each, and caches a lane on the content of everything it reads. It replaced
`gate.sh` and `build.sh`, 299 lines of shell that did the same work worse, and
nothing in this repo is a shell script now.

ez is a separate binary built from a separate repo, so it still runs and still
reports when bolt itself is broken, which is the whole of the argument that
used to keep `gate.sh` around.

CI is that flake check. `.github/workflows/ci.yml` runs `nix flake check`:
the bolt package and checks.test.

**ez is not a prerequisite for bolt.**
`bend bolt/main.bend -o bin/bolt.bin` is the entire build: no ez, no nix.
shake, ezjson and snap are git-backed ledger deps; `BEND_LIB` must hold
those packages (the flake and `ez fetch` both do). `tests/bare.bend` still
builds with bare `bend` and no ez, laying each out from its pinned rev.

Design specs and plans are not kept in this repo; they live under
`~/.superpowers/projects/bolt/`.

## Conventions

- New proveable behavior is a law in `LAWS.bend`, then a filling in
  `PROOF.bend`. Watch `bend PROOF.bend` fail, then prove.
- `SPEC.md` lists every guaranteed behavior by ID. A quantified law that
  proves one carries `# <ID>` on its own line directly above its `law` line,
  and the row moves from `pending` to `proved` in the same change.
- `bolt` (bolt/README.md) runs at the end of the gate, every rule an error
  by the root bolt.bend: keep it clean. The binary the gate lints with is the
  one `tests/bare.bend` has just built from this tree, never whatever `bolt`
  happens to be on the PATH: a bolt from an older release answers `clean` to
  findings it does not implement yet, and a `bin/bolt.bin` left over from an
  older build answers `clean` to nearly everything.
  Every top-level def, type and law gets a comment right above it (helpers
  named `x.go` ride on x's); a parameter that is there to be ignored starts
  with `_`; no let or pattern binder may share a name with a def above it;
  a project with a LAWS.bend has every def named by some law, IO included.
  Helpers (dotted names), tests, and the law files themselves are out of
  scope.
- Dependencies are injected the `core` way (see core/README.md): a service is
  a folder, `x/service.bend` plus one file per implementation exporting
  `new()`.
- A service file's header says whether it is pure (GPU-safe) or an effect
  (CPU event loop only). Only pure code may sit under a `!` call.
- Never `bend --publish`, and never `ez publish`: both upload to the public
  hub, and an upload is public and cannot be taken back. An agent does not
  publish bolt, in CI or on a machine, and does not ask to be allowed to: the
  one way bolt reaches the hub is a human running `.github/workflows/publish.yml`
  from Actions on an existing tag, and that dispatch *is* the ask. Nothing
  else in this repo uploads anything. release-please opens the GitHub Release
  on merge; publish stays a manual hub upload. To exercise the publish path
  without publishing, point it at a dead port: `BEND_HUB=http://127.0.0.1:1`.

## Bend gotchas (each one cost a failed check here)

- A template cannot destructure its own `~` argument ("an undestructed
  scrutinee"): pass it to a plain accessor def that destructures it.
- A pattern binder may not share a name with a top-level def of the module:
  in a module that defines `now`, write `Clock{f} = c`, not `Clock{now} = c`.
- Argument quantities are part of a function type: a field typed
  `@+i:U32 -> U32` only takes defs declared `(+i: U32)`.
- A template is not checked until something instantiates it: every template
  needs a use that calls it (a law is enough).
- User code may not call a law before its def is filled, so Base's mutually
  recursive arm/go lemma shape does not work here. Give the arm the induction
  hypothesis as a parameter, and erase its other arguments (`for -at`) so the
  caller can still recurse on them (see core/PROOF.bend, Word.xor_assoc).
- `match` takes parameters and pattern-bound variables only, in binder order;
  to branch on a computed value, pass it to a helper (see `report` in
  core/check/service.bend).
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
- `Bool.pick`, `Bool.and`, `Bool.or`, `&&` and `||` are defs, so every
  argument is evaluated before the call. Never put a different recursive call
  in each branch (that is exponential; `bolt`'s `pick` rule catches it), and
  do not hide a search's recursion in one branch either: it runs whatever the
  condition says, so the search never exits early (native, 100 searches over
  100k cells: 0.10 s for a hit at the head, 0.11 s at the end). Bind the one
  recursive call with `+rest = ..` and pick between values built from it, or
  take the early exit from `lazy/lazy.bend` (`Lazy.stop`, `Lazy.or_else`,
  `Lazy.and_then`: the last argument is a `Unit -> T` thunk, applied only on
  the branch that needs it; the same search costs 0.00 s). The same goes for
  any expensive expression in a branch: a scan of the whole token list inside
  a per-token pick runs for every token (bind's notes were 20 s that way,
  20 ms as one pass). `bolt`'s `strict` rule catches the Bool.and/or shape.
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
  `for` names are safe. `bolt`'s `shadow` rule catches it.
- `bend x.bend` runs main after checking. To check only, `bend <file.bend> --check-only` (or `bend x.bend -o t.js`).
- A foreign effect `def a.b(..) -> IO(T)` with `import "./x.c"` and
  `import "./x.js"` bodies is `a_b_run` + `io_eff(CID_A_B, ..)` in C and
  `function a_b(..)` in JS (bolt/lsp/checker/exec.*).
- A server's stdin and stdout may be sockets (node spawns children that way),
  and no path opens a socket: wrap descriptors 0 and 1 (bolt/lsp/transport/fd.c),
  never `File.open("/dev/stdin")`. Test a server spawned from node
  (bolt/lsp/tests/spawn.js), not only through pipes.
- A *compiled* Bend binary passes its whole command line to `IO.args()`,
  flags included (2.0.16; 2.0.5 did not, which is where "a Bend binary takes
  no arguments" came from). The runtime keeps only its own — `--threads`,
  `--gpu`, `--gpu-build`, `--help` — and strips them wherever they stand, so
  `bolt lsp --gpu off` reaches `IO.args()` as `[lsp]` (`bolt lsp` with no
  `--gpu` is that same launch); `--` hands even those
  to the program. `IO.args()` has no argv[0], so a binary cannot find itself
  by it. The *interpreted* lane differs: `bend f.bend a b` passes positional
  arguments but bend's own CLI rejects flags it does not know.
- A pair `A & B` is never `Data`: a list of pairs is `List<&1, A & B>`.
- `x.of` and `x_of` mangle to the same C name ("two names mangle to
  FID_.."): never both in one module.
- The JS lane overflows its stack on long strings (~65KB). Head such a test
  `# lanes: native`; anything long-running ships as the native binary.
- The GPU is on by default in a native binary: the CPU lane is `--gpu off`.
  `bolt lsp` with no `--gpu` starts again as `--gpu off` before the runtime
  chooses a device; `--gpu on` or `--gpu 4GB` is left as written. Launchers
  may still pass `--gpu off` (tests/bare.bend, bolt/lsp/tests/spawn.js, the
  VS Code extension, the nix wrapper).
- Link native binaries with `bend-cc` only. The wrapped nix clang links nix's
  glibc and nvrtc then fails to load `libnvrtc-builtins`.
