# Design: bolt lint in planner form

## Draft Status

State: Draft, for the maintainer's review. Nothing here changes `bolt` yet; the work packages below do.

This is the design for the fourth phase of [bolt-spec.md](bolt-spec.md): converting `bolt` (the lint command) to a pure planner and a thin interpreter, then proving the requirements that need the file system: BOLT-SCOPE-1 to SCOPE-5, BOLT-OUT-3 to OUT-5, and BOLT-CFG-4. It follows ez's planner for `ez lock` ([ez-lock-planner.md](https://github.com/Emerging-Patterns/ez/blob/main/docs/rfc/ez-lock-planner.md)) wherever the two problems are the same, so the two repositories keep one shape. `bolt check` (BOLT-CHK-1), the command line (BOLT-CLI) and the language server (BOLT-LSP) are later phases with their own designs. `SPEC.md` does not change until a requirement's law lands.

### Open questions

Decided with the maintainer before drafting:

- [x] <!-- REVIEW (resolved): The World is data, as in ez: the planner asks questions, the interpreter answers each by IO, and the World is the list of answers. Laws quantify over every World. -->
- [x] <!-- REVIEW (resolved): Lint first, in one PR, byte-identical to today. The check, CLI and LSP planners follow, each planned on its own. -->
- [x] <!-- REVIEW (resolved): The two known bugs, relative-path config lookup (BOLT-CFG-4, bolt-spec.md REVIEW-5) and a directory named on the command line reading as empty text (BOLT-OUT-5), are fixed in separate `fix:` PRs after the planner lands, each with its law. -->
- [x] <!-- REVIEW (resolved): One trust row for every interpreter, in ez's words (EZ-TRUST-2), added by the first planner PR and cited by the later ones. This replaces bolt-spec.md REVIEW-14's three rows. -->

Open:

- [ ] <!-- REVIEW-P1: Config candidates are asked up front, for the directory chain of every linted path and of SPEC.md, instead of once per finding as today. Every finding's path is one of those, so the grading is the same; bolt reads each bolt.bend once per directory instead of once per finding. A law ties it: the planner never grades with a candidate it did not ask for. -->
- [ ] <!-- REVIEW-P2: A directory listing that fails is read as empty, as `bolt/walk/dir.c` answers today. Making it a finding is a behavior change, left for a later `fix:` PR if wanted. -->
- [ ] <!-- REVIEW-P3: BOLT-OUT-3's wording says the output ends with `coverage` and `unsafe`, but `Rules.project` also runs `trace` after them. We propose the row reads "then `coverage`, `unsafe` and `trace`" when OUT-3's law lands. -->
- [ ] <!-- REVIEW-P4: The rows BOLT-LAW-1, LAW-2 and LAW-3 do not need the planner: `closed` is a per-file rule and `coverage` and `unsafe` are pure functions of the digests. They move to the rule-row queue and are proved over digests; only "the files in the run" (SCOPE-2, SCOPE-3) is the planner's. -->

---

## Summary

`bolt/lint.bend`'s `run` already makes every decision in pure functions. What keeps its behavior out of the laws is that those functions are called from inside IO, with three effects woven between them: the walk (`Glob.find` over `WalkDisk`), the file reads (`Files.read` over `Disk`) and grading, which reads the bolt.bend candidates of every finding's directory, once per finding. This design gives the pure part a value to run on. A World holds every answer the run needed; `Plan.wants(w)` says which questions are still open; `Plan.plan(w)` returns the lines to print and the exit status. The interpreter loops, answering questions, until nothing is wanted, then prints and exits. Output is byte-identical to today's.

## What bolt lint reads today

| Read | Where | When |
| :---- | :---- | :---- |
| directory listings | `Glob.find(~WalkDisk.new(), ".")`, BFS with fuel 100000, then sorted | no files named |
| each source file | `read_all(~Disk.new(), sources(files))`; a bolt.bend is dropped first | always |
| `SPEC.md` | `Files.read(Disk.new(), "SPEC.md")` | always; `trace` uses it only when the whole tree is linted |
| bolt.bend candidates | `Files.read_all(Config.candidates(64n, dir_of(path)))`, per finding | for every finding |

Everything else, parsing, the per-file rules, the project rules, grading, counting and rendering, is already pure.

## The World

```
# a question the planner asks. Each is answered by one IO action.
type Ask is Data:
  Entries{dir: String}          # list a directory (bolt/walk/dir.c)
  Text{path: String}            # read a file (bolt/lsp/files/disk)

# the answer to one question. A directory that cannot be opened lists as
# empty, as dir.c answers today (REVIEW-P2).
type Answer is Data:
  Listed{names: List<&2, String>}   # a directory's names, a sub-directory's ending in "/"
  Read{text: String}
  Unread{}

# one question, answered
type Reply is Data:
  Reply{ask: Ask, answer: Answer}

# everything `bolt` reads: the paths named on the command line, and every
# answer the interpreter gave
type World is Data:
  World{paths: List<&2, String>, replies: List<&2, Reply>}
```

As in ez, the World holds only what the command reads: the named paths and the answers. There is no `cwd` field yet; the CFG-4 fix adds it (bolt-spec.md REVIEW-5), and that PR is where the World grows.

### How the interpreter gathers each answer

| Ask | Gathered by | When the planner asks |
| :---- | :---- | :---- |
| `Entries{dir}` | `Walk.entries(WalkDisk.new(), dir)` | no files named, for each directory the walk has queued and not yet had answered |
| `Text{path}` for a source | `Files.read(Disk.new(), path)` | once the file list is known: each named or walked path that is not a bolt.bend |
| `Text{"SPEC.md"}` | the same | always, in the same round as the sources |
| `Text{".../bolt.bend"}` | the same | in the same round: `Config.candidates(64n, dir_of(p))` for every source path and for `SPEC.md`, each asked once (REVIEW-P1) |

### Laziness without losing purity

The file list is known only after the walk, and the walk's next directories are known only after the last listing. We use ez's demand loop:

|  |
|:---:|
| <pre>round 1:  World{[], []}                          -> wants [Entries "."]<br>round 2:  World{[], [. listed]}                  -> wants [Entries "./bolt", Entries "./core", ...]<br>...       (one round per level of the tree)<br>round k:  World{[], [every dir listed]}          -> wants [Text a.bend, ..., Text SPEC.md, Text bolt.bend, ...]<br>round k+1: World{[], [... every text read]}     -> wants []  ->  plan(w) = Plan{lines, exit}</pre> |
| Caption: With files named, the walk rounds are skipped and round 1 asks for the texts. |

`wants(w)` is cheap: it re-runs the walk as a fold over the listings the World has, and never parses a file. `plan(w)` parses and lints once. The planner is a total function of the World: on a World missing an answer it needs, `plan` treats it as `Unread` (a `read` finding for a source, the defaults for a bolt.bend), but the interpreter only calls `plan` once `wants` is empty, and a law ties the two (below). The loop is the interpreter's, runs under fuel (100000 plus 2 rounds, the walk's bound plus the two read rounds), and each round adds at least one answer, since `wants` never asks what the World already answers.

## The Plan

```
# what `bolt` prints, in order, and the status it exits with
type Plan is Data:
  Plan{lines: List<&2, String>, exit: U32}
```

`plan(w)` is today's pipeline with the reads replaced by lookups: the file list (`chosen`), `sources`, `srcs_of`, `findings`, grading by `Config.nearest` over the looked-up candidates, `show_all`, and the `summary` line. `exit` is 1 exactly when some graded finding is an error, which is what `Status.stop` receives today.

## Planner, interpreter and module layout

```
# bolt/lint/world.bend: Ask, Answer, Reply, World, and the lookups
#   (listing(w, dir), text(w, path)) the planner reads the World through
# bolt/lint/plan.bend: the planner, pure: wants(w), plan(w), and the walk as a
#   fold over the World's listings (from bolt/glob.bend, which it replaces)
# bolt/lint.bend: the interpreter: gather until nothing is wanted, print
#   plan.lines, stop with plan.exit. `run(paths)` keeps its signature, so
#   bolt/main.bend does not change.
```

`bolt/glob.bend` goes: its walk becomes `Plan.walk`, a pure fold with the same fuel, queue order and sort. `bolt/walk/` stays, as the interpreter's listing effect. The laws go in `bolt/LAWS.bend` and `bolt/PROOF.bend`, beside the CFG and OUT laws.

## Laws

Each is stated over every World, against spec functions written apart from the planner.

| Row | Law, over every World `w` |
| :---- | :---- |
| (tie) | when `wants(w)` is empty, every question `plan(w)` looks up is answered in `w` |
| SCOPE-1 | with no paths named, the planner's file list is the sorted list of `.bend` names a spec BFS over `w`'s listings reaches from `.` within 100000 directories, skipping hidden names and `node_modules` |
| SCOPE-2 | `plan(w)`'s findings are `unread`, then `Rules.on` of each parsed source alone, then `Rules.project` of the digests of every source in the run |
| SCOPE-3 | stated over the digests the planner hands the project rules: every non-exempt file in the run is under law exactly when one of them is a LAWS.bend |
| SCOPE-5 | no path in the planner's source list is a bolt.bend, whatever `w.paths` names |
| OUT-3 | the lines are the read failures, then the per-file findings in file-list order and `Rules.on` order, then the project findings (REVIEW-P3), then the summary |
| OUT-4 | the last line is `clean` or `N errors, M warnings` for the graded findings, and `exit` is 1 exactly when one is an error |
| OUT-5 | a source whose answer is `Unread` yields one `read` finding graded with `correctness`; the directory case waits for its fix PR |
| CFG-4 | in the fix PR, once the World has `cwd`: a finding is graded by the first candidate, from its resolved directory upward, whose answer is `Read` |

SCOPE-4 ("exemptions are decided by the path alone") needs no World: every exemption is a function of the path string (BOLT-RULE-EXEMPT, #111), and it can be stated now as "a rule's findings on an exempt path are the same for every source text", in the rule-row queue.

## Verification

The planner PR is a refactor, so its evidence is that nothing changed:

- bolt built before and after prints byte-identical output and the same exit status over this tree (the self-lint), over the tree with a file named, with a missing file named, with a directory named (today's `clean`, kept until its fix), from a subdirectory, and over a fixture with nested bolt.bend files at different levels.
- `tests/bare.bend` and `bolt/lsp/tests/levels.bend` still pass unchanged.
- Every PROOF.bend checks, and each new law is mutation-checked.

## Trust

The PR that lands the planner adds one row to the trust boundary, in ez's words:

| ID | Assumption | Why it is trusted |
| :---- | :---- | :---- |
| BOLT-TRUST-9 | Each interpreter answers the World's questions and executes plans faithfully. | It makes no decisions and is kept small enough to review line by line. The listing and read effects it calls are BOLT-TRUST-3. |

The check, CLI and LSP planners cite the same row.

## Work packages

1. **WP1: the planner.** `bolt/lint/world.bend`, `bolt/lint/plan.bend`, the interpreter in `bolt/lint.bend`, `bolt/glob.bend` deleted, BOLT-TRUST-9. Laws: the tie, SCOPE-2, SCOPE-5, OUT-3 (with REVIEW-P3's wording), OUT-4, OUT-5 for `Unread`. Byte-identical.
2. **WP2: the walk.** SCOPE-1 and SCOPE-3. No behavior change.
3. **WP3: `fix(config)`: resolve paths against the working directory.** The World gains `cwd`; CFG-4's law; the relative-path finding in bolt-spec.md becomes a changelog entry.
4. **WP4: `fix(lint)`: a directory named on the command line is a `read` finding.** `Answer` gains `Directory{}`; OUT-5's law covers it.

## Alternatives considered

**Functions in the World** (`list: String -> Maybe<..>`, `read: String -> Maybe<String>`). Laws over every function are as general as laws over every reply list, but a function cannot be printed or compared, and ez already runs the data form. Rejected for consistency with ez.

**A pre-filled World** (bolt-spec.md's first sketch: `dirs` and `files` maps filled before planning). The interpreter would have to know which directories and files the planner needs, which is the walk and the candidate logic again, outside the laws. The demand loop keeps those decisions in the planner.

**Keep grading per finding.** Byte-identical by construction, but it needs a round after the lint to ask for the candidates of the findings' paths, so every file is parsed twice. Asking the candidates of every source up front (REVIEW-P1) grades the same findings the same way with one parse.
