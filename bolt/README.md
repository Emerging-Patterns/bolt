# bolt

The linter, written in Bend over the `syntax/` tree and binder, and the one
binary (`main.bend`) that is also `bolt check` and `bolt lsp` ([lsp/](lsp/)).
It enforces what the checker does not: comments, unused names, the
binder-vs-def trap, leftover holes, whitespace, recursion that is strict
where it should stop early or quadratic where it should be linear, unary
`Nat` blowups, silent wrong answers (`Map.put`, `\033`, unreachable arms),
foreign defs missing a lane, and laws that reach every def (IO included). Install:
`bend bolt/main.bend -o bin/bolt.bin` at the repo root (README.md there).

    bolt                every .bend file under the current directory
    bolt a.bend b.bend  the files given
    bolt check a.bend   the checker's errors, in the same shape
    bolt lsp            the language server
    bolt help           usage

Each finding is one line, `path:line:col: level: CODE: message`, with line
and column 1-based so a terminal can jump to it; then `clean` or the counts.
`CODE` is the rule's stable id (`S003` is `wrap`). In an editor the same
finding is source `bolt(style:wrap)` and code `S003`.
The exit code is 1 when anything was an error. `nix profile install
github:Emerging-Patterns/bolt` is what puts it on the PATH as `bolt`.

## bolt.bend

What bolt enforces, and how hard, is the project's to say, in a `bolt.bend`
at its root. Each file is graded by the nearest `bolt.bend` above it (its
directory, then each parent), so a monorepo can set one at the top and a
project can override below. The file is plain Bend that `bend` can check: a
def a setting, its body one string, `"off"`, `"warn"` or `"error"`.

```
# every rule an error
def correctness() -> String:
  "error"
def style() -> String:
  "error"
# but width is advice here
def space() -> String:
  "warn"
```

A group sets every rule in it; a rule set by name wins over its group; an
unset group has its default. The groups:

| group         | rules                                                                            | default |
|---------------|----------------------------------------------------------------------------------|---------|
| `correctness` | `shadow` `hole` `pick` `put` `arms` `escape` `twice` `strings` `chars` `foreign` | error   |
| `suspicious`  | `unused` `strict` `eager` `concat` `nat` `fuel` `index` `table` `hoist` `ring` `rewalk` `unit` | warn    |
| `style`       | `doc` `space` `wrap` `param`                                                     | warn    |
| `laws`        | `law` `closed` `unsafe` (`trace`: opt-in)                                        | warn    |
| `pedantic`    | `tail`                                                                           | off     |

The stable codes, assigned once (do not renumber):

| code | rule | code | rule | code | rule |
|------|------|------|------|------|------|
| C001 | `shadow` | U001 | `unused` | S001 | `doc` |
| C002 | `hole` | U002 | `strict` | S002 | `space` |
| C003 | `pick` | U003 | `eager` | S003 | `wrap` |
| C004 | `put` | U004 | `concat` | S004 | `param` |
| C005 | `arms` | U005 | `nat` | L001 | `law` |
| C006 | `escape` | U006 | `fuel` | L002 | `closed` |
| C007 | `twice` | U007 | `index` | L003 | `unsafe` |
| C008 | `strings` | U008 | `table` | L004 | retired |
| C009 | `chars` | U009 | `hoist` | L005 | `trace` |
| C010 | `foreign` | U010 | `ring` | P001 | `tail` |
| | | U011 | `rewalk` | | |
| | | U012 | `unit` | | |

Letters: `C` correctness, `U` suspicious, `S` style, `L` laws, `P` pedantic.

`pedantic` is advice that is noisy on idiomatic code: off until a project
asks for it. L004 was `quantify`, the opt-in strict mode of `closed`;
`closed` is strict itself now, and L004 is never reused. `trace` is opt-in:
it is in `laws`, but no group setting reaches it; only `def trace()` in a
bolt.bend turns it on. An unknown level word grades as an error, so a typo shows. A `bolt.bend` is
read, never linted. Without one, the defaults apply. This repo's
[bolt.bend](../bolt.bend) sets every group to error: the gate must see
`clean`.

## Rules

Each rule is a module under `rules/<group>/` with `check(src) -> List<Finding>`,
listed in `rules.bend`: the directory a rule sits in is the group it belongs
to. Adding a rule is adding a file, a line in `rules.bend`, and a row in
`codes.bend` (the stable code). A project rule has
`check(ds) -> List<Finding>` instead and sees every file the linter read at
once, as digests (`rules.bend`'s `project`).

A rule is handed a [`Src`](src.bend), not the text: the path, the text, and
the file's tokens, tree, binder and outline, each read once for the whole
set. A tree parse of a 156 KB file costs 1.5 s here, so twenty rules that
each parsed the text made the linter twenty times slower than it is now.
A project rule is handed one [`Digest`](rules/digest.bend) a file instead:
its phases use the whole list several times, and a `+` reuse copies what it
is given, so handing them the parsed `Src` duplicated every tree (100 files
cost 362 s, growing faster than the count; 28 s now). The digest carries
only what those rules ask: the paths, the top-level defs and types, what the
laws name, the imports and the `@unsafe` defs.
What the rules share, `rules/calls.bend` (the recursion rules),
`rules/tokens.bend`, `rules/imports.bend` and `rules/digest.bend`, sits
beside the groups.

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
- `wrap` — a def header's shape. A one-line header over 120 wide must break,
  counted the same way as `space` (a string literal is two characters). The
  header is the text through its `:`. A one-line header that fits stays one
  line however many parameters it has. A header that breaks puts `(` at the
  end of the first line and one parameter on each following line, then `)` and
  the return type. Several parameters on a line, a parameter left on the `def`
  line, or a parameter split across lines, is a finding.
- `param` — a parameter name shorter than 2 characters. A single uppercase
  letter is a type parameter (`A`, `T`), and a bare parameter or one typed
  `Quant` is a quantity. Locals, patterns and a law's `for` names are not
  parameters. A PROOF.bend's parameters are the names its law bound.
- `pick` — a def calls itself in a branch of a `Bool.pick`. Bool.pick is a
  function: both branches run whatever the condition. In both branches, two
  recursive calls a step is 2^n work (a per-token scan took 20 s this way and
  20 ms as one pass); in one branch, the call runs even when the condition
  says stop, so a search never exits early. Bind the call once above the pick
  (`+more = go(rest)`) and pick between `x <> more` and `more`, or hand a
  helper that matches on the Bool.
- `strict` — a self-call inside `Bool.and`/`Bool.or`, or either side of
  `&&`/`||`. They are functions too: both sides always run, so there is no
  short-circuit (a game's overlap test went 31 -> 55 fps once the call moved
  out). Bind the call above, or match on the first Bool.
- `eager` — a branch of a `Bool.pick` holds a call to another def of the
  same file. Bool.pick is a def too, so the branch runs whatever the
  condition says (a game's overlap test in a branch went 31 -> 55 fps once
  it moved out; one `gaps(..)` in a branch here cost 88 s of a 100 s run).
  `pick` sees only the self-call and `strict` only Bool.and/or, so the call
  to a neighbour is this rule's. Bind it above the pick, or take the branch
  through `Lazy.stop`/`Lazy.or_else`. A call into Base is not counted: a def
  of the file is the cheap proxy for work the file itself wrote.
- `concat` — a self-call whose argument grows a carried parameter by
  appending (`acc ++ x`, `List.append(&2, T, acc, ..)`): each step copies the
  accumulator, so the walk is quadratic. Prepend with `<>` and reverse once.
- `index` — `List.get`/`String.get` at a computed index inside a def that
  calls itself: the list is walked again each step. Walk the cells instead
  (one sort phase went 39 s -> 0.9 s).
- `table` — `List.get` or `List.set` at a computed index inside a def that
  calls itself, when the list is a fixed table (a literal, a sized array, or
  `List.replicate` / `Array.new` / `List.range` with a constant count). Keep
  it in an `Array`. A literal index, a growing list, and a data-dependent
  length stay with `index` or stay quiet, so one call is one finding.
- `hoist` — a list or array of more than eight constants, or a call that
  builds one from inputs that do not change, sits inside a def that calls
  itself and is then indexed. The build runs again on every step. Build it
  once, outside the recursion. Eight cells or fewer, and a build whose
  arguments depend on the step, are left alone.
- `ring` — a self-call replaces a binder with a drop of a constant count and
  an append (`List.drop` / `List.tail` / `String.drop` / `String.tail`, then
  `List.append` / `String.append` / `++`). Each step copies the window. Keep
  it in an `Array` and advance an index. A list the def matches as input, and
  a one-shot trim, are left alone.
- `rewalk` — one straight piece of a def calls the same walk twice on the
  same argument, and one result is used only for a single value (one index,
  one field, or a let read only that way) while the other result is kept
  whole. Take the value from that other result. A let of a name the
  argument uses between the two calls makes them different walks, and so
  does a different case arm.
- `unit` — a multiply or divide by the literal `1`, `1n` or `1.0` on a
  step that recurses, either as `*` / `/` or as `Nat.mul` / `U32.mul` /
  `F32.mul` (and `.div`, only when the divisor is one). Drop the operation.
  Any other factor or divisor is left alone.
- `put` — `Map.put`. It is Base's internal helper: at a leaf it keeps the old
  key and replaces the value without comparing, so a new key silently
  overwrites another entry. `Map.set` compares.
- `escape` — `\0` then a digit in a literal (`"\033"`). Bend has no octal
  escape: that is NUL followed by the digits. Write `\u{1B}`.
- `nat` — a `Nat` literal of 1000 or more. `Nat` is unary, so `4294967295n`
  as fuel or infinity is that many cells. Use `U32`, or `U32.to_nat` at run
  time.
- `strings` — a `match` over string-literal arms totalling more than 64
  characters: compile time and memory blow up with the characters (45 chars
  cost 0.8 s and 0.35 GB here, 480 chars 12 s and 4.8 GB). Map the string to
  a sum type once.
- `chars` — a `match` with more than eight character-literal arms
  (`case '.':`). `Char` is `Chr{code: U32}`, so each arm is a U32 literal
  inside a constructor pattern, and the C backend pays about 90 MB for one
  (eighteen arms cost 1.57 GB and 8.3 s here, 0.10 GB and 0.7 s once
  rewritten), compounding through every def downstream. It is the literals,
  not the arms: a match over eighteen constructors costs nothing measurable.
  Compare `Char.to_u32(c)` instead. Bind the fallback above the comparisons
  so `eager` does not fire on it, and take `+c: Char`, since the code point
  and the fallback both consume it. Where the arms carry linear values, as
  `bolt/lsp/frame.bend`'s do, leave the match alone: a cascade would break
  linearity and do every branch's work.
- `twice` — a case pattern that opens with the same literal twice
  (`case 10 <> 10 <> ..`) in a recursive def: the checker hangs. Match one
  element a step.
- `arms` — a later `Nat` arm that an earlier `kn+p` already matches, so it is
  unreachable. The checker takes it silently and the answer is wrong: put the
  narrow arms first.
- `foreign` — a foreign def with a `.c` body and no `.js` body, or the
  reverse: the missing lane cannot run it. A file headed `# lanes: native`
  needs no `.js`.
- `fuel` — a `Nat` literal passed to a def's `fuel`/`gas`/`steps`/`budget`
  parameter. Input past it is cut short with no error: derive the fuel from
  the input.
- `tail` (pedantic) — a self-call that is not a tail call, in a def whose
  first live parameter is a `List` or a `String`. On a long one the JS lane
  overflows its stack (a 48 KB header crashed a server; ~4,900 entries and
  ~64K elements elsewhere). Carry an accumulator.
- `closed` — a law in a LAWS.bend with no `for`/`exs` binder. A closed law,
  an equality (`{lhs == rhs : T}`, including `IO(T)`) or not, holds for the
  one input it names: a unit test the checker runs, not a guarantee.
  Nothing exempts one: quantify it, or delete it.
- `trace` (project, opt-in) — `SPEC.md`, read from the directory bolt runs
  in, and the laws agree. A requirement table is headed exactly
  `| ID | Requirement | Level | Status | Law |` and a trust table
  `| ID | Assumption | Why it is trusted |`. An ID is uppercase letters and
  digits in two or more `-` segments (`BOLT-CFG-1`). A law proves one when
  a line of its comment block is exactly that ID. A finding is a row that is
  not well formed, an ID listed twice, a Proved/proved row whose `<path>
  <law>` entry is missing, has no binder or lacks the tag, a Trusted row with
  no trust row, and a tag SPEC.md does not list as proved.
- `unsafe` (project) — an `@unsafe def` that a LAWS.bend or PROOF.bend
  reaches through its imports. There the checker prints "All terms check,
  but N defs rely on unsafe or foreign code:" and a `- name` list (2.0.16
  counted marks: "with N unsafe annotations.") and exits 0, so a gate that
  reads the exit status goes green on an unproven claim.
- `law` (project) — in a project that states laws (a LAWS.bend among the
  files bolt read), a def that no law names. IO is no exemption: a def that
  returns `IO(..)` is graded like any other (a law can state an IO equality
  or quantify over an IO value), and so is every pure def in a module that
  also does IO, or that says "IO" in a comment. What is out of scope is
  decided by the def's name and the file's path, never by the file's text.
  A law names a def when
  it is a quantified law in a LAWS.bend and its binders or statement use the
  def, through the law file's import alias (`M.join` in `core/LAWS.bend`
  names `join` of `core/monoid/service.bend`) or in the law's own file. A
  closed law, a law's own name, and a law outside a LAWS.bend (PROOF.bend's
  lemmas included) name nothing. A type is covered when such a law names it
  or a def of its module: a law about an instance names the accessors, never
  the service type. Out of scope: helpers (dotted names), tests, and the law
  files. `main` is a def: a law that names it covers it. A project without
  a LAWS.bend is not under law.

## One binary

`bolt` is also `bolt check file..` (the checker, `bend`, on each file, its
errors in the same shape, `path:line:1: error: message`) and `bolt lsp`
(the [language server](lsp/), over stdio). `main.bend` parses the command
line with [shake](https://github.com/Emerging-Patterns/shake)
(`import 0x65bf91e14c96bf0c25491d716ec9f68c/main.bend`) and dispatches on
the selected command; a first word that names no subcommand is a file, so
`bolt a.bend b.bend` lints those files, and with no files at all `bolt`
lints every `.bend` file under the current directory
(`glob.bend`, which never descends into a hidden directory or
`node_modules`, and reads a directory through the `walk/` service — a
foreign effect, `dir.c` and `dir.js`). `bolt help` prints usage. A run
that found errors exits 1. Bend's runtime takes its own flags out of the
line before the program sees it, so `bolt lsp` reaches `main` as `lsp`.
With no `--gpu` that launch is `--gpu off` (the cores); `--gpu on` or
`--gpu 4GB` asks for the device.

## In the editor

[lsp](lsp/) runs the per-file rules on each edit and publishes the
findings at the levels the nearest `bolt.bend` gives them: errors red,
warnings yellow, off ones not at all. A finding's code is its stable id
(`S003`) and its source is `bolt(group:slug)` (`bolt(style:wrap)`). The project rules (`law`) need every
file, so they run in bolt alone.

## In the gate

Proveable claims (including IO equalities) are laws in `LAWS.bend` /
`PROOF.bend`, not `#|` tests. `tests/bare.bend` is host/integration: it
ends by running bolt over the whole repo and must see `clean`. The binary
it lints with is the one it has just built from the tree under test, never
whatever `bolt` is on the PATH: a bolt from an older release answers
`clean` to every rule it does not implement yet, which reads exactly like
a repo with nothing wrong in it.
