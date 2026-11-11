# bolt

The linter, written in Bend over the `syntax/` tree and binder, and the one
binary (`main.bend`) that is also `bolt check` and `bolt lsp` ([lsp/](lsp/)).
It enforces what the checker does not: comments, unused names, the
binder-vs-def trap, leftover holes, whitespace, recursion that is strict
where it should stop early or quadratic where it should be linear, unary
`Nat` blowups, silent wrong answers (`Map.put`, `\033`, unreachable arms),
foreign defs missing a lane, and laws that reach every def (IO included). Install:
`bend main.bend -o bin/bolt.bin` at the repo root (README.md there).

    bolt                every .bend file under the current directory
    bolt a.bend b.bend  the files given
    bolt check a.bend   the checker's errors, in the same shape
    bolt lsp            the language server
    bolt help           usage

Each finding is one line, `path:line:col: level: CODE: message`, with line
and column 1-based so a terminal can jump to it; then `clean` or the counts.
`CODE` is the rule's stable id (`S003` is `wrap`). In an editor the same
finding is source `bolt(style:wrap)` and code `S003`.
A path that cannot be read, a missing file or a directory named on the
command line, is a `read` finding (`Cannot read this file.`), graded with
correctness. The exit code is 1 when anything was an error. `nix profile install
github:Emerging-Patterns/bolt` is what puts it on the PATH as `bolt`.

## bolt.bend

What bolt enforces, and how hard, is the project's to say, in a `bolt.bend`
at its root. Each file is graded by the nearest `bolt.bend` above it (its
directory, then each parent up to `/`), so a monorepo can set one at the top
and a project can override below. A relative path is resolved against the
working directory first, so the same file is graded the same way whether bolt
runs from the project root, a subdirectory or elsewhere. The file is plain Bend that `bend` can check: a
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

| group         | rules                                                                  | default |
|---------------|------------------------------------------------------------------------|---------|
| `correctness` | `hole` `pick` `put` `arms` `escape` `twice` `setting`                  | error   |
| `suspicious`  | `unused` `eager` `concat` `fromrev` `prefix` `empty` (`thunk`: opt-in) | warn    |
| `perf`        | `strings` `chars`                                                      | warn    |
| `style`       | `doc` `space` `wrap` `param` `noqa` (`transcong`: opt-in)              | warn    |
| `laws`        | (`coverage`, `closed`: opt-in)                                         | warn    |
| `pedantic`    | `foreign` `strict` `fuel` `index` `rewalk` `tail`                      | off     |

The stable codes, assigned once (do not renumber):

| code | rule | code | rule | code | rule |
|------|------|------|------|------|------|
| C001 | retired | U001 | `unused` | S001 | `doc` |
| C002 | `hole` | U002 | `strict` | S002 | `space` |
| C003 | `pick` | U003 | `eager` | S003 | `wrap` |
| C004 | `put` | U004 | `concat` | S004 | `param` |
| C005 | `arms` | U005 | retired | S005 | `noqa` |
| C006 | `escape` | U006 | `fuel` | S006 | `transcong` |
| C007 | `twice` | U007 | `index` | L001 | `coverage` |
| C008 | `strings` | U008 | retired | L002 | `closed` |
| C009 | `chars` | U009 | retired | L003 | retired |
| C010 | `foreign` | U010 | retired | L004 | retired |
| C011 | `setting` | U011 | `rewalk` | L005 | retired |
| | | U012 | retired | P001 | `tail` |
| | | U013 | retired | | |
| | | U014 | retired | | |
| | | U015 | `thunk` | | |
| | | U016 | `fromrev` | | |
| | | U017 | `prefix` | | |
| | | U018 | `empty` | | |

Letters: `C` correctness, `U` suspicious, `S` style, `L` laws, `P` pedantic,
for the group a rule had when its code was assigned. A code names the rule,
not its group, so a rule that moves keeps it: `strings` and `chars` (C008,
C009) are `perf`, what is slow but never wrong; `foreign` (C010), `strict`
(U002), `fuel` (U006), `index` (U007) and `rewalk` (U011) are `pedantic`,
where too few of their findings were defects, or their fix was slower, to
report by default.

`pedantic` is advice that is noisy on idiomatic code: off until a project
asks for it. L004 was `quantify`, the opt-in strict mode of `closed`;
`closed` is strict itself now, and L004 is never reused. U014 was `argv`,
a check on `IO.args()` readers, retired before its first release: every
reader already drops the program, and it could not tell one that does from
one that does not. U014 is never reused either. L005 was `trace`, which
held a SPEC.md table (now docs/SPEC.md) and the laws' ID tags to each other; a guarantee is
named by its law file now, and L005 is never reused. U008 `table`, U009
`hoist`, U010 `ring`, U012 `unit` and U013 `scan` were retired when an audit
of public Bend found none or few of their findings real (`index` still
leaves a get on a fixed table alone, src/rules/table.bend). L003 `unsafe`
was retired since bend 2.0.32 itself fails a proof that reaches an
`@unsafe` or foreign def. None of these codes is reused. A bolt.bend that
still sets one of them gets a `setting` finding (C011); delete the def.

`thunk` and `transcong` are opt-in: they are in their groups, but no group
setting reaches them; only `def thunk()` or `def transcong()` turns each on.
So are `coverage` and `closed`: what every def must be named by a law, and
whether a law with no binder is allowed, are a project's policy, not a
defect, so a project that keeps laws turns them on by name (`def
coverage() -> String: "warn"`). An unknown level word grades as an error, so a typo shows. A `bolt.bend` is
read, never linted. A setting whose name is no rule's slug and no group
sets nothing, so `setting` (C011) reports it. Without one, the defaults apply. This repo's
[bolt.bend](../bolt.bend) sets every group to error and turns the opt-in
laws rules on: the gate must see `clean`.

## Suppressing a finding

A comment on a finding's own line that names its code silences it, as in
ruff:

```
def run(args: List<String>) -> IO(Unit):  # noqa: L001 IO entry point
```

The comment is `#`, any spaces, `noqa:`, then one or more codes split by
commas (spaces around them allowed), then any text. Codes are the stable
ids above, case-sensitive, and a comment may name several
(`# noqa: U002, U003`). Only a real comment counts, as the lexer reads it:
`noqa` inside a string literal is text. The filter runs once every rule has
run, the project rule (`coverage`) included, and a
silenced finding is neither printed nor counted, so it changes neither the
summary nor the exit code. No rule reads the comments: what each rule finds
is the same with or without them. The editor applies the same filter.

A noqa comment that silences nothing is itself a finding, `noqa` (S005): a
bare `# noqa`, which names no code, and each code that silences nothing on
its line, an unknown code included. A project rule's code is judged only
when bolt lints the whole tree; over files named on the line, and in the
editor, those rules see only part of the laws, so their silence proves
nothing. `noqa` runs last, and no comment silences it (`# noqa: S005` is
itself reported). Like any rule, `def noqa() -> String: "off"` in a
bolt.bend turns it off.

## Rules

Each rule is a module under `rules/<group>/` with `check(src) -> List<Finding>`,
listed in `rules.bend`: the directory a rule sits in is the group it belongs
to. Adding a rule is adding a file, a line in `rules.bend`, and a row in
`codes.bend` (the stable code). A project rule has
`check(ds) -> List<Finding>` instead and sees many files at once, as
digests (`rules.bend`'s `project`).

The project rules run per package (laws/PackagesScoped.bend). Over the
whole tree, a package root is `.` and every other directory the walk reads
that holds a `main.bend`, and a file belongs to the nearest root at or above
it. `coverage` runs on one package's files at a time. Over files named on the line, `.` is the only package. So a repo with
nested packages, each with its own laws, lints in one run from the top, and
a law covers only defs of its own package.

Rules read a file's role from the imports, never from where it sits. A law
file is a `LAWS.bend` or a file one reaches through relative imports; a
proof file is a `PROOF.bend` or a file only a `PROOF.bend` reaches. A file a
package's `main.bend` reaches, or one no `LAWS.bend` or `PROOF.bend`
reaches, is code, even when a law imports it to state laws about it. So a
`LAWS.bend` of nothing but `import ./laws/<Name>.bend` lines makes those
files law files, and a proof may state lemma laws of its own.

The walk is over the whole tree under the working directory, even over files
named on the line: bolt reads every `.bend` file there for its imports
(lexed, never parsed), and each named file the walk does not find (one
outside the working directory), each file once, and lints only the files
named. A path is matched to its file however it is spelled (`a.bend`,
`./a.bend`, or absolute under the working directory). So a file named beside
a `LAWS.bend` that imports it is still code when a `main.bend` the run does
not name imports it, and a file under `laws/` named without its `LAWS.bend`
is still a law file. The editor reads the same graph as `bolt <path>` when a
document is opened or saved, from the directory it runs in, and keeps those
roles for the edits in between (laws/LspKeepsRoleMarks.bend), so a change
that adds or drops an import changes a file's role at the next save.

A rule is handed a [`Src`](src.bend), not the text: the path, the text, and
the file's tokens, tree, binder and outline, each read once for the whole
set. A tree parse of a 156 KB file costs 1.5 s here, so twenty rules that
each parsed the text made the linter twenty times slower than it is now.
A project rule is handed one [`Digest`](rules/digest.bend) a file instead:
its phases use the whole list several times, and a `+` reuse copies what it
is given, so handing them the parsed `Src` duplicated every tree (100 files
cost 362 s, growing faster than the count; 28 s now). The digest carries
only what those rules ask: the paths, the top-level defs and types, what the
laws name, the imports and the laws.
What the rules share, `rules/calls.bend` (the recursion rules),
`rules/tokens.bend`, `rules/imports.bend` and `rules/digest.bend`, sits
beside the groups. The cost rules built on `rules/calls.bend` (`pick`,
`strict`, `eager`, `tail`, `concat`, `index`, `rewalk`, `thunk`) skip what never runs: a law file, a proof file, and a def
that is a proof wherever it is, one that returns a proof (`-> {a == b : T}`)
or one written with no type at all (`def f(x, y):`, no `:` among its
parameters and no `->`), which is how Bend fills the law named `f`.

- `doc` — every top-level def, type and law has a comment block right above
  it: column-0 `#` lines with no blank line before the item, or before a run
  of column-0 `@` lines (`@unsafe`) right above it. A block of bare `#` lines
  counts. Helpers (dotted names like `show.go`) ride on their
  parent's, `main` needs none, a proof file fills laws that a law file
  documents, and a test (under `tests/`) is documented by its header and its
  check names.
- `unused` — a name bound by a let, a do-bind, a lambda or as a parameter is
  never used. Exempt: pattern binders (naming every field of `Tok{k, t, l, c}`
  reads better than `_`), names starting with `_`, erased parameters (`-x`),
  a law's `for` names, and every parameter of a foreign def, one whose body's
  first statement is `import` (its C and JS read them), wherever its
  header's `->` and return type fall. A name read in a dependent arrow's
  types (`@+x: U32 -> S`) is a use.
- `hole` — a TODO hole left in code, the one bend counts in "1 TODO found." /
  "N TODOs found." (under `SOME PROOFS FAIL`, exit 1):
  `?` and then `TODO`, with spaces, newlines or comments allowed between
  (`?TODO`, `? TODO`). `?todo` and `?TODO_later` are other names, a type
  error to bend, and are not reported. A law file is exempt: its laws are open
  claims by convention, filled by a proof file.
- `space` — trailing whitespace, a tab, or a line over 120 wide. Width counts
  a string literal as two characters: a long fixture or message does not make
  a line hard to read, code does. A comment counts at its full width. `#|`
  trailers are data and exempt from the width only: trailing whitespace on a
  `#|` line is still reported. A tab is reported anywhere, inside a string
  literal too.
- `wrap` — a def header's shape. A one-line header over 120 wide must break,
  counted the same way as `space` (a string literal is two characters), except
  that a comment counts nothing. The header is the text through its `:`; a
  comment after it is not part of it, so `def u(aa: U32) -> U32: # note` is a
  one-line header. A header breaks when a line break of its own is in it; one
  inside a string literal belongs to the string. A one-line header
  that fits stays one line however many parameters it has. A header that
  breaks puts `(` at the end of the first line and one parameter on each
  following line, then `)` and the return type on a line of their own after
  the last parameter. Several parameters on a line, a parameter left on the
  `(` line, a parameter split across lines, a `)` on the last parameter's
  line (`bb: U32) -> U32:`), a `)` with no `->` right after it on its line
  (the return type on a line of its own; a def that fills a law has no
  return type, so `):` ends it), or a parameter list across lines with no
  parameter in it (`def none(` then `) -> U32:`: join it onto one line), is
  a finding.
- `param` — a parameter name shorter than 2 characters. A single uppercase
  letter is a type parameter (`A`, `T`), and a bare parameter or one typed
  `Quant` is a quantity. Locals, patterns and a law's `for` names are not
  parameters. A proof file's parameters are the names its law bound.
- `noqa` — a noqa comment that silences nothing (see "Suppressing a
  finding"): a bare `# noqa`, or a code it names that no finding of its file
  on its line has, an unknown code included, one finding per code, at the
  comment. It reads the other rules' graded findings, so it runs after them
  and after the filter, and nothing silences it. A project rule's code is
  judged only over the whole tree.
- `pick` — a def calls itself in a branch of a `Bool.pick`. Bool.pick is a
  function: both branches run whatever the condition. In both branches, two
  recursive calls a step is 2^n work (a per-token scan took 20 s this way and
  20 ms as one pass); in one branch, the call runs even when the condition
  says stop, so a search never exits early. Bind the call once above the pick
  (`+more = go(rest)`) and pick between `x <> more` and `more`, or hand a
  helper that matches on the Bool. A self-call is the def's name followed by
  `(..)`, so a parameter named like the def is not one. A pick nested in a
  branch of one already reported is not reported again. A search that binds
  its recursion above the pick (`+more = go(rest)`, then
  `Bool.pick(T, hit, x, more)`) is reported too, at the let: the walk runs
  even when the head is the answer (ez's `text.at`: native 8.81 s, 4.15 s
  once it stopped). That is a let `x = name(..)` or `+x = name(..)` of the
  self-call alone, where the first statement after it in the same chain that
  reads x is a `Bool.pick(..)` alone whose condition and then branch do not
  read x and whose else branch does. A filter reads x in both branches and
  is not reported; nor is a do-bind (`x <- ..`), a let and a pick in
  different case arms, or a self-call that holds a `Bool.pick` on the pick's
  own condition (it makes the call cheap on purpose). When the else branch
  is x alone, carry the test as a Bool into the next call
  (`go(rest, k, test(h))`) and `match hit` first, as `strict` says; else
  match on the condition in a helper that takes it as a parameter. A `Lazy`
  thunk (`Lazy.stop(T, hit, x, _u => go(rest))`) stops early but leaves the
  loop on every step, and measured slower. Law files, proof files and defs
  that are proofs (they return a proof, or have no type) are exempt.
- `strict` (pedantic) — a self-call inside `Bool.and`/`Bool.or`, or either side of
  `&&`/`||`, matched by exactly those texts (a qualified `Base.Bool.or` is not
  seen). They are functions too: both sides always run, so there is no
  short-circuit (a game's overlap test went 31 -> 55 fps once the call moved
  out). Bind the call above, or match on the first Bool. A self-call in a
  lambda body (`_u => go(rest)`, a `Unit -> T` thunk) is not counted: the thunk
  does not run eagerly, unless its own body holds `&&`/`||`.
- `eager` — a branch of a `Bool.pick` holds a call to another def of the
  same file that loops (it calls itself, or reaches a def that does).
  Bool.pick is a def too, so the branch runs whatever the condition says (a
  game's overlap test in a branch went 31 -> 55 fps once it moved out; one
  `gaps(..)` in a branch here cost 88 s of a 100 s run). `pick` sees only the
  self-call and `strict` only Bool.and/or, so the call to a neighbour is this
  rule's. Bind it above the pick, or branch with `match` on the condition.
  For a search that recurses, carry the test as a Bool into the next call
  (`go(rest, k, test(h))`) and match on it first, so the step stays a loop;
  a `Unit -> T` thunk around the recursive call leaves the loop on every step
  (`thunk`). `src/lazy/lazy.bend`, which matches on the Bool and applies a
  thunk in one branch, stays right for work that does not recurse. A call
  into Base is not counted: a def of the file is the cheap proxy for work the
  file itself wrote. Nor is a call in a lambda's body (from `=>` to the next comma of
  its group), which the pick does not run; an argument after that comma
  counts again.
- `concat` — a self-call whose argument grows a carried parameter by
  appending (`acc ++ x`, `List.append(&2, T, acc, ..)`) in that parameter's
  own position: each step copies the accumulator, so the walk is quadratic.
  Prepend with `<>` and reverse once. A parameter appended into another slot
  is not counted. The append may sit inside parentheses (`(acc ++ x)`), or
  be bound by a let first (`+q = acc ++ x`, then `go(t, q)`): a lone name
  reads the nearest `q = ..` / `+q = ..` before the call in its block or an
  enclosing one, so a later let of the name shadows it and a let in another
  case arm is not seen. Typed and destructuring lets, do-binds and pattern
  binders are not followed. The same append passed through a continuation
  is reported too: an argument of a call of a function-typed parameter
  (`rest(file, List.append(&2, U32, acc, b <> t))`, where `rest` is
  `fl => a => slurp(f, fl, a)`) that appends onto any parameter of the def,
  read the same way. A `+` parameter the body reads more than once is left
  alone (`path ++ "/" ++ name` builds a value used elsewhere, not an
  accumulator). Prepend each chunk and reverse once at the end (ez's slurp,
  native: 14.75 s -> 0.36 s at 16 MB).
- `index` (pedantic) — `List.get`/`String.get` at a computed index inside a def that
  calls itself: the list is walked again each step. Walk the cells instead
  (one sort phase went 39 s -> 0.9 s). A get anywhere in the def is
  reported, one in a base arm that runs once included. A literal index of
  any size is exempt, and so is a `List.get` on a fixed table (a literal, a
  sized array, or `List.replicate` / `Array.new` / `List.range` with a
  constant count: src/rules/table.bend); a `String.get` always stays here. A get that is the def's own self-call (the
  step of a def named `List.get` or `String.get`, as Base's are) is exempt.
- `rewalk` (pedantic) — one straight piece of a def calls the same walk twice on the
  same argument, and one result is used only for a single value (one index,
  one field, or a let read only that way) while the other result is kept
  whole. Take the value from that other result. A let of a name the
  argument uses between the two calls makes them different walks, and so
  does a different case arm.
- `thunk` (opt-in) — a lambda whose body is exactly a self-call and whose
  parameter the call does not read, passed as the one lambda of a call: a
  `Unit -> T` thunk such as `Lazy.or_else(hit, _u => go(rest, k))`. The
  closure is allocated on every step and the call in it is not a tail call of
  the def, so the search leaves the loop each time round (bend 2.0.34, 500
  misses over 100k cells: JS 2.40 s against 0.28 s, native 1.18 s against
  0.76 s). Carry the test as a Bool into the next call, `go(rest, k,
  test(h))`, and match on it first: the step is then a tail call and compiles
  to a loop. `Lazy.*` stays right for guarding work that does not recurse.
  A dispatch, a call given two or more lambdas (`Lazy.either(T, c, _u =>
  go(a), _v => go(b))`), is left alone: one carried Bool does not replace it.
  Exactly: in the kids of a `(` group whose arguments (split at their commas)
  hold exactly one with a `=>` leaf of its own (not inside a bracket), a name
  leaf (the parameter), `=>`, the def's name and its `(` group, with the kids
  ending there or going on with a comma, and no name leaf in the group
  spelling the parameter or the parameter then a dot. A body that does more
  than the call (`_u => Some{go(t)}`), a continuation that reads its
  parameter (`a => go(f, a)`), or a lambda that is no call's argument
  (`x = _u => go(t)`) is left alone; `_ => loop(n)` is not, since the rule
  reads the shape and not the type.
- `fromrev` — `String.from_list(List.reverse(..))`: among the significant
  tokens, `String.from_list`, `(`, `List.reverse` and `(` right after one
  another, one finding on the first. A buffer of chars consed on the front
  and then reversed and read into a String walks the buffer twice and builds
  a list only to throw it away; `String.from_list` is not a tail call either,
  so a long buffer runs the JS lane out of stack. Fold the buffer onto a
  String with `SCon` in one pass (`src/rchars.bend`, bolt's own):

  ```bend
  def text.go(buf: List<&2, Char>, acc: String) -> String:
    match buf:
      case Nil{}:
        acc
      case Con{h, t}:
        text.go(t, SCon{h, acc})
  ```

  Called as `text.go(buf, SNil{})` (bend 2.0.34, a 100k-char buffer 200
  times: native 0.35 s against 0.17 s; JS at 20k chars 4.6 s against 3.1 s,
  and at 50k the two-pass form overflows). Anything between the four tokens,
  another `(` included, is not the shape, and neither is `List.reverse.go`.
  A law file or a proof file is exempt.
- `prefix` — `String.eq(String.take(s, 4n), "ERR ")`, either argument order:
  among the significant tokens, a dotted `String.eq`, `(`, `String.take`,
  `(`, the argument `s` (every token up to the first comma outside the
  brackets it opens, so a call such as `String.drop(m, 4n)` is one
  argument), a Nat literal `k`, `)`, `,`, a string literal and `)` (or
  `String.eq`, `(`, the literal, `,`, then the take and `)`), one finding on
  `String.eq`, and only when `k` is the literal's length (an escape, `\n`
  or `\u{1B}`, counts as one char), written as decimal digits and `n`. The
  take copies `k` chars into a new String only to compare them;
  `String.starts_with(s, "ERR ")` (Base) walks `s` in place and gives the
  same answer for every `s`, `False` when `s` is shorter (bend 2.0.28, 1M
  calls: native 1.14 s against 1.00 s, JS 1.68 s against 1.40 s). A take of
  another length is a different bug and is left alone, and so is a
  qualified or aliased name and a non-literal on the other side. A law file
  or a proof file is exempt.
- `empty` — `Nat.is_eq(List.length(.., x), 0n)` or
  `Nat.is_eq(String.length(x), 0n)` as an argument (right after a `(`, `[`,
  `{` or `,`), x a plain name read again after it in the same group: among
  the significant tokens, a dotted `Nat.is_eq`, `(`, then a dotted
  `List.length`, `(`, tokens up to its matching `)` whose last two are `,`
  and x, or a dotted `String.length`, `(`, x and `)`; then `,`, `0n` and
  `)`; then x as a plain name before the bracket that closes the group.
  One finding on `Nat.is_eq`. Base's lengths count every cell (and are not
  tail calls); `List.is_empty(.., x)` and `String.is_empty(x)` take the same
  arguments, look at one cell and give the same Bool. Only a kept x is
  reported, because only then does the fix pay on both lanes: the native
  lane frees a list the program never walked more slowly than it walks one,
  so where the test is x's last use the walk is the cheaper way to free it
  (bend 2.0.38, a 0-1000 char String: kept 1.57x faster native and 1.31x
  JS; dropped 0.27x native, 1.65x JS). A test whose group reads no x after
  it, one that reads x only before it, and one outside any group (`v =
  Nat.is_eq(..)`) are left alone. A law file or a proof file is exempt, and
  so is a `law` and a def that is a proof (`def f(x):`, or one that returns
  `-> {..}`) in any file: from its keyword to the next `def`, `type` or
  `import`.
- `put` — `Map.put`. It is Base's internal helper: at a leaf it keeps the old
  key and replaces the value without comparing, so a new key silently
  overwrites another entry. `Map.set` compares. A file that defines
  `Map.put` (`def Map.put`, Base's own source) is exempt.
- `escape` — `\0` then a digit in a literal (`"\033"`). Bend has no octal
  escape: that is NUL followed by the digits. Write `\u{1B}`.
- `strings` (perf) — a `match` over string-literal arms totalling more than 64
  characters: compile time and memory blow up with the characters (45 chars
  cost 0.8 s and 0.35 GB here, 480 chars 12 s and 4.8 GB). Map the string to
  a sum type once. Only the first match column is read, and a literal with no
  closing quote is not counted.
- `chars` (perf) — a `match` with more than eight character-literal arms
  (`case '.':`). `Char` is `Chr{code: U32}`, so each arm is a U32 literal
  inside a constructor pattern, and the C backend pays about 90 MB for one
  (eighteen arms cost 1.57 GB and 8.3 s here, 0.10 GB and 0.7 s once
  rewritten), compounding through every def downstream. It is the literals,
  not the arms: a match over eighteen constructors costs nothing measurable.
  Compare `Char.to_u32(c)` instead. Bind the fallback above the comparisons
  so `eager` does not fire on it, and take `+c: Char`, since the code point
  and the fallback both consume it. Where the arms carry linear values, leave
  the match alone: a cascade would break linearity and do every branch's
  work. Only the first match column is read, and only an arm whose pattern
  opens with a character literal counts (`case Con{'x', t}:` does not).
- `twice` — a case pattern that opens with the same literal twice
  (`case 10 <> 10 <> ..`) in a recursive def: the checker hangs. Match one
  element a step. A def is recursive when its body calls it (`name(..)`); a
  parameter named like the def is not a call. Only the first match column is
  read.
- `arms` — a case arm that an arm above it in the same match already
  matches, so it never runs. The checker takes it silently and the match
  answers with the arm above: put the narrow arms first, or delete the one
  that cannot run. Two checks, one finding an arm. The Nat check: a later
  `Nat` arm that an earlier `kn+p` already matches (`Succ{p}` and `Succ{_}`
  count as `1n+p`), in a single-scrutinee match. The cover check, in a
  match of any number of scrutinees: an arm whose pattern an earlier one
  covers, reading both part for part, where a binder of the earlier (a
  plain name or `_`, a `+` before it dropped) stands for a whole item of
  the later (a binder, a literal, a constructor with its `{..}`, a group,
  `kn+p`) and, when no `<>` follows the binder, for every `<> item` after
  it too. So it reports any arm under a lone binder (`case other:` then
  `case Con{h, t}:`), the same literal or constructor twice (`case 139:`
  in a table of opcodes, `case True{}:`), one shape under other names
  (`case Some{x}:` then `case Some{y}:`; two six-item `a <> .. <> Nil{}`
  patterns, each meant for its own mode), and `case h <> t:` above a
  longer list pattern. The message names the line of the arm above. An
  inline body (`case 139: 1`) is not part of the pattern. What it cannot
  read is not judged: a string literal is never the same as another, so
  `case "ab":` twice is not reported (what a string says changes no
  finding), a pattern holding any other operator (`"GET " ++ rest`) or an
  angle bracket covers nothing, `[a, b]` and `a <> b <> Nil{}` are
  different shapes, and a redundant `(x)` is not a binder. It never asks
  whether the arms above together cover an arm, only whether one of them
  does.
- `foreign` (pedantic) — a foreign def with a `.c` body and no `.js` body, or the
  reverse: the missing lane cannot run it. A file headed `# lanes: native`
  needs no `.js`: that exact line must be one of the comment lines before the
  file's first non-comment line.
- `setting` — a setting in a bolt.bend whose name is no rule's slug and no
  group (`def wrp() -> String: "off"`, or a retired name such as `quantify`
  or `shadow`): grading only looks names up, so it sets nothing, and the
  typo fails open. It is reported once for each bolt.bend that grades a
  file of the run, at that bolt.bend's path and the setting's `def` line,
  after the per-file findings and before `coverage`'s.
  It is graded by that bolt.bend like any rule (`def setting() -> String:
  "off"` there turns it off). A bolt.bend is read, not linted, so a noqa
  comment in one silences nothing. bolt runs it; the editor does not.
- `fuel` (pedantic) — a `Nat` literal (digits, then `n`), or `U32.to_nat` of a U32
  literal (`U32.to_nat(100000)`), passed in a call, `name(..)`, to a fuel
  parameter of a def of the same file. A fuel parameter is known by its name
  alone, the one before its colon: `fuel`, `gas`, `steps` or `budget`, or
  any name starting with `fuel`. Input past it is cut short with no error:
  derive the fuel from the input. In a law it is worse: a lemma proved over
  every fuel, used at a big fixed one against a goal written another way,
  overflows the checker's stack (bend 2.0.33/2.0.34). A literal of any size
  counts, `3n` included. Only an argument that is the literal alone, or
  `U32.to_nat(` it `)`, counts, so a let-bound literal and `(7n)` are not
  seen. A def's own calls are exempt, and so is a def that returns an
  effect: a header with `->` then the name `IO` (`-> IO(Unit):`), or one
  that ends in `->` with `IO(..):` on the next line. Its fuel bounds reads,
  frames or retries the outside world sets (a drain of 256 datagrams a
  tick, a read of 100000 chunks), not the size of an input it was given.
- `tail` (pedantic) — a self-call that is not a tail call, in a def whose
  first live parameter is a `List` or a `String`. On a long one the JS lane
  overflows its stack (a 48 KB header crashed a server; ~4,900 entries and
  ~64K elements elsewhere). Carry an accumulator. The test is on that
  parameter's type alone, never on whether the self-call shrinks it.
  Everything inside a `Bool.pick(..)` is skipped.
- `closed` (opt-in) — a law in a law file with no `for`/`exs` binder. A closed law,
  an equality (`{lhs == rhs : T}`, including `IO(T)`) or not, holds for the
  one input it names: a unit test the checker runs, not a guarantee.
  Nothing exempts one: quantify it, or delete it.
- `coverage` (project, opt-in) — in a package that states laws (a LAWS.bend among its
  files), a def or a type that no law of the package reaches. It is `coverage`, not `law`,
  because `law` is a Bend keyword: `def law()` is no def, so a bolt.bend
  could never set it by name. IO is no exemption: a def that
  returns `IO(..)` is graded like any other (a law can state an IO equality
  or quantify over an IO value), and so is every pure def in a module that
  also does IO, or that says "IO" in a comment. What is out of scope is
  decided by the def's name, its signature and the file's path, never by
  the file's text.
  A law names a def when
  it is a quantified law in a law file and its binders or statement use the
  def, through the law file's import alias (`Nav.text_of` in a law file that
  imports `src/lsp/nav.bend` as `Nav` names its `text_of`) or in the law's own
  file. A closed law, a law's own name, and a law outside a law file (a proof
  file's lemmas included) name nothing. A law reaches a def it names, and every def
  a reached def calls: a use on that def's lines, in its file or behind an
  import alias of a file in the run, so a helper that a law exercises only
  through its caller is covered, and one no law reaches is not. A type is
  covered when such a law or a reached def names it or one of its
  constructors (`M.Sq{nn}` covers `type Shape` with `Sq{..}`); naming
  another def of its module does not cover it, and a type reaches nothing.
  Out of scope: helper defs (dotted names; they still carry the reach to
  what they call), defs that are proofs (one whose signature returns a
  proof, `-> {a == b : T}`, or one written with no type, which is how Bend
  fills the law of its name: the law states its property; such a def is not
  graded and carries no reach), tests, and the law files (their defs carry
  the reach); a dotted type is graded. `main` is a def: a law that names it covers it. A
  project without a LAWS.bend is not under law.

## Proposing a rule

A new rule, or a widening of one (judged on the hits it adds), is measured
against public Bend 2 code other than bolt's own tree, such as the repos
[awesome-bend](https://github.com/777genius/awesome-bend) lists. It ships
when it meets all of these:

1. **Seen.** The shape occurs at 5 or more sites across 2 or more
   independent repos. The issue's own example does not count.
2. **Precise.** A prototype matcher over that code, every hit (or 30 at
   random) read by hand, is 95% or more true positives, and each
   false-positive class has an exclusion bolt can test from tokens. A rule
   that needs types or data sizes bolt does not have fails here.
3. **Legal fix.** The suggested fix is mechanical, type-checks and keeps
   behavior on every true positive, and the message names it, not just the
   smell. Where bolt cannot tell from tokens that the fix is legal, the rule
   does not suggest it.
4. **Faster, only for a perf-shaped rule.** A rule is perf-shaped when
   its message says the code is slow or costly, in time or memory, at run
   or at build, whatever group it sits in (`concat`, `prefix` and `empty`
   are, though they are `suspicious`). For such a rule the fix, applied to
   a real hit on a realistic input, is clearly faster on at least one lane
   (JS or native), repeatably and beyond noise, and no measured hit is
   slower on either. No other rule is measured: one whose case is a wrong
   answer, a failure, or the same thing said more plainly stands on the
   other four, and is not turned down for being no faster.
5. **New.** Neither the Bend checker nor another rule already reports it.

A public commit that rewrites a real instance into the fix strengthens the
case, but its absence is not held against a rule: most Bend code is written
with agents, and a shape nobody's agent flags stays unfixed whether or not
it is a defect.

A guard is the one exception to **Seen**: a rule whose shape is rare but
whose miss is a silently wrong result that `bend` never reports (`arms`,
`escape`, `setting`) may ship on fewer sites, as long as it is **Precise**,
its fix is legal, and it is **New**.

A rule is on by default only at near-zero false positives; anything less
certain starts opt-in or in `pedantic`. A shipped rule that projects often
`# noqa` is demoted or reworked.

## One binary

`bolt` is also `bolt check file..` (the checker, `bend`, on each file, its
errors in the same shape, `path:line:1: error: message`; a file bend could
not be run on is `path:1:1: error: could not run bend`, an error like any
other, never `clean`) and `bolt lsp`
(the [language server](lsp/), over stdio). `main.bend` parses the command
line with [shake](https://github.com/Emerging-Patterns/shake)
(`import shake@0.6.0.0/main.bend`, shake v0.6.0, its
interface only) and dispatches on
the selected command; a first word that names no subcommand is a file, so
`bolt a.bend b.bend` lints those files, and with no files at all `bolt`
lints every `.bend` file under the current directory (the walk in
`lint/plan.bend`, which never descends into a hidden directory or
`node_modules`). The lint is a pure planner, `lint/plan.bend`, over a
World of answers, `lint/world.bend`, and a thin interpreter, `lint.bend`,
that answers the planner's questions (a directory listed through
`walk/disk.bend`, a foreign effect in `dir.c` and `dir.js`; a file read
through `lsp/files/`) until it asks for nothing more, then prints the
plan's lines and exits with its status. `bolt help` prints usage. A run
that found errors exits 1. Bend's runtime takes its own flags out of the
line before the program sees it, so `bolt lsp` reaches `main` as `lsp`.
With no `--gpu` that launch is `--gpu off` (the cores); `--gpu on` or
`--gpu 4GB` asks for the device.

## In the editor

[lsp](lsp/) runs the per-file rules on each edit and publishes the
findings at the levels the nearest `bolt.bend` gives them: errors red,
warnings yellow, off ones not at all, less what the file's noqa comments
silence, then `noqa`'s own (never on a project rule's code). A finding's code is its stable id
(`S003`) and its source is `bolt(group:slug)` (`bolt(style:wrap)`). The project rules (`coverage`) need every
file, so they run in bolt alone.

## In the gate

Proveable claims (including IO equalities) are laws in `LAWS.bend` /
`PROOF.bend`, not `#|` tests. `tests/bare.bend` is host/integration: it
ends by running bolt over the whole repo and must see `clean`. The binary
it lints with is the one it has just built from the tree under test, never
whatever `bolt` is on the PATH: a bolt from an older release answers
`clean` to every rule it does not implement yet, which reads exactly like
a repo with nothing wrong in it.
