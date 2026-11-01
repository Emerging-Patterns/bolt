# src/lint/plan: `bolt` (the lint) as a pure planner. It reads a World
# (src/lint/world.bend) and returns either the questions it still needs
# answered (`wants`) or the Plan: the lines to print and the exit status
# (`plan`). The interpreter (src/lint.bend) loops on `wants`, answering each
# question by IO, until nothing is wanted, then prints `plan`'s lines and
# exits with its status. The design is docs/rfc/bolt-lint-planner.md.
#
# With no files named, the planner walks the tree under `.` as a fold over the
# World's listings: a directory not listed yet reads as empty and is asked
# for, so each round of the loop lists one more level of the tree. Once every
# directory the walk reads is listed, it asks for the text of each source and
# of every bolt.bend candidate of their directories, each once.
# A directory's candidates are taken once it is resolved against the World's
# working directory (Config.home), so a relative path is graded by the same
# bolt.bend wherever bolt runs from.
# `wants` never parses a file; `plan` parses and lints once, and reads the
# settings of each bolt.bend that grades a directory for `setting` (C011). Once every rule
# has run and each finding is graded, the noqa comments (src/noqa.bend)
# silence what they name, and then the `noqa` rule reports the comments that
# silenced nothing.
import Base
import ../lazy/lazy.bend as Lazy
import ./world.bend as W
import ../finding.bend as F
import ../src.bend as Src
import ../role.bend as Role
import ../rules.bend as Rules
import ../rules/imports.bend as Imports
import ../config.bend as Config
import ../noqa.bend as Noqa
import ../rules/style/noqa.bend as NoqaRule
import ../rules/correctness/setting.bend as Setting

# what `bolt` prints, in order, and the status it exits with
type Plan is Data:
  Plan{lines: List<&2, String>, exit: U32}

# the lines a plan prints
def lines.of(pl: Plan) -> List<&2, String>:
  Plan{lines, _exit} = pl
  lines

# the status a plan exits with
def exit.of(pl: Plan) -> U32:
  Plan{_lines, exit} = pl
  exit

# ---------------------------------------------------------------------------
# the walk: every `.bend` file under `.`, sorted. A hidden name (`.git`,
# `.gate`, `.claude`) and `node_modules` are not descended into. The walk keeps
# a queue of directories rather than nesting, as Bend has no mutual recursion:
# one def shrinks one argument, the fuel, which bounds how many directories are
# read.

# a directory the walk never descends into
def walk.skipped(+name: String) -> Bool:
  Bool.or(String.starts_with(name, "."), String.eq(name, "node_modules"))

# an entry's name without the "/" that marks it a directory
def walk.bare(+name: String) -> String:
  String.take(name, Nat.sub(String.length(name), 1n))

# a name directly under a directory, as a path
def walk.under(+dir: String, +name: String) -> String:
  dir ++ "/" ++ name

# the sub-directories of a listing worth descending into, as paths
def walk.dirs(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, rest}:
      +more = walk.dirs(rest, dir)
      +keep = Bool.and(String.ends_with(e, "/"), Bool.not(walk.skipped(walk.bare(e))))
      Bool.pick(List<&2, String>, keep, walk.under(dir, walk.bare(e)) <> more, more)

# the `.bend` files of a listing, as paths (a directory's name ends in "/")
def walk.bends(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, rest}:
      +more = walk.bends(rest, dir)
      Bool.pick(List<&2, String>, String.ends_with(e, ".bend"), walk.under(dir, e) <> more, more)

# a walk once it stops: the `.bend` files it found, and every directory it
# read, the last one read first
type Walk is Data:
  Walk{found: List<&2, String>, read: List<&2, String>}

# the files a walk found
def walk.found(wk: Walk) -> List<&2, String>:
  Walk{found, _read} = wk
  found

# the directories a walk read, in the order it read them
def walk.read(wk: Walk) -> List<&2, String>:
  Walk{_found, read} = wk
  List.reverse(&2, String, read)

# every `.bend` file under the directories still queued, the fuel bounding how
# many directories are read, each read through the World's listing. What is
# found is put in front of what came before, not after it, so the walk stays
# linear; `files` sorts at the end regardless.
def walk(
  fuel: Nat,
  +world: W.World,
  queue: List<&2, String>,
  acc: List<&2, String>,
  seen: List<&2, String>
) -> Walk:
  match fuel:
    case 0n:
      Walk{acc, seen}
    case 1n+f:
      match queue:
        case Nil{}:
          Walk{acc, seen}
        case Con{+dir, rest}:
          +es = W.listing(world, dir)
          walk(f, world, List.append(&2, String, rest, walk.dirs(es, dir)),
            List.append(&2, String, walk.bends(es, dir), acc), dir <> seen)

# how many directories the walk reads at most; past it the walk stops,
# silently. A literal, not `U32.to_nat(100000)`: the checker keeps a literal
# whole and steps it one at a time, so laws/ScopeWalksWholeTree.bend's law can name the bound,
# where it would expand the call in unary and overflow. The compiler emits
# the same `U32.to_nat` for either.
def limit() -> Nat:
  100000n

# the walk of the tree under `.`, reading at most `limit()` directories
def tree(+world: W.World) -> Walk:
  walk(limit(), world, ["."], [], [])

# ---------------------------------------------------------------------------
# the files of the run

# the files named, or every `.bend` file the walk finds when none were
def files.named(paths: List<&2, String>, +world: W.World) -> List<&2, String>:
  match paths:
    case Nil{}:
      +found = walk.found(tree(world))
      List.sort(~String, ~String.is_le, found)
    case Con{p, rest}:
      p <> rest

# the files the lint runs over
def files(+world: W.World) -> List<&2, String>:
  files.named(W.paths.of(world), world)

# a bolt.bend is configuration, not source
def is_config(+pp: String) -> Bool:
  Bool.or(String.eq(pp, "bolt.bend"), String.ends_with(pp, "/bolt.bend"))

# the paths that are source
def sources(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +more = sources(rest)
      Bool.pick(List<&2, String>, is_config(p), more, p <> more)

# the source files of the run, in file-list order
def inputs(+world: W.World) -> List<&2, String>:
  sources(files(world))

# a path as the one file it names wherever it is spelled from: resolved
# against the working directory when relative, then normalized
# (src/rules/imports.bend), so `a.bend`, `./a.bend` and `/w/a.bend` run
# from `/w` are one
def abs(+cwd: String, +path: String) -> String:
  Imports.norm(Bool.pick(String, String.starts_with(path, "/"), path, cwd ++ "/" ++ path))

# each path resolved (abs)
def norms(ps: List<&2, String>, +cwd: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      abs(cwd, p) <> norms(rest, cwd)

# the paths that resolve to none of the paths seen
def unseen(ps: List<&2, String>, +cwd: String, +seen: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +more = unseen(rest, cwd, seen)
      Bool.pick(List<&2, String>, Imports.has(seen, abs(cwd, p)), more, p <> more)

# the files a run reads its roles from: every source the walk of the tree
# finds, then each source of the run the walk does not find (one named
# outside the working directory), so each file is read once. A file's role
# follows the imports, and the file that makes a named file code, a
# package's main.bend that imports it, may be named or not
def graph(+world: W.World) -> List<&2, String>:
  +found = sources(walk.found(tree(world)))
  +cwd = W.cwd.of(world)
  List.append(&2, String, found, unseen(inputs(world), cwd, norms(found, cwd)))

# ---------------------------------------------------------------------------
# what the plan reads

# whether a path is among the paths
def seen.has(ps: List<&2, String>, +pp: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{p, rest}:
      Lazy.or_else(String.eq(p, pp), _u => seen.has(rest, pp))

# each path once, where it first appears
def uniq(ps: List<&2, String>, +seen: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +dup = seen.has(seen, p)
      +more = uniq(rest, p <> seen)
      Bool.pick(List<&2, String>, dup, more, p <> more)

# ---------------------------------------------------------------------------
# the packages (laws/ScopePackageRootsFound.bend): every directory the walk reads but `.` whose
# listing names a main.bend, in the order the walk reads them; none when files
# were named

# the directories the walk read that hold a main.bend, `.` left out
def roots.of(ds: List<&2, String>, +world: W.World) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      +more = roots.of(rest, world)
      +root = Bool.and(Bool.not(String.eq(d, ".")), seen.has(W.listing(world, d), "main.bend"))
      Bool.pick(List<&2, String>, root, d <> more, more)

# the package roots but `.`, as the walk names them (`./w3c`)
def roots.named(paths: List<&2, String>, +world: W.World) -> List<&2, String>:
  match paths:
    case Nil{}:
      roots.of(walk.read(tree(world)), world)
    case Con{_p, _rest}:
      Nil{}

# the package roots but `.`
def roots(+world: W.World) -> List<&2, String>:
  roots.named(W.paths.of(world), world)

# each package root as the project rules take it: its directory as a digest
# names one (`w3c/`)
def packages(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, rest}:
      Imports.dir_of(r ++ "/main.bend") <> packages(rest)

# the directory of each path
def dirs.of(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      Config.dir_of(p) <> dirs.of(rest)

# the directory of every source, each once: every finding's path is a
# source's, so these are the directories grading needs
def conf.dirs(+ps: List<&2, String>) -> List<&2, String>:
  uniq(dirs.of(ps), [])

# the bolt.bend candidates of a directory as a path names it, nearest first:
# the directory resolved against the working directory, then each parent up to
# the root
def conf.chain(+world: W.World, dir: String) -> List<&2, String>:
  Config.chain(Config.home(W.cwd.of(world), dir))

# the bolt.bend candidates of each directory, nearest first
def conf.cands(ds: List<&2, String>, +world: W.World) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      List.append(&2, String, conf.chain(world, d), conf.cands(rest, world))

# the listing of each directory, as a question
def asks.entries(ds: List<&2, String>) -> List<&2, W.Ask>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      W.Entries{d} <> asks.entries(rest)

# the text of each path, as a question
def asks.texts(ps: List<&2, String>) -> List<&2, W.Ask>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      W.Contents{p} <> asks.texts(rest)

# the listings the plan reads: every directory the walk of the tree reads,
# whether files were named or not, since a named file's role is read from the
# imports of the whole tree (graph)
def lists(+world: W.World) -> List<&2, W.Ask>:
  asks.entries(walk.read(tree(world)))

# the texts the plan reads: each source, every file of the graph, and every
# bolt.bend candidate of the sources' directories, each once
def texts(+world: W.World) -> List<&2, W.Ask>:
  +ps = inputs(world)
  asks.texts(uniq(List.concat(&2, String, [ps, graph(world), conf.cands(conf.dirs(ps), world)]),
    []))

# every question the plan reads the World through: the listings, then the
# texts
def looks(+world: W.World) -> List<&2, W.Ask>:
  List.append(&2, W.Ask, lists(world), texts(world))

# the questions a World does not answer yet
def unanswered(asks: List<&2, W.Ask>, +world: W.World) -> List<&2, W.Ask>:
  match asks:
    case Nil{}:
      Nil{}
    case Con{+a, rest}:
      +more = unanswered(rest, world)
      Bool.pick(List<&2, W.Ask>, W.answered(world, a), more, a <> more)

# the listings still open, or, once there are none, the texts still open
def wants.pick(ls: List<&2, W.Ask>, +world: W.World) -> List<&2, W.Ask>:
  match ls:
    case Nil{}:
      unanswered(texts(world), world)
    case Con{a, rest}:
      a <> rest

# the questions a World still leaves open. The file list is known only once
# every directory the walk reads is listed, so the texts wait for the walk.
def wants(+world: W.World) -> List<&2, W.Ask>:
  wants.pick(unanswered(lists(world), world), world)

# ---------------------------------------------------------------------------
# the findings

# a source path and the text the World holds for it
type Got is Data:
  Got{path: String, text: Maybe<&2, String>}

# each source with what the World answers for it
def gots(ps: List<&2, String>, +world: W.World) -> List<&2, Got>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      Got{p, W.text(world, p)} <> gots(rest, world)

# one finding for each source that could not be read
def unread(gs: List<&2, Got>) -> List<&2, F.Finding>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Got{+path, None{}}, rest}:
      F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> unread(rest)
    case Con{Got{_path, Some{_text}}, rest}:
      unread(rest)

# every source that was read, parsed once for every rule
def srcs_of(gs: List<&2, Got>) -> List<&2, Src.Src>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Got{_path, None{}}, rest}:
      srcs_of(rest)
    case Con{Got{path, Some{text}}, rest}:
      Src.of(path, text) <> srcs_of(rest)

# every source's findings from the per-file rules, each told its role among
# the marks (src/role.bend)
def per_file.role(+ms: List<&2, Role.Mark>, ss: List<&2, Src.Src>) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      Src.Src{+path, text, toks, tree, bound, items} = s
      List.concat(&2, F.Finding, [Rules.on.role(Role.of(ms, path), Src.Src{path, text, toks, tree, bound, items}),
        per_file.role(ms, rest)])

# the facts (src/role.bend) of each file the World read, from its text, each
# at its path resolved against the working directory (abs)
def facts.of(gs: List<&2, Got>, +cwd: String) -> List<&2, Role.Fact>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Got{_path, None{}}, rest}:
      facts.of(rest, cwd)
    case Con{Got{path, Some{text}}, rest}:
      Role.fact.text(abs(cwd, path), text) <> facts.of(rest, cwd)

# each path's mark as the path is spelled: its role among marks taken over
# resolved paths (abs), neither when it has none there
def marks.key(ps: List<&2, String>, +cwd: String, +ms: List<&2, Role.Mark>) -> List<&2, Role.Mark>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      Role.Mark{Imports.norm(p), Role.of.norm(ms, abs(cwd, p))} <> marks.key(rest, cwd, ms)

# the marks of a run over files named on the line: every file of the graph
# read for its imports, the walk taken over their resolved paths, and each
# named file's role looked up there as it is named
def marks.named(+world: W.World) -> List<&2, Role.Mark>:
  +cwd = W.cwd.of(world)
  marks.key(inputs(world), cwd, Role.marks.facts(facts.of(gots(graph(world), world), cwd)))

# the marks a run's roles are read from: over the whole tree, the sources'
# own; over files named on the line, the graph's, every file of the tree
# read for its imports, so the main.bend that imports a named file makes it
# code even when it is not named
def marks.run(paths: List<&2, String>, +world: W.World, +ss: List<&2, Src.Src>) -> List<&2, Role.Mark>:
  match paths:
    case Nil{}:
      Role.marks(ss)
    case Con{_p, _rest}:
      marks.named(world)

# the path of the first candidate the World holds a text for, as a list of
# one; none when it holds none
def conf.first(gs: List<&2, Got>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Got{path, Some{_text}}, _rest}:
      [path]
    case Con{Got{_path, None{}}, rest}:
      conf.first(rest)

# the bolt.bend that grades each directory, in directory order: the first of
# its candidates the World read, as conf.near reads it; none for a directory
# graded by the defaults
def conf.used(ds: List<&2, String>, +world: W.World) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, rest}:
      List.append(&2, String, conf.first(gots(conf.chain(world, d), world)), conf.used(rest, world))

# every bolt.bend grading reads, each once, in the order its directories come
def graders(+world: W.World) -> List<&2, String>:
  uniq(conf.used(conf.dirs(inputs(world)), world), [])

# the `setting` rule's findings on each bolt.bend the World read, in order
def settings.at(gs: List<&2, Got>) -> List<&2, F.Finding>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{Got{+path, Some{text}}, rest}:
      List.append(&2, F.Finding, Setting.check(path, text), settings.at(rest))
    case Con{Got{_path, None{}}, rest}:
      settings.at(rest)

# the `setting` rule's findings: each unknown setting of every bolt.bend
# grading reads (src/rules/correctness/setting.bend)
def settings(+world: W.World) -> List<&2, F.Finding>:
  settings.at(gots(graders(world), world))

# every finding of every rule, ungraded, from the sources and what the World
# answers for them: the read failures, the per-file findings of each source,
# then `setting`'s over each bolt.bend grading reads, then the project rules'
# over every source and the other packages
def found.at(+world: W.World, +gs: List<&2, Got>, +ss: List<&2, Src.Src>) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [unread(gs), per_file.role(marks.run(W.paths.of(world), world, ss), ss), settings(world),
    Rules.project(ss, packages(roots(world)))])

# every finding of every rule, ungraded
def found(+world: W.World) -> List<&2, F.Finding>:
  +gs = gots(inputs(world), world)
  found.at(world, gs, srcs_of(gs))

# ---------------------------------------------------------------------------
# grading

# a directory and the config its findings are graded by
type Conf is Data:
  Conf{dir: String, config: Config.Config}

# what the World holds at each path
def texts.at(ps: List<&2, String>, +world: W.World) -> List<&2, Maybe<&2, String>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      W.text(world, p) <> texts.at(rest, world)

# a directory's config: the nearest bolt.bend the World could read among its
# candidates, or the defaults
def conf.near(+world: W.World, dir: String) -> Config.Config:
  Config.nearest(texts.at(conf.chain(world, dir), world))

# each directory's config
def confs.at(ds: List<&2, String>, +world: W.World) -> List<&2, Conf>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, rest}:
      Conf{d, conf.near(world, d)} <> confs.at(rest, world)

# the config of every directory grading needs
def confs(+world: W.World) -> List<&2, Conf>:
  confs.at(conf.dirs(inputs(world)), world)

# the config of a directory, from the table; one the table does not hold is
# worked out the same way (every finding's directory is in the table, so this
# never happens in a run)
def conf.find(cs: List<&2, Conf>, +world: W.World, +dir: String) -> Config.Config:
  match cs:
    case Nil{}:
      conf.near(world, dir)
    case Con{Conf{d, cfg}, rest}:
      Lazy.stop(Config.Config, String.eq(d, dir), cfg, _u => conf.find(rest, world, dir))

# the config a finding at a path is graded by: its directory's
def config.at(+cs: List<&2, Conf>, +world: W.World, path: String) -> Config.Config:
  conf.find(cs, world, Config.dir_of(path))

# every finding graded by the config of its directory, in order, the ones at
# off dropped
def grade(+cs: List<&2, Conf>, +world: W.World, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{+path, line, col, len, rule, msg}, rest}:
      cfg = config.at(cs, world, path)
      List.append(&2, F.Graded, Rules.graded(cfg, [F.Finding{path, line, col, len, rule, msg}]), grade(cs, world, rest))

# ---------------------------------------------------------------------------
# silencing, then the `noqa` rule

# the `noqa` rule's findings on each file's marks, against the graded
# findings, each put at its file as a per-file rule's are
def noqa(ms: List<&2, Noqa.Marks>, +whole: Bool, +gs: List<&2, F.Graded>) -> List<&2, F.Finding>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Noqa.Marks{+path, mks}, rest}:
      List.append(&2, F.Finding, Rules.on.at(path, NoqaRule.check(mks, whole, path, gs)), noqa(rest, whole, gs))

# the graded findings no mark silences, in order, then the `noqa` rule's,
# graded by the grader given: nothing silences what `noqa` reports
def after(
  +ms: List<&2, Noqa.Marks>,
  +whole: Bool,
  +gs: List<&2, F.Graded>,
  grader: List<&2, F.Finding> -> List<&2, F.Graded>
) -> List<&2, F.Graded>:
  List.append(&2, F.Graded, Noqa.keep(ms, gs), grader(noqa(ms, whole, gs)))

# every finding of the run, graded, then silenced by the marks of the
# sources, then `noqa`'s own, which judges a project rule's code only when
# the run is the whole tree. The sources are parsed once for both.
def final(+world: W.World) -> List<&2, F.Graded>:
  +gs = gots(inputs(world), world)
  +ss = srcs_of(gs)
  +cs = confs(world)
  after(Noqa.of_srcs(ss), List.is_empty(&2, String, W.paths.of(world)), grade(cs, world, found.at(world, gs, ss)),
    fs => grade(cs, world, fs))

# ---------------------------------------------------------------------------
# the plan

# one more at error, or the count as it was
def errors.at(ll: Config.Level, more: U32) -> U32:
  match ll:
    case Config.Off{}:
      more
    case Config.Warn{}:
      more
    case Config.Error{}:
      U32.inc(more)

# how many are errors
def errors(gs: List<&2, F.Graded>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{F.Graded{ll, _ff}, rest}:
      errors.at(ll, errors(rest))

# one more below error, or the count as it was
def warnings.at(ll: Config.Level, more: U32) -> U32:
  match ll:
    case Config.Off{}:
      U32.inc(more)
    case Config.Warn{}:
      U32.inc(more)
    case Config.Error{}:
      more

# how many are not errors
def warnings(gs: List<&2, F.Graded>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{F.Graded{ll, _ff}, rest}:
      warnings.at(ll, warnings(rest))

# whether any is an error
def has_error(gs: List<&2, F.Graded>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{F.Graded{ll, _ff}, rest}:
      +more = has_error(rest)
      Bool.or(Config.is_error(ll), more)

# `1 error`, `2 errors`
def count(+nn: U32, +what: String) -> String:
  U32.show(nn) ++ " " ++ what ++ Bool.pick(String, U32.is_eq(nn, 1), "", "s")

# `clean`, or the counts
def summary(+gs: List<&2, F.Graded>) -> String:
  Lazy.stop(String, List.is_empty(&2, F.Graded, gs), "clean",
    _u => count(errors(gs), "error") ++ ", " ++ count(warnings(gs), "warning"))

# every graded finding as a line
def show_all(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> show_all(rest)

# `bolt` over a World: every graded finding no mark silences as a line, then
# `noqa`'s, then the summary of those, and exit 1 exactly when one is an error
def plan(+world: W.World) -> Plan:
  +gs = final(world)
  Plan{List.append(&2, String, show_all(gs), [summary(gs)]), Bool.pick(U32, has_error(gs), 1, 0)}
