# bolt/lint/plan: `bolt` (the lint) as a pure planner. It reads a World
# (bolt/lint/world.bend) and returns either the questions it still needs
# answered (`wants`) or the Plan: the lines to print and the exit status
# (`plan`). The interpreter (bolt/lint.bend) loops on `wants`, answering each
# question by IO, until nothing is wanted, then prints `plan`'s lines and
# exits with its status. The design is docs/rfc/bolt-lint-planner.md.
#
# With no files named, the planner walks the tree under `.` as a fold over the
# World's listings: a directory not listed yet reads as empty and is asked
# for, so each round of the loop lists one more level of the tree. Once every
# directory the walk reads is listed, it asks for the text of each source, of
# SPEC.md, and of every bolt.bend candidate of their directories, each once.
# A directory's candidates are taken once it is resolved against the World's
# working directory (Config.home), so a relative path is graded by the same
# bolt.bend wherever bolt runs from.
# `wants` never parses a file; `plan` parses and lints once.
import Base
import ../../lazy/lazy.bend as Lazy
import ./world.bend as W
import ../finding.bend as F
import ../src.bend as Src
import ../rules.bend as Rules
import ../config.bend as Config

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
# whole and steps it one at a time, so BOLT-SCOPE-1's law can name the bound,
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

# the directory of each path
def dirs.of(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, rest}:
      Config.dir_of(p) <> dirs.of(rest)

# the directory of every source and of SPEC.md, each once: every finding's
# path is a source's or SPEC.md, so these are the directories grading needs
def conf.dirs(+ps: List<&2, String>) -> List<&2, String>:
  uniq(dirs.of(List.append(&2, String, ps, ["SPEC.md"])), [])

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
      W.Text{p} <> asks.texts(rest)

# the directories the walk lists: every one it reads, none when files were
# named
def lists.named(paths: List<&2, String>, +world: W.World) -> List<&2, W.Ask>:
  match paths:
    case Nil{}:
      asks.entries(walk.read(tree(world)))
    case Con{_p, _rest}:
      Nil{}

# the listings the plan reads
def lists(+world: W.World) -> List<&2, W.Ask>:
  lists.named(W.paths.of(world), world)

# the texts the plan reads: each source, SPEC.md, and every bolt.bend
# candidate of their directories, each once
def texts(+world: W.World) -> List<&2, W.Ask>:
  +ps = inputs(world)
  asks.texts(uniq(List.concat(&2, String, [ps, ["SPEC.md"], conf.cands(conf.dirs(ps), world)]), []))

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

# every source's findings from the per-file rules
def per_file(ss: List<&2, Src.Src>) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, rest}:
      List.concat(&2, F.Finding, [Rules.on(s), per_file(rest)])

# every finding of every rule, ungraded: the read failures, the per-file
# findings of each source, then the project rules' over every source, told
# whether the run is the whole tree, and SPEC.md's text
def found(+world: W.World) -> List<&2, F.Finding>:
  +gs = gots(inputs(world), world)
  +ss = srcs_of(gs)
  List.concat(&2, F.Finding, [unread(gs), per_file(ss),
    Rules.project(ss, List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"))])

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
      List.append(&2, F.Graded, Rules.graded(config.at(cs, world, path), [F.Finding{path, line, col, len, rule, msg}]),
        grade(cs, world, rest))

# every finding of the run, graded
def graded(+world: W.World) -> List<&2, F.Graded>:
  grade(confs(world), world, found(world))

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

# `bolt` over a World: every graded finding as a line, then the summary, and
# exit 1 exactly when one is an error
def plan(+world: W.World) -> Plan:
  +gs = graded(world)
  Plan{List.append(&2, String, show_all(gs), [summary(gs)]), Bool.pick(U32, has_error(gs), 1, 0)}
