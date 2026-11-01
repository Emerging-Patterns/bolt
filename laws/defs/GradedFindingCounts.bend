# counts of graded findings by level and the setting findings of each
# bolt.bend
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../src/rules.bend as Rules
import ../../src/src.bend as Src
import ../../src/role.bend as Role
import ../../src/rules/laws/law.bend as Law
import ../../src/rules/imports.bend as Imports
import ../../src/lint/world.bend as W
import ../../src/lint/plan.bend as Plan
import ../../src/noqa.bend as Noqa
import ./GradingKeepsFindings.bend as D1
import ./ScopeWalkFiles.bend as D2

# a source's read failure: one `read` finding when the World holds no text
# for it. Law vocabulary, as are the specs below.
def unread_at(+path: String, mm: Maybe<&2, String>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      [F.Finding{path, 0, 0, 0, "read", "Cannot read this file."}]
    case Some{_text}:
      []

# every source's read failure, in file-list order
def unread_all(+world: W.World, ps: List<&2, String>) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.append(&2, F.Finding, unread_at(p, W.text(world, p)), unread_all(world, rest))

# a source's text, parsed alone, when the World holds one
def parsed_at(+path: String, mm: Maybe<&2, String>) -> List<&2, Src.Src>:
  match mm:
    case None{}:
      []
    case Some{text}:
      [Src.of(path, text)]

# every source the World holds a text for, parsed, in file-list order
def parsed_all(+world: W.World, ps: List<&2, String>) -> List<&2, Src.Src>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.append(&2, Src.Src, parsed_at(p, W.text(world, p)), parsed_all(world, rest))

# the per-file rules on one source, told its role among the marks
# (src/role.bend)
def on_at(+ms: List<&2, Role.Mark>, +path: String, mm: Maybe<&2, String>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      []
    case Some{text}:
      Rules.on.role(Role.of(ms, path), Src.of(path, text))

# the per-file rules on each source, each told its role among the marks, in
# file-list order
def on_all(+ms: List<&2, Role.Mark>, +world: W.World, ps: List<&2, String>) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.append(&2, F.Finding, on_at(ms, p, W.text(world, p)), on_all(ms, world, rest))

# the path of the first of the paths the World read a text for, as a list of
# one; none when it read none
def read_first.at(+path: String, mm: Maybe<&2, W.Answer>, more: List<&2, String>) -> List<&2, String>:
  match mm:
    case None{}:
      more
    case Some{W.Listed{_names}}:
      more
    case Some{W.Read{_text}}:
      [path]
    case Some{W.Unread{}}:
      more
    case Some{W.Directory{}}:
      more

# the path of the first of the paths the World read a text for
def read_first(+world: W.World, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      read_first.at(p, W.answer(world, W.Contents{p}), read_first(world, rest))

# the bolt.bend that grades each directory, in directory order: of its
# candidates (the directory resolved against the World's working directory,
# then each parent up to the root) the first the World read, as
# nearest_grades says; none for a directory the defaults grade
def graders_all(+world: W.World, ds: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{d, rest}:
      List.append(&2, String, read_first(world, Config.chain(Config.home(W.cwd.of(world), d))),
        graders_all(world, rest))

# one `setting` finding for each setting, at the bolt.bend's path and the
# line of the setting's def, in order
def flagged(+path: String, ss: List<&2, Config.Setting>) -> List<&2, F.Finding>:
  match ss:
    case Nil{}:
      []
    case Con{Config.Setting{n, _w, line}, rest}:
      F.Finding{path, line, 0, 0, "setting", "`" ++ n ++ "` names no rule or group, so it sets nothing."}
        <> flagged(path, rest)

# a bolt.bend's `setting` findings, its unknown settings, when the World
# read it
def flagged_at(+path: String, mm: Maybe<&2, W.Answer>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      []
    case Some{W.Listed{_names}}:
      []
    case Some{W.Read{text}}:
      flagged(path, Config.unknown(Config.settings(text)))
    case Some{W.Unread{}}:
      []
    case Some{W.Directory{}}:
      []

# each bolt.bend's `setting` findings, in order
def flagged_all(+world: W.World, ps: List<&2, String>) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.append(&2, F.Finding, flagged_at(p, W.answer(world, W.Contents{p})), flagged_all(world, rest))

# `setting`'s findings in a run: the unknown settings of every bolt.bend that
# grades a directory grading needs (a source's), each bolt.bend
# once, in the order its directories come
def settings_found(+world: W.World) -> List<&2, F.Finding>:
  flagged_all(world, Plan.uniq(graders_all(world, Plan.conf.dirs(Plan.inputs(world))), []))

# each package root as the project rules take it: its directory, as a digest
# names one (`w3c/`)
def pkgs(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      Imports.dir_of(r ++ "/main.bend") <> pkgs(rest)

# every finding of a run, ungraded: the read failures, then each source's
# per-file findings, each rule seeing that one source and its role among the
# run's law and proof files (src/role.bend), then `setting`'s,
# seeing each bolt.bend grading reads, then the project rules over every
# source in the run, by package
def in_scope(+world: W.World) -> List<&2, F.Finding>:
  +ps = Plan.inputs(world)
  List.concat(&2, F.Finding, [unread_all(world, ps), on_all(Role.marks(Plan.srcs_of(Plan.gots(ps, world))), world, ps),
    settings_found(world),
    D2.packed(parsed_all(world, ps), pkgs(Plan.roots(world)))])

# every finding at the level the config of its path gives its rule, in
# order, the ones at off dropped
def graded_by(+cs: List<&2, Plan.Conf>, +world: W.World, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{+path, line, col, len, +rule, msg}, rest}:
      D1.keep(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
        F.Finding{path, line, col, len, rule, msg}, graded_by(cs, world, rest))

# one more at error, or the count as it was
def at_error.one(ll: Config.Level, nn: Nat) -> Nat:
  match ll:
    case Config.Off{}:
      nn
    case Config.Warn{}:
      nn
    case Config.Error{}:
      1n+nn

# how many graded findings are at error
def at_error(gs: List<&2, F.Graded>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{F.Graded{ll, _ff}, rest}:
      at_error.one(ll, at_error(rest))

# one more below error, or the count as it was
def below_error.one(ll: Config.Level, nn: Nat) -> Nat:
  match ll:
    case Config.Off{}:
      1n+nn
    case Config.Warn{}:
      1n+nn
    case Config.Error{}:
      nn

# how many graded findings are below error
def below_error(gs: List<&2, F.Graded>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{F.Graded{ll, _ff}, rest}:
      below_error.one(ll, below_error(rest))

# `1 error`, `2 errors`
def plural(+nn: U32, +word: String) -> String:
  U32.show(nn) ++ " " ++ word ++ Bool.pick(String, U32.is_eq(nn, 1), "", "s")

# the counts of a run that graded something
def summary_of.counts(+gs: List<&2, F.Graded>) -> String:
  plural(U32.from_nat(at_error(gs)), "error") ++ ", " ++ plural(U32.from_nat(below_error(gs)), "warning")

# `clean` when nothing was graded, otherwise `N errors, M warnings`
def summary_of(gs: List<&2, F.Graded>) -> String:
  match gs:
    case Nil{}:
      "clean"
    case Con{g, rest}:
      summary_of.counts(g <> rest)

# a run's graded findings before any noqa comment is read: the planner's
# config for each path, over the findings in the order in_scope lists them
def run_raw(+world: W.World) -> List<&2, F.Graded>:
  graded_by(Plan.confs(world), world, in_scope(world))

# the noqa marks of every source the World holds a text for, in file-list
# order, each read from its own file's tokens
def marks_all(+world: W.World) -> List<&2, Noqa.Marks>:
  Noqa.of_srcs(parsed_all(world, Plan.inputs(world)))

# a run's graded findings: the ones no mark silences (noqa_keeps says which
# those are), in order, then the `noqa` rule's findings on every mark,
# graded by the config of their paths and silenced by none; `noqa` judges a
# project rule's code only when the run is the whole tree
def run_graded(+world: W.World) -> List<&2, F.Graded>:
  +ms = marks_all(world)
  +gs = run_raw(world)
  List.append(&2, F.Graded, Noqa.keep(ms, gs),
    graded_by(Plan.confs(world), world, Plan.noqa(ms, List.is_empty(&2, String, W.paths.of(world)), gs)))
