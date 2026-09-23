# bolt: the laws. Grading is a pure function of a config and the findings,
# so these laws quantify over every list of settings and every finding,
# never over one bolt.bend.
import Base
import ./config.bend as Config
import ./finding.bend as F
import ./rules.bend as Rules
import ./codes.bend as Codes
import ../lazy/lazy.bend as Lazy
import ./src.bend as Src
import ./rules/digest.bend as Digest
import ./rules/laws/law.bend as Law
import ./rules/laws/unsafe.bend as Unsafe
import ./rules/laws/trace.bend as Trace
import ./lint/world.bend as W
import ./lint/plan.bend as Plan
import ./args.bend as Args
import ./version.bend as Ver
import ./build_rev.bend as Rev
import ./check.bend as Check
import ./lsp/checker/service.bend as Checker
import ./lsp/checker/bend.bend as BendChecker
import ./lsp/report.bend as Rep
import 0xba6940aab8a335b70bf79944bd9b53c4/main.bend as Shake

# LAW: nothing is set in an empty config
# BOLT-CFG-1
law set_level_none:
  for name: String
  {Config.set_level([], name) == None{} : Maybe<&2, Config.Level>}

# LAW: a setting of the name, first in file order, is the name's setting
# BOLT-CFG-1
law set_level_first:
  for sets: List<&2, Config.Set>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == True{} : Bool}
  {Config.set_level(Config.Set{nn, ll} <> sets, name) == Some{ll} : Maybe<&2, Config.Level>}

# LAW: a setting of another name is passed over
# BOLT-CFG-1
law set_level_skip:
  for +sets: List<&2, Config.Set>
  for +name: String
  for +nn: String
  for ll: Config.Level
  for h: {String.eq(nn, name) == False{} : Bool}
  {Config.set_level(Config.Set{nn, ll} <> sets, name) == Config.set_level(sets, name)
    : Maybe<&2, Config.Level>}

# LAW: a rule's own setting is its level, whatever its group says, an
# opt-in rule's too
# BOLT-CFG-1
# BOLT-CFG-6
law level_own:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h: {Config.set_level(sets, rule) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == l : Config.Level}

# LAW: a rule with no setting of its own, and not opt-in, is at its group's
# setting
# BOLT-CFG-1
law level_group:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for +l: Config.Level
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == Some{l} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == l : Config.Level}

# LAW: a rule with no setting of its own, not opt-in, whose group has no
# setting either, is at its group's default
# BOLT-CFG-1
law level_default:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  for h_opt: {Config.opt_in(rule) == False{} : Bool}
  for h_group: {Config.set_level(sets, group) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.default(group) : Config.Level}

# a finding at a level onto what grading keeps of the rest: dropped at off,
# kept with its level otherwise
def keep(ll: Config.Level, ff: F.Finding, rest: List<&2, F.Graded>) -> List<&2, F.Graded>:
  match ll:
    case Config.Off{}:
      rest
    case Config.Warn{}:
      F.Graded{Config.Warn{}, ff} <> rest
    case Config.Error{}:
      F.Graded{Config.Error{}, ff} <> rest

# every finding at the level the config gives its rule, in order, the ones
# at off dropped
def kept(+cfg: Config.Config, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      keep(Config.level(cfg, Rules.group(rule), rule), F.Finding{path, line, col, len, rule, msg}, kept(cfg, rest))

# LAW: grading drops each finding whose rule is at off and attaches its
# rule's level to every other, in order
# BOLT-CFG-2
law graded_keeps:
  for +cfg: Config.Config
  for fs: List<&2, F.Finding>
  {Rules.graded(cfg, fs) == kept(cfg, fs) : List<&2, F.Graded>}

# LAW: a level word that is neither `off` nor `warn` is an error, so a typo
# makes a rule stricter, never silently off
# BOLT-CFG-3
law word_error:
  for +ww: String
  for h_off: {String.eq(ww, "off") == False{} : Bool}
  for h_warn: {String.eq(ww, "warn") == False{} : Bool}
  {Config.of_word(ww) == Config.Error{} : Config.Level}

# LAW: correctness defaults to error
# BOLT-CFG-5
law default_correctness:
  for +group: String
  for h: {group == "correctness" : String}
  {Config.default(group) == Config.Error{} : Config.Level}

# LAW: pedantic defaults to off
# BOLT-CFG-5
law default_pedantic:
  for +group: String
  for h: {group == "pedantic" : String}
  {Config.default(group) == Config.Off{} : Config.Level}

# LAW: every other group defaults to warn
# BOLT-CFG-5
law default_rest:
  for +group: String
  for h_c: {String.eq(group, "correctness") == False{} : Bool}
  for h_p: {String.eq(group, "pedantic") == False{} : Bool}
  {Config.default(group) == Config.Warn{} : Config.Level}

# LAW: an opt-in rule with no setting of its own is off, whatever its group
# says (with one, level_own gives it that setting)
# BOLT-CFG-6
law opt_in_off:
  for +sets: List<&2, Config.Set>
  for +group: String
  for +rule: String
  for h_opt: {Config.opt_in(rule) == True{} : Bool}
  for h_rule: {Config.set_level(sets, rule) == None{} : Maybe<&2, Config.Level>}
  {Config.level(Config.Config{sets}, group, rule) == Config.Off{} : Config.Level}

# The code table and the printed line (BOLT-OUT). The table is finite, so
# its laws quantify over every index into it: the row there, looked up again
# by its slug and by its code, is the same row.

# the row at an index, looked up again by its slug; none stays none
def by_slug(mm: Maybe<&2, Codes.Entry>) -> Maybe<&2, Codes.Entry>:
  match mm:
    case None{}:
      None{}
    case Some{Codes.Entry{+s, _id, _grp}}:
      Codes.find(Codes.table(), s)

# this row carries the code
def by_code.same(+row: Codes.Entry, +id: String) -> Bool:
  Codes.Entry{_s, +rid, _grp} = row
  String.eq(rid, id)

# the first row with the code
def by_code(rows: List<&2, Codes.Entry>, +id: String) -> Maybe<&2, Codes.Entry>:
  match rows:
    case Nil{}:
      None{}
    case Con{+row, rest}:
      Lazy.stop(Maybe<&2, Codes.Entry>, by_code.same(row, id), Some{row}, _u => by_code(rest, id))

# the row at an index, looked up again by its code; none stays none
def code_back(mm: Maybe<&2, Codes.Entry>) -> Maybe<&2, Codes.Entry>:
  match mm:
    case None{}:
      None{}
    case Some{Codes.Entry{_s, +id, _grp}}:
      by_code(Codes.table(), id)

# LAW: every row of the code table is the row its own slug finds, so no slug
# is listed twice and `code`, `group` and `source` read each rule's own row
# BOLT-OUT-1
law slug_finds_row:
  for +n: Nat
  {by_slug(List.get(&2, Codes.Entry, Codes.table(), n)) == List.get(&2, Codes.Entry, Codes.table(), n)
    : Maybe<&2, Codes.Entry>}

# LAW: every row of the code table is the row its own code finds, so no code
# is listed twice: with slug_finds_row, slugs and codes are one-to-one
# BOLT-OUT-1
law code_finds_row:
  for +n: Nat
  {code_back(List.get(&2, Codes.Entry, Codes.table(), n)) == List.get(&2, Codes.Entry, Codes.table(), n)
    : Maybe<&2, Codes.Entry>}

# LAW: a graded finding prints as `path:line:col: level: CODE: message`, line
# and column counted from 1, the level as the config shows it and the code
# the table's for the finding's rule
# BOLT-OUT-2
law shown:
  for path: String
  for line: U32
  for col: U32
  for len: U32
  for rule: String
  for msg: String
  for level: Config.Level
  {F.show_graded(F.Graded{level, F.Finding{path, line, col, len, rule, msg}})
    == path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":" ++ U32.show((col + 1 : U32)) ++ ": "
      ++ Config.show(level) ++ ": " ++ Codes.code(rule) ++ ": " ++ msg : String}

# The lint planner (lint/plan.bend) over its World (lint/world.bend). Every
# law below quantifies over every World: every list of paths the command line
# may name and every list of replies, whatever the interpreter would have
# answered. That the interpreter answers each question faithfully and prints
# the plan it is handed is BOLT-TRUST-9.

# whether a World answers every question. Law vocabulary: bolt never calls it.
def answered_all(+world: W.World, asks: List<&2, W.Ask>) -> Bool:
  match asks:
    case Nil{}:
      True{}
    case Con{a, rest}:
      +more = answered_all(world, rest)
      Bool.and(W.answered(world, a), more)

# LAW: the loop stops exactly when the plan has what it reads: nothing is
# wanted when, and only when, the World answers every question the planner
# reads it through (each listing the walk reads, each source, SPEC.md and
# every bolt.bend candidate), so `plan` never runs on a question it would
# read as unanswered
law wants_tie:
  for +world: W.World
  {answered_all(world, Plan.looks(world)) == List.is_empty(&2, W.Ask, Plan.wants(world)) : Bool}

# whether no path is a bolt.bend. Law vocabulary.
def no_config(ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+p, rest}:
      +more = no_config(rest)
      Bool.and(Bool.not(Plan.is_config(p)), more)

# LAW: no path the planner lints is a bolt.bend, whatever the command line
# names: a bolt.bend is only ever read, as a candidate config
# BOLT-SCOPE-5
law no_config_linted:
  for +world: W.World
  {no_config(Plan.inputs(world)) == True{} : Bool}

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

# the per-file rules on one source alone
def on_at(+path: String, mm: Maybe<&2, String>) -> List<&2, F.Finding>:
  match mm:
    case None{}:
      []
    case Some{text}:
      Rules.on(Src.of(path, text))

# the per-file rules on each source alone, in file-list order
def on_all(+world: W.World, ps: List<&2, String>) -> List<&2, F.Finding>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.append(&2, F.Finding, on_at(p, W.text(world, p)), on_all(world, rest))

# every finding of a run, ungraded: the read failures, then each source's
# per-file findings, each rule seeing that one source, then coverage, unsafe
# and trace, each seeing the digests of every source in the run (trace also
# whether the run is the whole tree, and SPEC.md's text)
def in_scope(+world: W.World) -> List<&2, F.Finding>:
  +ps = Plan.inputs(world)
  +ds = Digest.all(parsed_all(world, ps))
  List.concat(&2, F.Finding, [unread_all(world, ps), on_all(world, ps), Law.check(ds), Unsafe.check(ds),
    Trace.check(List.is_empty(&2, String, W.paths.of(world)), W.text(world, "SPEC.md"), ds)])

# LAW: the planner's findings are the read failures, then the per-file rules
# on each source's Src alone, then the project rules on the digests of every
# source in the run, and nothing else
# BOLT-SCOPE-2
law scope_findings:
  for +world: W.World
  {Plan.found(world) == in_scope(world) : List<&2, F.Finding>}

# every finding at the level the config of its path gives its rule, in
# order, the ones at off dropped
def graded_by(+cs: List<&2, Plan.Conf>, +world: W.World, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{+path, line, col, len, +rule, msg}, rest}:
      keep(Config.level(Plan.config.at(cs, world, path), Rules.group(rule), rule),
        F.Finding{path, line, col, len, rule, msg}, graded_by(cs, world, rest))

# each graded finding's line, in order
def shown_all(gs: List<&2, F.Graded>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, rest}:
      F.show_graded(g) <> shown_all(rest)

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

# true at error, or what the rest says
def any_error.one(ll: Config.Level, more: Bool) -> Bool:
  match ll:
    case Config.Off{}:
      more
    case Config.Warn{}:
      more
    case Config.Error{}:
      True{}

# whether some graded finding is at error
def any_error(gs: List<&2, F.Graded>) -> Bool:
  match gs:
    case Nil{}:
      False{}
    case Con{F.Graded{ll, _ff}, rest}:
      any_error.one(ll, any_error(rest))

# a run's graded findings: the planner's config for each path, over the
# findings in the order in_scope lists them
def run_graded(+world: W.World) -> List<&2, F.Graded>:
  graded_by(Plan.confs(world), world, in_scope(world))

# the lines a run prints: each graded finding, in order, then the summary
def out_lines(+world: W.World) -> List<&2, String>:
  +gs = run_graded(world)
  List.append(&2, String, shown_all(gs), [summary_of(gs)])

# LAW: `bolt` prints the read failures, then the per-file findings in
# file-list order and `Rules.on` order, then coverage, unsafe and trace, each
# graded finding as one line and the ones at off dropped, then the summary
# BOLT-OUT-3
law lines_in_order:
  for +world: W.World
  {Plan.lines.of(Plan.plan(world)) == out_lines(world) : List<&2, String>}

# LAW: the last line is `clean` or `N errors, M warnings` for the graded
# findings
# BOLT-OUT-4
law last_line_summary:
  for +world: W.World
  {List.last(&2, String, Plan.lines.of(Plan.plan(world))) == Some{summary_of(run_graded(world))}
    : Maybe<&2, String>}

# LAW: the exit status is 1 exactly when some graded finding is an error,
# and 0 otherwise
# BOLT-OUT-4
law exit_on_error:
  for +world: W.World
  {Plan.exit.of(Plan.plan(world)) == Bool.pick(U32, any_error(run_graded(world)), 1, 0) : U32}

# LAW: a source the World answers as unreadable is one `read` finding at its
# path, in its place among the read failures
# BOLT-OUT-5
law unread_one_finding:
  for +world: W.World
  for +path: String
  for ps: List<&2, String>
  for h: {W.answer(world, W.Text{path}) == Some{W.Unread{}} : Maybe<&2, W.Answer>}
  {Plan.unread(Plan.gots(path <> ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}

# LAW: a path the World answers as a directory is one `read` finding at its
# path, in its place among the read failures, as an unreadable file is: a
# directory named on the command line has no text to lint
# BOLT-OUT-5
law directory_one_finding:
  for +world: W.World
  for +path: String
  for ps: List<&2, String>
  for h: {W.answer(world, W.Text{path}) == Some{W.Directory{}} : Maybe<&2, W.Answer>}
  {Plan.unread(Plan.gots(path <> ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}

# LAW: a `read` finding is graded with correctness: whatever the config, its
# level is the one correctness gives the rule `read`
# BOLT-OUT-5
law read_is_correctness:
  for +cfg: Config.Config
  for path: String
  for line: U32
  for col: U32
  for len: U32
  for msg: String
  {Rules.graded(cfg, [F.Finding{path, line, col, len, "read", msg}])
    == keep(Config.level(cfg, "correctness", "read"), F.Finding{path, line, col, len, "read", msg}, [])
    : List<&2, F.Graded>}

# The walk (BOLT-SCOPE-1). With no paths named, the planner lints what a
# breadth-first search over the World's listings reaches from `.`. The spec
# below writes that search apart from plan.bend's walk, which threads a queue,
# the files found so far and the directories read through one fuelled loop:
# here the directories read come first, in order, and their files are
# gathered after. walk_bfs holds for every bound on the directories read;
# walk_files is the row, at 100000.

# an entry's name without the "/" that marks a directory
def entry_name(+ee: String) -> String:
  String.take(ee, Nat.sub(String.length(ee), 1n))

# whether an entry is a directory the search descends into: it ends in "/",
# and its name neither starts with "." (hidden) nor is node_modules
def descends(+ee: String) -> Bool:
  +nn = entry_name(ee)
  Bool.and(String.ends_with(ee, "/"), Bool.not(Bool.or(String.starts_with(nn, "."), String.eq(nn, "node_modules"))))

# the directories a listing of a directory names and the search descends
# into, as paths, in listing order
def subdirs(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{+ee, rest}:
      +more = subdirs(rest, dir)
      Bool.pick(List<&2, String>, descends(ee), (dir ++ "/" ++ entry_name(ee)) <> more, more)

# the `.bend` files a listing of a directory names, as paths, in listing
# order
def bends_in(es: List<&2, String>, +dir: String) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{+ee, rest}:
      +more = bends_in(rest, dir)
      Bool.pick(List<&2, String>, String.ends_with(ee, ".bend"), (dir ++ "/" ++ ee) <> more, more)

# the directories a breadth-first search from the queue reads, in the order
# it reads them, at most `reads` of them: each is listed, and the ones its
# listing names that the search descends into join the back of the queue.
# Past that bound the search stops, and says nothing.
def bfs(reads: Nat, +world: W.World, queue: List<&2, String>) -> List<&2, String>:
  match reads:
    case 0n:
      []
    case 1n+ff:
      match queue:
        case Nil{}:
          []
        case Con{+dd, rest}:
          dd <> bfs(ff, world, List.append(&2, String, rest, subdirs(W.listing(world, dd), dd)))

# the `.bend` files the listings of the directories name, the last directory
# read first (the order the planner sorts from)
def found_in(ds: List<&2, String>, +world: W.World) -> List<&2, String>:
  match ds:
    case Nil{}:
      []
    case Con{+dd, rest}:
      List.append(&2, String, found_in(rest, world), bends_in(W.listing(world, dd), dd))

# LAW: the walk from `.`, reading at most `reads` directories, finds the
# `.bend` files of the directories the breadth-first search reads within that
# bound: those its listings name, and none from a directory it does not
# descend into (hidden, or node_modules) or does not reach before the bound
law walk_bfs:
  for +reads: Nat
  for +world: W.World
  {Plan.walk.found(Plan.walk(reads, world, ["."], [], [])) == found_in(bfs(reads, world, ["."]), world)
    : List<&2, String>}

# LAW: with no paths named, the planner's file list is the `.bend` files the
# search reaches from `.` within the first 100000 directories it reads,
# sorted by code point; past that bound the walk stops silently
# BOLT-SCOPE-1
law walk_files:
  for +world: W.World
  for h: {W.paths.of(world) == [] : List<&2, String>}
  {Plan.files(world) == List.sort(~String, ~String.is_le, found_in(bfs(100000n, world, ["."]), world))
    : List<&2, String>}

# Under law (BOLT-SCOPE-3). The coverage rule (rules/laws/law.bend) grades a
# file's defs and types only when the file is under law. This law says, over
# the digests the planner hands the project rules, which files those are.

# the digests the planner hands the project rules: one for each source of the
# run it could read
def handed(+world: W.World) -> List<&2, Digest.Digest>:
  Digest.all(Plan.srcs_of(Plan.gots(Plan.inputs(world), world)))

# whether some file of the run is a LAWS.bend
def has_laws(ds: List<&2, Digest.Digest>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{Digest.Digest{_path, _norm, _dir, is_laws, _is_law_file, _exempt, _tops, _says, _deps, _unsafes, _laws},
      rest}:
      Bool.or(is_laws, has_laws(rest))

# a file under law, graded against what the laws name: nothing when it is
# exempt, otherwise every def and type of it that no law names
def graded_file(
  exempt: Bool,
  +tops: List<&2, Digest.Top>,
  +ms: List<&2, Digest.Mention>,
  +norm: String,
  path: String
) -> List<&2, F.Finding>:
  match exempt:
    case True{}:
      []
    case False{}:
      Law.gaps(tops, ms, norm, path)

# every file of the run put under law, each graded against what the laws
# name, in order
def under_law(ds: List<&2, Digest.Digest>, +ms: List<&2, Digest.Mention>) -> List<&2, F.Finding>:
  match ds:
    case Nil{}:
      []
    case Con{Digest.Digest{path, norm, _dir, _is_laws, _is_law_file, exempt, tops, _says, _deps, _unsafes, _laws},
      rest}:
      List.append(&2, F.Finding, graded_file(exempt, tops, ms, norm, path), under_law(rest, ms))

# a run's coverage findings: every file under law when the run holds a
# LAWS.bend, none otherwise
def coverage_of(on: Bool, ds: List<&2, Digest.Digest>, ms: List<&2, Digest.Mention>) -> List<&2, F.Finding>:
  match on:
    case True{}:
      under_law(ds, ms)
    case False{}:
      []

# LAW: when the files in the run include a LAWS.bend, every file in the run
# that is not exempt is under law, graded against what every law of the run
# names; otherwise none is
# BOLT-SCOPE-3
law under_law_all:
  for +world: W.World
  {Law.check(handed(world)) == coverage_of(has_laws(handed(world)), handed(world), Law.named(handed(world)))
    : List<&2, F.Finding>}

# Where a finding is graded (BOLT-CFG-4). The planner grades a finding by the
# config of its path's directory (plan.bend, config.at), from a table it builds
# once for each directory in the run. The laws below say what that config is,
# for every World and every path: the path's directory is resolved against
# the World's working directory (Config.home: absolute, then home.step over
# each segment), and of it and each parent up to the root (Config.chain),
# nearest first, the first whose bolt.bend the World holds a text for grades
# the finding.

# LAW: a path that starts at the root is itself, wherever bolt runs from
# BOLT-CFG-4
law absolute_root:
  for +cwd: String
  for +path: String
  for h: {String.starts_with(path, "/") == True{} : Bool}
  {Config.absolute(cwd, path) == path : String}

# LAW: any other path is read under the working directory
# BOLT-CFG-4
law absolute_under:
  for +cwd: String
  for +path: String
  for h: {String.starts_with(path, "/") == False{} : Bool}
  {Config.absolute(cwd, path) == cwd ++ "/" ++ path : String}

# LAW: an empty segment (from `//`, or the `/` a directory ends in) leaves the
# directory where it is
# BOLT-CFG-4
law home_empty:
  for +above: List<&2, String>
  {Config.home.step("", above) == above : List<&2, String>}

# LAW: a `.` segment leaves the directory where it is
# BOLT-CFG-4
law home_here:
  for +above: List<&2, String>
  {Config.home.step(".", above) == above : List<&2, String>}

# LAW: a `..` segment goes up one directory: it drops the innermost one, and
# at the root there is none to drop (home.up)
# BOLT-CFG-4
law home_up:
  for +above: List<&2, String>
  {Config.home.step("..", above) == Config.home.up(above) : List<&2, String>}

# LAW: any other segment goes into the directory it names
# BOLT-CFG-4
law home_down:
  for +seg: String
  for +above: List<&2, String>
  for h_here: {Bool.or(String.is_empty(seg), String.eq(seg, ".")) == False{} : Bool}
  for h_up: {String.eq(seg, "..") == False{} : Bool}
  {Config.home.step(seg, above) == seg <> above : List<&2, String>}

# LAW: a resolved directory's candidates are its own bolt.bend, then its
# parent's candidates, so they reach every parent up to the root
# BOLT-CFG-4
law chain_parent:
  for +dd: String
  for +rest: List<&2, String>
  {Config.chain(dd <> rest) == (Config.root(dd <> rest, "") ++ "bolt.bend") <> Config.chain(rest)
    : List<&2, String>}

# the config a World's answer for a candidate gives: its text parsed when it
# was read, else what the candidates after it give. Law vocabulary, as is
# first_read.
def first_read.at(mm: Maybe<&2, W.Answer>, more: Config.Config) -> Config.Config:
  match mm:
    case None{}:
      more
    case Some{W.Listed{_names}}:
      more
    case Some{W.Read{text}}:
      Config.parse(text)
    case Some{W.Unread{}}:
      more
    case Some{W.Directory{}}:
      more

# the config of the first of the paths the World read a text for, the
# defaults when it read none of them
def first_read(+world: W.World, ps: List<&2, String>) -> Config.Config:
  match ps:
    case Nil{}:
      Config.none()
    case Con{p, rest}:
      first_read.at(W.answer(world, W.Text{p}), first_read(world, rest))

# LAW: a finding at a path is graded by the nearest bolt.bend the World read:
# of the bolt.bend in the path's directory, resolved against the working
# directory, then in each parent up to the root, the first read, and only
# that one; the defaults when none was
# BOLT-CFG-4
law nearest_grades:
  for +world: W.World
  for +path: String
  {Plan.config.at(Plan.confs(world), world, path)
    == first_read(world, Config.chain(Config.home(W.cwd.of(world), Config.dir_of(path))))
    : Config.Config}

# The command line (BOLT-CLI). shake parses argv against bolt's spec
# (BOLT-TRUST-8), Args.out decides what the parse does, and main only does
# it (BOLT-TRUST-9): a Stop prints its text to its stream and exits with its
# code, and a Go runs its subcommand over the files, which then exits as that
# command decides (BOLT-OUT-4 for lint). The laws below quantify over every
# list of words after the command, and the exit laws over every argv. An argv
# here is the list IO.args hands the program: a compiled binary's runtime has
# already taken its own flags and the first `--` out of the command line, so
# at a shell `bolt -- -- -x.bend` is what reaches shake as `-- -x.bend`.

# a word bolt reads as a file after a command: neither `--` nor `help`, and
# not starting with `-` (a flag)
def plain_word(+ww: String) -> Bool:
  Bool.not(Bool.or(String.eq(ww, "--"), Bool.or(String.eq(ww, "help"), String.starts_with(ww, "-"))))

# a word bolt reads as a file with no command before it: a plain word that
# names no subcommand
def loose_word(+ww: String) -> Bool:
  Bool.and(plain_word(ww),
    Bool.not(Bool.or(String.eq("lint", ww), Bool.or(String.eq("check", ww), String.eq("lsp", ww)))))

# whether every word is plain
def all_plain(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(plain_word(ww), all_plain(rest))

# whether every word is loose
def all_loose(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+ww, rest}:
      Bool.and(loose_word(ww), all_loose(rest))

# LAW: `bolt file..` lints the files, when no word is a flag, `--`, `help` or
# a subcommand's name (none at all lints the tree)
# BOLT-CLI-1
law cli_bare:
  for +fs: List<&2, String>
  for +h: {all_loose(fs) == True{} : Bool}
  {Args.out(Args.parse(fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt -- word..` lints every word after the `--`, whatever it is
# BOLT-CLI-1
law cli_bare_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint file..` lints the files, when no word is a flag, `--` or
# `help`
# BOLT-CLI-1
law cli_lint:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  {Args.out(Args.parse("lint" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt lint -- word..` lints every word after the `--`
# BOLT-CLI-1
law cli_lint_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("lint" <> "--" <> fs)) == Args.Go{Args.CLint{}, fs} : Args.Out}

# LAW: `bolt check file..` checks the files, when no word is a flag, `--` or
# `help`
# BOLT-CLI-1
law cli_check:
  for +fs: List<&2, String>
  for h: {all_plain(fs) == True{} : Bool}
  {Args.out(Args.parse("check" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# LAW: `bolt check -- word..` checks every word after the `--`
# BOLT-CLI-1
law cli_check_raw:
  for +fs: List<&2, String>
  {Args.out(Args.parse("check" <> "--" <> fs)) == Args.Go{Args.CCheck{}, fs} : Args.Out}

# what `bolt lsp word..` does, the words plain: serve an editor when there
# are none; `lsp` takes no word, so the first is an unexpected argument
def lsp_out(ws: List<&2, String>) -> Args.Out:
  match ws:
    case Nil{}:
      Args.Go{Args.CLsp{}, []}
    case Con{ww, _rest}:
      Args.Stop{Args.Err{}, Args.err_text(Shake.Unexpected{ww}), 1}

# LAW: `bolt lsp` serves an editor, and a plain word after it is an error
# BOLT-CLI-1
law cli_lsp:
  for +ws: List<&2, String>
  for h: {all_plain(ws) == True{} : Bool}
  {Args.out(Args.parse("lsp" <> ws)) == lsp_out(ws) : Args.Out}

# LAW: `bolt help cmd..` prints the usage of that command path to stdout and
# exits 0, whatever the words
# BOLT-CLI-1
law cli_help:
  for +ps: List<&2, String>
  {Args.out(Args.parse("help" <> ps)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: `bolt --version` prints bolt, then the release and the commit, and
# exits 0, with or without files after it
# BOLT-CLI-1
# BOLT-CLI-2
law cli_version:
  for +fs: List<&2, String>
  for +h: {all_loose(fs) == True{} : Bool}
  {Args.out(Args.parse("--version" <> fs))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}

# whether a parse error is a request for usage
def asks_help(ee: Shake.ParseErr) -> Bool:
  match ee:
    case Shake.UnknownFlag{_ww}:
      False{}
    case Shake.Missing{_nn}:
      False{}
    case Shake.BadValue{_nn, _vv}:
      False{}
    case Shake.NeedHelp{_path}:
      True{}
    case Shake.Unexpected{_ww}:
      False{}

# LAW: every argv shake cannot parse, other than a request for usage, prints
# the error to stderr and exits 1
# BOLT-CLI-1
law cli_error_exits:
  for +av: List<&2, String>
  for +ee: Shake.ParseErr
  for h: {Args.parse(av) == Fail{ee} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_help: {asks_help(ee) == False{} : Bool}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Err{}, Args.err_text(ee), 1} : Args.Out}

# LAW: every argv that asks for usage prints the usage of its command path to
# stdout and exits 0
# BOLT-CLI-1
law cli_help_exits:
  for +av: List<&2, String>
  for +ps: List<&2, String>
  for h: {Args.parse(av) == Fail{Shake.NeedHelp{ps}} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  {Args.out(Args.parse(av)) == Args.Stop{Args.Page{}, Args.help_text(ps), 0} : Args.Out}

# LAW: every argv that parses with `--version` set prints bolt, then the
# release and the commit, and exits 0, whatever else it names
# BOLT-CLI-1
# BOLT-CLI-2
law cli_version_exits:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == True{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Stop{Args.Line{}, "bolt " ++ Args.version.at(Ver.text(), Rev.text()), 0} : Args.Out}

# LAW: every other argv that parses runs the command it selects (`lint` when
# none) over the files it bound
# BOLT-CLI-1
law cli_runs:
  for +av: List<&2, String>
  for +mm: Shake.Matched
  for h: {Args.parse(av) == Done{mm} : Result<&2, &2, Shake.ParseErr, Shake.Matched>}
  for h_ver: {Shake.on(mm, "version") == False{} : Bool}
  {Args.out(Args.parse(av))
    == Args.Go{Args.command(String.join(Shake.path_of(mm), "/")), Shake.get_all(mm, "files")} : Args.Out}

# LAW: a build with no commit prints the release alone
# BOLT-CLI-2
law version_release:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == True{} : Bool}
  {Args.version.at(rel, rev) == rel : String}

# LAW: a build with a commit prints the release, then the commit in
# parentheses
# BOLT-CLI-2
law version_commit:
  for +rel: String
  for +rev: String
  for h: {String.is_empty(rev) == False{} : Bool}
  {Args.version.at(rel, rev) == rel ++ " (" ++ rev ++ ")" : String}

# The checker (BOLT-CHK). `bolt check` runs bend on each file (BOLT-TRUST-5
# for what bend prints, bolt/lsp/report.bend for how it is read), and
# Check.out decides, from the diagnostics each file got, every line the
# command prints and its exit code; Check.run only does it (BOLT-TRUST-9).
# The laws below quantify over every list of files and every diagnostics
# each could get, and over a file bend could not be run on: exec tags its
# text (checker/bend.bend's bendcheck.exec; that the tag is honest is
# BOLT-TRUST-9), BendChecker.answer reads the tag, and a file with no check
# is an error line of its own. What they do not cover is "on the line bend
# marks": that bend's text says what Rep.parse reads is BOLT-TRUST-5, and an
# error in an import lands on line 0, so the row stays pending.

# the line for an error bend reported at a 0-based line of a file: the
# path, the line counted from 1, column 1, and the message
def chk_line(path: String, dd: Rep.Diag) -> String:
  Rep.Diag{line, msg} = dd
  path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":1: error: " ++ Check.message(msg)

# one file's error lines, in the order bend reported them, onto more
def chk_file(ds: List<&2, Rep.Diag>, +path: String, more: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      more
    case Con{dd, rest}:
      chk_line(path, dd) <> chk_file(rest, path, more)

# every file's error lines, file by file in the order given
def chk_lines(runs: List<&2, Check.Run>) -> List<&2, String>:
  match runs:
    case Nil{}:
      []
    case Con{Check.Run{path, ds}, rest}:
      chk_file(ds, path, chk_lines(rest))
    case Con{Check.Failed{path}, rest}:
      (path ++ ":1:1: error: could not run bend") <> chk_lines(rest)

# how many errors bend reported, over every file, and one for each file
# bend could not be run on
def chk_count(runs: List<&2, Check.Run>) -> Nat:
  match runs:
    case Nil{}:
      0n
    case Con{Check.Run{_path, ds}, rest}:
      Nat.add(List.length(&2, Rep.Diag, ds), chk_count(rest))
    case Con{Check.Failed{_path}, rest}:
      1n+chk_count(rest)

# LAW: `bolt check` prints, for each file in turn, one line per error bend
# reported, in bend's order, on the line bend marked, and for a file bend
# could not be run on, `path:1:1: error: could not run bend`
# BOLT-CHK-1
law check_lines:
  for runs: List<&2, Check.Run>
  {Check.lines_of(runs) == chk_lines(runs) : List<&2, String>}

# LAW: there are exactly as many error lines as errors, a file bend could
# not be run on counting as one
# BOLT-CHK-1
law check_one_each:
  for runs: List<&2, Check.Run>
  {List.length(&2, String, Check.lines_of(runs)) == chk_count(runs) : Nat}

# LAW: with no error in any file, `bolt check` prints `clean` alone and
# exits 0
# BOLT-CHK-1
law check_clean:
  for +runs: List<&2, Check.Run>
  for h: {chk_count(runs) == 0n : Nat}
  {Check.out(runs) == Check.Out{["clean"], 0} : Check.Out}

# LAW: with one error, `bolt check` prints its line, then `1 error`, and
# exits 1
# BOLT-CHK-1
law check_one:
  for +runs: List<&2, Check.Run>
  for h: {chk_count(runs) == 1n : Nat}
  {Check.out(runs) == Check.Out{List.append(&2, String, chk_lines(runs), ["1 error, 0 warnings"]), 1} : Check.Out}

# LAW: with more errors, `bolt check` prints their lines, then the count,
# and exits 1
# BOLT-CHK-1
law check_many:
  for +runs: List<&2, Check.Run>
  for +more: Nat
  for h: {chk_count(runs) == 2n+more : Nat}
  {Check.out(runs)
    == Check.Out{List.append(&2, String, chk_lines(runs),
      [U32.show(U32.from_nat(2n+more)) ++ " errors, 0 warnings"]), 1} : Check.Out}

# an Out's exit code
def chk_code(oo: Check.Out) -> U32:
  Check.Out{_lines, code} = oo
  code

# LAW: a file bend could not be run on is an error: whatever the other files
# got, `bolt check` exits 1
# BOLT-CHK-1
law check_unrun_error:
  for +path: String
  for +runs: List<&2, Check.Run>
  {chk_code(Check.out(Check.Failed{path} <> runs)) == 1 : U32}

# LAW: a file's run is the checker's diagnostics for it
# BOLT-CHK-1
law check_run_of:
  for +path: String
  for ds: List<&2, Rep.Diag>
  {Check.run_of(path, Checker.Checked{ds}) == Check.Run{path, ds} : Check.Run}

# LAW: a checker that could not run bend gives a failed run, never a clean one
# BOLT-CHK-1
law check_run_unrun:
  for +path: String
  {Check.run_of(path, Checker.Unrun{}) == Check.Failed{path} : Check.Run}

# LAW: when bend ran and exited, however it exited, the checker's answer is
# what it printed read as diagnostics, as it was before exec tagged its text
# BOLT-CHK-1
law check_exec_ran:
  for text: String
  {BendChecker.answer("r" ++ text) == Checker.Checked{Rep.parse(text)} : Checker.Answer}

# LAW: when bend could not be run (no pipe, no fork, or exit 127), the answer
# is Unrun, whatever was printed
# BOLT-CHK-1
law check_exec_unrun:
  for text: String
  {BendChecker.answer("x" ++ text) == Checker.Unrun{} : Checker.Answer}

# LAW: when a signal killed bend before it reported an error, the answer is
# Unrun, not clean
# BOLT-CHK-1
law check_exec_died:
  for +text: String
  for h: {Rep.parse(text) == [] : List<&2, Rep.Diag>}
  {BendChecker.answer("s" ++ text) == Checker.Unrun{} : Checker.Answer}

# LAW: when a signal killed bend after it reported errors, the answer is
# those errors
# BOLT-CHK-1
law check_exec_died_reported:
  for +text: String
  for dd: Rep.Diag
  for ds: List<&2, Rep.Diag>
  for h: {Rep.parse(text) == dd <> ds : List<&2, Rep.Diag>}
  {BendChecker.answer("s" ++ text) == Checker.Checked{dd <> ds} : Checker.Answer}

# LAW: any other text from exec, the empty text included, is Unrun: text
# with no tag is never read as a clean check
# BOLT-CHK-1
law check_exec_untagged:
  for +cc: Char
  for text: String
  for h: {Bool.or(Char.is_eq(cc, 'r'), Char.is_eq(cc, 's')) == False{} : Bool}
  {BendChecker.answer(SCon{cc, text}) == Checker.Unrun{} : Checker.Answer}

# LAW: a LAWS.bend whose PROOF.bend bend could not be run on is not settled
# clean: its answer is Unrun
# BOLT-CHK-1
law check_proof_unrun:
  for ds: List<&2, Rep.Diag>
  {BendChecker.proved(Checker.Unrun{}, ds) == Checker.Unrun{} : Checker.Answer}
