# src/rules: every rule, and its group. A rule is a module under
# rules/<group>/ with `check(src) -> List<Finding>`, run over each file read
# once (src/src.bend); a project rule has `check(ds) -> List<Finding>` and
# sees many files at once, as the digests of rules/digest.bend: `coverage`
# one package's files at a time (`project` below). The directory
# names the group, and codes.bend says it again for the config.
# Adding one is adding it here and a row in codes.bend. One rule is not
# listed here, `noqa` (rules/style/noqa.bend): it reads the other rules'
# graded findings, so the planner runs it after them (lint/plan.bend). Nor
# is `setting` (rules/correctness/setting.bend): it reads each bolt.bend that
# grades the run, not a source, so the planner runs it between the per-file
# and the project rules.
# The groups are what a bolt.bend switches at once: correctness (what will
# fail or blow up), suspicious (what is probably a slip), perf (what is
# slow but right), style, laws, and pedantic (advice that is noisy on
# idiomatic code: off unless a project asks for it).
import Base
import ./finding.bend as F
import ./codes.bend as Codes
import ./src.bend as Src
import ./role.bend as Role
import ./rules/digest.bend as Digest
import ./rules/imports.bend as Imports
import ./lazy/lazy.bend as Lazy
import ./config.bend as Config
import ./rules/style/doc.bend as Doc
import ./rules/suspicious/unused.bend as Unused
import ./rules/correctness/hole.bend as Hole
import ./rules/style/space.bend as Space
import ./rules/style/wrap.bend as Wrap
import ./rules/style/param.bend as Param
import ./rules/style/transcong.bend as Transcong
import ./rules/correctness/pick.bend as Pick
import ./rules/laws/law.bend as Law
import ./rules/pedantic/strict.bend as Strict
import ./rules/suspicious/eager.bend as Eager
import ./rules/pedantic/tail.bend as Tail
import ./rules/suspicious/concat.bend as Concat
import ./rules/pedantic/index.bend as Index
import ./rules/pedantic/rewalk.bend as Rewalk
import ./rules/suspicious/thunk.bend as Thunk
import ./rules/suspicious/fromrev.bend as Fromrev
import ./rules/suspicious/prefix.bend as Prefix
import ./rules/suspicious/empty.bend as Empty
import ./rules/style/blank.bend as Blank
import ./rules/correctness/put.bend as Put
import ./rules/correctness/escape.bend as Escape
import ./rules/perf/strings.bend as Strings
import ./rules/pedantic/chars.bend as Chars
import ./rules/correctness/arms.bend as Arms
import ./rules/pedantic/foreign.bend as Foreign
import ./rules/pedantic/fuel.bend as Fuel
import ./rules/laws/closed.bend as Closed

# the file a Src was read from
def on.path(ss: Src.Src) -> String:
  Src.Src{path, _text, _toks, _tree, _bound, _items} = ss
  path

# findings put at a path: a per-file rule reports on its own file, so this
# keeps what each rule gave and makes it hold by construction
def on.at(+path: String, fs: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{_path, line, col, len, rule, msg}, rest}:
      F.Finding{path, line, col, len, rule, msg} <> on.at(path, rest)

# which check a per-file rule's entry runs: one a check, a rule with two
# checks (pick, concat, arms) having two
type Which is Data:
  WDoc{}
  WUnused{}
  WHole{}
  WSpace{}
  WWrap{}
  WParam{}
  WPick{}
  WSearch{}
  WStrict{}
  WEager{}
  WTail{}
  WConcat{}
  WCont{}
  WIndex{}
  WRewalk{}
  WThunk{}
  WFromrev{}
  WPrefix{}
  WEmpty{}
  WBlank{}
  WPut{}
  WEscape{}
  WStrings{}
  WChars{}
  WArms{}
  WCover{}
  WForeign{}
  WFuel{}
  WClosed{}
  WTranscong{}

# one per-file rule of the list: its slug, and the check to run
type Run is Data:
  Run{slug: String, which: Which}

# a check's findings on a file, told its role (src/role.bend): the rules a
# law or proof file changes (doc, hole, param, fromrev, prefix, empty, blank,
# closed) read the role, never the path, and the cost rules check nothing in
# a law or proof file
def on.run(ww: Which, +rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  match ww:
    case WDoc{}:
      Doc.check.role(rr, ss)
    case WUnused{}:
      Unused.check(ss)
    case WHole{}:
      Hole.check.role(rr, ss)
    case WSpace{}:
      Space.check(ss)
    case WWrap{}:
      Wrap.check(ss)
    case WParam{}:
      Param.check.role(rr, ss)
    case WPick{}:
      Role.skip(rr, _u => Pick.check(ss))
    case WSearch{}:
      Role.skip(rr, _u => Pick.search(ss))
    case WStrict{}:
      Role.skip(rr, _u => Strict.check(ss))
    case WEager{}:
      Role.skip(rr, _u => Eager.check(ss))
    case WTail{}:
      Role.skip(rr, _u => Tail.check(ss))
    case WConcat{}:
      Role.skip(rr, _u => Concat.check(ss))
    case WCont{}:
      Role.skip(rr, _u => Concat.cont(ss))
    case WIndex{}:
      Role.skip(rr, _u => Index.check(ss))
    case WRewalk{}:
      Role.skip(rr, _u => Rewalk.check(ss))
    case WThunk{}:
      Role.skip(rr, _u => Thunk.check(ss))
    case WFromrev{}:
      Fromrev.check.role(rr, ss)
    case WPrefix{}:
      Prefix.check.role(rr, ss)
    case WEmpty{}:
      Empty.check.role(rr, ss)
    case WBlank{}:
      Blank.check.role(rr, ss)
    case WPut{}:
      Put.check(ss)
    case WEscape{}:
      Escape.check(ss)
    case WStrings{}:
      Strings.check(ss)
    case WChars{}:
      Chars.check(ss)
    case WArms{}:
      Arms.check(ss)
    case WCover{}:
      Arms.cover(ss)
    case WForeign{}:
      Foreign.check(ss)
    case WFuel{}:
      Fuel.check(ss)
    case WClosed{}:
      Closed.check.role(rr, ss)
    case WTranscong{}:
      Transcong.check(ss)

# every per-file rule's entry, in the order their findings come
def on.table() -> List<&2, Run>:
  [
    Run{"doc", WDoc{}},
    Run{"unused", WUnused{}},
    Run{"hole", WHole{}},
    Run{"space", WSpace{}},
    Run{"wrap", WWrap{}},
    Run{"param", WParam{}},
    Run{"pick", WPick{}},
    Run{"pick", WSearch{}},
    Run{"strict", WStrict{}},
    Run{"eager", WEager{}},
    Run{"tail", WTail{}},
    Run{"concat", WConcat{}},
    Run{"concat", WCont{}},
    Run{"index", WIndex{}},
    Run{"rewalk", WRewalk{}},
    Run{"thunk", WThunk{}},
    Run{"fromrev", WFromrev{}},
    Run{"prefix", WPrefix{}},
    Run{"empty", WEmpty{}},
    Run{"blank", WBlank{}},
    Run{"put", WPut{}},
    Run{"escape", WEscape{}},
    Run{"strings", WStrings{}},
    Run{"chars", WChars{}},
    Run{"arms", WArms{}},
    Run{"arms", WCover{}},
    Run{"foreign", WForeign{}},
    Run{"fuel", WFuel{}},
    Run{"closed", WClosed{}},
    Run{"transcong", WTranscong{}}]

# findings named for a rule: each one's `rule` is the slug, so a rule's
# findings are its own by construction, as on.at makes them its file's
def on.slug(+slug: String, fs: List<&2, F.Finding>) -> List<&2, F.Finding>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, _rule, msg}, rest}:
      F.Finding{path, line, col, len, slug, msg} <> on.slug(slug, rest)

# every entry of a table run on a file, its findings named for its rule, in
# order
def on.all(rs: List<&2, Run>, +rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Run{+slug, ww}, rest}:
      List.append(&2, F.Finding, on.slug(slug, on.run(ww, rr, ss)), on.all(rest, rr, ss))

# every per-file rule's findings on a file, told its role
def on.rules.role(+rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  on.all(on.table(), rr, ss)

# every rule's findings on a file read once, told its role, each at that file
def on.role(+rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(ss), on.rules.role(rr, ss))

# Packages (laws/ScopePackageRootsFound.bend). A package root other than `.` is a directory
# holding a main.bend; a file belongs to the nearest root at or above it, and
# `coverage` runs on each package's files alone. A directory is
# named here as Digest.dir names one: normalized, with its slash (`w3c/`),
# and `` for `.`.

# whether a directory is among the directories
def has(ds: List<&2, String>, +dd: String) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, rest}:
      Lazy.or_else(String.eq(d, dd), _u => has(rest, dd))

def ups.go(rs: List<&2, String>) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{s, +rest}:
      (String.join(List.reverse(&2, String, s <> rest), "/") ++ "/") <> ups.go(rest)

# a directory and each of its parents but ``, nearest first: `a/b/` is
# `a/b/` then `a/`
def ups(dir: String) -> List<&2, String>:
  ups.go(List.reverse(&2, String, Imports.init(String.split(dir, '/'))))

# the first of the directories that is a root, or `` (the package `.`)
def owner.go(us: List<&2, String>, +roots: List<&2, String>) -> String:
  match us:
    case Nil{}:
      ""
    case Con{+u, rest}:
      Lazy.stop(String, has(roots, u), u, _u => owner.go(rest, roots))

# the package of a file in a directory: the nearest root at or above it
def owner(+roots: List<&2, String>, dir: String) -> String:
  owner.go(ups(dir), roots)

# the files of one package, in order
def members(ds: List<&2, Digest.Digest>, +roots: List<&2, String>, +pkg: String) -> List<&2, Digest.Digest>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Digest.Digest{path, norm, +dir, is_laws, is_law_file, exempt, tops, says, deps, laws}, rest}:
      +more = members(rest, roots, pkg)
      Bool.pick(List<&2, Digest.Digest>, String.eq(owner(roots, dir), pkg),
        Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, laws} <> more, more)

# `coverage` on each package but `.`
def covers(rs: List<&2, String>, +ds: List<&2, Digest.Digest>, +roots: List<&2, String>) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+dir, rest}:
      List.append(&2, F.Finding, Law.check(members(ds, roots, dir)), covers(rest, ds, roots))

# every project rule's findings on the files and the package roots but `.`
# (each a directory as Digest.dir names one): each file is read down to its
# digest once (rules/digest.bend); `coverage` runs on each package's files,
# `.` first
def project(+srcs: List<&2, Src.Src>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  +ds = Digest.all.role(Role.marks(srcs), srcs)
  List.concat(&2, F.Finding, [Law.check(members(ds, rs, "")), covers(rs, ds, rs)])

# the group a rule is in; an unknown slug grades with correctness
def group(+rule: String) -> String:
  +named = Codes.group(rule)
  Bool.pick(String, String.is_empty(named), "correctness", named)

# the findings at the levels a config gives their rules; the ones set off
# are dropped
def graded(+cfg: Config.Config, fs: List<&2, F.Finding>) -> List<&2, F.Graded>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      +more = graded(cfg, rest)
      +l = Config.level(cfg, group(rule), rule)
      Bool.pick(List<&2, F.Graded>, Config.is_off(l), more,
        F.Graded{l, F.Finding{path, line, col, len, rule, msg}} <> more)

# is a rule off under a config?
def on.off(cfg: Config.Config, +slug: String) -> Bool:
  Config.is_off(Config.level(cfg, group(slug), slug))

# an entry's findings, named for its rule, unless the rule is off: then the
# check is not run
def on.gate(off: Bool, slug: String, ww: Which, rr: Role.Role, ss: Src.Src) -> List<&2, F.Finding>:
  match off:
    case True{}:
      Nil{}
    case False{}:
      on.slug(slug, on.run(ww, rr, ss))

# every entry of a table a config does not set off, run on a file, in order.
# Grading drops an off rule's findings, so not running it changes nothing
# graded (laws/OffRulesAreNotRun.bend), and the rules off by default
# (pedantic, the opt-in ones) were a tenth to a sixth of a run
def on.live(rs: List<&2, Run>, +cfg: Config.Config, +rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Run{+slug, ww}, rest}:
      List.append(&2, F.Finding, on.gate(on.off(cfg, slug), slug, ww, rr, ss), on.live(rest, cfg, rr, ss))

# the findings on a file of every rule its config does not set off, each at
# that file
def on.role.live(+cfg: Config.Config, +rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(ss), on.live(on.table(), cfg, rr, ss))
