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
import ./rules/style/reach.bend as Reach
import ./rules/style/size.bend as Size
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
import ./rules/suspicious/idle.bend as Idle
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
def on.path(s: Src.Src) -> String:
  Src.Src{path, _text, _toks, _tree, _bound, _items} = s
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
  WReach{max: U32}
  WSize{dim: Size.Dim, max: U32}
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
  WIdle{}
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
# law or proof file changes (doc, hole, reach, fromrev, prefix, empty, blank,
# closed) read the role, never the path, and the cost rules check nothing in
# a law or proof file
def on.run(w: Which, +role: Role.Role, +src: Src.Src) -> List<&2, F.Finding>:
  match w:
    case WDoc{}:
      Doc.check.role(role, src)
    case WUnused{}:
      Unused.check(src)
    case WHole{}:
      Hole.check.role(role, src)
    case WSpace{}:
      Space.check(src)
    case WWrap{}:
      Wrap.check(src)
    case WReach{max}:
      Reach.check.role(role, src, max)
    case WSize{dim, max}:
      Role.skip(role, _u => Size.check(dim, src, max))
    case WPick{}:
      Role.skip(role, _u => Pick.check(src))
    case WSearch{}:
      Role.skip(role, _u => Pick.search(src))
    case WStrict{}:
      Role.skip(role, _u => Strict.check(src))
    case WEager{}:
      Role.skip(role, _u => Eager.check(src))
    case WTail{}:
      Role.skip(role, _u => Tail.check(src))
    case WConcat{}:
      Role.skip(role, _u => Concat.check(src))
    case WCont{}:
      Role.skip(role, _u => Concat.cont(src))
    case WIndex{}:
      Role.skip(role, _u => Index.check(src))
    case WRewalk{}:
      Role.skip(role, _u => Rewalk.check(src))
    case WThunk{}:
      Role.skip(role, _u => Thunk.check(src))
    case WIdle{}:
      Role.skip(role, _u => Idle.check(src))
    case WFromrev{}:
      Fromrev.check.role(role, src)
    case WPrefix{}:
      Prefix.check.role(role, src)
    case WEmpty{}:
      Empty.check.role(role, src)
    case WBlank{}:
      Blank.check.role(role, src)
    case WPut{}:
      Put.check(src)
    case WEscape{}:
      Escape.check(src)
    case WStrings{}:
      Strings.check(src)
    case WChars{}:
      Chars.check(src)
    case WArms{}:
      Arms.check(src)
    case WCover{}:
      Arms.cover(src)
    case WForeign{}:
      Foreign.check(src)
    case WFuel{}:
      Fuel.check(src)
    case WClosed{}:
      Closed.check.role(role, src)
    case WTranscong{}:
      Transcong.check(src)

# every per-file rule's entry, in the order their findings come
def on.table() -> List<&2, Run>:
  [
    Run{"doc", WDoc{}},
    Run{"unused", WUnused{}},
    Run{"hole", WHole{}},
    Run{"space", WSpace{}},
    Run{"wrap", WWrap{}},
    Run{"reach", WReach{Reach.limit()}},
    Run{"arity", WSize{Size.DArity{}, Size.limit(Size.DArity{})}},
    Run{"length", WSize{Size.DLength{}, Size.limit(Size.DLength{})}},
    Run{"depth", WSize{Size.DDepth{}, Size.limit(Size.DDepth{})}},
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
    Run{"idle", WIdle{}},
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
def on.all(rs: List<&2, Run>, +r: Role.Role, +s: Src.Src) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Run{+slug, w}, rest}:
      List.append(&2, F.Finding, on.slug(slug, on.run(w, r, s)), on.all(rest, r, s))

# a check at the limit a config sets for its rule (`def reach_max()`,
# `def arity_max()` in a bolt.bend); a check with no limit, or one the config does not set, is as
# it was
def on.tune(cfg: Config.Config, w: Which) -> Which:
  match w:
    case WReach{max}:
      WReach{Config.limit(cfg, "reach_max", max)}
    case WSize{+dim, max}:
      WSize{dim, Config.limit(cfg, Size.limit_name(dim), max)}
    case other:
      other

# every entry of a table, each check at the limit a config sets
def on.tuned(rs: List<&2, Run>, +cfg: Config.Config) -> List<&2, Run>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Run{slug, w}, rest}:
      Run{slug, on.tune(cfg, w)} <> on.tuned(rest, cfg)

# every per-file rule's findings on a file, told its role, each rule at the
# limit the file's config sets
def on.rules.role(+cfg: Config.Config, +r: Role.Role, +s: Src.Src) -> List<&2, F.Finding>:
  on.all(on.tuned(on.table(), cfg), r, s)

# every rule's findings on a file read once, told its role and at its
# config's limits, each at that file
def on.role(+cfg: Config.Config, +r: Role.Role, +s: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(s), on.rules.role(cfg, r, s))

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

# every project rule's findings on the files' digests and the package roots
# but `.` (each a directory as Digest.dir names one): `coverage` runs on each
# package's files, `.` first
def project.digests(+ds: List<&2, Digest.Digest>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [Law.check(members(ds, rs, "")), covers(rs, ds, rs)])

# every project rule's findings on the files and the package roots but `.`:
# each file is read down to its digest once (rules/digest.bend), told its
# role among the files' own marks
def project(+srcs: List<&2, Src.Src>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  project.digests(Digest.all.role(Role.marks(srcs), srcs), rs)

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
def on.gate(off: Bool, slug: String, w: Which, r: Role.Role, s: Src.Src) -> List<&2, F.Finding>:
  match off:
    case True{}:
      Nil{}
    case False{}:
      on.slug(slug, on.run(w, r, s))

# every entry of a table a config does not set off, run on a file, in order.
# Grading drops an off rule's findings, so not running it changes nothing
# graded (laws/OffRulesAreNotRun.bend), and the rules off by default
# (pedantic, the opt-in ones) were a tenth to a sixth of a run
def on.live(rs: List<&2, Run>, +cfg: Config.Config, +r: Role.Role, +s: Src.Src) -> List<&2, F.Finding>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{Run{+slug, w}, rest}:
      List.append(&2, F.Finding, on.gate(on.off(cfg, slug), slug, w, r, s), on.live(rest, cfg, r, s))

# the findings on a file of every rule its config does not set off, each at
# that file
def on.role.live(+cfg: Config.Config, +r: Role.Role, +s: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(s), on.live(on.tuned(on.table(), cfg), cfg, r, s))
