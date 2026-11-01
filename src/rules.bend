# src/rules: every rule, and its group. A rule is a module under
# rules/<group>/ with `check(src) -> List<Finding>`, run over each file read
# once (src/src.bend); a project rule has `check(ds) -> List<Finding>` and
# sees many files at once, as the digests of rules/digest.bend: `coverage`
# one package's files, `unsafe` every file (`project` below). The directory
# names the group, and codes.bend says it again for the config.
# Adding one is adding it here and a row in codes.bend. One rule is not
# listed here, `noqa` (rules/style/noqa.bend): it reads the other rules'
# graded findings, so the planner runs it after them (lint/plan.bend). Nor
# is `setting` (rules/correctness/setting.bend): it reads each bolt.bend that
# grades the run, not a source, so the planner runs it between the per-file
# and the project rules.
# The groups are what a bolt.bend switches at once: correctness (what will
# fail or blow up), suspicious (what is probably a slip), style, laws, and
# pedantic (advice that is noisy on idiomatic code: off unless a project
# asks for it).
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
import ./rules/suspicious/strict.bend as Strict
import ./rules/suspicious/eager.bend as Eager
import ./rules/pedantic/tail.bend as Tail
import ./rules/suspicious/concat.bend as Concat
import ./rules/suspicious/index.bend as Index
import ./rules/suspicious/table.bend as Table
import ./rules/suspicious/hoist.bend as Hoist
import ./rules/suspicious/ring.bend as Ring
import ./rules/suspicious/rewalk.bend as Rewalk
import ./rules/suspicious/unit.bend as Unit
import ./rules/suspicious/scan.bend as Scan
import ./rules/suspicious/thunk.bend as Thunk
import ./rules/suspicious/fromrev.bend as Fromrev
import ./rules/suspicious/prefix.bend as Prefix
import ./rules/correctness/put.bend as Put
import ./rules/correctness/escape.bend as Escape
import ./rules/correctness/strings.bend as Strings
import ./rules/correctness/chars.bend as Chars
import ./rules/correctness/twice.bend as Twice
import ./rules/correctness/arms.bend as Arms
import ./rules/correctness/foreign.bend as Foreign
import ./rules/suspicious/fuel.bend as Fuel
import ./rules/laws/closed.bend as Closed
import ./rules/laws/unsafe.bend as Unsafe

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

# every per-file rule on a file, told its role (src/role.bend): the rules a
# law or proof file changes (doc, hole, param, scan, fromrev, prefix,
# closed) read the role, never the path, and the cost rules check nothing
# in a law or proof file
def on.rules.role(+rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [
    Doc.check.role(rr, ss),
    Unused.check(ss),
    Hole.check.role(rr, ss),
    Space.check(ss),
    Wrap.check(ss),
    Param.check.role(rr, ss),
    Role.skip(rr, _u => Pick.check(ss)),
    Role.skip(rr, _u => Pick.search(ss)),
    Role.skip(rr, _u => Strict.check(ss)),
    Role.skip(rr, _u => Eager.check(ss)),
    Role.skip(rr, _u => Tail.check(ss)),
    Role.skip(rr, _u => Concat.check(ss)),
    Role.skip(rr, _u => Concat.cont(ss)),
    Role.skip(rr, _u => Index.check(ss)),
    Role.skip(rr, _u => Table.check(ss)),
    Role.skip(rr, _u => Hoist.check(ss)),
    Role.skip(rr, _u => Ring.check(ss)),
    Role.skip(rr, _u => Rewalk.check(ss)),
    Role.skip(rr, _u => Unit.check(ss)),
    Scan.check.role(rr, ss),
    Role.skip(rr, _u => Thunk.check(ss)),
    Fromrev.check.role(rr, ss),
    Prefix.check.role(rr, ss),
    Put.check(ss),
    Escape.check(ss),
    Strings.check(ss),
    Chars.check(ss),
    Twice.check(ss),
    Arms.check(ss),
    Foreign.check(ss),
    Fuel.check(ss),
    Closed.check.role(rr, ss),
    Transcong.check(ss)])

# every rule's findings on a file read once, as each rule gives them, its
# role read from its name
def on.rules(+ss: Src.Src) -> List<&2, F.Finding>:
  on.rules.role(Role.of_path(on.path(ss)), ss)

# every rule's findings on a file read once, each at that file
def on(+ss: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(ss), on.rules(ss))

# every rule's findings on a file read once, told its role, each at that file
def on.role(+rr: Role.Role, +ss: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(ss), on.rules.role(rr, ss))

# every rule's findings on a file
def all(+path: String, +text: String) -> List<&2, F.Finding>:
  on(Src.of(path, text))

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
    case Con{Digest.Digest{path, norm, +dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws}, rest}:
      +more = members(rest, roots, pkg)
      Bool.pick(List<&2, Digest.Digest>, String.eq(owner(roots, dir), pkg),
        Digest.Digest{path, norm, dir, is_laws, is_law_file, exempt, tops, says, deps, unsafes, laws} <> more, more)

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
# `.` first, and `unsafe` on every file
def project(+srcs: List<&2, Src.Src>, +rs: List<&2, String>) -> List<&2, F.Finding>:
  +ds = Digest.all.role(Role.marks(srcs), srcs)
  List.concat(&2, F.Finding, [Law.check(members(ds, rs, "")), covers(rs, ds, rs), Unsafe.check(ds)])

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
