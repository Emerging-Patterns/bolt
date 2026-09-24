# bolt/rules: every rule, and its group. A rule is a module under
# rules/<group>/ with `check(src) -> List<Finding>`, run over each file read
# once (bolt/src.bend); a project rule has `check(ds) -> List<Finding>` and
# sees every file at once, as the digests of rules/digest.bend. The directory
# names the group, and codes.bend says it again for the config.
# Adding one is adding it here and a row in codes.bend. One rule is not
# listed here, `noqa` (rules/style/noqa.bend): it reads the other rules'
# graded findings, so the planner runs it after them (lint/plan.bend).
# The groups are what a bolt.bend switches at once: correctness (what will
# fail or blow up), suspicious (what is probably a slip), style, laws, and
# pedantic (advice that is noisy on idiomatic code: off unless a project
# asks for it).
import Base
import ./finding.bend as F
import ./codes.bend as Codes
import ./src.bend as Src
import ./rules/digest.bend as Digest
import ./config.bend as Config
import ./rules/style/doc.bend as Doc
import ./rules/suspicious/unused.bend as Unused
import ./rules/correctness/hole.bend as Hole
import ./rules/style/space.bend as Space
import ./rules/style/wrap.bend as Wrap
import ./rules/style/param.bend as Param
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
import ./rules/correctness/put.bend as Put
import ./rules/correctness/escape.bend as Escape
import ./rules/correctness/strings.bend as Strings
import ./rules/correctness/chars.bend as Chars
import ./rules/correctness/twice.bend as Twice
import ./rules/correctness/arms.bend as Arms
import ./rules/correctness/foreign.bend as Foreign
import ./rules/suspicious/fuel.bend as Fuel
import ./rules/laws/closed.bend as Closed
import ./rules/laws/trace.bend as Trace
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

# every rule's findings on a file read once, as each rule gives them
def on.rules(+ss: Src.Src) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [
    Doc.check(ss),
    Unused.check(ss),
    Hole.check(ss),
    Space.check(ss),
    Wrap.check(ss),
    Param.check(ss),
    Pick.check(ss),
    Strict.check(ss),
    Eager.check(ss),
    Tail.check(ss),
    Concat.check(ss),
    Index.check(ss),
    Table.check(ss),
    Hoist.check(ss),
    Ring.check(ss),
    Rewalk.check(ss),
    Unit.check(ss),
    Put.check(ss),
    Escape.check(ss),
    Strings.check(ss),
    Chars.check(ss),
    Twice.check(ss),
    Arms.check(ss),
    Foreign.check(ss),
    Fuel.check(ss),
    Closed.check(ss)])

# every rule's findings on a file read once, each at that file
def on(+ss: Src.Src) -> List<&2, F.Finding>:
  on.at(on.path(ss), on.rules(ss))

# every rule's findings on a file
def all(+path: String, +text: String) -> List<&2, F.Finding>:
  on(Src.of(path, text))

# every project rule's findings on the files and SPEC.md's text (None when
# there is none): each file is read down to its digest once
# (rules/digest.bend), and the rules run over those
def project(srcs: List<&2, Src.Src>, whole: Bool, spec: Maybe<&2, String>) -> List<&2, F.Finding>:
  +ds = Digest.all(srcs)
  List.concat(&2, F.Finding, [Law.check(ds), Unsafe.check(ds), Trace.check(whole, spec, ds)])

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
