# bolt/rules: every rule, and its group. A rule is a module under
# rules/<group>/ with `check(src) -> List<Finding>`, run over each file read
# once (bolt/src.bend); a project rule has `check(ds) -> List<Finding>` and
# sees every file at once, as the digests of rules/digest.bend. The directory
# names the group, and `group` below says it again for the config.
# Adding one is adding it here, and to `group`. The groups are what a
# bolt.bend switches at once: correctness (what will fail or blow up),
# suspicious (what is probably a slip), style, laws, and pedantic (advice
# that is noisy on idiomatic code: off unless a project asks for it).
import Base
import ./finding.bend as F
import ./src.bend as Src
import ./rules/digest.bend as Digest
import ./config.bend as Config
import ./rules/style/doc.bend as Doc
import ./rules/suspicious/unused.bend as Unused
import ./rules/correctness/shadow.bend as Shadow
import ./rules/correctness/hole.bend as Hole
import ./rules/style/space.bend as Space
import ./rules/correctness/pick.bend as Pick
import ./rules/laws/law.bend as Law
import ./rules/suspicious/strict.bend as Strict
import ./rules/suspicious/eager.bend as Eager
import ./rules/pedantic/tail.bend as Tail
import ./rules/suspicious/concat.bend as Concat
import ./rules/suspicious/index.bend as Index
import ./rules/correctness/put.bend as Put
import ./rules/correctness/escape.bend as Escape
import ./rules/suspicious/nat.bend as Nat_
import ./rules/correctness/strings.bend as Strings
import ./rules/correctness/twice.bend as Twice
import ./rules/correctness/arms.bend as Arms
import ./rules/correctness/foreign.bend as Foreign
import ./rules/suspicious/fuel.bend as Fuel
import ./rules/laws/closed.bend as Closed
import ./rules/laws/unsafe.bend as Unsafe

# every rule's findings on a file read once
def on(+s: Src.Src) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [
    Doc.check(s),
    Unused.check(s),
    Shadow.check(s),
    Hole.check(s),
    Space.check(s),
    Pick.check(s),
    Strict.check(s),
    Eager.check(s),
    Tail.check(s),
    Concat.check(s),
    Index.check(s),
    Put.check(s),
    Escape.check(s),
    Nat_.check(s),
    Strings.check(s),
    Twice.check(s),
    Arms.check(s),
    Foreign.check(s),
    Fuel.check(s),
    Closed.check(s)])

# every rule's findings on a file
def all(+path: String, +text: String) -> List<&2, F.Finding>:
  on(Src.of(path, text))

# every project rule's findings on the files: each file is read down to its
# digest once (rules/digest.bend), and the rules run over those
def project(srcs: List<&2, Src.Src>) -> List<&2, F.Finding>:
  +ds = Digest.all(srcs)
  List.concat(&2, F.Finding, [Law.check(ds), Unsafe.check(ds)])

# the group a rule is in
def group(+rule: String) -> String:
  Bool.pick(String, List.contains(~String, ~String.eq,
      ["shadow", "hole", "pick", "put", "arms", "escape", "twice", "strings", "foreign"], rule), "correctness",
    Bool.pick(String, List.contains(~String, ~String.eq,
        ["unused", "strict", "eager", "concat", "nat", "fuel", "index"], rule), "suspicious",
      Bool.pick(String, List.contains(~String, ~String.eq, ["doc", "space"], rule), "style",
        Bool.pick(String, List.contains(~String, ~String.eq, ["law", "closed", "unsafe"], rule), "laws",
          Bool.pick(String, String.eq(rule, "tail"), "pedantic", "correctness")))))

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
