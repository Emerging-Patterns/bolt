# bolt/rules: every rule, and its group. A rule is a module under rules/
# with `check(path, text) -> List<Finding>`, run over each file; a project
# rule has `check(files) -> List<Finding>` and sees every file at once.
# Adding one is adding it here, and to `group`. The groups are what a
# bolt.bend switches at once: correctness (what will fail or blow up),
# suspicious (what is probably a slip), style, and laws.
import Base
import ./finding.bend as F
import ./file.bend as File
import ./config.bend as Config
import ./rules/doc.bend as Doc
import ./rules/unused.bend as Unused
import ./rules/shadow.bend as Shadow
import ./rules/hole.bend as Hole
import ./rules/space.bend as Space
import ./rules/pick.bend as Pick
import ./rules/law.bend as Law

# every rule's findings on a file
def all(+path: String, +text: String) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [
    Doc.check(path, text),
    Unused.check(path, text),
    Shadow.check(path, text),
    Hole.check(path, text),
    Space.check(path, text),
    Pick.check(path, text)])

# every project rule's findings on the files
def project(files: List<&2, File.File>) -> List<&2, F.Finding>:
  Law.check(files)

# the group a rule is in
def group(+rule: String) -> String:
  Bool.pick(String, List.contains(~String, ~String.eq, ["shadow", "hole", "pick"], rule), "correctness",
    Bool.pick(String, List.contains(~String, ~String.eq, ["unused"], rule), "suspicious",
      Bool.pick(String, List.contains(~String, ~String.eq, ["doc", "space"], rule), "style",
        Bool.pick(String, String.eq(rule, "law"), "laws", "correctness"))))

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
