# lint/rules: every rule. A rule is a module under rules/ with
# `check(path, text) -> List<Finding>`, run over each file; a project rule
# has `check(files) -> List<Finding>` and sees every file at once. Adding one
# is adding it here.
import Base
import ./finding.bend as F
import ./file.bend as File
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
