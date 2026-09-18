# lint/rules: every rule, run over a file. A rule is a module under rules/
# with `check(path, text) -> List<Finding>`; adding one is adding it here.
import Base
import ./finding.bend as F
import ./rules/doc.bend as Doc
import ./rules/unused.bend as Unused
import ./rules/shadow.bend as Shadow
import ./rules/hole.bend as Hole
import ./rules/space.bend as Space

# every rule's findings on a file
def all(+path: String, +text: String) -> List<&2, F.Finding>:
  List.concat(&2, F.Finding, [
    Doc.check(path, text),
    Unused.check(path, text),
    Shadow.check(path, text),
    Hole.check(path, text),
    Space.check(path, text)])
