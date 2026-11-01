# When `.` is the only package root and the run holds a file, the project
# rules' findings are those of `coverage` over the digests of every file in
# the run: a repo with one package is linted as it was before packages.
import Base
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../src/src.bend as Src
import ../src/role.bend as Role
import ../src/rules/digest.bend as Digest
import ../src/rules/laws/law.bend as Law

# LAW: when `.` is the only package root and the run holds a file, the
# project findings are coverage over every file's digest: a repo with one
# package is linted as before
law one_package:
  for +s: Src.Src
  for +ss: List<&2, Src.Src>
  {Rules.project(s <> ss, [])
    == List.concat(&2, F.Finding, [Law.check(Digest.all.role(Role.marks(s <> ss), s <> ss)), []])
    : List<&2, F.Finding>}
