import Base
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../src/src.bend as Src
import ./defs/ScopeWalkFiles.bend as D1

# LAW: `coverage` sees the digests of one package's files at a time, and
# `unsafe` sees every file's
law packages_scoped:
  for +srcs: List<&2, Src.Src>
  for +rs: List<&2, String>
  {Rules.project(srcs, rs) == D1.packed(srcs, rs) : List<&2, F.Finding>}
