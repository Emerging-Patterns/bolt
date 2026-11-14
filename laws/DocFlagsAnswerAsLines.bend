# `doc` asks, for each item, whether a comment block ends right above its
# line. It reads the answer from flags taken in one pass down the file's
# lines, where it used to read the lines from the top for every item. The
# flags answer as that reading does, for any lines and any line asked, so
# the rule with them finds what the rule without them finds
# (laws/DocReportsUndocumentedItems.bend states what that is).
import Base
import ../src/finding.bend as F
import ../src/syntax/outline.bend as Outline
import ../src/rules/style/doc.bend as Doc

# LAW: the flags of any lines say a comment block ends right above a line
# exactly when reading those lines down to it says so
law flags_answer:
  for +lines: List<&2, String>
  for +n: U32
  {Doc.above.at(Doc.flags(lines), n) == Doc.check.above(lines, n) : Bool}

# LAW: doc over the flags of the lines finds what doc over the lines finds
law fast_is_go:
  for items: List<&2, Outline.Item>
  for +path: String
  for +lines: List<&2, String>
  {Doc.check.fast(items, path, Doc.flags(lines)) == Doc.check.go(items, path, lines) : List<&2, F.Finding>}
