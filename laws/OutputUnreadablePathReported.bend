# A path that cannot be read is a `read` finding graded with correctness.
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ./defs/GradingKeepsFindings.bend as D1

# LAW: a source the World answers as unreadable is one `read` finding at its
# path, in its place among the read failures
law unread_one_finding:
  for +world: W.World
  for +path: String
  for ps: List<&2, String>
  for h: {W.answer(world, W.Contents{path}) == Some{W.Unread{}} : Maybe<&2, W.Answer>}
  {Plan.unread(Plan.gots(path <> ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}

# LAW: a path the World answers as a directory is one `read` finding at its
# path, in its place among the read failures, as an unreadable file is: a
# directory named on the command line has no text to lint
law directory_one_finding:
  for +world: W.World
  for +path: String
  for ps: List<&2, String>
  for h: {W.answer(world, W.Contents{path}) == Some{W.Directory{}} : Maybe<&2, W.Answer>}
  {Plan.unread(Plan.gots(path <> ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}

# LAW: a `read` finding is graded with correctness: whatever the config, its
# level is the one correctness gives the rule `read`
law read_is_correctness:
  for +cfg: Config.Config
  for path: String
  for line: U32
  for col: U32
  for len: U32
  for msg: String
  {Rules.graded(cfg, [F.Finding{path, line, col, len, "read", msg}])
    == D1.keep(Config.level(cfg, "correctness", "read"), F.Finding{path, line, col, len, "read", msg}, [])
    : List<&2, F.Graded>}
