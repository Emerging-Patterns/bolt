# proofs of laws/OutputUnreadablePathReported.bend
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/lint/world.bend as W
import ../src/lint/plan.bend as Plan
import ../laws/OutputUnreadablePathReported.bend as Laws
import ./lemmas/GradeStepAgrees.bend as M1

def Laws.unread_one_finding(world, path, ps, h):
  e = Equal.sym(Maybe<&2, W.Answer>, W.answer(world, W.Contents{path}), Some{W.Unread{}}, h)
  %e : {Plan.unread(Plan.Got{path, W.text.got(_)} <> Plan.gots(ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}
  {==}

def Laws.directory_one_finding(world, path, ps, h):
  e = Equal.sym(Maybe<&2, W.Answer>, W.answer(world, W.Contents{path}), Some{W.Directory{}}, h)
  %e : {Plan.unread(Plan.Got{path, W.text.got(_)} <> Plan.gots(ps, world))
    == F.Finding{path, 0, 0, 0, "read", "Cannot read this file."} <> Plan.unread(Plan.gots(ps, world))
    : List<&2, F.Finding>}
  {==}

def Laws.read_is_correctness(cfg, path, line, col, len, msg):
  M1.grade.step(Config.level(cfg, "correctness", "read"), F.Finding{path, line, col, len, "read", msg}, [], [], {==})
