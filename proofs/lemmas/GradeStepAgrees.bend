# one finding graded the planner's way agrees with the spec's grading
import Base
import ../../src/config.bend as Config
import ../../src/finding.bend as F
import ../../laws/defs/GradingKeepsFindings.bend as D1

# one finding graded the way the rest were: grading's pick agrees with keep
law grade.step:
  for l: Config.Level
  for -f: F.Finding
  for -a: List<&2, F.Graded>
  for -b: List<&2, F.Graded>
  for e: {a == b : List<&2, F.Graded>}
  {Bool.pick(List<&2, F.Graded>, Config.is_off(l), a, F.Graded{l, f} <> a)
    == D1.keep(l, f, b) : List<&2, F.Graded>}

def grade.step(l, f, a, _b, e):
  match l:
    case Config.Off{}:
      e
    case Config.Warn{}:
      %e : {F.Graded{Config.Warn{}, f} <> a == F.Graded{Config.Warn{}, f} <> _ : List<&2, F.Graded>}
      {==}
    case Config.Error{}:
      %e : {F.Graded{Config.Error{}, f} <> a == F.Graded{Config.Error{}, f} <> _ : List<&2, F.Graded>}
      {==}
