# proofs of laws/ConfigGradingDropsOff.bend
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/rules.bend as Rules
import ../laws/ConfigGradingDropsOff.bend as Laws
import ../laws/defs/GradingKeepsFindings.bend as D1
import ./lemmas/GradeStepAgrees.bend as M1

def Laws.graded_keeps(cfg, fs):
  match fs:
    case Nil{}:
      {==}
    case Con{F.Finding{path, line, col, len, +rule, msg}, rest}:
      M1.grade.step(Config.level(cfg, Rules.group(rule), rule), F.Finding{path, line, col, len, rule, msg},
        Rules.graded(cfg, rest), D1.kept(cfg, rest), Laws.graded_keeps(cfg, rest))
