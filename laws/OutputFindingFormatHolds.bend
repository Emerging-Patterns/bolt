# A finding prints as `path:line:col: level: CODE: message`, 1-based. The
# level prints as `warning` or `error` (and `off`, which grading drops).
import Base
import ../src/config.bend as Config
import ../src/finding.bend as F
import ../src/codes.bend as Codes

# the word for each level, as law vocabulary
def level.word(ll: Config.Level) -> String:
  match ll:
    case Config.Off{}:
      "off"
    case Config.Warn{}:
      "warning"
    case Config.Error{}:
      "error"

# LAW: each level prints as its own word
law level_words:
  for ll: Config.Level
  {Config.show(ll) == level.word(ll) : String}

# LAW: a graded finding prints as `path:line:col: level: CODE: message`, line
# and column counted from 1, the level as the config shows it and the code
# the table's for the finding's rule
law shown:
  for path: String
  for line: U32
  for col: U32
  for len: U32
  for rule: String
  for msg: String
  for level: Config.Level
  {F.show_graded(F.Graded{level, F.Finding{path, line, col, len, rule, msg}})
    == path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":" ++ U32.show((col + 1 : U32)) ++ ": "
      ++ Config.show(level) ++ ": " ++ Codes.code(rule) ++ ": " ++ msg : String}
