# bolt/finding: what a rule reports. Shown as `path:line:col: level: CODE:
# message` (line and col 1-based, as editors count; CODE is the stable id in
# bolt/codes.bend), so a terminal can jump to it; an editor gets it as a
# diagnostic over `len` characters from the column (0: to the end of the
# line), with that code and source `bolt(group:slug)`. The level is the
# project's (bolt.bend), not the rule's: a rule only finds. `rule` on a
# finding is still the slug.
import Base
import ./config.bend as Config
import ./codes.bend as Codes

# where (and how far), which rule, what
type Finding is Data:
  Finding{path: String, line: U32, col: U32, len: U32, rule: String, msg: String}

# one line, `path:line:col: CODE: message`
def show(ff: Finding) -> String:
  Finding{path, line, col, len, rule, msg} = ff
  path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":" ++ U32.show((col + 1 : U32)) ++ ": " ++ Codes.code(rule) ++ ": " ++ msg

# a finding at the level the project set for its rule
type Graded is Data:
  Graded{level: Config.Level, finding: Finding}

# one line, `path:line:col: level: CODE: message`
def show_graded(gg: Graded) -> String:
  Graded{level, Finding{path, line, col, len, rule, msg}} = gg
  path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":" ++ U32.show((col + 1 : U32)) ++ ": " ++ Config.show(level) ++ ": "
    ++ Codes.code(rule) ++ ": " ++ msg

# every finding as a line
def show_all(fs: List<&2, Finding>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      show(f) <> show_all(t)
