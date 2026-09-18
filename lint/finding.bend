# lint/finding: what a rule reports. Shown as `path:line:col: rule: message`
# (line and col 1-based, as editors count), so a terminal can jump to it.
import Base

# where, which rule, what
type Finding is Data:
  Finding{path: String, line: U32, col: U32, rule: String, msg: String}

# one line, `path:line:col: rule: message`
def show(f: Finding) -> String:
  Finding{path, line, col, rule, msg} = f
  path ++ ":" ++ U32.show((line + 1 : U32)) ++ ":" ++ U32.show((col + 1 : U32)) ++ ": " ++ rule ++ ": " ++ msg

# every finding as a line
def show_all(fs: List<&2, Finding>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      show(f) <> show_all(t)
